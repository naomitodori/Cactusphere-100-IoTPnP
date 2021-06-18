/*
 * Copyright (c) Microsoft Corporation. All rights reserved.
 * Copyright (c) 2021 Atmark Techno, Inc.
 *
 * MIT License
 *
 * Permission is hereby granted, free of charge, to any person obtaining a copy
 * of this software and associated documentation files (the "Software"), to deal
 * in the Software without restriction, including without limitation the rights
 * to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
 * copies of the Software, and to permit persons to whom the Software is
 * furnished to do so, subject to the following conditions:
 *
 * The above copyright notice and this permission notice shall be included in
 * all copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
 * IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
 * FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
 * AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
 * LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
 * OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN
 * THE SOFTWARE.
 */

#include <signal.h>
#include <stdbool.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>
#include <stdio.h>
#include <stdarg.h>
#include <errno.h>
#include <ctype.h>
#include <getopt.h>

#include <sys/timerfd.h>

// applibs_versions.h defines the API struct versions to use for applibs APIs.
#include "applibs_versions.h"
#include <applibs/log.h>
#include <applibs/networking.h>
#include <applibs/gpio.h>
#include <applibs/storage.h>
#include <applibs/i2c.h>

#include <hw/mt3620.h>

#include "eventloop_timer_utilities.h"

// Azure IoT SDK
#include <iothub_client_core_common.h>
#include <iothub_device_client_ll.h>
#include <iothub_client_options.h>
#include <iothubtransportmqtt.h>
#include <iothub.h>
#include <azure_sphere_provisioning.h>
#include <iothub_security_factory.h>

#include <prov_security_factory.h>
#include <prov_transport_mqtt_client.h>
#include <applibs/application.h>

#include "drivers/at24c0.h"

/// <summary>
/// Exit codes for this application. These are used for the
/// application exit code.  They they must all be between zero and 255,
/// where zero is reserved for successful termination.
/// </summary>
typedef enum {
    ExitCode_Success = 0,

    ExitCode_TermHandler_SigTerm,

    ExitCode_Main_EventLoopFail,

    ExitCode_AzureTimer_Consume,
    ExitCode_WatchDogTimer_Consume,
    ExitCode_LedTimer_Consume,
    ExitCode_GpioTimer_Consume,
    ExitCode_HeartBeatTimer_Consume,

    ExitCode_Init_AzureTimer,
    ExitCode_Init_WatchDogTimer,
    ExitCode_Init_LedTimer,
    ExitCode_Init_GpioTimer,
    ExitCode_Init_HeartBeatTimer,

    ExitCode_SetUpSysEvent_EventLoop,

    ExitCode_InterfaceConnectionStatus_Failed,

    ExitCode_Validate_ConnectionType,
    ExitCode_Validate_ScopeId,
    ExitCode_Validate_IotHubHostname,
} ExitCode;

static volatile sig_atomic_t exitCode = ExitCode_Success;

#include "json.h"

#include "LibCloud.h"

#include "cactusphere_product.h"
#include "cactusphere_eeprom.h"
#include "cactusphere_error.h"

static int ct_error = 0;

// cache buffer size (telemetry data)
#define CACHE_BUF_SIZE (50 * 1024)

/// <summary>
/// Connection types to use when connecting to the Azure IoT Hub.
/// </summary>
typedef enum {
    ConnectionType_NotDefined = 0,
    ConnectionType_DPS = 1,
    ConnectionType_Direct = 2,
    ConnectionType_PnP = 3
} ConnectionType;

/// <summary>
/// Authentication state of the client with respect to the Azure IoT Hub.
/// </summary>
typedef enum {
    /// <summary>Client is not authenticated by the Azure IoT Hub.</summary>
    IoTHubClientAuthenticationState_NotAuthenticated = 0,
    /// <summary>Client has initiated authentication to the Azure IoT Hub.</summary>
    IoTHubClientAuthenticationState_AuthenticationInitiated = 1,
    /// <summary>Client is authenticated by the Azure IoT Hub.</summary>
    IoTHubClientAuthenticationState_Authenticated = 2
} IoTHubClientAuthenticationState;

/// <summary>
/// Information such as the connection status to network and the reading status of EEPROM.
/// (If even one is disabled, the Status LED will not turn on.)
/// </summary>
typedef struct {
    bool isEepromReadSuccess;
    bool isEepromDataValid;
    IoTHubClientAuthenticationState IoTHubClientAuthState; // Authentication state with respect to the Azure IoT Hub.
    bool isNetworkConnected;
    bool isPropertySettingValid;
} SphereStatus;

SphereStatus sphereStatus = {false,false,IoTHubClientAuthenticationState_NotAuthenticated,false,false};

// Azure IoT definitions.
static char *scopeId = NULL;                                      // ScopeId for DPS.
static char *hubHostName = NULL;                                  // Azure IoT Hub Hostname.
static bool isConnectionTypeInCmdArgs = false;
static ConnectionType connectionType = ConnectionType_NotDefined; // Type of connection to use.

#define dpsUrl "global.azure-devices-provisioning.net"
static PROV_DEVICE_RESULT dpsRegisterStatus = PROV_DEVICE_REG_HUB_NOT_SPECIFIED;
static char* iotHubUri = NULL;
// dtdl
#define MAX_DTDL_BUFFER_SIZE 128
static const char* azureSphereModelId = "dtmi:atmark_techno:Cactusphere:Cactusphere_Basic;1";

static IOTHUB_DEVICE_CLIENT_LL_HANDLE iothubClientHandle = NULL;
static const int keepalivePeriodSeconds = 20;
static bool iothubFirstConnected = false;
static const int deviceIdForDaaCertUsage = 1; // A constant used to direct the IoT SDK to use
                                              // the DAA cert under the hood.

// Network interface
static const char wlan_networkInterface[] = "wlan0";
static const char eth_networkInterface[] = "eth0";

static const char *GetReasonString(IOTHUB_CLIENT_CONNECTION_STATUS_REASON reason);
static const char *getAzureSphereProvisioningResultString(
    AZURE_SPHERE_PROV_RETURN_VALUE provisioningResult);
static void SetupAzureClient(void);

// Initialization/Cleanup
static ExitCode InitPeripheralsAndHandlers(void);
static void ClosePeripheralsAndHandlers(void);

// Software Watchdog
const struct itimerspec watchdogInterval = { { 300, 0 },{ 300, 0 } };
timer_t watchdogTimer;

// Status LED
typedef enum {
    LED_OFF = 0,
    LED_ON,
    LED_BLINK,
} LED_Status;
int gLedState = LED_OFF;
int ledGpioFd = -1;

// UserSW
int swGpioFd = -1;
static GPIO_Value_Type userSWState = GPIO_Value_High;

// Heartbeat
#define JSON_BUFFER_SIZE 512
static int heartBeatValue = 0;

// Timer / polling
static EventLoop *eventLoop = NULL;
static EventLoopTimer *azureTimer = NULL;
static EventLoopTimer *watchdogLoopTimer = NULL;
static EventLoopTimer *ledEventLoopTimer = NULL;
static EventLoopTimer *gpioEventLoopTimer = NULL;
static EventLoopTimer *heartbeatEventLoopTimer = NULL;

// Azure IoT poll periods
static const int AzureIoTDefaultPollPeriodSeconds = 1; // 1[s]
static const int AzureIoTMinReconnectPeriodSeconds = 60;
static const int AzureIoTMaxReconnectPeriodSeconds = 10 * 60;

static int azureIoTPollPeriodSeconds = -1;

static void AzureTimerEventHandler(EventLoopTimer *timer);
static void WatchdogEventHandler(EventLoopTimer *timer);
static void LedEventHandler(EventLoopTimer *timer);
static void GpioEventHandler(EventLoopTimer *timer);
static void HeartBeatEventHandler(EventLoopTimer *timer);
static ExitCode ValidateUserConfiguration(void);
static void ParseCommandLineArguments(int argc, char *argv[]);
static bool SetupAzureIoTHubClientWithDaa(void);
static bool SetupAzureIoTHubClientWithDps(void);
static bool SetupAzureIoTHubClientWithDpsPnP(void);
static bool ChangeLedStatus(LED_Status led_status);

typedef struct
{
    const char name[20];
    char value[20];
} EventMsgData;

eepromData eeprom;

// Usage text for command line arguments in application manifest.
static const char *cmdLineArgsUsageText =
    "DPS connection type: \"CmdArgs\": [\"--ScopeID\", \"<scope_id>\"]\n"
    "Direction connection type: \"CmdArgs\": [\"--Hostname\", \"<azureiothub_hostname>\"]\n";

/// <summary>
///     Signal handler for termination requests. This handler must be async-signal-safe.
/// </summary>
static void TerminationHandler(int signalNumber)
{
    // Don't use Log_Debug here, as it is not guaranteed to be async-signal-safe.
    exitCode = ExitCode_TermHandler_SigTerm;
}

bool IsAuthenticationDone(void)
{
    return (IoTHubClientAuthenticationState_Authenticated == sphereStatus.IoTHubClientAuthState) ? true : false;
}

void SetupWatchdog(void)
{
    struct sigevent alarmEvent;
    alarmEvent.sigev_notify = SIGEV_SIGNAL;
    alarmEvent.sigev_signo = SIGALRM;
    alarmEvent.sigev_value.sival_ptr = &watchdogTimer;

    timer_create(CLOCK_MONOTONIC, &alarmEvent, &watchdogTimer);
    timer_settime(watchdogTimer, 0, &watchdogInterval, NULL);
}

// Must be called periodically
void ExtendWatchdogExpiry(void)
{
    //check that application is operating normally
    //if so, reset the watchdog
    timer_settime(watchdogTimer, 0, &watchdogInterval, NULL);
}

/// <summary>
/// Change the LED status.
/// </summary>
/// <returns>Returns false if the LED cannot be turned on.</returns>
static bool ChangeLedStatus(LED_Status led_status)
{
    bool ret = true;
    switch (led_status)
    {
    case LED_OFF:
        gLedState = LED_OFF;
        break;
    case LED_BLINK:
        gLedState = LED_BLINK;
        break;
    case LED_ON:
        /// If even one value of "sphereStatus" is invalid, the LED cannot turn on.
        if (sphereStatus.isEepromDataValid &&
            sphereStatus.isNetworkConnected &&
            sphereStatus.isEepromReadSuccess &&
            sphereStatus.isPropertySettingValid &&
            (IoTHubClientAuthenticationState_Authenticated == sphereStatus.IoTHubClientAuthState)) {
            gLedState = LED_ON;
        }
        else {
            gLedState = LED_BLINK;
            ret = false;
        }
        break;
    default:
        ret = false;
        break;
    }
    return ret;
}

/// <summary>
///     Main entry point for this sample.
/// </summary>
int main(int argc, char *argv[])
{
    int err;
    Log_Debug("IoT Hub/Central Application starting.\n");

    // Desired property does not receive.
    sphereStatus.isPropertySettingValid = true;

    Log_Debug("Getting EEPROM information.\n");
    err = GetEepromProperty(&eeprom);
    if (err < 0) {
        ct_error = -EEPROM_READ_ERROR;
        sphereStatus.isEepromReadSuccess = false;
        ChangeLedStatus(LED_BLINK);
    }
    else {
        sphereStatus.isEepromReadSuccess = true;
    }

    static Networking_Interface_HardwareAddress ha;

    for (int i = 0; i < HARDWARE_ADDRESS_LENGTH; i++) {
        ha.address[i] = eeprom.ethernetMac[HARDWARE_ADDRESS_LENGTH - (i + 1)];
    }
    err = Networking_SetHardwareAddress("eth0", ha.address, HARDWARE_ADDRESS_LENGTH);
    if (err < 0) {
        Log_Debug("Error setting hardware address (eth0) %d\n", errno);
    }

    err = Networking_SetInterfaceState("eth0", true);
    if (err < 0) {
        Log_Debug("Error setting interface state (eth0) %d\n", errno);
    }
    ParseCommandLineArguments(argc, argv);

    exitCode = ValidateUserConfiguration();
    if (exitCode != ExitCode_Success) {
        return exitCode;
    }

    exitCode = InitPeripheralsAndHandlers();

    // Main loop
    while (exitCode == ExitCode_Success) {
        EventLoop_Run_Result result = EventLoop_Run(eventLoop, -1, true);
        // Continue if interrupted by signal, e.g. due to breakpoint being set.
        if (result == EventLoop_Run_Failed && errno != EINTR) {
            exitCode = ExitCode_Main_EventLoopFail;
        }
    }

    while(ct_error < 0) {
        // hang
        EventLoop_Run_Result result = EventLoop_Run(eventLoop, -1, true);
        // Continue if interrupted by signal, e.g. due to breakpoint being set.
        if (result == EventLoop_Run_Failed && errno != EINTR) {
            exitCode = ExitCode_Main_EventLoopFail;
        }
    }
    ClosePeripheralsAndHandlers();

    Log_Debug("Application exiting.\n");

    return exitCode;
}

/// <summary>
/// Azure timer event:  Check connection status and send telemetry
/// </summary>
static void AzureTimerEventHandler(EventLoopTimer *timer)
{
    if (ConsumeEventLoopTimerEvent(timer) != 0) {
        exitCode = ExitCode_AzureTimer_Consume;
        return;
    }

    // Check whether the device is connected to the internet.
    Networking_InterfaceConnectionStatus eth_status;
    Networking_InterfaceConnectionStatus wlan_status;
    int ret_eth_status = Networking_GetInterfaceConnectionStatus(eth_networkInterface, &eth_status);
    int ret_wlan_status = Networking_GetInterfaceConnectionStatus(wlan_networkInterface, &wlan_status);

    if ((ret_eth_status == 0 && (eth_status & Networking_InterfaceConnectionStatus_ConnectedToInternet)) ||
        (ret_wlan_status == 0 && (wlan_status & Networking_InterfaceConnectionStatus_ConnectedToInternet))) {
        if (sphereStatus.IoTHubClientAuthState == IoTHubClientAuthenticationState_NotAuthenticated) {
            SetupAzureClient();
            IoT_CentralLib_Initialize(CACHE_BUF_SIZE, false);
        }
        sphereStatus.isNetworkConnected = true;
        ChangeLedStatus(LED_ON);
    }
    else {
        sphereStatus.isNetworkConnected = false;
        ChangeLedStatus(LED_BLINK);
        if (errno != EAGAIN) {
            Log_Debug("ERROR: Networking_GetInterfaceConnectionStatus: %d (%s)\n", errno,
                strerror(errno));
            exitCode = ExitCode_InterfaceConnectionStatus_Failed;
            return;
        }
    }

    if (ct_error < 0) {
        goto dowork;
    }

dowork:
    if (iothubClientHandle != NULL) {
        IoTHubDeviceClient_LL_DoWork(iothubClientHandle);
    }
}

/// <summary>
///     Parse the command line arguments given in the application manifest.
/// </summary>
static void ParseCommandLineArguments(int argc, char *argv[])
{
    int option = 0;
    static const struct option cmdLineOptions[] = {{"ConnectionType", required_argument, NULL, 'c'},
                                                   {"ScopeID", required_argument, NULL, 's'},
                                                   {"Hostname", required_argument, NULL, 'h'},
                                                   {NULL, 0, NULL, 0}};

    if (argc == 2) {
        scopeId = argv[1];
        connectionType = ConnectionType_DPS;
        Log_Debug("ScopeID: %s\n", scopeId);
    } else {
        // Loop over all of the options
        while ((option = getopt_long(argc, argv, "c:s:h:d:", cmdLineOptions, NULL)) != -1) {
            // Check if arguments are missing. Every option requires an argument.
            if (optarg != NULL && optarg[0] == '-') {
                Log_Debug("Warning: Option %c requires an argument\n", option);
                continue;
            }
            switch (option) {
            case 'c':
                Log_Debug("ConnectionType: %s\n", optarg);
                isConnectionTypeInCmdArgs = true;
                if (strcmp(optarg, "DPS") == 0) {
                    connectionType = ConnectionType_DPS;
                } else if (strcmp(optarg, "Direct") == 0) {
                    connectionType = ConnectionType_Direct;
                } else if (strcmp(optarg, "PnP") == 0) {
                    connectionType = ConnectionType_PnP;
                }
                break;
            case 's':
                Log_Debug("ScopeID: %s\n", optarg);
                scopeId = optarg;
                connectionType = isConnectionTypeInCmdArgs ? connectionType : ConnectionType_DPS;
                break;
            case 'h':
                Log_Debug("Hostname: %s\n", optarg);
                hubHostName = optarg;
                connectionType = isConnectionTypeInCmdArgs ? connectionType : ConnectionType_Direct;
                break;
            default:
                // Unknown options are ignored.
                break;
            }
        }
    }
}

/// <summary>
///     Validates if the values of the Scope ID, IotHub Hostname and Device ID were set.
/// </summary>
/// <returns>ExitCode_Success if the parameters were provided; otherwise another
/// ExitCode value which indicates the specific failure.</returns>
static ExitCode ValidateUserConfiguration(void)
{
    ExitCode validationExitCode = ExitCode_Success;

    if (connectionType < ConnectionType_DPS || connectionType > ConnectionType_PnP) {
        validationExitCode = ExitCode_Validate_ConnectionType;
    }
    
    if (!isConnectionTypeInCmdArgs && scopeId != NULL && hubHostName != NULL){
        connectionType = ConnectionType_DPS;
    }

    if (connectionType == ConnectionType_DPS) {
        if (scopeId == NULL) {
            validationExitCode = ExitCode_Validate_ScopeId;
        } else {
            Log_Debug("Using DPS Connection: Azure IoT DPS Scope ID %s\n", scopeId);
        }
    }

    if (connectionType == ConnectionType_Direct) {
        if (hubHostName == NULL) {
            validationExitCode = ExitCode_Validate_IotHubHostname;
        }
        if (validationExitCode == ExitCode_Success) {
            Log_Debug("Using Direct Connection: Azure IoT Hub Hostname %s\n", hubHostName);
        }
    }

    if (connectionType == ConnectionType_PnP) {
        if (scopeId == NULL) {
            validationExitCode = ExitCode_Validate_ScopeId;
        } else {
            Log_Debug("Using DPS Connection: Azure IoT DPS Scope ID %s\n", scopeId);
        }
    }

    if (validationExitCode != ExitCode_Success) {
        Log_Debug("Command line arguments for application shoud be set as below\n%s",
                  cmdLineArgsUsageText);
    }
    return validationExitCode;
}

static void WatchdogEventHandler(EventLoopTimer *timer)
{
    if (ConsumeEventLoopTimerEvent(timer) != 0) {
        exitCode = ExitCode_WatchDogTimer_Consume;
        return;
    }

    ExtendWatchdogExpiry();
}

/// <summary>
/// LED event:  Opration LED
/// </summary>
void LedEventHandler(EventLoopTimer *timer)
{
    if (ConsumeEventLoopTimerEvent(timer) != 0) {
        exitCode = ExitCode_LedTimer_Consume;
        return;
    }

    GPIO_Value_Type LED_State;
    switch (gLedState)
    {
    case LED_OFF:
        GPIO_SetValue(ledGpioFd, GPIO_Value_High);
        break;
    case LED_ON:
        GPIO_SetValue(ledGpioFd, GPIO_Value_Low);
        break;
    case LED_BLINK:
        GPIO_GetValue(ledGpioFd, &LED_State);
        GPIO_SetValue(ledGpioFd, (GPIO_Value_Type)(1 - LED_State));
        break;
    default:
        break;
    }
}

/// <summary>
/// Gpio event: Check the status of the userSW
/// </summary>
void GpioEventHandler(EventLoopTimer *timer)
{
    if (ConsumeEventLoopTimerEvent(timer) != 0) {
        exitCode = ExitCode_GpioTimer_Consume;
        return;
    }

    GPIO_Value_Type userSWNewState;
    int result = GPIO_GetValue(swGpioFd, &userSWNewState);
    if (result != 0) {
        Log_Debug("ERROR: Could not read GPIO: %s (%d).\n", strerror(errno), errno);
    }

    if ((userSWNewState == GPIO_Value_Low) && (userSWNewState != userSWState)){
        Log_Debug("UserSW pressed!!!\n");
        uint32_t timeStamp = IoT_CentralLib_GetTmeStamp();
        IoT_CentralLib_SendTelemetry("{ \"UserSWEvent\": 1 }", &timeStamp);
    }

    userSWState = userSWNewState;
}

/// <summary>
/// Heartbeat event : Count up heartbeat value.
/// </summary>
void HeartBeatEventHandler(EventLoopTimer *timer)
{
    if (ConsumeEventLoopTimerEvent(timer) != 0) {
        exitCode = ExitCode_HeartBeatTimer_Consume;
        return;
    }

    heartBeatValue ++;
    if (heartBeatValue >= 3600) {
        heartBeatValue = 1;
    }

    uint32_t timeStamp = IoT_CentralLib_GetTmeStamp();
    char *sendTelemetry = (char *)malloc(JSON_BUFFER_SIZE);
    sprintf(sendTelemetry, "{\"%s\": %d}", "HeartBeat", heartBeatValue);

    IoT_CentralLib_SendTelemetry(sendTelemetry, &timeStamp);
    free(sendTelemetry);
}

/// <summary>
///     Set up SIGTERM termination handler, initialize peripherals, and set up event handlers.
/// </summary>
/// <returns>ExitCode_Success if all resources were allocated successfully; otherwise another
/// ExitCode value which indicates the specific failure.</returns>
static ExitCode InitPeripheralsAndHandlers(void)
{
    struct sigaction action;
    memset(&action, 0, sizeof(struct sigaction));
    action.sa_handler = TerminationHandler;
    sigaction(SIGTERM, &action, NULL);

    eventLoop = EventLoop_Create();
    if (eventLoop == NULL) {
        Log_Debug("Could not create event loop.\n");
        return ExitCode_SetUpSysEvent_EventLoop;
    }

    SetupWatchdog();
    struct timespec watchdogKickPeriod = {.tv_sec = 0, .tv_nsec = 500 * 1000 * 1000};
    watchdogLoopTimer =
        CreateEventLoopPeriodicTimer(eventLoop, &WatchdogEventHandler, &watchdogKickPeriod);
    if (watchdogLoopTimer == NULL) {
        return ExitCode_Init_WatchDogTimer;
    }

    azureIoTPollPeriodSeconds = AzureIoTDefaultPollPeriodSeconds;
    struct timespec azureTelemetryPeriod = {.tv_sec = azureIoTPollPeriodSeconds, .tv_nsec = 0};
    azureTimer =
        CreateEventLoopPeriodicTimer(eventLoop, &AzureTimerEventHandler, &azureTelemetryPeriod);
    if (azureTimer == NULL) {
        return ExitCode_Init_AzureTimer;
    }

    // LED
	Log_Debug("Opening MT3620_GPIO8 as output\n");
	ledGpioFd =
		GPIO_OpenAsOutput(MT3620_GPIO8, GPIO_OutputMode_PushPull, GPIO_Value_High);
	if (ledGpioFd < 0) {
		Log_Debug("ERROR: Could not open LED: %s (%d).\n", strerror(errno), errno);
		return ExitCode_TermHandler_SigTerm;
	}
    struct timespec checkLedStatusPeriod = {.tv_sec = 0, .tv_nsec = 500 * 1000 * 1000};
    ledEventLoopTimer =
        CreateEventLoopPeriodicTimer(eventLoop, &LedEventHandler, &checkLedStatusPeriod);
    if (ledEventLoopTimer == NULL) {
        return ExitCode_Init_LedTimer;
    }
    // LED ON
    ChangeLedStatus(LED_ON);

    // GPIO
    Log_Debug("Opening MT3620_GPIO12 as input\n");
    swGpioFd = 
        GPIO_OpenAsInput(MT3620_GPIO12);
    if (swGpioFd < 0) {
        Log_Debug("ERROR: Could not open UserSW: %s (%d).\n", strerror(errno), errno);
        return ExitCode_TermHandler_SigTerm;
    }
    struct timespec gpioPeriod = {.tv_sec = 0, .tv_nsec = 1000 * 1000};
    gpioEventLoopTimer =
        CreateEventLoopPeriodicTimer(eventLoop, &GpioEventHandler, &gpioPeriod);
    if (gpioEventLoopTimer == NULL) {
        return ExitCode_Init_GpioTimer;
    }

    // Heartbeat
    struct timespec heartbeatPeriod = {.tv_sec = 1, .tv_nsec = 0};
    heartbeatEventLoopTimer =
        CreateEventLoopPeriodicTimer(eventLoop, &HeartBeatEventHandler, &heartbeatPeriod);
    if (heartbeatEventLoopTimer == NULL) {
        return ExitCode_Init_HeartBeatTimer;
    }

    return ExitCode_Success;
}

/// <summary>
///     Close peripherals and handlers.
/// </summary>
static void ClosePeripheralsAndHandlers(void)
{
    Log_Debug("Closing file descriptors\n");

    DisposeEventLoopTimer(azureTimer);
    DisposeEventLoopTimer(watchdogLoopTimer);
    DisposeEventLoopTimer(ledEventLoopTimer);
    DisposeEventLoopTimer(gpioEventLoopTimer);
    DisposeEventLoopTimer(heartbeatEventLoopTimer);

    EventLoop_Close(eventLoop);
}

/// <summary>
///     Sets the IoT Hub authentication state for the app
///     The SAS Token expires which will set the authentication state
/// </summary>
static void HubConnectionStatusCallback(IOTHUB_CLIENT_CONNECTION_STATUS result,
                                        IOTHUB_CLIENT_CONNECTION_STATUS_REASON reason,
                                        void *userContextCallback)
{
    Log_Debug("Azure IoT connection status: %s\n", GetReasonString(reason));

    if (result != IOTHUB_CLIENT_CONNECTION_AUTHENTICATED) {
        sphereStatus.IoTHubClientAuthState = IoTHubClientAuthenticationState_NotAuthenticated;
        ChangeLedStatus(LED_BLINK);
        return;
    }
    sphereStatus.IoTHubClientAuthState = IoTHubClientAuthenticationState_Authenticated;

    Log_Debug("IoT Hub Authenticated: %s\n", GetReasonString(reason));

    if (reason == IOTHUB_CLIENT_CONNECTION_OK) {
        if(!iothubFirstConnected) {
            cactusphere_error_notify(FIRST_CONNECT_IOTC);
            iothubFirstConnected = true;
        } else {
            cactusphere_error_notify(RE_CONNECT_IOTC);
        }

        if (ct_error == -EEPROM_READ_ERROR) {
            sphereStatus.isEepromReadSuccess = false;
            ChangeLedStatus(LED_BLINK);
            cactusphere_error_notify(EEPROM_READ_ERROR);
            exitCode = ExitCode_TermHandler_SigTerm;
        } else {
            static const char* EventMsgTemplate = "{ \"%s\": \"%s\" }";
            static char propertyStr[280] = { 0 };

            // Send App version
            // HLApp
            snprintf(propertyStr, sizeof(propertyStr), EventMsgTemplate, "HLAppVersion", HLAPP_VERSION);
            IoT_CentralLib_SendProperty(propertyStr);
            // RTApp - None
            snprintf(propertyStr, sizeof(propertyStr), EventMsgTemplate, "RTAppVersion", "---");
            IoT_CentralLib_SendProperty(propertyStr);
            
            sphereStatus.isEepromReadSuccess = true;
            ChangeLedStatus(LED_ON);

            static EventMsgData eepromProperty[] = {
                {"SerialNumber", ""},
                {"EthMacAddr", ""},
                {"ProductId", ""},
                {"VendorId", ""},
                {"WlanMacAddr", ""},
                {"Generation", ""},
            };

            setEepromString(eepromProperty[0].value, eeprom.serial, sizeof(eeprom.serial));
            setEepromString(eepromProperty[1].value, eeprom.ethernetMac, sizeof(eeprom.ethernetMac));
            setEepromString(eepromProperty[2].value, eeprom.productId, sizeof(eeprom.productId));
            setEepromString(eepromProperty[3].value, eeprom.venderId, sizeof(eeprom.venderId));
            setEepromString(eepromProperty[4].value, eeprom.wlanMac, sizeof(eeprom.wlanMac));
            setEepromString(eepromProperty[5].value, eeprom.generation, sizeof(eeprom.generation));

            // Send Property
            for (int i = 0; i < (sizeof(eepromProperty) / sizeof(eepromProperty[0])); i++) {
                snprintf(propertyStr, sizeof(propertyStr), EventMsgTemplate, eepromProperty[i].name, eepromProperty[i].value);
                IoT_CentralLib_SendProperty(propertyStr);
            }
            if (ct_error < 0) {
                sphereStatus.isEepromDataValid = false;
                ChangeLedStatus(LED_BLINK);
                cactusphere_error_notify(ILLEGAL_PACKAGE);
                exitCode = ExitCode_TermHandler_SigTerm;
            }
            else {
                sphereStatus.isEepromDataValid = true;
            }
        }
    } else {
        ChangeLedStatus(LED_BLINK);
    }
}

/// <summary>
///     Sets up the Azure IoT Hub connection (creates the iothubClientHandle)
///     When the SAS Token for a device expires the connection needs to be recreated
///     which is why this is not simply a one time call.
/// </summary>
static void SetupAzureClient(void)
{
    bool isAzureClientSetupSuccessful = false;

    if (iothubClientHandle != NULL)
        IoTHubDeviceClient_LL_Destroy(iothubClientHandle);

    if (connectionType == ConnectionType_Direct) {
        isAzureClientSetupSuccessful = SetupAzureIoTHubClientWithDaa();
    } else if (connectionType == ConnectionType_DPS) {
        isAzureClientSetupSuccessful = SetupAzureIoTHubClientWithDps();
    } else if (connectionType == ConnectionType_PnP) {
        isAzureClientSetupSuccessful = SetupAzureIoTHubClientWithDpsPnP();
    }

    if (!isAzureClientSetupSuccessful) {
        ChangeLedStatus(LED_BLINK);

        // If we fail to connect, reduce the polling frequency, starting at
        // AzureIoTMinReconnectPeriodSeconds and with a backoff up to
        // AzureIoTMaxReconnectPeriodSeconds
        if (azureIoTPollPeriodSeconds == AzureIoTDefaultPollPeriodSeconds) {
            azureIoTPollPeriodSeconds = AzureIoTMinReconnectPeriodSeconds;
        } else {
            azureIoTPollPeriodSeconds *= 2;
            if (azureIoTPollPeriodSeconds > AzureIoTMaxReconnectPeriodSeconds) {
                azureIoTPollPeriodSeconds = AzureIoTMaxReconnectPeriodSeconds;
            }
        }

        struct timespec azureTelemetryPeriod = {azureIoTPollPeriodSeconds, 0};
        SetEventLoopTimerPeriod(azureTimer, &azureTelemetryPeriod);

        Log_Debug("ERROR: failure to create IoTHub Handle - will retry in %i seconds.\n",
                  azureIoTPollPeriodSeconds);
        return;
    }

    // Successfully connected, so make sure the polling frequency is back to the default
    azureIoTPollPeriodSeconds = AzureIoTDefaultPollPeriodSeconds;
    struct timespec azureTelemetryPeriod = {.tv_sec = azureIoTPollPeriodSeconds, .tv_nsec = 0};
    SetEventLoopTimerPeriod(azureTimer, &azureTelemetryPeriod);

    // Set client authentication state to initiated. This is done to indicate that
    // SetUpAzureIoTHubClient() has been called (and so should not be called again) while the
    // client is waiting for a response via the ConnectionStatusCallback().
    sphereStatus.IoTHubClientAuthState = IoTHubClientAuthenticationState_AuthenticationInitiated;

    ChangeLedStatus(LED_ON);

    if (IoTHubDeviceClient_LL_SetOption(iothubClientHandle, OPTION_KEEP_ALIVE,
                                        &keepalivePeriodSeconds) != IOTHUB_CLIENT_OK) {
        Log_Debug("ERROR: failure setting option \"%s\"\n", OPTION_KEEP_ALIVE);
        return;
    }

    IoTHubDeviceClient_LL_SetConnectionStatusCallback(iothubClientHandle,
                                                      HubConnectionStatusCallback, NULL);
}

/// <summary>
///     Sets up the Azure IoT Hub connection (creates the iothubClientHandle)
///     with DAA
/// </summary>
static bool SetupAzureIoTHubClientWithDaa(void)
{
    // Set up auth type
    int retError = iothub_security_init(IOTHUB_SECURITY_TYPE_X509);
    if (retError != 0) {
        Log_Debug("ERROR: iothub_security_init failed with error %d.\n", retError);
        return false;
    }

    // Create Azure Iot Hub client handle
    iothubClientHandle =
        IoTHubDeviceClient_LL_CreateWithAzureSphereFromDeviceAuth(hubHostName, MQTT_Protocol);

    if (iothubClientHandle == NULL) {
        Log_Debug("IoTHubDeviceClient_LL_CreateFromDeviceAuth returned NULL.\n");
        return false;
    }

    // Enable DAA cert usage when x509 is invoked
    if (IoTHubDeviceClient_LL_SetOption(iothubClientHandle, "SetDeviceId",
                                        &deviceIdForDaaCertUsage) != IOTHUB_CLIENT_OK) {
        Log_Debug("ERROR: Failure setting Azure IoT Hub client option \"SetDeviceId\".\n");
        return false;
    }

    return true;
}

/// <summary>
///     Sets up the Azure IoT Hub connection (creates the iothubClientHandle)
///     with DPS
/// </summary>
static bool SetupAzureIoTHubClientWithDps(void)
{
    AZURE_SPHERE_PROV_RETURN_VALUE provResult =
        IoTHubDeviceClient_LL_CreateWithAzureSphereDeviceAuthProvisioning(scopeId, 10000,
                                                                          &iothubClientHandle);
    Log_Debug("IoTHubDeviceClient_LL_CreateWithAzureSphereDeviceAuthProvisioning returned '%s'.\n",
              getAzureSphereProvisioningResultString(provResult));

    if (provResult.result != AZURE_SPHERE_PROV_RESULT_OK) {
        return false;
    }

    return true;
}

/// <summary>
///     DPS provisioning callback with status
/// </summary>
static void RegisterDeviceCallback(PROV_DEVICE_RESULT registerResult, const char* callbackHubUri, const char* deviceId, void* userContext)
{
    dpsRegisterStatus = registerResult;

	if (registerResult == PROV_DEVICE_RESULT_OK && callbackHubUri != NULL) {

		size_t uriSize = strlen(callbackHubUri) + 1; // +1 for NULL string termination

		iotHubUri = (char*)malloc(uriSize);

		if (iotHubUri == NULL) {
			Log_Debug("ERROR: IoT Hub URI malloc failed.\n");
		}
		else {
			strncpy(iotHubUri, callbackHubUri, uriSize);
		}
	}
}

/// <summary>
///     Provision with DPS and assign IoT Plug and Play Model ID
/// </summary>
static bool SetupAzureIoTHubClientWithDpsPnP(void)
{
	PROV_DEVICE_LL_HANDLE prov_handle = NULL;
	PROV_DEVICE_RESULT prov_result;
	bool result = false;
    static char dtdlBuffer[MAX_DTDL_BUFFER_SIZE];
	int deviceIdForDaaCertUsage = 0;  // set DaaCertUsage to false

	int len = snprintf(dtdlBuffer, MAX_DTDL_BUFFER_SIZE, "{\"modelId\":\"%s\"}", azureSphereModelId);
	if (len < 0 || len >= MAX_DTDL_BUFFER_SIZE) {
		Log_Debug("ERROR: Cannot write Model ID to buffer.\n");
		goto cleanup;
	}

	// Initiate security with X509 Certificate
	if (prov_dev_security_init(SECURE_DEVICE_TYPE_X509) != 0) {
		Log_Debug("ERROR: Failed to initiate X509 Certificate security\n");
		goto cleanup;
	}

	// Create Provisioning Client for communication with DPS using MQTT protocol
	if ((prov_handle = Prov_Device_LL_Create(dpsUrl, scopeId, Prov_Device_MQTT_Protocol)) == NULL) {
		Log_Debug("ERROR: Failed to create Provisioning Client\n");
		goto cleanup;
	}

	// Sets Device ID on Provisioning Client
	if ((prov_result = Prov_Device_LL_SetOption(prov_handle, "SetDeviceId", &deviceIdForDaaCertUsage)) != PROV_DEVICE_RESULT_OK) {
		Log_Debug("ERROR: Failed to set Device ID in Provisioning Client, error=%d\n", prov_result);
		goto cleanup;
	}

	// Sets Model ID provisioning data
	if (dtdlBuffer != NULL) {
		if ((prov_result = Prov_Device_LL_Set_Provisioning_Payload(prov_handle, dtdlBuffer)) != PROV_DEVICE_RESULT_OK) {
			Log_Debug("Error: Failed to set Model ID in Provisioning Client, error=%d\n", prov_result);
			goto cleanup;
		}
	}

	// Sets the callback function for device registration
	if ((prov_result = Prov_Device_LL_Register_Device(prov_handle, RegisterDeviceCallback, NULL, NULL, NULL)) != PROV_DEVICE_RESULT_OK) {
		Log_Debug("ERROR: Failed to set callback function for device registration, error=%d\n", prov_result);
		goto cleanup;
	}

	// Begin provisioning device with DPS
	// Initiates timer to prevent timing out
	static const long timeoutMs = 60000; // aloow up to 60 seconds before timeout
	static const long workDelayMs = 25;
	const struct timespec sleepTime = { .tv_sec = 0, .tv_nsec = workDelayMs * 1000 * 1000 };
	long time_elapsed = 0;

	dpsRegisterStatus = PROV_DEVICE_REG_HUB_NOT_SPECIFIED;

	while (dpsRegisterStatus != PROV_DEVICE_RESULT_OK && time_elapsed < timeoutMs) {
		Prov_Device_LL_DoWork(prov_handle);
		nanosleep(&sleepTime, NULL);
		time_elapsed += workDelayMs;
	}

	if (dpsRegisterStatus != PROV_DEVICE_RESULT_OK) {
		Log_Debug("ERROR: Failed to register device with provisioning service\n");
		goto cleanup;
	}

	if ((iothubClientHandle = IoTHubDeviceClient_LL_CreateWithAzureSphereFromDeviceAuth(iotHubUri, MQTT_Protocol)) == NULL) {
		Log_Debug("ERROR: Failed to create client IoT Hub Client Handle\n");
		goto cleanup;
	}

	// IOTHUB_CLIENT_RESULT iothub_result 
	int deviceId = 1;
	if (IoTHubDeviceClient_LL_SetOption(iothubClientHandle, "SetDeviceId", &deviceId) != IOTHUB_CLIENT_OK) {
		IoTHubDeviceClient_LL_Destroy(iothubClientHandle);
		iothubClientHandle = NULL;
		Log_Debug("ERROR: Failed to set Device ID on IoT Hub Client\n");
		goto cleanup;
	}

	// Sets auto URL encoding on IoT Hub Client
	bool urlAutoEncodeDecode = true;
	if (IoTHubDeviceClient_LL_SetOption(iothubClientHandle, OPTION_AUTO_URL_ENCODE_DECODE, &urlAutoEncodeDecode) != IOTHUB_CLIENT_OK) {
		Log_Debug("ERROR: Failed to set auto Url encode option on IoT Hub Client\n");
		goto cleanup;
	}

	if (dtdlBuffer != NULL) {
		if (IoTHubDeviceClient_LL_SetOption(iothubClientHandle, OPTION_MODEL_ID, azureSphereModelId) != IOTHUB_CLIENT_OK)
		{
			Log_Debug("ERROR: failure setting option \"%s\"\n", OPTION_MODEL_ID);
			goto cleanup;
		}
	}

	result = true;

cleanup:
	if (iotHubUri != NULL) {
		free(iotHubUri);
		iotHubUri = NULL;
	}

	if (prov_handle != NULL) {
		Prov_Device_LL_Destroy(prov_handle);
	}

	prov_dev_security_deinit();
	return result;
}

/// <summary>
///     Converts the IoT Hub connection status reason to a string.
/// </summary>
static const char *GetReasonString(IOTHUB_CLIENT_CONNECTION_STATUS_REASON reason)
{
    static char *reasonString = "unknown reason";
    switch (reason) {
    case IOTHUB_CLIENT_CONNECTION_EXPIRED_SAS_TOKEN:
        reasonString = "IOTHUB_CLIENT_CONNECTION_EXPIRED_SAS_TOKEN";
        break;
    case IOTHUB_CLIENT_CONNECTION_DEVICE_DISABLED:
        reasonString = "IOTHUB_CLIENT_CONNECTION_DEVICE_DISABLED";
        break;
    case IOTHUB_CLIENT_CONNECTION_BAD_CREDENTIAL:
        reasonString = "IOTHUB_CLIENT_CONNECTION_BAD_CREDENTIAL";
        break;
    case IOTHUB_CLIENT_CONNECTION_RETRY_EXPIRED:
        reasonString = "IOTHUB_CLIENT_CONNECTION_RETRY_EXPIRED";
        break;
    case IOTHUB_CLIENT_CONNECTION_NO_NETWORK:
        reasonString = "IOTHUB_CLIENT_CONNECTION_NO_NETWORK";
        break;
    case IOTHUB_CLIENT_CONNECTION_COMMUNICATION_ERROR:
        reasonString = "IOTHUB_CLIENT_CONNECTION_COMMUNICATION_ERROR";
        break;
    case IOTHUB_CLIENT_CONNECTION_OK:
        reasonString = "IOTHUB_CLIENT_CONNECTION_OK";
        break;
    case IOTHUB_CLIENT_CONNECTION_NO_PING_RESPONSE:
        reasonString = "IOTHUB_CLIENT_CONNECTION_NO_PING_RESPONSE";
        break;
    }
    return reasonString;
}

/// <summary>
///     Converts AZURE_SPHERE_PROV_RETURN_VALUE to a string.
/// </summary>
static const char *getAzureSphereProvisioningResultString(
    AZURE_SPHERE_PROV_RETURN_VALUE provisioningResult)
{
    switch (provisioningResult.result) {
    case AZURE_SPHERE_PROV_RESULT_OK:
        return "AZURE_SPHERE_PROV_RESULT_OK";
    case AZURE_SPHERE_PROV_RESULT_INVALID_PARAM:
        return "AZURE_SPHERE_PROV_RESULT_INVALID_PARAM";
    case AZURE_SPHERE_PROV_RESULT_NETWORK_NOT_READY:
        return "AZURE_SPHERE_PROV_RESULT_NETWORK_NOT_READY";
    case AZURE_SPHERE_PROV_RESULT_DEVICEAUTH_NOT_READY:
        return "AZURE_SPHERE_PROV_RESULT_DEVICEAUTH_NOT_READY";
    case AZURE_SPHERE_PROV_RESULT_PROV_DEVICE_ERROR:
        return "AZURE_SPHERE_PROV_RESULT_PROV_DEVICE_ERROR";
    case AZURE_SPHERE_PROV_RESULT_GENERIC_ERROR:
        return "AZURE_SPHERE_PROV_RESULT_GENERIC_ERROR";
    default:
        return "UNKNOWN_RETURN_VALUE";
    }
}

IOTHUB_DEVICE_CLIENT_LL_HANDLE Get_IOTHUB_DEVICE_CLIENT_LL_HANDLE(void) {
    return iothubClientHandle;
}
