/* FreeRTOS includes */
#include "FreeRTOS.h"
#include "task.h"
#include "queue.h"
#include "semphr.h"

/* Standard includes */
#include <stdio.h>
#include <string.h>
#include <stdint.h>

/* Constants */
#define SENSOR_QUEUE_LENGTH    10
#define SENSOR_ITEM_SIZE       sizeof(uint32_t)
#define MAX_TEMPERATURE        100
#define MIN_TEMPERATURE        0
#define STACK_SIZE            configMINIMAL_STACK_SIZE * 2

/* Global variables */
static QueueHandle_t xSensorQueue = NULL;
static SemaphoreHandle_t xSensorMutex = NULL;
static TaskHandle_t xSensorTaskHandle = NULL;
static TaskHandle_t xProcessTaskHandle = NULL;

/* Sensor reading structure */
typedef struct {
    uint32_t temperature;
    uint32_t timestamp;
} SensorData_t;

/* Function prototypes */
static void vSensorTask(void *pvParameters);
static void vProcessingTask(void *pvParameters);
static uint32_t ulGetSensorReading(void);
static void vProcessSensorData(const SensorData_t* pxData);

/* Sensor reading simulation function */
static uint32_t ulGetSensorReading(void) {
    static uint32_t ulValue = 25;
    
    /* Simulate temperature changes */
    uint32_t ulChange = (rand() % 3) - 1;  /* -1, 0, or 1 */
    ulValue += ulChange;
    
    /* Ensure value stays within bounds */
    if (ulValue > MAX_TEMPERATURE) {
        ulValue = MAX_TEMPERATURE;
    } else if (ulValue < MIN_TEMPERATURE) {
        ulValue = MIN_TEMPERATURE;
    }
    
    return ulValue;
}

/* Task to read sensor data */
static void vSensorTask(void *pvParameters) {
    SensorData_t xData;
    TickType_t xLastWakeTime = xTaskGetTickCount();
    
    for (;;) {
        if (xSemaphoreTake(xSensorMutex, pdMS_TO_TICKS(100)) == pdTRUE) {
            /* Read sensor data */
            xData.temperature = ulGetSensorReading();
            xData.timestamp = xTaskGetTickCount();
            
            /* Send to processing task */
            if (xQueueSend(xSensorQueue, &xData, pdMS_TO_TICKS(100)) != pdPASS) {
                /* Handle queue full error */
                printf("Queue full - sensor reading dropped\n");
            }
            
            xSemaphoreGive(xSensorMutex);
        }
        
        /* Read sensor every 500ms */
        vTaskDelayUntil(&xLastWakeTime, pdMS_TO_TICKS(500));
    }
}

/* Task to process sensor readings */
static void vProcessingTask(void *pvParameters) {
    SensorData_t xReceivedData;
    
    for (;;) {
        /* Wait for data from the queue */
        if (xQueueReceive(xSensorQueue, &xReceivedData, portMAX_DELAY) == pdPASS) {
            /* Process the sensor reading */
            vProcessSensorData(&xReceivedData);
        }
    }
}

/* Process sensor data and trigger alerts if needed */
static void vProcessSensorData(const SensorData_t* pxData) {
    if (pxData == NULL) {
        return;
    }
    
    /* Check for temperature thresholds */
    if (pxData->temperature > 80) {
        printf("WARNING: High temperature detected: %lu at tick %lu\n", 
               pxData->temperature, pxData->timestamp);
    } else if (pxData->temperature < 10) {
        printf("WARNING: Low temperature detected: %lu at tick %lu\n", 
               pxData->temperature, pxData->timestamp);
    }
}

/* Initialize the system */
bool initSystem(void) {
    /* Create queue */
    xSensorQueue = xQueueCreate(SENSOR_QUEUE_LENGTH, sizeof(SensorData_t));
    if (xSensorQueue == NULL) {
        return false;
    }
    
    /* Create mutex */
    xSensorMutex = xSemaphoreCreateMutex();
    if (xSensorMutex == NULL) {
        vQueueDelete(xSensorQueue);
        return false;
    }
    
    /* Create tasks */
    BaseType_t xResult;
    
    xResult = xTaskCreate(
        vSensorTask,
        "SensorTask",
        STACK_SIZE,
        NULL,
        tskIDLE_PRIORITY + 2,
        &xSensorTaskHandle
    );
    
    if (xResult != pdPASS) {
        vQueueDelete(xSensorQueue);
        vSemaphoreDelete(xSensorMutex);
        return false;
    }
    
    xResult = xTaskCreate(
        vProcessingTask,
        "ProcessTask",
        STACK_SIZE,
        NULL,
        tskIDLE_PRIORITY + 1,
        &xProcessTaskHandle
    );
    
    if (xResult != pdPASS) {
        vQueueDelete(xSensorQueue);
        vSemaphoreDelete(xSensorMutex);
        vTaskDelete(xSensorTaskHandle);
        return false;
    }
    
    return true;
}

/* Application entry point */
int main(void) {
    /* Initialize system */
    if (!initSystem()) {
        printf("System initialization failed!\n");
        return -1;
    }
    
    /* Start the scheduler */
    vTaskStartScheduler();
    
    /* Should never get here */
    for (;;) {
    }
    
    return 0;
}