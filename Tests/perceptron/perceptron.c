#include <stdio.h>
#include <time.h>
#include <stdlib.h>
#define LEARNING_RATE 0.05
#define NB_EPOCHS 100
#define NB_SAMPLES 1000
#define DIMENSION 2 // dimension of the input vector

double *weight = NULL;
double bias = 0;
int (*activation_func)(double) = NULL;

// Activation function
int unit_step_function(double x)
{
    return (x >= 0) ? 1 : 0;
}

int relu_activation(double x)
{
    return (x > 0) ? x : 0;
}

// init malloc etc.
void init(int n_samples)
{
    weight = malloc(n_samples * sizeof(int));
    for (int i = 0; i < n_samples; i++)
    {
        srand(time(NULL)); // Initialization, should only be called once.
        weight[i] = (double)rand() / RAND_MAX;
    }
    bias = (double)rand() / RAND_MAX;
}

int predit(double *array)
{
    double activation = bias;
    for (int i = 0; i < DIMENSION; i++)
    {
        activation += array[i] * weight[i];
    }
    return activation_func(activation);
}

// fit with predict data (train)
void fit(double **training_data, int *expected_result, int data_length)
{
    int prediction, error;
    for (int i = 0; i < NB_EPOCHS; i++)
    {
        for (int j = 0; j < data_length; j++)
        {
            prediction = predit(training_data[j]);
            error = expected_result[j] - prediction;
            // s'il y a une erreur dans notre prediction actuelle (la catégorisation), on adapte le biais et les poids.
            bias += LEARNING_RATE * error;
            for (int k = 0; k < DIMENSION; k++)
            {
                weight[k] += LEARNING_RATE * error * training_data[j][k];
            }
        }
    }
}

int main()
{
    activation_func = &unit_step_function;
    // On columns 1 with have the input and on column 2 the number which should be preticted.
    init(DIMENSION);
    double **training_data = malloc(NB_SAMPLES * sizeof(double *));
    for (int i = 0; i < NB_SAMPLES; i++)
    {
        training_data[i] = malloc(DIMENSION * sizeof(double));
        for (int j = 0; j < DIMENSION; j++)
        {
            training_data[i][j] = (double)rand() / RAND_MAX;
        }
    }
    int expected_results[NB_SAMPLES];
    for (int i = 0; i < NB_SAMPLES; i++)
    {
        expected_results[i] = (training_data[i][1] > training_data[i][0]) ? 1 : 0;
    }

    // On fit le modèle
    printf("Fitting the model...\n");
    fit(training_data, expected_results, NB_SAMPLES);
    printf("Model fitted !\n");
    printf("Bias: %f\n", bias);
    printf("Weights: ");
    for (int i = 0; i < DIMENSION; i++)
    {
        printf("%f ", weight[i]);
    }
    printf("\n");
    printf("Predicting (testing my model)...\n");
    // et on test si nos prédictions sont proches
    double **test_data = malloc(NB_SAMPLES * sizeof(double *));
    double prediction_success = 0;
    for (int i = 0; i < NB_SAMPLES; i++)
    {
        test_data[i] = malloc(DIMENSION * sizeof(double));
        for (int j = 0; j < DIMENSION; j++)
        {
            test_data[i][j] = (double)rand() / RAND_MAX;
        }
        if (predit(test_data[i]) == (test_data[i][1] > test_data[i][0]) ? 1 : 0)
        {
            prediction_success++;
        }
    }
    printf("Prediction success rate: %f\n", prediction_success / NB_SAMPLES);
    // considering above .9 success rate OK.
    if (prediction_success / NB_SAMPLES > 0.9)
    {
        printf("Success !\n");
    }
    else
    {
        printf("Failure !\n");
    }
    // Freeing memory
    for (int i = 0; i < NB_SAMPLES; i++)
    {
        free(training_data[i]);
        free(test_data[i]);
    }
    free(training_data);
    free(weight);
    return EXIT_SUCCESS;
}