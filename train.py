#!/usr/bin/python3.7

import pandas
import torch
from sklearn.model_selection import train_test_split
from model import FFN

data_file = "weatherAUS.csv"
nn_file_name = "FFN.nn"
N_HL = 4
RANDOM_SEED = 42

# training functions
######################################################################################################################
def calculate_accuracy(y_true, y_pred):
    predicted = y_pred.ge(.5).view(-1)
    return (y_true == predicted).sum().float() / len(y_true)

def round_tensor(t, decimal_places=3):
    return round(t.item(), decimal_places)

def train_network(data, network, optimizer, criterion, nn_file_name):
    (x_train, y_train, x_val, y_val) = data

    for epoch in range(1000):
        y_pred = network(x_train)
        y_pred = torch.squeeze(y_pred)
        train_loss = criterion(y_pred, y_train)

        if epoch % 100 == 0:
            train_acc = calculate_accuracy(y_train, y_pred)
            y_val_pred = network(x_val)
            y_val_pred = torch.squeeze(y_val_pred)
            val_loss = criterion(y_val_pred, y_val)
            val_acc = calculate_accuracy(y_val, y_val_pred)

            tr_lss = round_tensor(train_loss)
            tr_acc = round_tensor(train_acc)
            vl_lss = round_tensor(val_loss)
            vl_acc = round_tensor(val_acc)

        optimizer.zero_grad()
        train_loss.backward()
        optimizer.step()

    torch.save(network, nn_file_name)

# main
######################################################################################################################

raw_data = pandas.read_csv(data_file)

cols = ['Rainfall', 'Humidity3pm', 'Pressure9am', 'RainToday', 'RainTomorrow']
processed_data = raw_data[cols]

processed_data['RainToday'].replace({'No': 0, 'Yes': 1}, inplace=True)
processed_data['RainTomorrow'].replace({'No': 0, 'Yes': 1}, inplace=True)

processed_data = processed_data.dropna(how='any')

processed_data = ( processed_data - processed_data.min() ) / ( processed_data.max() - processed_data.min() )

x = processed_data[['Rainfall', 'Humidity3pm', 'RainToday', 'Pressure9am']]
y = processed_data[['RainTomorrow']]

x_train, x_val, y_train, y_val = train_test_split(x, y, test_size=0.2, random_state=RANDOM_SEED)

x_train = torch.from_numpy(x_train.to_numpy()).float()
y_train = torch.squeeze(torch.from_numpy(y_train.to_numpy()).float())
x_val = torch.from_numpy(x_val.to_numpy()).float()
y_val = torch.squeeze(torch.from_numpy(y_val.to_numpy()).float())

splitted_data = (x_train, y_train, x_val, y_val)
network = FFN(x_train.shape[1], N_HL)
optimizer = torch.optim.Adam(network.parameters(), lr=0.001)
criterion = torch.nn.BCELoss()

train_network(splitted_data, network, optimizer, criterion, nn_file_name)
