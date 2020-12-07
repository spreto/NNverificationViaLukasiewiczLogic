from torch import nn

# setting up the net
######################################################################################################################
class FFN(nn.Module):

    def __init__(self, n_features, n_hl):
        super(FFN, self).__init__()
        self.hidden_layer = nn.Linear(n_features, n_hl)
        self.output_layer = nn.Linear(n_hl, 1)

    def forward(self, x):
        hl = nn.functional.relu(self.hidden_layer(x))
        y = nn.functional.hardtanh(self.output_layer(hl), min_val=0, max_val=1)
        return y
