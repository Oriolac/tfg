BUSOM = busom
RECSI = recsi
NETWORK = network
GARRA = garra

all: $(BUSOM) $(RECSI) $(NETWORK) $(GARRRA)
	@echo "DONE"

$(BUSOM):
	java -jar plantuml.jar jlatexmath-minimal-1.0.3.jar jlm_cyrillic.jar jlm_greek.jar $(BUSOM).puml

$(RECSI):
	java -jar plantuml.jar jlatexmath-minimal-1.0.3.jar jlm_cyrillic.jar jlm_greek.jar $(RECSI).puml

$(NETWORK):
	java -jar plantuml.jar jlatexmath-minimal-1.0.3.jar jlm_cyrillic.jar jlm_greek.jar $(NETWORK).puml

$(GARRA):
	java -jar plantuml.jar jlatexmath-minimal-1.0.3.jar jlm_cyrillic.jar jlm_greek.jar $(GARRA).puml
