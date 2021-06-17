CRIPTO = cripto
DTO = dto
STATEMACHINE = statemachine
CONNECTION = connection
DTOSER = dtoser
CURVE = curve
SOCKET = socket

all: $(CRIPTO) $(DTO) $(STATEMACHINE) $(CONNECTION) $(DTOSER) $(CURVE) $(SOCKET)
	@echo "DONE"

$(CRIPTO):
	java -jar plantuml.jar jlatexmath-minimal-1.0.3.jar jlm_cyrillic.jar jlm_greek.jar $(CRIPTO).puml

$(DTO):
	java -jar plantuml.jar jlatexmath-minimal-1.0.3.jar jlm_cyrillic.jar jlm_greek.jar $(DTO).puml

$(STATEMACHINE):
	java -jar plantuml.jar jlatexmath-minimal-1.0.3.jar jlm_cyrillic.jar jlm_greek.jar $(STATEMACHINE).puml

$(CONNECTION):
	java -jar plantuml.jar jlatexmath-minimal-1.0.3.jar jlm_cyrillic.jar jlm_greek.jar $(CONNECTION).puml

$(DTOSER):
	java -jar plantuml.jar jlatexmath-minimal-1.0.3.jar jlm_cyrillic.jar jlm_greek.jar $(DTOSER).puml
	
$(CURVE):
	java -jar plantuml.jar jlatexmath-minimal-1.0.3.jar jlm_cyrillic.jar jlm_greek.jar $(CURVE).puml
	
$(SOCKET):
	java -jar plantuml.jar jlatexmath-minimal-1.0.3.jar jlm_cyrillic.jar jlm_greek.jar $(SOCKET).puml
