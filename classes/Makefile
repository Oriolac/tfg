CRIPTO = cripto
DTO = dto
STATEMACHINE = statemachine

all: $(CRIPTO) $(DTO) $(STATEMACHINE)
	@echo "DONE"

$(CRIPTO):
	java -jar plantuml.jar jlatexmath-minimal-1.0.3.jar jlm_cyrillic.jar jlm_greek.jar $(CRIPTO).puml

$(DTO):
	java -jar plantuml.jar jlatexmath-minimal-1.0.3.jar jlm_cyrillic.jar jlm_greek.jar $(DTO).puml

$(STATEMACHINE):
	java -jar plantuml.jar jlatexmath-minimal-1.0.3.jar jlm_cyrillic.jar jlm_greek.jar $(STATEMACHINE).puml
