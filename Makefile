VENV = .venv
BIN = $(VENV)/bin/
STAMP = $(VENV)/.stamp

.PHONY: precommit
precommit: check format

.PHONY: install
install: $(VENV)

.PHONY: check
check: $(VENV)
	$(BIN)mypy --strict *.py

.PHONY: format
format: $(VENV)
	$(BIN)black *.py

.PHONY: %.py
%.py: $(VENV) check
	$(BIN)python $@

.PHONY: $(VENV)
$(VENV): $(STAMP)

$(STAMP): requirements.txt
	python3.13 -m venv $(VENV)
	$(BIN)pip install -r requirements.txt
	touch $(STAMP)

.PHONY: clean
clean:
	rm -rf $(VENV)