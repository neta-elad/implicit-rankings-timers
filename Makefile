VENV = .venv
STAMP = $(VENV)/.stamp
LIB_INTERFACE = typed_z3 ts temporal timers termination orders ranks

ifeq ($(OS),Windows_NT)
	SYS_PYTHON = py -3.13
    PYTHON = $(VENV)/Scripts/python
    RM = rmdir /s /q $(VENV)
    TOUCH = powershell -Command "New-Item -ItemType File -Path $(STAMP) -Force"
else
	SYS_PYTHON = python3.13
	PYTHON = PYTHONPATH=. $(VENV)/bin/python
    RM = rm -rf $(VENV)
    TOUCH = touch $(STAMP)
endif

DOCS = $(PYTHON) -m pdoc -t docs --no-include-undocumented --no-show-source $(LIB_INTERFACE)

.PHONY: precommit
precommit: check format

.PHONY: install
install: $(VENV)

.PHONY: check
check: $(VENV)
	$(PYTHON) -m mypy --strict . --exclude .venv

.PHONY: format
format: $(VENV)
	$(PYTHON) -m black . --exclude .venv

.PHONY: %.py
.PRECIOUS: %.py
%.py: $(VENV) check
	$(PYTHON) $@

.PHONY: docs/examples/ticket.md
.PRECIOUS: docs/examples/ticket.md
docs/examples/ticket.md:
	make literate.py FILE=examples/ticket.py

.PHONY: docs
docs: docs/examples/ticket.md
	$(DOCS) -n

.PHONY: open_docs
open-docs: docs/examples/ticket.md
	$(DOCS)


.PHONY: $(VENV)
$(VENV): $(STAMP)

$(STAMP): requirements.txt
	$(SYS_PYTHON) -m venv $(VENV)
	$(PYTHON) -m pip install --upgrade pip
	$(PYTHON) -m pip install -r requirements.txt
	$(TOUCH)

.PHONY: clean
clean:
	$(RM)