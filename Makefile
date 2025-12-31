VENV = .venv
STAMP = $(VENV)/.stamp
LIB_INTERFACE = typed_z3 ts temporal timers orders ranks proofs
IMAGE_PREFIX = artifact

remove-docker-image = docker image ls | grep -q $(1) && docker image rm $(IMAGE_PREFIX)-$(1) || echo Skipping $(1)
build-docker-image = docker buildx build -t $(IMAGE_PREFIX)-$(1) --platform linux/$(1) .
save-docker-image = docker image save $(IMAGE_PREFIX)-$(1) | gzip > $(IMAGE_PREFIX)-$(1).tar.gz

ifeq ($(OS),Windows_NT)
	SYS_PYTHON = py -3.13
    PYTHON = $(VENV)/Scripts/python
    RM = rmdir /s /q
    TOUCH = powershell -Command "New-Item -ItemType File -Path $(STAMP) -Force"
else
	SYS_PYTHON = python3.13
	PYTHON = PYTHONPATH=. $(VENV)/bin/python
    RM = rm -rf
    TOUCH = touch $(STAMP)
endif

DOCS = $(PYTHON) -m pdoc -t docs --no-include-undocumented --no-show-source $(LIB_INTERFACE)

.PHONY: precommit
precommit: check format

.PHONY: all
all: $(wildcard examples/*.py)

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
	@$(PYTHON) $@

.PHONY: docs/examples/ticket.md
.PRECIOUS: docs/examples/ticket.md
docs/examples/ticket.md:
	make literate.py FILE=examples/ticket.py

.PHONY: docs-server
docs-server: docs/examples/ticket.md
	$(DOCS) -n

.PHONY: docs-server-open
docs-server-open: docs/examples/ticket.md
	$(DOCS)

.PHONY: docs/out
docs/out: docs/examples/ticket.md
	$(DOCS) -o $@

.PHONY: docs/out-open
docs/out-open: docs/out
	open docs/out/index.html

$(IMAGE_PREFIX)-%.tar.gz: FORCE
	-$(call build-docker-image,$*)
	-$(call save-docker-image,$*)
	-$(call remove-docker-image,$*)

$(IMAGE_PREFIX)-%: FORCE
	-$(call build-docker-image,$*)


.PHONY: $(VENV)
$(VENV): $(STAMP)

$(STAMP): requirements.txt
	$(SYS_PYTHON) -m venv $(VENV)
	$(PYTHON) -m pip install --upgrade pip
	$(PYTHON) -m pip install -r requirements.txt
	$(TOUCH)

.PHONY: clean
clean:
	$(RM) $(VENV)
	$(RM) models
	$(RM) cores
	$(RM) docs/out

FORCE:
