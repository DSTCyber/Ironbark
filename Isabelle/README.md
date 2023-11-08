# Summary
Ironbark is a CPU architecture that supports formal verification. This folder contains the formal model of the Ironbark processor.  
The formal model targets Isabelle 2023.

# First Time Setup
First, download this repository and install Isabelle 2023 (available here: https://isabelle.in.tum.de/website-Isabelle2023/index.html).  

The location of "ROOT" file in this folder needs to be added to the Isabelle ROOTS file. By default, the ROOTS file is installed to %UserProfile%\.isabelle\Isabelle2023 on Windows, and ~/.isabelle/Isabelle2023 on Linux.  
Note that Isabelle uses cygwin to access files on Windows, so paths needed to be prepended with "/cygdrive/".  
For example, if the repository was cloned to C:\Ironbark, then you would need to add the following to the ROOTS file:
```
/cygdrive/c/Ironbark/Isabelle
```

To take effect, Isabelle needs to be restarted.

## (Optional) Building Theory Document as a pdf
For convenience, a pre-generated pdf of the theory document is provided in this folder as Ironbark.pdf. To re-build the theory document output, a TeX typesetting system is required to be installed. The build process has been tested under Windows using TeX Live (available here: https://tug.org/texlive/).

# "Running" the Proofs
Once Isabelle is installed and the ROOTS file has been updated, the proofs can be "run" by opening top_proof.thy (located in the root of this repository) in Isabelle.

## (Optional) Building Theory Document as a pdf
To build the theory document, select "Ironbark_execution" from the dropdown list in the theories panel, and restart Isabelle. This should cause Isabelle to build the dependencies for Ironbark, and most of the Ironbark results, and may take some time. Once finished, select "Ironbark_processor" from the dropdown list in the theories panel, and restart Isabelle. This will build the remainder of the theories and build the theory document as a pdf.

# Review
The contents of this folder owes thanks to the review by Micah Brown, Brendan Mahoney, and Jim McCarthy.

# Licence
    Copyright (C) 2023 Commonwealth of Australia
        Micah Brown
        Brendan Mahony
        Jim McCarthy

    This file is part of Ironbark.

    This program is free software: you can redistribute it and/or modify
    it under the terms of the GNU General Public License as published by
    the Free Software Foundation, either version 3 of the License, or
    (at your option) any later version.

    This program is distributed in the hope that it will be useful,
    but WITHOUT ANY WARRANTY; without even the implied warranty of
    MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
    GNU General Public License for more details.

    You should have received a copy of the GNU General Public License
    along with this program. If not, see <http://www.gnu.org/licenses/>.