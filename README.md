# A formal correspondence between elements of HRBn and B-approximable real numbers

# Authors
Nicolas Magaud

# Compiling the development

Works with Coq 8.10.2 (January 2020).

1/ Download exact-real-arithmetic-homework3 from github (choose download and unzip in the directory coq)
2/ Compile the HR directory (make in the appropriate directory)
3/ make COQFLAGS="-R ../exact-real-arithmetic-homework3 ExactRealArithmetic -R ../HR HR -R . Top"


# Sources

derived from HRBnVMM.tex

# TODO

proving Hrw_Vmm2 in Rw_VMM_Elie.v or showing it is a false statement

# Changes 

encadrement_nat (changed n:nat into n:Z)
remove soustractionIZR and replace it with Z_R_minus
remove superieurausucc and replace it with Zarith_inegalites.Zlt_le_Zs