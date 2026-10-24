import PFUL.InfiniteLink
import PFUL.QubitTensor
import PFUL.AFNBPure
import PFUL.KrausAny
import PFUL.PureFiniteInf
import PFUL.CounterexampleInfLink
-- gap (b)
#print axioms PFUL.Counterexample.mul_conjTranspose_eq_one
#print axioms PFUL.Counterexample.exists_finite_compression
#print axioms PFUL.Counterexample.isPureKer_of_isPure
#print axioms PFUL.Counterexample.isUnitaryKer_of_isPure
#print axioms PFUL.Counterexample.isPureHilbert_of_isPure
#print axioms PFUL.Counterexample.isPure_iff_isUnitaryKer
#print axioms PFUL.Counterexample.isPure_iff_isPureHilbert
#print axioms PFUL.Counterexample.isPure_iff_isPureKer
-- gap (c)
#print axioms PFUL.PM.exists_unitary_of_unitaryLink
#print axioms PFUL.PM.unitaryLink_choiPM
#print axioms PFUL.PM.isPurePM_iff
-- gap (d)
#print axioms PFUL.Countable.KernelPSD.exists_factor_any
#print axioms PFUL.Countable.exists_kraus_of_choi_any
#print axioms exists_kraus_of_normalCPTP_any
#print axioms isNormalCPTP_iff_kraus_any
#print axioms PFUL.Counterexample.valid_normalCPTP_Vsb_any
-- gap (a)
#print axioms PFUL.PM.psd_norm_le
#print axioms PFUL.PM.posSemidef_of_sections
#print axioms PFUL.PM.link_posSemidef_any
#print axioms PFUL.PM.hasSum_pi_prod_any
#print axioms PFUL.PM.isCPTPChoi_reduceKer
#print axioms PFUL.PM.IsValidPM.isValidPMInf
#print axioms PFUL.PM.isValidPMInf_iff
#print axioms PFUL.PM.isIsoKernel_lmat
#print axioms PFUL.PM.isUnitaryKer_lmat
#print axioms PFUL.PM.isPurePMInf_iff
-- C² ⊗ K
#print axioms PFUL.Counterexample.qsplitEquiv
#print axioms PFUL.Counterexample.completeSpace_qubitTensor
#print axioms PFUL.Counterexample.qubitBasis
#print axioms PFUL.Counterexample.qubitBasis_apply
#print axioms PFUL.Counterexample.isPure_qubitTensor
-- counterexample, infinite-ancilla link product
#print axioms PFUL.Counterexample.isValidPMInf_Wcl_iff
#print axioms PFUL.Counterexample.isPurePMInf_choiMat_Vsb
#print axioms PFUL.Counterexample.purification_conjecture_false_choiInf
