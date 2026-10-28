module

public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.SporadicActions.J4.PairActions.Coverage.FixedTwoSubgroup.Elementary.InvolutionAbsorption.QuotientIncidence.FiniteIncidence.Obstructions.Representatives000
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.SporadicActions.J4.PairActions.Coverage.FixedTwoSubgroup.Elementary.InvolutionAbsorption.QuotientIncidence.FiniteIncidence.Obstructions.Representatives010
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.SporadicActions.J4.PairActions.Coverage.FixedTwoSubgroup.Elementary.InvolutionAbsorption.QuotientIncidence.FiniteIncidence.Obstructions.Representatives020
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.SporadicActions.J4.PairActions.Coverage.FixedTwoSubgroup.Elementary.InvolutionAbsorption.QuotientIncidence.FiniteIncidence.Obstructions.Representatives030
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.SporadicActions.J4.PairActions.Coverage.FixedTwoSubgroup.Elementary.InvolutionAbsorption.QuotientIncidence.FiniteIncidence.Obstructions.Representatives040
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.SporadicActions.J4.PairActions.Coverage.FixedTwoSubgroup.Elementary.InvolutionAbsorption.QuotientIncidence.FiniteIncidence.Obstructions.Representatives050
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.SporadicActions.J4.PairActions.Coverage.FixedTwoSubgroup.Elementary.InvolutionAbsorption.QuotientIncidence.FiniteIncidence.Obstructions.Representatives060
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.SporadicActions.J4.PairActions.Coverage.FixedTwoSubgroup.Elementary.InvolutionAbsorption.QuotientIncidence.FiniteIncidence.Obstructions.Representatives070
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.SporadicActions.J4.PairActions.Coverage.FixedTwoSubgroup.Elementary.InvolutionAbsorption.QuotientIncidence.FiniteIncidence.Obstructions.Representatives080
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.SporadicActions.J4.PairActions.Coverage.FixedTwoSubgroup.Elementary.InvolutionAbsorption.QuotientIncidence.FiniteIncidence.Obstructions.Representatives090
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.SporadicActions.J4.PairActions.Coverage.FixedTwoSubgroup.Elementary.InvolutionAbsorption.QuotientIncidence.FiniteIncidence.Obstructions.Representatives100

/-!
# Candidate memberships and power obstructions for finite incidence

The four published generators lie in both concrete candidates. Each of the
110 representatives either lies in a candidate or generates, together with the
base subgroup, an element whose 2304th power is nonidentity. The certificates
check the actual matrix words, inverse right action on the line, and expressions
in the three generators of the second candidate. For the excluded cases, small
powers give nonidentity elements killed by 5, 7, or 11, all coprime to 2304.

Source context: Aschbacher–Smith, Proposition 1.3.4, printed p.511/PDF p.528,
citing Aschbacher (1986). This proves the finite alternatives only; subgroup
order and exhaustive double-coset coverage are independent obligations.
-/

public section
open Subgroup
namespace CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.SporadicActions.J4Reduction.FiniteIncidence
open ObstructionCertificate

theorem baseSubgroup_le_line : baseSubgroup ≤ involutionMatrixLineStabilizer := by
  apply (baseSubgroup_le_iff _).mpr
  intro i
  fin_cases i
  · exact s0_line
  · exact s1_line
  · exact s2_line
  · exact s3_line

theorem baseSubgroup_le_second : baseSubgroup ≤ involutionMatrixSecondSubgroup := by
  apply (baseSubgroup_le_iff _).mpr
  intro i
  fin_cases i
  · exact s0_second
  · exact s1_second
  · exact s2_second
  · exact s3_second

theorem representative_alternatives (j : Fin 110) :
    representative j ∈ involutionMatrixLineStabilizer ∨
    representative j ∈ involutionMatrixSecondSubgroup ∨
    ∃ x ∈ baseSubgroup ⊔ Subgroup.zpowers (representative j), x ^ 2304 ≠ 1 := by
  fin_cases j
  · exact alternative0
  · exact alternative1
  · exact alternative2
  · exact alternative3
  · exact alternative4
  · exact alternative5
  · exact alternative6
  · exact alternative7
  · exact alternative8
  · exact alternative9
  · exact alternative10
  · exact alternative11
  · exact alternative12
  · exact alternative13
  · exact alternative14
  · exact alternative15
  · exact alternative16
  · exact alternative17
  · exact alternative18
  · exact alternative19
  · exact alternative20
  · exact alternative21
  · exact alternative22
  · exact alternative23
  · exact alternative24
  · exact alternative25
  · exact alternative26
  · exact alternative27
  · exact alternative28
  · exact alternative29
  · exact alternative30
  · exact alternative31
  · exact alternative32
  · exact alternative33
  · exact alternative34
  · exact alternative35
  · exact alternative36
  · exact alternative37
  · exact alternative38
  · exact alternative39
  · exact alternative40
  · exact alternative41
  · exact alternative42
  · exact alternative43
  · exact alternative44
  · exact alternative45
  · exact alternative46
  · exact alternative47
  · exact alternative48
  · exact alternative49
  · exact alternative50
  · exact alternative51
  · exact alternative52
  · exact alternative53
  · exact alternative54
  · exact alternative55
  · exact alternative56
  · exact alternative57
  · exact alternative58
  · exact alternative59
  · exact alternative60
  · exact alternative61
  · exact alternative62
  · exact alternative63
  · exact alternative64
  · exact alternative65
  · exact alternative66
  · exact alternative67
  · exact alternative68
  · exact alternative69
  · exact alternative70
  · exact alternative71
  · exact alternative72
  · exact alternative73
  · exact alternative74
  · exact alternative75
  · exact alternative76
  · exact alternative77
  · exact alternative78
  · exact alternative79
  · exact alternative80
  · exact alternative81
  · exact alternative82
  · exact alternative83
  · exact alternative84
  · exact alternative85
  · exact alternative86
  · exact alternative87
  · exact alternative88
  · exact alternative89
  · exact alternative90
  · exact alternative91
  · exact alternative92
  · exact alternative93
  · exact alternative94
  · exact alternative95
  · exact alternative96
  · exact alternative97
  · exact alternative98
  · exact alternative99
  · exact alternative100
  · exact alternative101
  · exact alternative102
  · exact alternative103
  · exact alternative104
  · exact alternative105
  · exact alternative106
  · exact alternative107
  · exact alternative108
  · exact alternative109

end CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.SporadicActions.J4Reduction.FiniteIncidence
