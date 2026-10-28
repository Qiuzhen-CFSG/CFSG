module
public import Theory.SpecificGroups.ProjectiveLinearInvolutions
public import Theory.SpecificGroups.GL2.SemidihedralSylow
public import Theory.SpecificGroups.SL3.InvolutionConjugacy
public import Theory.SpecificGroups.SL3.CenterProjectiveComparison
public import Theory.GroupTheory.SingleInvolutionClassSylow
public import Theory.GroupTheory.SylowCoprimeEquivalence
/-!
# Sylow centers in odd PSL₃ in the semidihedral congruence

The explicit GL₂ Sylow has center of order two. Its determinant-corrected
block embedding identifies an involution centralizer in SL₃, of odd index
by the single involution class. The central cubic projective quotient
preserves Sylow two-subgroups. These actual comparisons prove the assertion
for every prescribed PSL₃ Sylow, including the field of order three.
Source: ABG II.2 Lemma 1; Aschbacher–Smith E.2.2(2d), printed pp.215–216.
-/
public section
open Subgroup Matrix
open scoped MatrixGroups
namespace Matrix.PSL3.OddSylowCenter
variable (F:Type*) [Field F] [Finite F]
theorem card_center (hmod:Nat.card F%4=3) (T:Sylow 2 PSL(3,F)) :
    Nat.card (center T)=2 := by
  have hodd : Odd (Nat.card F) := Nat.odd_iff.mpr (by omega)
  have h2 : (2:F)≠0 := Field.two_ne_zero_of_odd_card F hodd
  obtain ⟨P,n,hn,_,a,b,ha,_,_,_,hZ,_⟩ :=
    GeneralLinearGroup.exists_semidihedral_sylow F hmod
  have hPZ : Nat.card (center P)=2 := by
    rw [hZ,Nat.card_zpowers,orderOf_pow_of_dvd (by positivity)
      (ha ▸ Nat.pow_dvd_pow 2 (by omega : n-2≤n-1)),ha]
    rw [show n-1=(n-2)+1 by omega,pow_succ,Nat.mul_div_cancel_left _ (by positivity)]
  let S:Sylow 2 SL(3,F) := Classical.choice inferInstance
  have hi := odd_index_centralizer_of_one_involution_class
    (SL3.standardInvolution F) (SL3.standardInvolution_orderOf F h2)
    (fun z hz=>SL3.involution_isConj_standard F z hz h2)
  obtain ⟨e⟩ := sylow_equiv_of_odd_index _ hi
    (SL3.standardInvolutionCentralizerEquiv F h2).symm S P
  have hk : Nat.Coprime 2 (Nat.card (projection F).ker) := by
    rw [projection_ker]
    exact Nat.coprime_two_left.mpr (SL3.odd_card_center F)
  let eT := Sylow.equivOfSurjectiveCoprime (projection F) (projection_surjective F) hk S T
  rw [← Nat.card_congr (Subgroup.centerCongr eT).toEquiv,
    Nat.card_congr (Subgroup.centerCongr e).toEquiv]
  exact hPZ
end Matrix.PSL3.OddSylowCenter
