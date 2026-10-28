module

public import CFSG.Quasithin.MainConverse.SolvableSections
public import Theory.SpecificGroups.PSL3.BinaryComparison
public import Glauberman.DicksonClassification
public import GorensteinWalter.LinearRingEquiv
public import Theory.GroupTheory.SolvableNormalSup
public import Theory.SpecificGroups.SymmetricFourSolvable
public import Theory.SpecificGroups.DihedralSolvable

/-!
# Proper simple sections of PSL₃(2)

The proved exceptional isomorphism PSL₃(2) ≃ PSL₂(7), transported from an
arbitrary two-element coefficient field, reduces the subgroup calculation
to Dickson's intrinsic theorem. Its A₅ case is excluded by the parameter
restriction, its projective subfield case is the whole group, and its PGL₂
case would require an even positive integer to divide one. All remaining
cases are solvable. Every simple section of a proper subgroup is therefore
actually isomorphic to the additive group of a prime field.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, Main
Hypothesis 0.1.1(K) and Theorem 0.1.2(1), printed p.4, repeated on p.482;
Huppert, *Endliche Gruppen I*, II.8.27. The exceptional isomorphism uses
the common faithful eight-point action; the imported ATLAS port retains its
source attribution and license. No K-group hypothesis enters that proof.

Only inclusion of these finite simple carriers in full K is left explicit.
The general PSL₃(2^f) calculation is separate from this binary endpoint.
-/

namespace CFSG.Quasithin.MainConverse

open CFSG.KnownSimple
open BenderSuzuki.MatrixGroups GorensteinWalter Glauberman.Dickson

private instance prime_seven : Fact (Nat.Prime 7) := ⟨by decide⟩

private theorem psl2Seven_properSubgroup_isSolvable
    (H : Subgroup (PSL2MatrixGroup (GaloisField 7 1))) (hH : H ≠ ⊤) :
    Group.IsSolvable H := by
  let : Fact (Nat.Prime 7) := ⟨by decide⟩
  have hFcard : Nat.card (GaloisField 7 1) = 7 ^ 1 := GaloisField.card 7 1 (by decide)
  rcases huppert_II_8_27_dickson_psl2_subgroup_classification
      (p := 7) (f := 1) hFcard H with
      hEl | hCy | hDi | hA4 | hS4 | hA5 | hSemi | hPSL | hPGL
  · let : IsElementaryAbelian 7 H := hEl
    exact Group.isSolvable_of_comm fun a b => IsMulCommutative.is_comm.comm a b
  · obtain ⟨_, _, _, hcyc⟩ := hCy
    let : IsCyclic H := hcyc
    let : CommGroup H := IsCyclic.commGroup
    infer_instance
  · obtain ⟨z, _, _, ⟨e⟩⟩ := hDi
    let : Group.IsSolvable (DihedralGroup z) := GLS3.Chapter5.dihedralGroup_isSolvable z
    exact Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective
  · obtain ⟨_, ⟨e⟩⟩ := hA4
    let : Group.IsSolvable (alternatingGroup (Fin 4)) := alternatingGroup_fin_four_isSolvable
    exact Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective
  · obtain ⟨_, ⟨e⟩⟩ := hS4
    let : Group.IsSolvable (Equiv.Perm (Fin 4)) := Equiv.Perm.isSolvable_fin_four
    exact Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective
  · norm_num at hA5
  · obtain ⟨_, _, _, _, N, C, hNnormal, hNelem, _, hCcyc, _, _, hsup⟩ := hSemi
    let : N.Normal := hNnormal
    let : IsElementaryAbelian 7 N := hNelem
    let : IsCyclic C := hCcyc
    let : CommGroup C := IsCyclic.commGroup
    let : Group.IsSolvable N := Group.isSolvable_of_comm fun a b =>
      IsMulCommutative.is_comm.comm a b
    exact Group.isSolvable_of_normal_sup_eq_top N C hsup
  · obtain ⟨m, _, hmdiv, ⟨e⟩⟩ := hPSL
    have hm : m = 1 := Nat.dvd_one.mp hmdiv
    subst m
    exact (hH (H.eq_top_of_card_eq (Nat.card_congr e.toEquiv))).elim
  · obtain ⟨m, hm, hmdiv, _⟩ := hPGL
    have h2m : 2 * m = 1 := Nat.dvd_one.mp hmdiv
    omega

/-- Every proper subgroup of the actual binary degree-three model is solvable. -/
public theorem psl3_two_properSubgroup_isSolvable
    {G : Type*} [Group G] (hG : ClassicalGroup.IsPSL G 3 2)
    (U : Subgroup G) (hU : U ≠ ⊤) : Group.IsSolvable U := by
  obtain ⟨F, hF, hfin, hcard, ⟨e⟩⟩ := hG
  let : Fintype (GaloisField 7 1) := Fintype.ofFinite _
  let eF : ZMod 7 ≃+* GaloisField 7 1 := FiniteField.ringEquivOfCardEq (by
    simpa only [← Nat.card_eq_fintype_card, Nat.card_zmod, pow_one] using
      (GaloisField.card 7 1 (by decide)).symm)
  let a : G ≃* PSL2MatrixGroup (GaloisField 7 1) :=
    (e.trans (Matrix.PSL3.binaryEquivPsl2Seven F hcard)).trans (psl2RingEquiv eF)
  have hp : U.map a.toMonoidHom ≠ ⊤ := by
    intro h
    apply hU
    have hh := congrArg (Subgroup.map a.symm.toMonoidHom) h
    simpa [Subgroup.map_map] using hh
  let b := Subgroup.equivMapOfInjective U a.toMonoidHom a.injective
  let : Group.IsSolvable (U.map a.toMonoidHom) := psl2Seven_properSubgroup_isSolvable _ hp
  exact Group.isSolvable_of_isSolvable_injective (f := b.toMonoidHom) b.injective

/-- The section target may lie in a different universe from the ambient group. -/
public theorem psl3_two_simpleSection_isPrimeCyclic
    {G : Type*} [Group G] (hG : ClassicalGroup.IsPSL G 3 2)
    (U : Subgroup G) (hU : U ≠ ⊤) (V : Subgroup U)
    {S : Type*} [Group S] [IsSimpleGroup S]
    (f : V →* S) (hf : Function.Surjective f) : IsPrimeCyclicCarrier S := by
  let : Group.IsSolvable U := psl3_two_properSubgroup_isSolvable hG U hU
  let : Group.IsSolvable S := Group.isSolvable_of_surjective (f := f) hf
  exact primeCyclic_of_solvable_simple S

/-- Quotient formulation, with normality inside the subgroup being quotiented. -/
public theorem psl3_two_simpleQuotient_isPrimeCyclic
    {G : Type*} [Group G] (hG : ClassicalGroup.IsPSL G 3 2)
    (U : Subgroup G) (hU : U ≠ ⊤) (V : Subgroup U)
    (N : Subgroup V) [N.Normal] [IsSimpleGroup (V ⧸ N)] :
    IsPrimeCyclicCarrier (V ⧸ N) :=
  psl3_two_simpleSection_isPrimeCyclic hG U hU V
    (QuotientGroup.mk' N) (QuotientGroup.mk'_surjective N)

/-- The cyclic branch of the catalogue contains every proper simple section. -/
public theorem psl3_two_properK_constructed
    {G : Type*} [Group G] (hG : ClassicalGroup.IsPSL G 3 2) :
    HasProperKSubgroups IsConstructedCarrier G := by
  intro U hU
  let : Group.IsSolvable U := psl3_two_properSubgroup_isSolvable hG U hU
  exact solvable_isKGroup_constructed U

/-- The binary PSL₃ proper-K clause, assuming only finite simple carrier inclusion. -/
public theorem psl3_two_properK_of_catalogue
    {G : Type*} [Group G] [Finite G] {K : GroupClass}
    (hK : ∀ (S : Type _) [Group S] [Finite S] [IsSimpleGroup S],
      IsConstructedCarrier S → K S)
    (hG : ClassicalGroup.IsPSL G 3 2) : HasProperKSubgroups K G := by
  intro U hU S _ hS V f hf
  let := hS
  let : Finite S := Finite.of_surjective f hf
  exact hK S (.cyclic (psl3_two_simpleSection_isPrimeCyclic hG U hU V f hf))

end CFSG.Quasithin.MainConverse
