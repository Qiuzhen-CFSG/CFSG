module

public import Glauberman.DicksonClassification
public import GorensteinWalter.LinearThreeEquiv
public import GorensteinWalter.LinearRingEquiv
public import Theory.GroupTheory.SolvableNormalSup
public import Theory.SpecificGroups.SymmetricFourSolvable
public import Theory.SpecificGroups.DihedralSolvable
public import Theory.AtlasPort.ExceptionalIsomorphisms.Order360
public import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple

/-!
# Proper subgroups of A₆ through its projective-line model

Dickson's actual subgroup theorem for PSL₂(9) leaves solvable groups and
copies of A₅. Its proper subfields have order three, so the corresponding
PSL₂ and PGL₂ groups are the proved A₄ and S₄ models. The full PSL₂(9)
case is excluded by properness. The checked PSL₂(9) ≃ A₆ equivalence
transports this classification to any isomorphic carrier.

Sources: Huppert II.8.27 via `Glauberman.DicksonClassification`, and the
PSL₂(9)/A₆ action comparison in
`Theory.AtlasPort.ExceptionalIsomorphisms.Order360`. This supplies the
A₆ subgroup calculation for Aschbacher–Smith, Theorem 0.1.2(3), condition K,
printed pp.4 and 482. No classification by abstract order is used.
-/

namespace CFSG.Quasithin.MainConverse

open BenderSuzuki.MatrixGroups GorensteinWalter Glauberman.Dickson


private noncomputable def field_three : ZMod 3 ≃+* GaloisField 3 1 := by
  letI : Fintype (GaloisField 3 1) := Fintype.ofFinite _
  apply FiniteField.ringEquivOfCardEq
  have hGF : Fintype.card (GaloisField 3 1) = 3 := by
    simpa [Nat.card_eq_fintype_card] using GaloisField.card 3 1 (by simp)
  simp [hGF]

private theorem psl2Nine_subgroup_solvable_or_altFive (H : Subgroup (PSL2MatrixGroup (GaloisField 3 2)))
    (hproper : H ≠ ⊤) :
    Group.IsSolvable H ∨ Nonempty (H ≃* alternatingGroup (Fin 5)) := by
  let : Fact (Nat.Prime 3) := ⟨by decide⟩
  have hFcard : Nat.card (GaloisField 3 2) = 3 ^ 2 := GaloisField.card 3 2 (by decide)
  rcases huppert_II_8_27_dickson_psl2_subgroup_classification
      (p := 3) (f := 2) hFcard H with
      hEl | hCy | hDi | hA4 | hS4 | hA5 | hSemi | hPSL | hPGL
  · left
    let : IsElementaryAbelian 3 H := hEl
    exact Group.isSolvable_of_comm fun a b => IsMulCommutative.is_comm.comm a b
  · left
    obtain ⟨_, _, _, hcyc⟩ := hCy
    let : IsCyclic H := hcyc
    let : CommGroup H := IsCyclic.commGroup
    infer_instance
  · left
    obtain ⟨z, _, _, ⟨e⟩⟩ := hDi
    let : Group.IsSolvable (DihedralGroup z) := GLS3.Chapter5.dihedralGroup_isSolvable z
    exact Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective
  · left
    obtain ⟨_, ⟨e⟩⟩ := hA4
    let : Group.IsSolvable (alternatingGroup (Fin 4)) := alternatingGroup_fin_four_isSolvable
    exact Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective
  · left
    obtain ⟨_, ⟨e⟩⟩ := hS4
    let : Group.IsSolvable (Equiv.Perm (Fin 4)) := Equiv.Perm.isSolvable_fin_four
    exact Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective
  · exact Or.inr hA5.2
  · left
    obtain ⟨_, _, _, _, N, C, hNnormal, hNelem, _, hCcyc, _, _, hsup⟩ := hSemi
    let : N.Normal := hNnormal
    let : IsElementaryAbelian 3 N := hNelem
    let : IsCyclic C := hCcyc
    let : CommGroup C := IsCyclic.commGroup
    let : Group.IsSolvable N := Group.isSolvable_of_comm fun a b =>
      IsMulCommutative.is_comm.comm a b
    exact Group.isSolvable_of_normal_sup_eq_top N C hsup
  · obtain ⟨m, _, hmdiv, ⟨e⟩⟩ := hPSL
    rcases (Nat.dvd_prime Nat.prime_two).mp hmdiv with hm1 | hm2
    · left
      subst m
      let eA : PSL2MatrixGroup (GaloisField 3 1) ≃* alternatingGroup (Fin 4) :=
        (psl2RingEquiv field_three).symm.trans psl2_three_equiv_alternatingGroup
      let : Group.IsSolvable (alternatingGroup (Fin 4)) := alternatingGroup_fin_four_isSolvable
      exact Group.isSolvable_of_isSolvable_injective
        (f := (e.trans eA).toMonoidHom) (e.trans eA).injective
    · subst m
      exact (hproper (H.eq_top_of_card_eq (Nat.card_congr e.toEquiv))).elim
  · left
    obtain ⟨m, hm, hmdiv, ⟨e⟩⟩ := hPGL
    have hm1 : m = 1 := by
      have hb := Nat.le_of_dvd (by decide : 0 < 2) hmdiv
      omega
    subst m
    let eS : Matrix.ProjGenLinGroup (Fin 2) (GaloisField 3 1) ≃*
        Equiv.Perm (Fin 4) := (pgl2RingEquiv field_three).symm.trans pgl2_three_equiv_perm
    let : Group.IsSolvable (Equiv.Perm (Fin 4)) := Equiv.Perm.isSolvable_fin_four
    exact Group.isSolvable_of_isSolvable_injective
      (f := (e.trans eS).toMonoidHom) (e.trans eS).injective

/-- A proper subgroup of the actual A₆ is solvable or isomorphic to A₅. -/
public theorem alternatingSix_subgroup_solvable_or_altFive {G : Type*} [Group G] (e : G ≃* alternatingGroup (Fin 6))
    (H : Subgroup G) (hH : H ≠ ⊤) :
    Group.IsSolvable H ∨ Nonempty (H ≃* alternatingGroup (Fin 5)) := by
  let a := e.trans Atlas.Comparisons.Exceptional.psl2NineEquivAlt6.symm
  have hp : H.map a.toMonoidHom ≠ ⊤ := by
    intro h
    apply hH
    have hh := congrArg (Subgroup.map a.symm.toMonoidHom) h
    simpa [Subgroup.map_map] using hh
  let b := Subgroup.equivMapOfInjective H a.toMonoidHom a.injective
  rcases psl2Nine_subgroup_solvable_or_altFive (H.map a.toMonoidHom) hp with hs | hc
  · let := hs
    exact Or.inl (Group.isSolvable_of_isSolvable_injective (f := b.toMonoidHom) b.injective)
  · obtain ⟨c⟩ := hc
    exact Or.inr ⟨b.trans c⟩

end CFSG.Quasithin.MainConverse
