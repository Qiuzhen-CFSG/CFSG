module
public import Theory.SpecificGroups.SU3.SmallThreeCore
public import Theory.SpecificGroups.SU3.EvenProjectiveComparison
public import Theory.GroupTheory.PCoreQuotientInnerJoin
public import Theory.ElementaryAbelian.AutomorphismLinearEmbedding
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card

/-!
# The two-primary enlargement bound for PSU₃(2)

Restriction to the characteristic elementary nine detects every automorphism
preserving an actual Sylow two-subgroup. The resulting embedding in GL₂(3)
bounds a two-group of such actors by sixteen. If it contains the inner image
of an actual Sylow, its intersection with the full inner group has order at
least eight. Consequently adjoining it to the inner group has relative index
at most two; a strict enlargement has order 144.

This retains the possible outer involution in the small projective row. It
supplies the literal enlargement alternative in the source application, not
an exclusion of that alternative. Source: DGS, Groups and Graphs (1985),
p.104 and 6.1, pp.118--119.
-/

public noncomputable section
open Subgroup MulAction
namespace BenderSuzuki.MatrixGroups.HermitianForm.SmallThreeCore
variable {F : Type*} [Field F] [Finite F] (J : HermitianForm 3 F)

/-- A faithful Sylow-preserving two-group of PSU₃(2) automorphisms has order dividing sixteen. -/
theorem projective_two_actor_card_dvd_sixteen
    (hc : Nat.card F = 2^2) (hconj : ∀ x, J.conj x = x^2)
    {A : Type*} [Group A] [Finite A] (hp : IsPGroup 2 A)
    (action : A →* MulAut (ProjectiveSpecialUnitaryMatrixGroup J))
    (hi : Function.Injective action)
    (T : Sylow 2 (ProjectiveSpecialUnitaryMatrixGroup J))
    (hT : ∀ a : A, (T : Subgroup _).map (action a).toMonoidHom = T) :
    Nat.card A ∣ 16 := by
  let N := pCore 3 (ProjectiveSpecialUnitaryMatrixGroup J)
  let : Finite (ProjectiveSpecialUnitaryMatrixGroup J) :=
    Nat.finite_of_card_ne_zero (by rw [FixedFieldTwo.card_projective J hc hconj]; decide)
  let := (projective_core_structure J hc hconj).2.1
  let r : A →* MulAut N := (MulAut.characteristic N).comp action
  have hr : Function.Injective r := by
    apply r.ker_eq_bot_iff.mp
    apply (eq_bot_iff_forall _).mpr
    intro a ha
    apply hi
    rw [action.map_one]
    apply projective_aut_eq_one_of_core_and_sylow J hc hconj T (action a) (hT a)
    intro n hn
    exact congrArg Subtype.val (DFunLike.congr_fun ha (⟨n,hn⟩ : N))
  obtain ⟨f,hf⟩ := IsElementaryAbelian.exists_injective_mulAut_generalLinear_of_card_le
    (p := 3) (n := 2) N (by rw [(projective_core_structure J hc hconj).1]; decide)
  have hd : Nat.card A ∣ 48 := by
    have hd := card_dvd_of_injective (f.comp r) (hf.comp hr)
    have h48 : Nat.card (Matrix.GeneralLinearGroup (Fin 2) (ZMod 3)) = 48 := by
      rw [Matrix.card_GL_field]
      norm_num [Fin.prod_univ_succ, ZMod.card]
    exact h48 ▸ hd
  obtain ⟨n,hn⟩ := hp.exists_card_eq
  rw [hn] at hd ⊢
  have hle : n ≤ 4 := by
    by_contra hh
    have h32 : 32 ∣ 48 := (pow_dvd_pow 2 (by omega : 5 ≤ n)).trans hd
    norm_num at h32
  exact pow_dvd_pow 2 hle

/-- A Sylow-preserving two-subgroup containing the original inner Sylow enlarges
PSU3(2) by at most a factor of two. -/
theorem projective_inner_join_two_actor_index
    (hc : Nat.card F = 2^2) (hconj : ∀ x, J.conj x = x^2)
    (A : Subgroup (MulAut (ProjectiveSpecialUnitaryMatrixGroup J)))
    (hp : IsPGroup 2 A)
    (T : Sylow 2 (ProjectiveSpecialUnitaryMatrixGroup J))
    (hT : ∀ a : A, (T : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)).map
      (a : MulAut (ProjectiveSpecialUnitaryMatrixGroup J)).toMonoidHom = T)
    (U : Sylow 2 (ProjectiveSpecialUnitaryMatrixGroup J))
    (hU : (U : Subgroup _).map (MulAut.conj : _ →* MulAut _) ≤ A) :
    let I := MulAut.innerSubgroup (ProjectiveSpecialUnitaryMatrixGroup J)
    I.relIndex (I ⊔ A) ≤ 2 ∧
      (I ⊔ A = I ∨ Nat.card (I ⊔ A : Subgroup _) = 144) := by
  let D := ProjectiveSpecialUnitaryMatrixGroup J
  let : Finite D := Nat.finite_of_card_ne_zero
    (by rw [FixedFieldTwo.card_projective J hc hconj]; decide)
  let I := MulAut.innerSubgroup D
  have hz : center D = ⊥ := EvenProjectiveComparison.center_eq_bot J
    (n := 1) (by decide) (by simpa using hc) (by simpa using hconj)
  have hinj := Theory.GroupTheory.conj_injective_of_center_eq_bot hz
  let f : U →* I.subgroupOf A :=
    (((MulAut.conj : D →* MulAut D).comp (U : Subgroup D).subtype).codRestrict A
      (fun u => hU (mem_map_of_mem _ u.property))).codRestrict (I.subgroupOf A)
      (fun u => ⟨u.val,rfl⟩)
  have hf : Function.Injective f := by
    intro u v he
    exact Subtype.ext (hinj (congrArg (fun a : I.subgroupOf A => (a : MulAut D)) he))
  have hUc : Nat.card U = 8 := by
    rw [U.card_eq_multiplicity,FixedFieldTwo.card_projective J hc hconj]
    decide +kernel
  have h8 : 8 ≤ Nat.card (I.subgroupOf A) :=
    hUc ▸ Nat.card_le_card_of_injective f hf
  have h16 : Nat.card A ≤ 16 := Nat.le_of_dvd (by decide)
    (projective_two_actor_card_dvd_sixteen J hc hconj hp A.subtype A.subtype_injective T hT)
  have hmul := (I.subgroupOf A).card_mul_index
  have hidx : I.relIndex A ≤ 2 := by
    change Nat.card (I.subgroupOf A) * I.relIndex A = Nat.card A at hmul
    nlinarith
  have hidx' : I.relIndex (I ⊔ A) ≤ 2 := by
    rwa [relIndex_sup_left]
  refine ⟨hidx', ?_⟩
  by_cases he : I ⊔ A = I
  · exact Or.inl he
  right
  have hnot : I.relIndex (I ⊔ A) ≠ 1 := by
    intro hh
    exact he (le_antisymm (relIndex_eq_one.mp hh) le_sup_left)
  have hpos : 0 < I.relIndex (I ⊔ A) := Nat.pos_of_ne_zero (Subgroup.index_ne_zero_of_finite (H := I.subgroupOf (I ⊔ A)))
  have htwo : I.relIndex (I ⊔ A) = 2 := by omega
  have hIc : Nat.card I = 72 := by
    rw [←Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv,
      FixedFieldTwo.card_projective J hc hconj]
  have hcard : Nat.card (I.subgroupOf (I ⊔ A)) = 72 :=
    (Nat.card_congr (subgroupOfEquivOfLe (show I ≤ I ⊔ A from le_sup_left)).toEquiv).trans hIc
  have hh := (I.subgroupOf (I ⊔ A)).card_mul_index
  change Nat.card (I.subgroupOf (I ⊔ A)) * I.relIndex (I ⊔ A) = _ at hh
  rw [hcard,htwo] at hh
  exact hh.symm
end BenderSuzuki.MatrixGroups.HermitianForm.SmallThreeCore
