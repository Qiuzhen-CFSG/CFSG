module
public import Theory.SpecificGroups.AlternatingSix.SylowParabolicAction
public import Theory.Representation.BinaryPermutationAlternatingActions
public import Theory.GroupTheory.SolvableSylowControl.AbelianProduct
public import Theory.GroupTheory.FrobeniusKernelNormalSubgroup
public import CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.Parameter

/-!
# Cartan witnesses for the diagram-moving A₆ row

In a two-group extension of A₆, a proper Sylow overgroup meets A₆ in
order eight or twenty-four. The latter case has index three and forces
the full action to preserve the natural S₆ marking. Thus, when the actual
action moves that marking, every solvable Sylow overgroup is a two-group.
An odd abelian Sylow permuter is trivial, giving Cartan parameter one.

The last lemma detects this movement from inequivalence of the original
seed and its twist, using the actual six-letter permutation action.
NonFFSourceDoubledSymplecticSixCartan supplies the original chosen-module
application, retaining A₆ as the derived binary group.
Source: Aschbacher--Smith 7.3.4, printed p.699, and I.5,
printed pp.419--422, refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped Pointwise IsMulCommutative
namespace CFSG.Quasithin.Chapter7.NormalizedSource.DoubledSymplecticSixCartan
open AlternatingSix.ShadowLocal ChapterE.Section06.FixedPointBounds

variable {X : Type*} [Group X] [Finite X]

private theorem sylow_relative_index (C : Subgroup X) [C.Normal]
    (S : Sylow 2 X) (P : Subgroup X) (hSP : (S : Subgroup X) ≤ P)
    (hgen : C ⊔ (S : Subgroup X) = ⊤) :
    ((S : Subgroup X).subgroupOf C).relIndex (P.subgroupOf C) =
      (S : Subgroup X).relIndex P := by
  have hCP : C ⊔ P = ⊤ := top_unique (hgen ▸ sup_le_sup_left hSP C)
  have hCS : C.relIndex (S : Subgroup X) = C.index := by
    rw [← relIndex_sup_left, hgen, relIndex_top_right]
  have hCPi : C.relIndex P = C.index := by
    rw [← relIndex_sup_left, hCP, relIndex_top_right]
  have hmul := relIndex_inf_mul_relIndex (S : Subgroup X) C P
  have hmul' := relIndex_mul_relIndex ((S : Subgroup X) ⊓ C) S P inf_le_left hSP
  rw [inf_relIndex_left, hCS] at hmul'
  rw [hCPi, ← hmul', mul_comm C.index] at hmul
  have he : (S : Subgroup X).relIndex (C ⊓ P) = (S : Subgroup X).relIndex P :=
    Nat.mul_right_cancel (Nat.pos_of_ne_zero (Subgroup.index_ne_zero_of_finite (H := C))) hmul
  rw [subgroupOf, relIndex_comap, subgroupOf, map_comap_eq, range_subtype, inf_comm]
  simpa only [inf_comm] using he

theorem solvable_sylow_overgroup_two (C : Subgroup X) [C.Normal] (e : C ≃* A6)
    (hq : IsPGroup 2 (X ⧸ C))
    (hout : ¬ (conjugationAction C e).range ≤ natural)
    (S : Sylow 2 X) (P : Subgroup X) (hSP : (S : Subgroup X) ≤ P)
    (hs : Group.IsSolvable P) : IsPGroup 2 P := by
  have hgen : C ⊔ (S : Subgroup X) = ⊤ := by
    simpa only [sup_comm] using S.sup_eq_top_of_quotient_isPGroup C hq
  obtain ⟨Q,hQ⟩ := S.exists_subgroupOf_eq_of_normal C
  let Q' := Q.mapSurjective (f := e.toMonoidHom) e.surjective
  let B := (P.subgroupOf C).map e.toMonoidHom
  have hQB : (Q' : Subgroup A6) ≤ B := by
    apply map_mono
    rw [hQ]
    exact comap_mono hSP
  have hproper : B ≠ ⊤ := by
    intro he
    let := hs
    let j : P.subgroupOf C →* P := {
      toFun x := ⟨x.val.val,x.property⟩
      map_one' := rfl
      map_mul' _ _ := rfl }
    have hj : Function.Injective j := by
      intro x y he
      exact Subtype.ext (Subtype.ext (congrArg (fun z : P => (z : X)) he))
    let : Group.IsSolvable (P.subgroupOf C) := Group.isSolvable_of_isSolvable_injective hj
    let b := (P.subgroupOf C).equivMapOfInjective e.toMonoidHom e.injective
    let : Group.IsSolvable B := Group.isSolvable_of_surjective
      (f := b.toMonoidHom) b.surjective
    have hA : Group.IsSolvable A6 := Group.isSolvable_of_surjective
      (f := ((MulEquiv.subgroupCongr he).trans Subgroup.topEquiv).toMonoidHom)
      ((MulEquiv.subgroupCongr he).trans Subgroup.topEquiv).surjective
    exact Group.IsPerfect.not_isSolvable A6 hA
  have hQcard : Nat.card Q = 8 := by
    have hh := alternatingSylow_card Q'
    change Nat.card ((Q : Subgroup C).map e.toMonoidHom) = 8 at hh
    rwa [card_map_of_injective e.injective] at hh
  have hc := AlternatingSix.ProperSylowOvergroups.card_eight_or_twentyFour Q' B hQB hproper
  have hindex : (Q : Subgroup C).relIndex (P.subgroupOf C) = (S : Subgroup X).relIndex P := by
    rw [hQ]
    exact sylow_relative_index C S P hSP hgen
  have hcount := relIndex_mul_relIndex (⊥ : Subgroup C) Q (P.subgroupOf C) bot_le
    (show (Q : Subgroup C) ≤ P.subgroupOf C by rw [hQ]; exact comap_mono hSP)
  rw [relIndex_bot_left, relIndex_bot_left, hQcard, hindex] at hcount
  have hBcard : Nat.card B = Nat.card (P.subgroupOf C) := card_map_of_injective e.injective
  rw [hBcard] at hc
  rcases hc with hc | hc
  · have hi : (S : Subgroup X).relIndex P = 1 := by
      omega
    have he : P = (S : Subgroup X) := le_antisymm (relIndex_eq_one.mp hi) hSP
    exact he ▸ S.isPGroup'
  · have hi : (S : Subgroup X).relIndex P = 3 := by omega
    exact (hout (AlternatingSix.SylowParabolicAction.parabolic_natural C e S P hSP hgen hi)).elim

theorem odd_permuter_eq_bot (C : Subgroup X) [C.Normal] (e : C ≃* A6)
    (hq : IsPGroup 2 (X ⧸ C))
    (hout : ¬ (conjugationAction C e).range ≤ natural)
    (S : Sylow 2 X) (B : Subgroup X) [IsMulCommutative B]
    (ho : Odd (Nat.card B))
    (hp : (B : Set X) * S = (S : Set X) * B) : B = ⊥ := by
  have hs := solvable_of_odd_abelian_permuting_two_subgroup B S ho S.isPGroup' hp
  have htwo := (solvable_sylow_overgroup_two C e hq hout S
    (B ⊔ (S : Subgroup X)) le_sup_right hs).to_le
      (show B ≤ B ⊔ (S : Subgroup X) from le_sup_left)
  obtain ⟨n,hn⟩ := htwo.exists_card_eq
  apply card_eq_one.mp
  have hzero : n = 0 := by
    by_contra hh
    exact ho.not_two_dvd_nat (hn ▸ dvd_pow_self 2 hh)
  simp only [hn,hzero,pow_zero]

theorem nPrime_le_one (C : Subgroup X) [C.Normal] (e : C ≃* A6)
    (hq : IsPGroup 2 (X ⧸ C))
    (hout : ¬ (conjugationAction C e).range ≤ natural) : nPrime X ≤ 1 := by
  apply nPrime_le_iff.mpr
  intro c w
  let := w.abelian
  have hb := odd_permuter_eq_bot C e hq hout w.sylow w.abelianGroup w.odd w.permutes
  have hc : w.cyclicGroup = ⊥ := bot_unique (hb ▸ w.cyclic_le)
  have he := w.card
  rw [hc,card_bot] at he
  have hh := c.lt_two_pow_self
  omega

theorem automorphism_subgroup_nPrime_le_one (A : Subgroup AutA6)
    (hi : AlternatingSix.ShadowLocal.inner ≤ A) (hout : ¬ A ≤ natural) : nPrime A ≤ 1 := by
  let C := AlternatingSix.ShadowLocal.inner.subgroupOf A
  let e : C ≃* A6 := (subgroupOfEquivOfLe hi).trans innerEquiv.symm
  have hq : IsPGroup 2 (A ⧸ C) := by
    apply IsPGroup.of_card_dvd_pow (n := 2)
    change C.index ∣ 4
    exact inner_index ▸ AlternatingSix.ShadowLocal.inner.relIndex_dvd_index_of_normal A
  have he (x : C) : MulAut.conj (e x) = (x.val : AutA6) := by
    exact congrArg Subtype.val (innerEquiv.apply_symm_apply ⟨x.val.val,x.property⟩)
  have ha : A.subtype = conjugationAction C e := by
    apply eq_conjugationAction_of_compatible
    intro a c
    apply inner_injective
    rw [he]
    change MulAut.conj (a.val (e c)) = (MulAut.conjNormal a c).val.val
    rw [show MulAut.conj (a.val (e c)) = a.val * MulAut.conj (e c) * a.val⁻¹ by ext x; simp]
    rw [he]
    rfl
  apply nPrime_le_one C e hq
  rw [←ha,range_subtype]
  exact hout

open Representation in
theorem nonnatural_of_seed_inequivalent {J U : Type*} [Group J]
    [AddCommGroup U] [Module (ZMod 2) U]
    (ρ : Representation (ZMod 2) J U) (q : J →* A6)
    (e : U ≃ₗ[ZMod 2] BinaryPermutation.natural (Fin 6))
    (he : ∀ j v, e (ρ j v) = BinaryPermutation.alternatingNaturalRepresentation (Fin 6) (q j) (e v))
    (α : MulAut J) (a : AutA6) (ha : ∀ j, a (q j) = q (α j))
    (hne : ¬ ∃ E : U ≃ₗ[ZMod 2] U, ∀ j v, E (ρ j v) = ρ (α j) (E v)) :
    a ∉ natural := by
  rintro ⟨s,hs⟩
  let τ := BinaryPermutation.naturalRepresentation (Fin 6)
  let b : BinaryPermutation.natural (Fin 6) ≃ₗ[ZMod 2] BinaryPermutation.natural (Fin 6) :=
    LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) _ (τ.asGroupHom s)
  let E := (e.trans b).trans e.symm
  apply hne
  refine ⟨E,?_⟩
  intro j v
  apply e.injective
  change e (e.symm (b (e (ρ j v)))) = e (ρ (α j) (E v))
  rw [e.apply_symm_apply,he,he,←ha,←hs]
  change τ s (τ (q j).val (e v)) = τ (s * (q j).val * s⁻¹) (e (e.symm (b (e v))))
  rw [e.apply_symm_apply]
  change τ s (τ (q j).val (e v)) = τ (s * (q j).val * s⁻¹) (τ s (e v))
  simp only [map_mul,Module.End.mul_apply,Representation.inv_self_apply]

end CFSG.Quasithin.Chapter7.NormalizedSource.DoubledSymplecticSixCartan
