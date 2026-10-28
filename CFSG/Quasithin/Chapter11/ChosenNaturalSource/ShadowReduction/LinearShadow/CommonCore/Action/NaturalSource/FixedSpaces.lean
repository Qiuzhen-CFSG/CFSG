module

public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.LinearShadow.CommonCore.Action.NaturalSource.Orbit
public import Theory.GroupAction.AutomorphismFixedSubgroup
public import Mathlib.GroupTheory.GroupAction.FixedPoints

/-!
# Uniform fixed spaces of the selected star image

Once the selected A-star has the source rank n = s(G,V), every nonidentity
cyclic subgroup has corank less than n. Pulling it back along the literal
star projection and applying E.3.6 gives its fixed space on the original V_H.
The conclusion uses the actual automorphism induced by the star element.
The rank/Sylow assertion is a separate input, not proved by this calculation.

Source: Aschbacher--Smith, 11.3.7, printed p.773, and E.3.6, printed p.232.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.CommonCore

private theorem corank_lt_rank {X : Type*} [Group X] [Finite X]
    {A B : Subgroup X} [IsElementaryAbelian 2 A] (hBA : B ≤ A) (hB : B ≠ ⊥) :
    Nat.log 2 (B.relIndex A) < Representation.BinaryOffender.rank A := by
  let : Nontrivial B := (nontrivial_iff_ne_bot B).mpr hB
  have hcardB : 1 < Nat.card (B.subgroupOf A) := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hBA).toEquiv]
    exact Finite.one_lt_card
  have hpos : 0 < B.relIndex A := Nat.pos_of_ne_zero
    (B.subgroupOf A).index_ne_zero_of_finite
  have hc := (B.subgroupOf A).index_mul_card
  change B.relIndex A * Nat.card (B.subgroupOf A) = Nat.card A at hc
  obtain ⟨r,hr⟩ := (IsElementaryAbelian.isPGroup 2 A).exists_card_eq
  have hp : Nat.card A = 2 ^ Representation.BinaryOffender.rank A := by
    rw [Representation.BinaryOffender.rank,hr,Nat.log_pow (by decide : 1 < 2)]
  apply (Nat.log_lt_iff_lt_pow (by decide) (Nat.ne_of_gt hpos)).mpr
  rw [← hp,← hc]
  nlinarith

variable {G : Type*} [Group G] (T : Sylow 2 G) (H : Subgroup G)

private theorem lift_star_subgroup {A : Subgroup G} (hAH : A ≤ H)
    (B : Subgroup (Star T H))
    (hB : B ≤ (A.subgroupOf H).map (starProjection T H)) :
    ∃ C ≤ A, (C.subgroupOf H).map (starProjection T H) = B ∧
      ChapterE.subgroupCorank A C =
        Nat.log 2 (B.relIndex ((A.subgroupOf H).map (starProjection T H))) := by
  let q := starProjection T H
  let C₀ := A.subgroupOf H ⊓ B.comap q
  let C := C₀.map H.subtype
  have hCA : C ≤ A := by rintro _ ⟨c,hc,rfl⟩; exact hc.1
  have hCH : C.subgroupOf H = C₀ := comap_map_eq_self_of_injective H.subtype_injective C₀
  have him : C₀.map q = B := by
    apply le_antisymm
    · rintro _ ⟨x,hx,rfl⟩; exact hx.2
    · intro b hb
      obtain ⟨x,hx,he⟩ := hB hb
      exact ⟨x,⟨hx,(show q x ∈ B from he.symm ▸ hb)⟩,he⟩
  refine ⟨C,hCA,?_,?_⟩
  · change (C.subgroupOf H).map q = B
    rw [hCH,him]
  · unfold ChapterE.subgroupCorank
    congr 1
    rw [← relIndex_subgroupOf (H := C) hAH,hCH]
    exact (inf_relIndex_left (A.subgroupOf H) (B.comap q)).trans
      (relIndex_comap B q (A.subgroupOf H))

variable [Finite G] {T H} {L V : Subgroup G}
    {D : Chapter12.Section02.ChosenModule T L V} {S : D.NonbinaryNaturalInput}
    {U₁ : Submodule (ZMod 2) D.chosenCentralQuotient}

/-- Each nonidentity star element has exactly the full actor's fixed subgroup.
The rank premise is on the literal selected image, with no replacement of A by V. -/
theorem selected_star_uniform_fixed_of_rank
    (s : Hypothesis1131At D S U₁ H) (g : G)
    (hg : V.map (MulAut.conj g).toMonoidHom ≤ (T : Subgroup G))
    (hs : @ChapterE.globalS G _ V D.elementary = (S.field.degree : ℕ∞))
    (hr : Representation.BinaryOffender.rank
      (((V.map (MulAut.conj g).toMonoidHom).subgroupOf H).map (starProjection T H)) =
        S.field.degree)
    (a : Star T H)
    (ha : a ∈ ((V.map (MulAut.conj g).toMonoidHom).subgroupOf H).map (starProjection T H))
    (ha1 : a ≠ 1) :
    (starAction T H a).fixedSubgroup =
      (centralizer (V.map (MulAut.conj g).toMonoidHom : Set G)).subgroupOf
        (omegaClosure T H) := by
  let := D.elementary
  let A := V.map (MulAut.conj g).toMonoidHom
  let : IsElementaryAbelian 2 A := IsElementaryAbelian.map _
  have hAH : A ≤ H := hg.trans s.outside.1.1.2
  let : IsElementaryAbelian 2 (A.subgroupOf H) := IsElementaryAbelian.subgroupOf hAH
  let Astar := (A.subgroupOf H).map (starProjection T H)
  let : IsElementaryAbelian 2 Astar := IsElementaryAbelian.map _
  have hB : zpowers a ≤ Astar := zpowers_le.mpr ha
  have hB0 : zpowers a ≠ ⊥ := by
    intro he
    exact ha1 (mem_bot.mp (he ▸ mem_zpowers a))
  obtain ⟨C,hCA,hCB,hindex⟩ := lift_star_subgroup T H hAH (zpowers a) hB
  have hcor : (ChapterE.subgroupCorank A C : ℕ∞) < ChapterE.globalS A := by
    rw [ChapterE.globalS_map_equiv V (MulAut.conj g),hs,hindex]
    exact_mod_cast (hr ▸ corank_lt_rank hB hB0)
  have he := ChapterE.centralizer_inf_eq_of_corank_lt_globalS hCA hcor
    (@IsElementaryAbelian.isPGroup 2 _ _ (source_omegaClosure_elementary s))
  ext v
  rw [MulAut.mem_fixedSubgroup]
  change starAction T H a v = v ↔ (v : G) ∈ centralizer (A : Set G)
  constructor
  · intro hv
    apply (he.le ⟨v.property,?_⟩).2
    intro c hc
    have hcB : starProjection T H ⟨c,hAH (hCA hc)⟩ ∈ zpowers a :=
      hCB ▸ mem_map_of_mem (starProjection T H) hc
    obtain ⟨j,hj⟩ := hcB
    have hf : starAction T H (starProjection T H ⟨c,hAH (hCA hc)⟩) v = v := by
      rw [← hj,map_zpow]
      exact MulAction.mem_fixedBy_zpow (G := MulAut (omegaClosure T H)) hv j
    have hcfix := congrArg (fun w : omegaClosure T H => (w : G)) hf
    rw [starAction_apply] at hcfix
    exact mul_inv_eq_iff_eq_mul.mp hcfix
  · intro hv
    obtain ⟨x,hx,rfl⟩ := ha
    apply Subtype.ext
    rw [starAction_apply]
    exact mul_inv_eq_iff_eq_mul.mpr (hv x hx)

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.CommonCore
