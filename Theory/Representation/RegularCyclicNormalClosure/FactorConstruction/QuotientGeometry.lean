module

public import Theory.Representation.RegularCyclicNormalClosure.FactorConstruction.QuotientFaithful
public import Theory.Representation.RegularCyclicNormalClosure.FactorConstruction.LocalTI

/-!
# The genuine local Goldschmidt–O'Nan input

For F inside the fixed space, quotienting the actual pointwise fixer action
identifies its fixed space with U/F and its moved space with the injective
image of S. Fixed quotient vectors have fixed lifts because displacements
lie in both F and S. Stabilizing U/F lifts to stabilizing U.

The proved maximal-intersection equality gives TI for the local quotient.
Together with the independent shear-faithfulness argument, this discharges
every clause of the Goldschmidt–O'Nan input. It does not assume ambient TI
or a quotient involution bound.

This supplies the local reduction for Aschbacher–Smith E.6.24, printed
p.255, using the actual hypotheses of GLS Number 2, C.14.1–14.2, printed
pp.85–89 of `books/KGroup/GLS_Number2_ChapterG_GeneralGroupTheory.pdf`.
-/

public section

open Module Subgroup Representation.BinaryOffender
namespace Representation.RegularCyclicNormalClosure
open FactorConstruction
variable {A W : Type*} [Group A] [AddCommGroup W] [Module (ZMod 2) W]
  {ρ : Representation (ZMod 2) A W} {C : Subgroup A}

/-- Quotienting by a subspace of the fixed space gives precisely the image
of the original moved space, with the actor restricted to the actual fixer. -/
theorem movedSpace_quotientOnFixer (F : Submodule (ZMod 2) W)
    (hFU : F ≤ fixedSpace ρ C) :
    displacementSpan (quotientOnFixer ρ F) (C.subgroupOf (pointwiseFixer ρ F)) ⊤ =
      (displacementSpan ρ C ⊤).map F.mkQ := by
  have hCK := (le_pointwiseFixer_iff ρ C F).mpr hFU
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨c, hc, v, _, rfl⟩
    obtain ⟨w, rfl⟩ := F.mkQ_surjective v
    rw [quotientOnFixer_mkQ, ← map_sub]
    exact Submodule.mem_map_of_mem (Submodule.subset_span ⟨c, hc, w, Submodule.mem_top, rfl⟩)
  · apply Submodule.map_le_iff_le_comap.mpr
    apply Submodule.span_le.mpr
    rintro _ ⟨c, hc, v, _, rfl⟩
    change F.mkQ (ρ c v - v) ∈
      displacementSpan (quotientOnFixer ρ F) (C.subgroupOf (pointwiseFixer ρ F)) ⊤
    rw [map_sub]
    exact Submodule.subset_span
      ⟨⟨c, hCK hc⟩, hc, F.mkQ v, Submodule.mem_top, rfl⟩

/-- Quotient-fixed vectors have fixed lifts, since their displacements lie
both in F and in the complementary moved space. -/
theorem Input.fixedSpace_quotientOnFixer (h : Input ρ C)
    (F : Submodule (ZMod 2) W) (hFU : F ≤ fixedSpace ρ C) :
    fixedSpace (quotientOnFixer ρ F) (C.subgroupOf (pointwiseFixer ρ F)) =
      (fixedSpace ρ C).map F.mkQ := by
  have hCK := (le_pointwiseFixer_iff ρ C F).mpr hFU
  apply le_antisymm
  · intro v hv
    obtain ⟨w, rfl⟩ := F.mkQ_surjective v
    refine ⟨w, ?_, rfl⟩
    intro c
    have he := hv ⟨⟨c, hCK c.property⟩, c.property⟩
    change F.mkQ (ρ (c : A) w) = F.mkQ w at he
    have hF := (Submodule.Quotient.eq F).mp he
    have hS : ρ (c : A) w - w ∈ displacementSpan ρ C ⊤ :=
      Submodule.subset_span ⟨c, c.property, w, Submodule.mem_top, rfl⟩
    exact sub_eq_zero.mp (Submodule.disjoint_def.mp h.split.disjoint _ (hFU hF) hS)
  · rintro _ ⟨v, hv, rfl⟩ c
    change F.mkQ (ρ (c.val.val) v) = F.mkQ v
    rw [show ρ (c.val.val) v = v from hv ⟨c.val.val, c.property⟩]

namespace FactorConstruction

/-- The quotient map intertwines the actual action on subspaces. -/
theorem map_quotientOnFixer (F U : Submodule (ZMod 2) W) (g : pointwiseFixer ρ F) :
    (U.map (ρ (g : A))).map F.mkQ =
      (U.map F.mkQ).map (quotientOnFixer ρ F g) := by
  rw [← Submodule.map_comp, ← Submodule.map_comp]
  rfl

/-- Subspaces meeting exactly in the quotient kernel have disjoint images. -/
theorem disjoint_quotient_images (F U V : Submodule (ZMod 2) W)
    (hFV : F ≤ V) (hUV : U ⊓ V = F) : Disjoint (U.map F.mkQ) (V.map F.mkQ) := by
  apply disjoint_iff.mpr
  rw [Submodule.map_inf_eq_map_inf_comap, Submodule.comap_map_mkQ,
    sup_eq_right.mpr hFV, hUV, Submodule.mkQ_map_self]

end FactorConstruction

variable [Finite W]

omit [Finite W] in
/-- The moved space injects into the quotient, so its dimension is unchanged. -/
theorem Input.moved_finrank_quotientOnFixer (h : Input ρ C)
    (F : Submodule (ZMod 2) W) (hFU : F ≤ fixedSpace ρ C) :
    finrank (ZMod 2)
        (displacementSpan (quotientOnFixer ρ F) (C.subgroupOf (pointwiseFixer ρ F)) ⊤) =
      finrank (ZMod 2) (displacementSpan ρ C ⊤) := by
  rw [movedSpace_quotientOnFixer F hFU, ← LinearMap.range_domRestrict]
  apply LinearMap.finrank_range_of_inj
  intro v w he
  apply Subtype.ext
  apply sub_eq_zero.mp
  have hF := (Submodule.Quotient.eq F).mp he
  exact Submodule.disjoint_def.mp h.split.disjoint _ (hFU hF)
    ((displacementSpan ρ C ⊤).sub_mem v.property w.property)

/-- Rank-nullity gives the exact dimension of the quotient's fixed space. -/
theorem Input.fixed_finrank_quotientOnFixer (h : Input ρ C)
    (F : Submodule (ZMod 2) W) (hFU : F ≤ fixedSpace ρ C) :
    finrank (ZMod 2)
        (fixedSpace (quotientOnFixer ρ F) (C.subgroupOf (pointwiseFixer ρ F))) +
      finrank (ZMod 2) F = finrank (ZMod 2) (fixedSpace ρ C) := by
  rw [h.fixedSpace_quotientOnFixer F hFU]
  have hr := (F.mkQ.domRestrict (fixedSpace ρ C)).finrank_range_add_finrank_ker
  rw [LinearMap.range_domRestrict, LinearMap.ker_domRestrict, Submodule.ker_mkQ] at hr
  have he := Submodule.finrank_map_subtype_eq (fixedSpace ρ C)
    (F.comap (fixedSpace ρ C).subtype)
  rw [Submodule.map_comap_subtype, inf_eq_right.mpr hFU] at he
  omega

/-- The actual maximal-intersection quotient satisfies every Goldschmidt–O'Nan
input clause, including faithfulness and TI, under the displayed maximum condition. -/
theorem Input.goldschmidtONan_onFixer (h : Input ρ C)
    (F : Submodule (ZMod 2) W) (hFU : F < fixedSpace ρ C)
    (hsmall : finrank (ZMod 2) (fixedSpace ρ C) ≤ finrank (ZMod 2) F +
      finrank (ZMod 2) (displacementSpan ρ C ⊤))
    (hmax : ∀ b : A, (fixedSpace ρ C).map (ρ b) ≠ fixedSpace ρ C →
      finrank (ZMod 2) ↥(fixedSpace ρ C ⊓ (fixedSpace ρ C).map (ρ b)) ≤
        finrank (ZMod 2) F) :
    GoldschmidtONan.Input (quotientOnFixer ρ F) (C.subgroupOf (pointwiseFixer ρ F)) := by
  have hCK := (le_pointwiseFixer_iff ρ C F).mpr hFU.le
  have hfixed := h.fixedSpace_quotientOnFixer F hFU.le
  have hmoved := movedSpace_quotientOnFixer F hFU.le
  have horbit (g : pointwiseFixer ρ F) :
      (fixedSpace (quotientOnFixer ρ F) (C.subgroupOf (pointwiseFixer ρ F))).map
          (quotientOnFixer ρ F g) = ((fixedSpace ρ C).map (ρ (g : A))).map F.mkQ := by
    rw [hfixed, map_quotientOnFixer]
  refine ⟨h.quotientOnFixer_faithful F hFU.le hsmall, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro he
    apply h.nontrivial
    rw [← Subgroup.map_subgroupOf_eq_of_le hCK, he, Subgroup.map_bot]
  · let : IsCyclic C := h.cyclic
    exact isCyclic_of_injective (Subgroup.subgroupOfEquivOfLe hCK).toMonoidHom
      (Subgroup.subgroupOfEquivOfLe hCK).injective
  · rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hCK).toEquiv]
    exact h.odd_card
  · rw [hmoved]
    rintro _ ⟨v, hv, rfl⟩ hv0 _ ⟨w, hw, rfl⟩ hw0
    have hv' : v ≠ 0 := fun he => hv0 (by rw [he, map_zero])
    have hw' : w ≠ 0 := fun he => hw0 (by rw [he, map_zero])
    obtain ⟨c, hc, _⟩ := h.regular v hv hv' w hw hw'
    refine ⟨⟨⟨c, hCK c.property⟩, c.property⟩, ?_⟩
    change F.mkQ (ρ (c : A) v) = F.mkQ w
    rw [hc]
  · rw [hfixed]
    intro he
    have hh := congrArg (fun L : Submodule (ZMod 2) (W ⧸ F) => L.comap F.mkQ) he
    rw [Submodule.comap_map_mkQ, sup_eq_right.mpr hFU.le,
      Submodule.comap_bot, Submodule.ker_mkQ] at hh
    exact hFU.ne hh.symm
  · rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩ hne
    dsimp only at hne ⊢
    rw [horbit, horbit]
    have hne' : (fixedSpace ρ C).map (ρ (x : A)) ≠
        (fixedSpace ρ C).map (ρ (y : A)) := by
      intro he
      apply hne
      rw [horbit, horbit, he]
    apply disjoint_quotient_images
    · exact (pointwiseFixer_map F y).ge.trans (Submodule.map_mono hFU.le)
    · exact inf_eq_of_maximal (fixedSpace ρ C) F hFU.le hmax x y hne'
  · intro x hx
    rw [horbit, hfixed] at hx
    have hFx : F ≤ (fixedSpace ρ C).map (ρ (x : A)) :=
      (pointwiseFixer_map F x).ge.trans (Submodule.map_mono hFU.le)
    have hh := congrArg (fun L : Submodule (ZMod 2) (W ⧸ F) => L.comap F.mkQ) hx
    rw [Submodule.comap_map_mkQ, Submodule.comap_map_mkQ,
      sup_eq_right.mpr hFx, sup_eq_right.mpr hFU.le] at hh
    apply Subgroup.mem_normalizer_iff_map_conj_eq.mp
    apply Subgroup.le_normalizer_comap (pointwiseFixer ρ F).subtype
    exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr (h.normal_in_stabilizer x hh)

end Representation.RegularCyclicNormalClosure
