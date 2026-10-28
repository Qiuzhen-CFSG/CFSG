module

public import CFSG.Quasithin.ChapterG.Section02.RankOneHigherFields.Reduction
public import Theory.GroupTheory.PResidual.SylowSupplement
public import Theory.ElementaryAbelian.Quotient

/-!
# Faithful natural action of the higher-field star quotient

The original LT-action has kernel O₂(LT): irreducibility makes the core
centralize V, faithfulness of the supplied SL₂-model detects the kernel on L,
and LT/L is a two-group. Hence the literal quotient acts faithfully on the
specified natural coordinates. Its U-image fixes the marked field line
pointwise, and the preceding Frattini bound makes that image elementary.

The kernel proof adapts the field-independent part of
`Binary.Recognition.Action`; the Frattini transport also occurs in
`LinearThree.Structure.Radical.Action`. No starred containment, Sylow or
generation conclusion is assumed.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
G.2.1–3, printed pp.332–334, PDF pp.343–345.
-/

@[expose] public section
open Subgroup Matrix
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterG.Section02.RankOneHigherFields.Hypothesis
open Setup
variable {G : Type*} [Group G] [Finite G]
  {D : Setup G} {F : Type*} [Field F] [Finite F] {n : ℕ} {g : G}
  (d : Hypothesis D F n g)
include d

theorem LT_normalizes_V : D.LT ≤ normalizer (D.V : Set G) :=
  sup_le (normalizes_of_span D d.span_eq) d.setup.T_normalizes_V

/-- The original conjugation action, before taking the two-core quotient. -/
def conjugation : D.LT →* MulAut D.V :=
  D.V.normalizerMonoidHom.comp (inclusion d.LT_normalizes_V)

theorem conjugation_apply (x : D.LT) (v : D.V) :
    ((d.conjugation x v : D.V) : G) = (x : G) * (v : G) * (x : G)⁻¹ := rfl

theorem conjugation_on_L (l : D.L) (v : D.V) :
    (d.coordinates (d.conjugation (inclusion (show D.L ≤ D.LT from le_sup_left) l) v)).toAdd =
      (d.model (starProjection D l)).val *ᵥ (d.coordinates v).toAdd :=
  d.equivariant l v

private theorem starProjection_eq_one_of_conjugation_eq_one (l : D.L)
    (hl : d.conjugation (inclusion (show D.L ≤ D.LT from le_sup_left) l) = 1) :
    starProjection D l = 1 := by
  apply d.model.injective
  rw [map_one]
  apply Matrix.SL2.naturalAction_injective
  rw [map_one]
  apply MulEquiv.ext
  intro v
  obtain ⟨w, rfl⟩ := d.coordinates.surjective v
  apply Multiplicative.toAdd.injective
  exact (d.conjugation_on_L l w).symm.trans (by rw [hl]; rfl)

/-- Faithfulness on L and the two-group quotient LT/L make the full
conjugation kernel a two-group. -/
theorem conjugation_kernel_isPGroup : IsPGroup 2 d.conjugation.ker := by
  let a := d.conjugation
  let N := D.L.subgroupOf D.LT
  have hn : N.Normal := (normal_subgroupOf_iff_le_normalizer le_sup_left).mpr
    (sup_le D.L.le_normalizer d.setup.T_normalizes_L)
  let := hn
  have ht : N ⊔ D.T.subgroupOf D.LT = ⊤ := by
    rw [← subgroupOf_sup (show D.L ≤ D.LT from le_sup_left) le_sup_right]
    exact subgroupOf_self _
  have hp : IsPGroup 2 (D.LT ⧸ N) :=
    isPGroup_quotient_of_sup_eq_top N (D.T.subgroupOf D.LT)
      d.setup.toBaseHypothesis.binary_T_isPGroup.comap_subtype ht
  let r : a.ker →* D.LT ⧸ N := (QuotientGroup.mk' N).comp a.ker.subtype
  have hr : IsPGroup 2 r.ker := by
    let j : r.ker →* pCore 2 D.LT :=
      { toFun := fun x => ⟨x.val.val, by
          have hxl : (x.val.val : G) ∈ D.L :=
            (QuotientGroup.eq_one_iff (N := N) x.val.val).mp x.property
          have hx := d.starProjection_eq_one_of_conjugation_eq_one
            ⟨x.val.val, hxl⟩ x.val.property
          exact (QuotientGroup.eq_one_iff _).mp (congrArg Subtype.val hx)⟩
        map_one' := rfl
        map_mul' := fun _ _ => rfl }
    apply pCore_isPGroup.of_injective j
    intro x y he
    exact Subtype.ext (Subtype.ext (congrArg (fun z : pCore 2 D.LT => z.val) he))
  have hh := (hp.to_subgroup ⊤).comap_of_ker_isPGroup r hr
  rw [comap_top] at hh
  exact hh.of_equiv topEquiv

/-- The natural action has exactly the kernel used in the source star quotient. -/
theorem conjugation_kernel : d.conjugation.ker = pCore 2 D.LT := by
  have hle : d.conjugation.ker ≤ pCore 2 D.LT :=
    le_sSup ⟨inferInstance, d.conjugation_kernel_isPGroup⟩
  apply le_antisymm hle
  intro x hx
  apply MulEquiv.ext
  intro v
  apply Subtype.ext
  change (x : G) * (v : G) * (x : G)⁻¹ = v
  have hc := d.LT_core_centralizes_V (mem_map_of_mem D.LT.subtype hx) v.val v.property
  change (v : G) * (x : G) = (x : G) * (v : G) at hc
  rw [← hc, mul_assoc, mul_inv_cancel, mul_one]

/-- The faithful action of the literal source quotient on its original V. -/
noncomputable def starAction : D.Star →* MulAut D.V :=
  QuotientGroup.lift (pCore 2 D.LT) d.conjugation d.conjugation_kernel.ge

theorem starAction_mk (x : D.LT) :
    d.starAction (QuotientGroup.mk' (pCore 2 D.LT) x) = d.conjugation x := rfl

theorem starAction_injective : Function.Injective d.starAction := by
  apply (MonoidHom.ker_eq_bot_iff _).mp
  apply le_antisymm ?_ bot_le
  intro x hx
  obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 D.LT) x
  exact (QuotientGroup.eq_one_iff y).mpr (d.conjugation_kernel.le hx)

/-- The quotient action in the specified natural coordinates. -/
noncomputable def coordinateAction : D.Star →* MulAut (Multiplicative (Fin 2 → F)) :=
  (MulAut.congr d.coordinates).toMonoidHom.comp d.starAction

theorem coordinateAction_injective : Function.Injective d.coordinateAction :=
  (MulAut.congr d.coordinates).injective.comp d.starAction_injective

theorem coordinateAction_apply (x : D.Star) (v : Multiplicative (Fin 2 → F)) :
    d.coordinateAction x v = d.coordinates (d.starAction x (d.coordinates.symm v)) := rfl

/-- Every element of the marked L* acts by its given determinant-one matrix. -/
theorem coordinateAction_on_L (x : D.star D.L) :
    d.coordinateAction x = Matrix.SL2.naturalAction F (d.model x) := by
  obtain ⟨l, rfl⟩ := starProjection_surjective D x
  apply MulEquiv.ext
  intro v
  obtain ⟨w, rfl⟩ := d.coordinates.surjective v
  apply Multiplicative.toAdd.injective
  rw [coordinateAction_apply, MulEquiv.symm_apply_apply]
  exact d.conjugation_on_L l w

/-- L* is normal in LT*, with the relative normality transported through
the actual quotient map. -/
theorem star_L_normal : (D.star D.L).Normal := by
  have hn : (D.L.subgroupOf D.LT).Normal :=
    (normal_subgroupOf_iff_le_normalizer le_sup_left).mpr
      (sup_le D.L.le_normalizer d.setup.T_normalizes_L)
  let := hn
  exact Subgroup.Normal.map inferInstance (QuotientGroup.mk' (pCore 2 D.LT))
    (QuotientGroup.mk'_surjective _)

/-- In the faithful quotient action, U* still fixes the entire specified
field line pointwise, rather than just stabilizing it. -/
theorem coordinateAction_U_fixes_point (u : D.star D.U) (v : Fin 2 → F)
    (hv : v ∈ d.point) : d.coordinateAction u (Multiplicative.ofAdd v) =
      Multiplicative.ofAdd v := by
  obtain ⟨x, hx, he⟩ := u.property
  let w := d.coordinates.symm (Multiplicative.ofAdd v)
  have hw : (w : G) ∈ D.V₁ := (d.point_mem w).mpr (by simpa [w] using hv)
  have hc := d.setup.toBaseHypothesis.U_le_centralizer_point hx w hw
  change (w : G) * (x : G) = (x : G) * w at hc
  have hfix : d.conjugation x w = w := by
    apply Subtype.ext
    change (x : G) * (w : G) * (x : G)⁻¹ = w
    rw [← hc, mul_inv_cancel_right]
  rw [coordinateAction_apply, ← he, starAction_mk]
  change d.coordinates (d.conjugation x w) = _
  rw [hfix, MulEquiv.apply_symm_apply]

theorem star_U_isPGroup (hUT : D.U ≤ D.T) : IsPGroup 2 (D.star D.U) :=
  (d.U_isPGroup hUT).comap_subtype.map (QuotientGroup.mk' (pCore 2 D.LT))

/-- The nontriviality in G.2.3 is detected by the actual natural action. -/
theorem exists_star_U_moves_vector : ∃ (u : D.star D.U) (v : Fin 2 → F),
    d.coordinateAction u (Multiplicative.ofAdd v) ≠ Multiplicative.ofAdd v := by
  obtain ⟨u, hu⟩ := ne_bot_iff_exists_ne_one.mp d.star_U_ne_bot
  by_contra! h
  apply hu
  apply Subtype.ext
  apply d.coordinateAction_injective
  rw [Subgroup.coe_one, map_one]
  apply MulEquiv.ext
  intro v
  exact h u v.toAdd

/-- The normal elementary natural module is killed by the original star map. -/
theorem V_le_LT_core : D.V ≤ D.LT.pCoreIn 2 := by
  let := d.setup.elementary
  exact le_pCoreIn_of_normalizes (IsElementaryAbelian.isPGroup 2 D.V)
    (d.setup.V_le_T.trans le_sup_right) d.LT_normalizes_V

/-- The original quotient map restricted to U. -/
def UStarProjection (hUT : D.U ≤ D.T) : D.U →* D.star D.U :=
  ((QuotientGroup.mk' (pCore 2 D.LT)).comp
    (inclusion (hUT.trans le_sup_right))).codRestrict _
      (fun u => ⟨⟨u, (hUT.trans le_sup_right) u.property⟩, u.property, rfl⟩)

omit d [Finite G] [Field F] [Finite F] in
theorem UStarProjection_surjective (hUT : D.U ≤ D.T) :
    Function.Surjective (UStarProjection (D := D) hUT) := by
  rintro ⟨q, x, hx, rfl⟩
  exact ⟨⟨x, hx⟩, rfl⟩

/-- G.2.2's Frattini conclusion makes the actual starred U elementary. -/
theorem star_U_elementary (hUT : D.U ≤ D.T)
    (hf : (frattini D.U).map D.U.subtype ≤ D.V₁) : IsElementaryAbelian 2 (D.star D.U) := by
  let : Fact (IsPGroup 2 D.U) := ⟨d.U_isPGroup hUT⟩
  let : IsElementaryAbelian 2 (D.U ⧸ frattini D.U) := isElementaryAbelian_quotient_frattini
  have hker : frattini D.U ≤ (UStarProjection (D := D) hUT).ker := by
    intro u hu
    apply Subtype.ext
    apply (QuotientGroup.eq_one_iff _).mpr
    have hk := d.V_le_LT_core (d.setup.point_le (hf (mem_map_of_mem D.U.subtype hu)))
    obtain ⟨v, hv, he⟩ := hk
    exact (show v = inclusion (hUT.trans le_sup_right) u from Subtype.ext he) ▸ hv
  exact IsElementaryAbelian.of_surjective
    (QuotientGroup.lift (frattini D.U) (UStarProjection (D := D) hUT) hker)
    (QuotientGroup.lift_surjective_of_surjective (frattini D.U) _
      (UStarProjection_surjective (D := D) hUT) hker)

end CFSG.Quasithin.ChapterG.Section02.RankOneHigherFields.Hypothesis
