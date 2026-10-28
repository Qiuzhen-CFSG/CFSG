module

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.LocalBorel.CentralizingCalculation.Covered.ActionData
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.LinearThree.Geometry.CoveredProduct.ResidualPlacement.LocalAction.CubicOrders
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.LinearThree.Geometry.CoveredProduct.ResidualPlacement.LocalAction.ResidualDirections

/-!
# The covered marked actor and the central kernel intersection

The actual cubic X/O₂(X) has an inverter in T∩L. Converting its quotient
action to the intrinsic-core predicate retains that same element, its
centralization of L₀/O₂(L₀), and the bound [B_C,⟨t⟩] ≤ O₂(B_C).
The central-preimage definition also gives L₀ ≤ B_C and
O²(B_C ∩ L₁) = L₀, using the earlier factorization L₁ = XL₀.

The full local calculation is still open: the concrete action-image premise
of `product_eq_of_action_image`, centralization of V, the identity
B_C = O³(B)L₀, placement in BX, and the index three require further proof.
None of these assertions is assumed in the marked-inverter construction.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
Notation 13.2.1 and 13.2.2(3), p.877; proof of 13.8.20, p.954/PDF p.971.
-/

@[expose] public section
open Subgroup
open scoped commutatorElement Pointwise
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.LocalBorel.CentralizingCalculation
open CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.LinearThree.Geometry.CoveredProduct.ResidualPlacement
namespace Covered
universe u v
variable {G : Type u} [Group G]

/-- The representative formula is inversion on the actual intrinsic quotient. -/
theorem inversion_iff (X : Subgroup G) (t : normalizer (X : Set G)) :
    InvertsTwoCoreQuotient X t.val ↔
      ∀ q : X ⧸ pCore 2 X, coreAction X t q = q⁻¹ := by
  constructor
  · intro h q
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 X) q
    rw [coreAction_mk]
    have hx : X.normalizerMonoidHom t x * x ∈ pCore 2 X := by
      obtain ⟨y, hy, he⟩ := h.2 x.val x.property
      have he' : y = X.normalizerMonoidHom t x * x := Subtype.ext he
      exact he' ▸ hy
    have he := (QuotientGroup.eq_one_iff _).mpr hx
    change QuotientGroup.mk' (pCore 2 X) (X.normalizerMonoidHom t x * x) = 1 at he
    rw [map_mul] at he
    exact eq_inv_of_mul_eq_one_left he
  · intro h
    refine ⟨t.property, ?_⟩
    intro x hx
    let a : X := ⟨x, hx⟩
    have he := h (QuotientGroup.mk' (pCore 2 X) a)
    rw [coreAction_mk] at he
    have hm : X.normalizerMonoidHom t a * a ∈ pCore 2 X := by
      apply (QuotientGroup.eq_one_iff _).mp
      change QuotientGroup.mk' (pCore 2 X) (X.normalizerMonoidHom t a * a) = 1
      rw [map_mul, he, inv_mul_cancel]
    exact ⟨_, hm, rfl⟩

/-- The defining quotient center centralizes L modulo its intrinsic two-core. -/
theorem centralPreimage_commutator (L : Subgroup G) :
    ⁅centralPreimage L, L⁆ ≤ L.pCoreIn 2 := by
  apply commutator_le.mpr
  rintro z ⟨a, ha, rfl⟩ l hl
  let b : L := ⟨l, hl⟩
  refine ⟨⁅a, b⁆, ?_, rfl⟩
  apply (QuotientGroup.eq_one_iff _).mp
  change QuotientGroup.mk' (pCore 2 L) ⁅a, b⁆ = 1
  rw [map_commutatorElement]
  exact (commutatorElement_eq_one_iff_mul_comm).mpr (mem_center_iff.mp ha _).symm

/-- Centralization of the quotient, inside L, is the central preimage. -/
theorem le_centralPreimage (D L : Subgroup G) (hDL : D ≤ L)
    (hc : ⁅D, L⁆ ≤ L.pCoreIn 2) : D ≤ centralPreimage L := by
  intro x hx
  refine ⟨⟨x, hDL hx⟩, ?_, rfl⟩
  apply mem_center_iff.mpr
  intro q
  obtain ⟨l, rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 L) q
  have hm := hc (commutator_mem_commutator hx l.property)
  obtain ⟨a, ha, he⟩ := hm
  have he' : a = ⁅(⟨x, hDL hx⟩ : L), l⁆ := Subtype.ext he
  have hh := (QuotientGroup.eq_one_iff _).mpr (he' ▸ ha)
  change QuotientGroup.mk' (pCore 2 L) ⁅(⟨x, hDL hx⟩ : L), l⁆ = 1 at hh
  rw [map_commutatorElement] at hh
  exact ((commutatorElement_eq_one_iff_mul_comm).mp hh).symm

variable [Finite G]

/-- Two-perfectness places the full L₀ in the two-residual of the action kernel. -/
theorem zero_le_centralizingResidual (B L L₁ : Subgroup G) (hz : zero L ≤ L₁) :
    zero L ≤ centralizingResidual B L₁ L := by
  have hk : zero L ≤ borelCentralizer B L₁ L :=
    le_commutatorPreimage (hz.trans le_sup_right)
      ((commutator_mono (residual_le _) le_rfl).trans (centralPreimage_commutator L))
  have hr : residualIn 2 (zero L) = zero L := by
    unfold residualIn
    rw [(pResidual_eq_top_iff 2 _).mpr
      (show IsPPerfect 2 (zero L) from residual_isPPerfect (centralPreimage L)),
      ← MonoidHom.range_eq_map, range_subtype]
  rw [← hr]
  exact embedded_pResidual_mono 2 hk

/-- The two-residual of the local kernel's intersection with L₁ is exactly L₀. -/
theorem residual_intersection_one (B L L₁ : Subgroup G)
    (hJL : B ⊔ L₁ ≤ normalizer (L : Set G))
    (hL₁L : L₁ ≤ L) (hz : zero L ≤ L₁) :
    residualIn 2 (centralizingResidual B L₁ L ⊓ L₁) = zero L := by
  apply le_antisymm
  · apply embedded_pResidual_mono 2
    apply le_centralPreimage _ _ (inf_le_right.trans hL₁L)
    exact (commutator_mono inf_le_left le_rfl).trans
      (centralizingResidual_commutator_le _ _ _
        (hJL.trans (normalizer_le_normalizer_characteristic_image L (pCore 2 L))))
  · have hr : residualIn 2 (zero L) = zero L := by
      unfold residualIn
      rw [(pResidual_eq_top_iff 2 _).mpr
      (show IsPPerfect 2 (zero L) from residual_isPPerfect (centralPreimage L)),
      ← MonoidHom.range_eq_map, range_subtype]
    rw [← hr]
    exact embedded_pResidual_mono 2
      (le_inf (zero_le_centralizingResidual B L L₁ hz) hz)

variable {T : Sylow 2 G} {H K L V V₁ V₂ V₃ M G₁ : Subgroup G}
  [(Source.starImage H K).Normal] {n : ℕ} {unitary four : Bool}
  (d : SourceContext.{u,v} T H K L V V₁ V₂ V₃ M G₁ n unitary four)
  (a : LocalAction.NaturalSetup L (T : Subgroup G) V V₁ V₃)
  (hfactor : one L (T : Subgroup G) V₁ = plus L (T : Subgroup G) V₁ ⊔ zero L)

include hfactor in
/-- The literal source kernel already contains the whole central residual. -/
theorem source_zero_le : zero L ≤ centralizingResidual d.B (one L (T : Subgroup G) V₁) L :=
  zero_le_centralizingResidual _ _ _ (LocalAction.zero_le_one_of_factorization _ _ _ hfactor)

include hfactor in
/-- The intersection calculation uses only the earlier factorization and relative normality. -/
theorem source_residual_intersection :
    residualIn 2 (centralizingResidual d.B (one L (T : Subgroup G) V₁) L ⊓
      one L (T : Subgroup G) V₁) = zero L :=
  residual_intersection_one _ _ _ d.product_normalizes_L
    (LocalAction.one_le_L_of_factorization _ _ _ d.standing.normalizes_L hfactor)
    (LocalAction.zero_le_one_of_factorization _ _ _ hfactor)

include a hfactor in
/-- The single source actor supplies inversion, centralization of the central mark,
and the full cyclic-commutator bound with its intrinsic two-core denominator. -/
theorem exists_marked_inverter :
    ∃ t : ((T : Subgroup G) ⊓ L : Subgroup G),
      InvertsTwoCoreQuotient (plus L (T : Subgroup G) V₁) t.val ∧
      coreAction (zero L) ⟨t.val, L_normalizes_zero L t.property.2⟩ = 1 ∧
      ⁅centralizingResidual d.B (one L (T : Subgroup G) V₁) L, zpowers t.val⁆ ≤
        (centralizingResidual d.B (one L (T : Subgroup G) V₁) L).pCoreIn 2 := by
  obtain ⟨t, hinv, hzero⟩ := LocalAction.exists_plus_inverter L (T : Subgroup G) V₁
    a.normalizes_L a.line_stable hfactor (a.plus_core_card hfactor)
  refine ⟨t, ?_, hzero, ?_⟩
  · exact (inversion_iff _
      ⟨t.val, T_normalizes_plus L (T : Subgroup G) V₁
        a.normalizes_L a.line_stable t.property.1⟩).mpr hinv
  · exact centralizingResidual_commutator_core _ _ _ d.product_normalizes_L
      t.val t.property.2 (d.T_normalizes_product t.property.1)

end Covered
end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.LocalBorel.CentralizingCalculation
