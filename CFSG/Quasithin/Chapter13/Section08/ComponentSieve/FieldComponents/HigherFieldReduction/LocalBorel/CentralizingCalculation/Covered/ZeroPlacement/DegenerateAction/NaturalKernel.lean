module

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.LocalBorel.CentralizingCalculation.Covered.ModelImage

-- Internal quotient-map reduction used by ModelImage.action_one.
import all CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.LinearThree.Geometry.CoveredProduct.ResidualPlacement.LocalAction.CubicOrders.Transport

/-!
# The exact natural-action kernel of the covered Borel product

Conjugation by an element of C_{BL₁}(L/O₂(L)) commutes on V with the
full natural A₆ action. Its checked trivial centralizer therefore gives
actual centralization of V. Conversely, the concrete covered normalizer
calculation writes the action of each element of BL₁ as inner conjugation
by an element of L₁. If the original element centralizes V, so does this
representative; the genuine local action identifies it with a central
element of L/O₂(L), hence its inner action is trivial.

Thus the two actual actions have the same kernel, and the literal B_C
is O²(C_{BL₁}(V)). Inner conjugation also fixes the central mark, giving
[BL₁,L₀] ≤ O₂(L). This is the local core of L, not O₂(H); neither this
bound nor the natural-action kernel identification asserts normalization
of L₀* by K* in H/O₂(H). The rank-one branch remains open.

The conjugation transport in the first implication follows the general
argument in `Ordinary.Centralization`, strengthened here from its residual
to the full quotient centralizer. All model premises are discharged using
`Covered.ModelImage` and the actual standing natural representation.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
§13.2 and 13.2.2(3), printed pp.876–877; 13.7.3(9), p.936;
the local action calculation in 13.8.20, p.954/PDF p.971.
-/

public section

open Subgroup
open scoped commutatorElement
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.LocalBorel.CentralizingCalculation.Covered.ZeroPlacement.DegenerateAction.NaturalKernel
open CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.LinearThree.Geometry.CoveredProduct.ResidualPlacement
open LocalAction
universe u v
variable {G : Type u} [Group G] [Finite G]
variable {T : Sylow 2 G} {H K L V V₁ V₂ V₃ M G₁ : Subgroup G}
  [(Source.starImage H K).Normal] {n : ℕ} {unitary four : Bool}
  (d : SourceContext.{u,v} T H K L V V₁ V₂ V₃ M G₁ n unitary four)
  (a : NaturalSetup L (T : Subgroup G) V V₁ V₃)
  (hfactor : one L (T : Subgroup G) V₁ = plus L (T : Subgroup G) V₁ ⊔ zero L)

private theorem product_normalizes_V : d.B ⊔ one L (T : Subgroup G) V₁ ≤ normalizer (V : Set G) := by
  have hj : d.B ⊔ one L (T : Subgroup G) V₁ ≤ H ⊓ M :=
    le_inf (sup_le ((borel_le_component _ _ _ _ _).trans d.component_le) d.one_le_H)
      (sup_le d.borel_in_M d.one_le_M)
  rw [d.intersection] at hj
  exact hj.trans inf_le_right

include d in
private theorem core_centralizes_V : L.pCoreIn 2 ≤ centralizer (V : Set G) := by
  rintro _ ⟨l, hl, rfl⟩
  change l ∈ (centralizer (V : Set G)).subgroupOf L
  rw [← d.standing.centralCore_eq_centralizer]
  change QuotientGroup.mk' (pCore 2 L) l ∈ center (L ⧸ pCore 2 L)
  have hq : QuotientGroup.mk' (pCore 2 L) l = 1 := (QuotientGroup.eq_one_iff l).mpr hl
  rw [hq]
  exact one_mem _

private noncomputable def coordinateAction : normalizer (V : Set G) →*
    MulAut (Multiplicative (BinaryPermutation.natural (Fin 6))) :=
  (MulAut.congr d.standing.coordinate).toMonoidHom.comp V.normalizerMonoidHom

private theorem coordinateAction_L (l : L) :
    coordinateAction d ⟨l.val, d.standing.normalizes_V (mem_sup_left l.property)⟩ =
      BinaryPermutation.naturalMulAction (Fin 6)
        (d.standing.local_quotient
          (QuotientGroup.mk' (TransvectionRecognition.Component.ModelExtension.centralCore L) l)).val := by
  apply MulEquiv.ext
  intro w
  obtain ⟨v, rfl⟩ := d.standing.coordinate.surjective w
  change d.standing.coordinate (V.normalizerMonoidHom _
    (d.standing.coordinate.symm (d.standing.coordinate v))) = _
  rw [d.standing.coordinate.symm_apply_apply]
  exact d.standing.conjugation l v

private theorem coordinateAction_eq_one_iff (x : normalizer (V : Set G)) :
    coordinateAction d x = 1 ↔ x.val ∈ centralizer (V : Set G) := by
  change MulAut.congr d.standing.coordinate (V.normalizerMonoidHom x) = 1 ↔ _
  rw [map_eq_one_iff _ (MulAut.congr d.standing.coordinate).injective]
  change x ∈ V.normalizerMonoidHom.ker ↔ _
  rw [normalizerMonoidHom_ker]
  rfl

/-- The full quotient centralizer, before taking its residual, centralizes all V. -/
theorem borelCentralizer_le_centralizer :
    borelCentralizer d.B (one L (T : Subgroup G) V₁) L ≤ centralizer (V : Set G) := by
  intro c hc
  have hcV := product_normalizes_V d (commutatorPreimage_le _ _ _ hc)
  let x : normalizer (V : Set G) := ⟨c, hcV⟩
  apply (coordinateAction_eq_one_iff d x).mp
  have hm : coordinateAction d x ∈ centralizer ((alternatingGroup (Fin 6)).map
      (BinaryPermutation.naturalMulAction (Fin 6)) :
        Set (MulAut (Multiplicative (BinaryPermutation.natural (Fin 6))))) := by
    apply mem_centralizer_iff.mpr
    rintro _ ⟨s, hs, rfl⟩
    obtain ⟨q, hq⟩ := d.standing.local_quotient.surjective ⟨s, hs⟩
    obtain ⟨l, rfl⟩ := QuotientGroup.mk'_surjective
      (TransvectionRecognition.Component.ModelExtension.centralCore L) q
    let y : normalizer (V : Set G) :=
      ⟨l.val, d.standing.normalizes_V (mem_sup_left l.property)⟩
    have hy := coordinateAction_L d l
    rw [hq] at hy
    change coordinateAction d y = BinaryPermutation.naturalMulAction (Fin 6) s at hy
    rw [← hy]
    suffices hcomm : ⁅coordinateAction d x, coordinateAction d y⁆ = 1 by
      exact (commutatorElement_eq_one_iff_mul_comm.mp hcomm).symm
    rw [← map_commutatorElement]
    apply (coordinateAction_eq_one_iff d _).mpr
    exact core_centralizes_V d
      (commutator_commutatorPreimage_le (d.B ⊔ one L (T : Subgroup G) V₁) L (L.pCoreIn 2)
        (d.product_normalizes_L.trans (normalizer_le_normalizer_characteristic_image L (pCore 2 L)))
          (commutator_mem_commutator hc l.property))
  rw [Representation.Hexacode.CubicLocalModel.naturalAlternating_centralizer] at hm
  exact hm

include hfactor in
/-- Triviality of the actual covered action is exactly centralization of V. -/
theorem modelAction_eq_one_iff_centralizes
    (g : (d.B ⊔ one L (T : Subgroup G) V₁ : Subgroup G)) :
    modelAction d a g = 1 ↔ g.val ∈ centralizer (V : Set G) := by
  have hk (x : (d.B ⊔ one L (T : Subgroup G) V₁ : Subgroup G))
      (hx : modelAction d a x = 1) : x.val ∈ centralizer (V : Set G) := by
    apply borelCentralizer_le_centralizer d
    rw [← modelAction_kernel d a]
    exact mem_map_of_mem _ hx
  constructor
  · exact hk g
  · intro hg
    obtain ⟨l, hl⟩ := ModelImage.action_image d a hfactor g
    let lJ : (d.B ⊔ one L (T : Subgroup G) V₁ : Subgroup G) := inclusion le_sup_right l
    have hc : (g * lJ⁻¹).val ∈ centralizer (V : Set G) := hk _ (by
      rw [map_mul, map_inv, hl]
      exact mul_inv_cancel _)
    have hlV : l.val ∈ centralizer (V : Set G) := by
      have h := (centralizer (V : Set G)).mul_mem
        ((centralizer (V : Set G)).inv_mem hc) hg
      change (g.val * l.val⁻¹)⁻¹ * g.val ∈ _ at h
      simpa only [mul_inv_rev, inv_inv, mul_assoc, inv_mul_cancel, mul_one] using h
    have hDL := one_le_L_of_factorization _ _ _ a.normalizes_L hfactor
    let lL : L := inclusion hDL l
    have hz : QuotientGroup.mk' (pCore 2 L) lL ∈ center (L ⧸ pCore 2 L) := by
      change lL ∈ TransvectionRecognition.Component.ModelExtension.centralCore L
      rw [d.standing.centralCore_eq_centralizer]
      exact hlV
    have hzc : a.cover (QuotientGroup.mk' (pCore 2 L) lL) ∈
        center Atlas.Codes.HexEvenAutomorphisms :=
      (centerCongr a.cover ⟨_, hz⟩).property
    rw [hl, ModelImage.action_one d a hfactor l]
    apply MulEquiv.ext
    intro x
    change a.cover (QuotientGroup.mk' (pCore 2 L) lL) * x *
      (a.cover (QuotientGroup.mk' (pCore 2 L) lL))⁻¹ = x
    rw [← (mem_center_iff.mp hzc x), mul_inv_cancel_right]


include a hfactor in
/-- The two full centralizers agree inside the literal product BL₁. -/
theorem borelCentralizer_eq_natural_kernel :
    borelCentralizer d.B (one L (T : Subgroup G) V₁) L =
      (d.B ⊔ one L (T : Subgroup G) V₁) ⊓ centralizer (V : Set G) := by
  apply le_antisymm
  · exact le_inf (commutatorPreimage_le _ _ _) (borelCentralizer_le_centralizer d)
  · rintro g ⟨hg, hc⟩
    rw [← modelAction_kernel d a]
    exact ⟨⟨g, hg⟩, (modelAction_eq_one_iff_centralizes d a hfactor ⟨g, hg⟩).mpr hc, rfl⟩

include a hfactor in
/-- The source B_C is the two-residual of the natural-action kernel. -/
theorem centralizingResidual_eq_natural_residual :
    centralizingResidual d.B (one L (T : Subgroup G) V₁) L =
      residual ((d.B ⊔ one L (T : Subgroup G) V₁) ⊓ centralizer (V : Set G)) := by
  unfold centralizingResidual
  rw [borelCentralizer_eq_natural_kernel d a hfactor]
  rfl

/-- Conjugation on V by the actual Borel product, without passing to H*. -/
noncomputable def naturalAction : (d.B ⊔ one L (T : Subgroup G) V₁ : Subgroup G) →* MulAut V :=
  V.normalizerMonoidHom.comp (inclusion (product_normalizes_V d))

/-- The public formula retains literal ambient conjugation on V. -/
theorem naturalAction_apply_coe
    (g : (d.B ⊔ one L (T : Subgroup G) V₁ : Subgroup G)) (w : V) :
    ((naturalAction d g) w : G) = g.val * w.val * g.val⁻¹ := by
  rfl

private theorem naturalAction_eq_one_iff (g : (d.B ⊔ one L (T : Subgroup G) V₁ : Subgroup G)) :
    naturalAction d g = 1 ↔ g.val ∈ centralizer (V : Set G) := by
  change inclusion (product_normalizes_V d) g ∈ V.normalizerMonoidHom.ker ↔ _
  rw [normalizerMonoidHom_ker]
  rfl

include hfactor in
/-- Equality of the actual homomorphism kernels; no quotient kernel is discarded. -/
theorem naturalAction_kernel : (naturalAction d).ker = (modelAction d a).ker := by
  ext g
  exact (naturalAction_eq_one_iff d g).trans
    (modelAction_eq_one_iff_centralizes d a hfactor g).symm


include a hfactor in
/-- The inner covered image fixes L₀ modulo O₂(L), even before the degenerate branch. -/
theorem product_zero_commutator_le_local_core :
    ⁅d.B ⊔ one L (T : Subgroup G) V₁, zero L⁆ ≤ L.pCoreIn 2 := by
  apply commutator_le.mpr
  intro g hg z hz
  let gJ : (d.B ⊔ one L (T : Subgroup G) V₁ : Subgroup G) := ⟨g, hg⟩
  let zL : L := ⟨z, zero_le L hz⟩
  have hzcenter : QuotientGroup.mk' (pCore 2 L) zL ∈ center (L ⧸ pCore 2 L) := by
    obtain ⟨w, hw, he⟩ := residual_le (centralPreimage L) hz
    have hwz : w = zL := Subtype.ext he
    exact hwz ▸ hw
  have hzc : a.cover (QuotientGroup.mk' (pCore 2 L) zL) ∈
      center Atlas.Codes.HexEvenAutomorphisms :=
    (centerCongr a.cover ⟨_, hzcenter⟩).property
  obtain ⟨l, hl⟩ := ModelImage.action_image d a hfactor gJ
  have he : modelAction d a gJ (a.cover (QuotientGroup.mk' (pCore 2 L) zL)) =
      a.cover (QuotientGroup.mk' (pCore 2 L) zL) := by
    rw [hl, ModelImage.action_one d a hfactor l]
    change _ * a.cover (QuotientGroup.mk' (pCore 2 L) zL) * _ = _
    rw [(mem_center_iff.mp hzc _), mul_inv_cancel_right]
  change a.cover (coreAction L ⟨g, d.product_normalizes_L hg⟩
    (a.cover.symm (a.cover (QuotientGroup.mk' (pCore 2 L) zL)))) = _ at he
  rw [a.cover.symm_apply_apply, coreAction_mk] at he
  have hq := a.cover.injective he
  let w := L.normalizerMonoidHom ⟨g, d.product_normalizes_L hg⟩ zL * zL⁻¹
  have hw : w ∈ pCore 2 L := by
    apply (QuotientGroup.eq_one_iff _).mp
    change QuotientGroup.mk' (pCore 2 L) w = 1
    dsimp only [w]
    rw [map_mul, map_inv, hq, mul_inv_cancel]
  exact ⟨w, hw, rfl⟩

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.LocalBorel.CentralizingCalculation.Covered.ZeroPlacement.DegenerateAction.NaturalKernel
