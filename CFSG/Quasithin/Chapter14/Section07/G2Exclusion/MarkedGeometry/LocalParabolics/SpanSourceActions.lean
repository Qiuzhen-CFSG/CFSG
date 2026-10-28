module

public import CFSG.Quasithin.Chapter14.Section07.G2Exclusion.MarkedGeometry.LocalParabolics.SpanSourceActions.Coordinates
public import CFSG.Quasithin.Chapter14.Section07.G2Exclusion.MarkedGeometry.LocalParabolics.SpanSourceActions.ResidualSeed
public import CFSG.Quasithin.Chapter14.Section07.G2Exclusion.MarkedGeometry.LocalParabolics.SpanSourceActions.IndependentBlocks
public import CFSG.Quasithin.Chapter14.Section07.G2Exclusion.MarkedGeometry.LocalParabolics.SpanSourceActions.QuotientBlocks

/-!
# The source actions filling the span parabolic in 14.7.56

This supplies the two remaining action inputs to
`LocalParabolics.source_span_image_of_block_and_residual_actions` and
`LocalParabolics.source_span_quotient_of_block_and_residual_actions`.
Coordinates taking V₂ to the marked plane are constructed from the ranks.

The residual-image two-core is nontrivial by coprime splitting and the
commutator-generation clause of 14.7.55(6). The YT/O₂(YT) ≃ S₃ clause
then gives the full second block. Finally [V₂,O₂(H)]=V₁, together with
the actual trivial O₂(H)-action on U/V₁, supplies an independent nontrivial
two-action in the first block. Normal closure inside the second-block
kernel fills the first S₃; this rules out the proper equal-sign subgroup.

The final theorem retains the literal conjugation homomorphisms, the
original quotient U → U/V₁, and Y=O²(C_H(V₂)). It assumes the earlier
source ranks, elementary abelianness, span invariance and full L₂T-action
on V₂. It does not assume a radical cover, seed, irreducibility, extra
normality, or either desired block conclusion. The parent source assembly
retains discharge of these earlier-source inputs.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), 14.7.4(1),(2),
14.7.55(3),(6), and 14.7.56(2), printed pp.1043 and 1066.
-/

public section
namespace CFSG.Quasithin.Chapter14.Section07.G2Exclusion.MarkedGeometry.LocalParabolics.SpanSourceActions

open Subgroup
open scoped IsMulCommutative
open BinaryLinear.FourParabolicRadical BinaryLinear.SmallParabolicLevi
open SpanSaturation
variable {G : Type*} [Group G]

private theorem elementary_of_le (D W : Subgroup G) [IsElementaryAbelian 2 W]
    (hDW : D ≤ W) : IsElementaryAbelian 2 D where
  toIsMulCommutative := ⟨⟨fun x y => by
    apply Subtype.ext
    change (x : G) * (y : G) = (y : G) * (x : G)
    exact congrArg Subtype.val (mul_comm (⟨x,hDW x.property⟩ : W)
      (⟨y,hDW y.property⟩ : W))⟩⟩
  exponent_dvd_p := by
    rw [Monoid.exponent_dvd_iff_forall_pow_eq_one]
    intro x
    apply Subtype.ext
    change (x : G) ^ 2 = 1
    exact congrArg Subtype.val (Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
      (IsElementaryAbelian.exponent_dvd_p 2 W) (⟨x,hDW x.property⟩ : W))

/-- The actual trivial quotient action gives the unstarred displacement bound. -/
theorem commutator_le_of_trivial_quotient_action (U Z Q : Subgroup G)
    [(Z.subgroupOf U).Normal] (hQU : Q ≤ normalizer (U : Set G))
    (hstar : ∀ q : Q, ∀ u : U,
      QuotientGroup.mk' (Z.subgroupOf U)
        ⟨(q : G) * (u : G) * (q : G)⁻¹,
          (mem_normalizer_iff.mp (hQU q.property) u).mp u.property⟩ =
        QuotientGroup.mk' (Z.subgroupOf U) u) : ⁅U,Q⁆ ≤ Z := by
  rw [commutator_comm]
  apply commutator_le.mpr
  intro q hq u hu
  have he := QuotientGroup.eq_iff_div_mem.mp (hstar ⟨q,hq⟩ ⟨u,hu⟩)
  change (q * u * q⁻¹) / u ∈ Z at he
  simpa only [div_eq_mul_inv,commutatorElement_def] using he

/-- Construct the marked coordinates and discharge both remaining inputs to
the literal span-image and span-quotient consumers. The starred kernel and
14.7.55(6) are given on their original quotient, with no action-image
conclusion among the hypotheses. -/
theorem source_span_action_inputs [Finite G]
    (H U V V₁ V₂ Y L₂ T : Subgroup G) [(V₁.subgroupOf U).Normal]
    [IsElementaryAbelian 2 (generatedLineFamily V Y)]
    (hY : Y = localResidual H V₂)
    (hV₂ : V₂ ≤ V) (hV₁ : V₁ ≤ V₂)
    (hWU : generatedLineFamily V Y ≤ U)
    (hW : Nat.card (generatedLineFamily V Y) = 16)
    (hD : Nat.card V₂ = 4) (hZ : Nat.card V₁ = 2)
    (hspan : normalizer (V₂ : Set G) ≤ normalizer (generatedLineFamily V Y : Set G))
    (hLT : L₂ ⊔ T ≤ normalizer (V₂ : Set G))
    (hfull : Function.Surjective (ambientAction (L₂ ⊔ T) V₂ hLT))
    (hcomm : ⁅V₂,H.pCoreIn 2⁆ = V₁)
    (hHU : H ≤ normalizer (U : Set G))
    (hstar : ∀ q : H.pCoreIn 2, ∀ u : U,
      QuotientGroup.mk' (V₁.subgroupOf U)
        ⟨(q : G) * (u : G) * (q : G)⁻¹,
          (mem_normalizer_iff.mp (hHU (pCoreIn_le 2 H q.property)) u).mp u.property⟩ =
        QuotientGroup.mk' (V₁.subgroupOf U) u)
    (hquot : ((⁅generatedLineFamily V Y,Y⁆).subgroupOf U).map
        (QuotientGroup.mk' (V₁.subgroupOf U)) =
      ((generatedLineFamily V Y).subgroupOf U).map
        (QuotientGroup.mk' (V₁.subgroupOf U)))
    (eYT : ((Y ⊔ T : Subgroup G) ⧸ pCore 2 (Y ⊔ T : Subgroup G)) ≃*
      Equiv.Perm (Fin 3)) :
    ∃ (hYV : Y ≤ normalizer (V₂ : Set G))
      (E : generatedLineFamily V Y ≃* Multiplicative BSpace)
      (hE : (V₂.subgroupOf (generatedLineFamily V Y)).map E.toMonoidHom =
        plane.toAddSubgroup.toSubgroup),
      Function.Surjective ((blockAction plane).comp
        (spanCoordinateAction V V₂ Y hV₂ hspan E hE)) ∧
      (ambientAction Y (generatedLineFamily V Y) (hYV.trans hspan)).range.pCoreIn 2 ≠ ⊥ := by
  let : IsElementaryAbelian 2 V₂ := elementary_of_le V₂ _
    (hV₂.trans (original_le_generated V Y))
  have hYC : Y ≤ centralizer (V₂ : Set G) := by
    rw [hY]
    exact localResidual_le_centralizer H V₂
  have hYV := hYC.trans (centralizer_le_normalizer _)
  obtain ⟨E,hE⟩ := source_span_coordinates V V₂ Y hV₂ hW hD
  have hseed := source_residual_image_core_ne_bot H U V V₁ V₂ Y hY hV₂ hV₁
    hWU hW hD hZ hspan hYV hquot
  have hsecond := source_quotient_block_surjective H V V₂ Y T hY hV₂ hspan hYV
    (le_sup_right.trans hLT) E hE eYT hseed
  have hstar' : ⁅generatedLineFamily V Y,H.pCoreIn 2⁆ ≤ V₁ :=
    (commutator_mono hWU le_rfl).trans
      (commutator_le_of_trivial_quotient_action U V₁ (H.pCoreIn 2)
        ((pCoreIn_le 2 H).trans hHU) hstar)
  exact ⟨hYV,E,hE,source_joint_block_surjective_of_quotient_action
    H V V₁ V₂ Y L₂ T hV₂ hV₁ hD hZ hspan E hE hLT hfull hcomm hstar' hsecond,hseed⟩

end CFSG.Quasithin.Chapter14.Section07.G2Exclusion.MarkedGeometry.LocalParabolics.SpanSourceActions
