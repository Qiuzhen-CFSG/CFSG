module

public import CFSG.Quasithin.Chapter14.Section07.G2Exclusion.MarkedGeometry.FamilyAction
public import CFSG.Quasithin.Chapter14.Section07.G2Exclusion.MarkedGeometry.Models
public import CFSG.Quasithin.Chapter14.Section07.G2Exclusion.MarkedGeometry.LocalParabolics.ConjugateCoverage
public import CFSG.Quasithin.Chapter14.Section07.G2Exclusion.MarkedGeometry.LocalParabolics.LocalAction
public import CFSG.Quasithin.Chapter14.Section07.G2Exclusion.MarkedGeometry.LocalParabolics.Saturation
public import CFSG.Quasithin.Chapter14.Section07.G2Exclusion.MarkedGeometry.LocalParabolics.ParabolicLift
public import CFSG.Quasithin.Chapter14.Section07.G2Exclusion.MarkedGeometry.LocalParabolics.MarkedParabolicAssembly
public import CFSG.Quasithin.Chapter14.Section07.G2Exclusion.MarkedGeometry.LocalParabolics.SpanSaturation
public import CFSG.Quasithin.Chapter14.Section07.G2Exclusion.MarkedGeometry.LocalParabolics.ResidualAction
public import CFSG.Quasithin.Chapter14.Section07.G2Exclusion.MarkedGeometry.LocalParabolics.SpanSourceActions
public import Theory.ElementaryAbelian.AbelianNormalClosure

/-!
# Conditional local deductions for the marked G₂ geometry

The marked quotient pencil from 14.7.55 lifts to exactly V^Y and to all
ambient conjugates of V containing V₂. The centralizer factorization
identifies the local vertex N_G(V₂)=L₂YT. The earlier commutator identities
prove that Y centralizes L₂/O₂(L₂), that L₂ fixes each member of the
pencil, and that the local vertex acts on its literal span. The kernel
is the relative centralizer of that span.

Y is the genuine two-residual O²(C_H(V₂)). The geometry parameter is the
actual quotient realization supplied by `Models`, with the marked-line
and quotient-orbit formulas of 14.7.55 left explicit. The earlier local
identities and the full action of L₂T on V₂ are likewise source inputs.

`ParabolicLift` proves the marked normalizer and radical deductions of
14.7.57(1),(2) from the explicit B.4.6 model facts and 14.7.4(4).

`MarkedParabolicAssembly` connects these lifts to the actual natural/Weyl
identification and proves the three-offender orbit of 14.7.57(3) in the
original starred action. Its earlier B.4.6 premises remain explicit.

`SpanSaturation` proves the binary plane-radical calculation, and
`ResidualAction` derives relative normality of the residual image. The final
span-image and quotient applications use `SpanSourceActions` to construct
marked coordinates and prove joint block surjectivity and the nontrivial
Y-image two-core from the earlier identities and 14.7.55(6). The final
`source_pencil_full_local_deductions` assembles every clause of 14.7.56
on the literal pencil preimage in the actual natural/Weyl geometry.
Only the authorized earlier local, rank, and 14.7.55 inputs remain;
`qt-14-07-g2-marked-geometry` owns their discharge.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), printed
pp.1066–1067, Lemmas 14.7.56–57.
-/

@[expose] public noncomputable section
namespace CFSG.Quasithin.Chapter14.Section07.G2Exclusion.MarkedGeometry.LocalParabolics
open Subgroup Atlas.G2
open Atlas.G2.EvenLocal.NormalizerCover.OctonionHexagon
variable {G : Type*} [Group G]

/-- The ambient centralizer really is contained in the local vertex, because
V₂ lies in the acted-on span. -/
theorem centralizer_span_le_vertex (V V₂ Y : Subgroup G) (hV₂ : V₂ ≤ V) :
    centralizer (generatedLineFamily V Y : Set G) ≤ normalizer (V₂ : Set G) :=
  (centralizer_le (hV₂.trans (original_le_generated V Y))).trans
    (centralizer_le_normalizer _)

/-- Assemble the literal pencil, ambient coverage, local vertex, relative
quotient action, and exact kernel from their earlier source hypotheses.
No conclusion of 14.7.56 is included among these inputs. -/
theorem source_pencil_local_deductions
    (H U Z V V₂ L L₂ Y T : Subgroup G) [(Z.subgroupOf U).Normal]
    (hY : Y = localResidual H V₂)
    (hVU : V ≤ U) (hZV : Z ≤ V) (hV₂ : V₂ ≤ V)
    (hYU : Y ≤ normalizer U) (hLV : L ≤ normalizer V)
    (htransV : ∀ W : Subgroup G, W ≤ V → Nat.card W = Nat.card V₂ →
      ∃ l : L, conjugate V₂ l = W)
    (hcomm : ⁅V,L₂⁆ = V₂)
    (hcommY : ⁅L₂,Y⁆ ≤ L₂ ⊓ centralizer (V₂ : Set G))
    (hcore : L₂ ⊓ centralizer (V₂ : Set G) = L₂.pCoreIn 2)
    (hLT : L₂ ⊔ T ≤ normalizer (V₂ : Set G))
    (hC : centralizer (V₂ : Set G) = Y ⊔ (T ⊓ centralizer (V₂ : Set G)))
    (hfull : Function.Surjective (ambientAction (L₂ ⊔ T) V₂ hLT))
    (hTV : T ≤ normalizer V) (hTY : T ≤ normalizer Y)
    (action : Y →* MulAut (U ⧸ Z.subgroupOf U))
    (hact : ∀ y : Y, ∀ u : U,
      action y (QuotientGroup.mk' (Z.subgroupOf U) u) =
        QuotientGroup.mk' (Z.subgroupOf U)
          ⟨(y : G) * (u : G) * (y : G)⁻¹,
            (mem_normalizer_iff.mp (hYU y.property) u).mp u.property⟩)
    (geom : QuotientGeometry (U ⧸ Z.subgroupOf U))
    (p : SingularPoints (ZMod 2)) (line : ZeroProductLine (ZMod 2))
    (hmark : (V.subgroupOf U).map (QuotientGroup.mk' (Z.subgroupOf U)) = geom.line line)
    (horbit : ∀ y : Y, (geom.line line).map (action y).toMonoidHom ∈ markedPencil geom p)
    (htrans : ∀ B ∈ markedPencil geom p,
      ∃ y : Y, (geom.line line).map (action y).toMonoidHom = B) :
    pencilPreimages U Z geom p = conjugateLineFamily V Y ∧
    pencilPreimages U Z geom p = ambientConjugatesThrough V V₂ ∧
    pencilSpanPreimage U Z geom p = generatedLineFamily V Y ∧
    normalizer (V₂ : Set G) = L₂ ⊔ Y ⊔ T ∧
    ⁅pencilSpanPreimage U Z geom p,L₂⁆ = V₂ ∧
    (∀ P ∈ pencilPreimages U Z geom p, L₂ ≤ normalizer P) ∧
    (∃ hYL : Y ≤ normalizer L₂, coreQuotientAction L₂ Y hYL = 1) ∧
    (∃ hspan : normalizer (V₂ : Set G) ≤ normalizer (pencilSpanPreimage U Z geom p : Set G),
      (@ambientAction G _ (normalizer (V₂ : Set G)) (pencilSpanPreimage U Z geom p) hspan).ker =
        (centralizer (pencilSpanPreimage U Z geom p : Set G)).subgroupOf (normalizer (V₂ : Set G)) ∧
      (@ambientAction G _ (normalizer (V₂ : Set G)) (pencilSpanPreimage U Z geom p) hspan).ker.map
        (normalizer (V₂ : Set G)).subtype = centralizer (pencilSpanPreimage U Z geom p : Set G)) := by
  have hYC : Y ≤ centralizer (V₂ : Set G) := by
    rw [hY]
    exact localResidual_le_centralizer H V₂
  obtain ⟨hYL,hquot⟩ := source_centralizes_core_quotient L₂ Y V₂ hcommY hcore
  have hvertex := vertex_eq_join V₂ L₂ Y T hLT hYC hC hfull
  have hfamily := pencil_preimages_eq_conjugate_family U Z V Y hVU hZV hYU
    action hact geom p line hmark horbit htrans
  have hspan := pencil_span_eq_generated U Z V Y geom p hfamily
  have hcover := source_ambient_coverage V V₂ L L₂ Y T hV₂ hLV htransV
    hvertex hcomm hYL hYC hTV hTY
  have hfix := source_family_action V V₂ L₂ Y hV₂ hcomm hYL hYC
  have hn : normalizer (V₂ : Set G) ≤ normalizer (pencilSpanPreimage U Z geom p : Set G) := by
    rw [hvertex,hspan]
    exact local_vertex_normalizes_span V L₂ Y T hfix.1 hTV hTY
  refine ⟨hfamily,hfamily.trans hcover.symm,hspan,hvertex,?_,?_,⟨hYL,hquot⟩,
    hn,ambientAction_kernel _ _ hn,?_⟩
  · rw [hspan]
    exact hfix.2
  · rw [hfamily]
    exact hfix.1
  · rw [ambientAction_kernel_map, inf_eq_right.mpr]
    rw [hspan]
    exact centralizer_span_le_vertex V V₂ Y hV₂

open scoped Pointwise in
/-- The saturation lemma applied to the literal source action and the actual
Aut(U(V₂)) stabilizer of V₂. The remaining linear branch must construct
these radical data; they are not hypotheses of the assembled source theorem. -/
theorem source_span_full_image_of_radical_data
    (V V₂ Y : Subgroup G)
    (hspan : normalizer (V₂ : Set G) ≤ normalizer (generatedLineFamily V Y : Set G))
    (hYV : Y ≤ normalizer (V₂ : Set G)) :
    let ρ := @ambientAction G _ (normalizer (V₂ : Set G)) (generatedLineFamily V Y) hspan
    let σ := @ambientAction G _ Y (generatedLineFamily V Y) (hYV.trans hspan)
    let P := MulAction.stabilizer (MulAut (generatedLineFamily V Y))
      (V₂.subgroupOf (generatedLineFamily V Y))
    ∀ R : Subgroup (MulAut (generatedLineFamily V Y)),
      ρ.range ⊔ R = P → ρ.range.pCoreIn 2 ≤ R →
      σ.range.pCoreIn 2 ≤ ρ.range.pCoreIn 2 → σ.range.pCoreIn 2 ≠ ⊥ →
      R ≤ centralizer (R : Set (MulAut (generatedLineFamily V Y))) →
      (∀ C : Subgroup (MulAut (generatedLineFamily V Y)), C ≤ R →
        P ≤ normalizer C → C = ⊥ ∨ C = R) → ρ.range = P := by
  dsimp only
  intro R hcover hcore hYcore hYne habelian hirr
  exact local_image_saturation _ _ R _ hcover hcore hYcore hYne habelian hirr

section FullSpanClosure
variable [Finite G]
open scoped Pointwise
open SpanSaturation ResidualAction
open BinaryLinear.FourParabolicRadical
open BinaryLinear.SmallParabolicLevi

/-- The source action image after the independent block and residual-image
calculations. Residual normality, containment of its two-core, the parabolic
radical, and radical irreducibility are all discharged here. Only the genuine
source-action hypotheses `hfull` and `hseed` are left explicit in this
intermediate theorem; `source_span_image_and_quotient` discharges both. -/
theorem source_span_image_of_block_and_residual_actions
    (H V V₂ Y : Subgroup G) (hY : Y = localResidual H V₂)
    (hC : centralizer (V₂ : Set G) ≤ H) (hV₂ : V₂ ≤ V)
    (hspan : normalizer (V₂ : Set G) ≤ normalizer (generatedLineFamily V Y : Set G))
    (hYV : Y ≤ normalizer (V₂ : Set G))
    (E : generatedLineFamily V Y ≃* Multiplicative BSpace)
    (hE : (V₂.subgroupOf (generatedLineFamily V Y)).map E.toMonoidHom =
      plane.toAddSubgroup.toSubgroup)
    (hfull : Function.Surjective ((blockAction plane).comp
      (spanCoordinateAction V V₂ Y hV₂ hspan E hE)))
    (hseed : (ambientAction Y (generatedLineFamily V Y)
      (hYV.trans hspan)).range.pCoreIn 2 ≠ ⊥) :
    (ambientAction _ _ hspan).range = MulAction.stabilizer
      (MulAut (generatedLineFamily V Y)) (V₂.subgroupOf (generatedLineFamily V Y)) := by
  have hcore := source_residual_action_core_le H V V₂ Y hY hC hspan hYV
  have hn : (ambientAction _ _ hspan).range.pCoreIn 2 ≠ ⊥ := by
    intro hz
    exact hseed (bot_unique (hz ▸ hcore))
  let c := autCoordinates E
  let : Finite (MulAut (generatedLineFamily V Y)) :=
    Finite.of_injective (fun a : MulAut (generatedLineFamily V Y) =>
      (a : generatedLineFamily V Y → generatedLineFamily V Y)) DFunLike.coe_injective
  let : Finite Lin := Finite.of_injective
    (fun a : Lin => (a : BSpace → BSpace)) DFunLike.coe_injective
  have hk : IsPGroup 2 c.toMonoidHom.ker := by
    rw [MonoidHom.ker_eq_bot _ c.injective]
    exact IsPGroup.of_bot
  apply source_full_span_image_of_joint_blocks V V₂ Y hV₂ hspan E hE hfull
  rw [MonoidHom.range_comp, ← map_pCoreIn_of_ker_isPGroup c.toMonoidHom hk]
  exact fun h => hn ((Subgroup.map_eq_bot_iff_of_injective _ c.injective).mp h)

/-- The literal local vertex modulo C_G(W), with the normality witness made
explicit, is the full stabilizer of V₂ in GL(W). The kernel is obtained from
conjugation on W, and coordinate linearity is supplied by `autCoordinates`.
This intermediate application retains the two source-action hypotheses of
`source_span_image_of_block_and_residual_actions`; the final assembly below
discharges them through `SpanSourceActions`. -/
theorem source_span_quotient_of_block_and_residual_actions
    (H V V₂ Y : Subgroup G) (hY : Y = localResidual H V₂)
    (hC : centralizer (V₂ : Set G) ≤ H) (hV₂ : V₂ ≤ V)
    (hspan : normalizer (V₂ : Set G) ≤ normalizer (generatedLineFamily V Y : Set G))
    (hYV : Y ≤ normalizer (V₂ : Set G))
    (E : generatedLineFamily V Y ≃* Multiplicative BSpace)
    (hE : (V₂.subgroupOf (generatedLineFamily V Y)).map E.toMonoidHom =
      plane.toAddSubgroup.toSubgroup)
    (hfull : Function.Surjective ((blockAction plane).comp
      (spanCoordinateAction V V₂ Y hV₂ hspan E hE)))
    (hseed : (ambientAction Y (generatedLineFamily V Y)
      (hYV.trans hspan)).range.pCoreIn 2 ≠ ⊥) :
    let N := normalizer (V₂ : Set G)
    let C := centralizer (generatedLineFamily V Y : Set G)
    C ≤ N ∧ ∃ hnormal : (C.subgroupOf N).Normal,
      let := hnormal
      Nonempty ((N ⧸ C.subgroupOf N) ≃*
        MulAction.stabilizer (MulAut (generatedLineFamily V Y))
          (V₂.subgroupOf (generatedLineFamily V Y))) := by
  dsimp only
  have hi := source_span_image_of_block_and_residual_actions H V V₂ Y hY hC
    hV₂ hspan hYV E hE hfull hseed
  have hk := ambientAction_kernel _ _ hspan
  have hn : ((centralizer (generatedLineFamily V Y : Set G)).subgroupOf
      (normalizer (V₂ : Set G))).Normal := hk ▸ inferInstance
  let := hn
  refine ⟨(centralizer_le (hV₂.trans (original_le_generated V Y))).trans
    (centralizer_le_normalizer _),hn,?_⟩
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hk.symm).trans
    ((QuotientGroup.quotientKerEquivRange (ambientAction _ _ hspan)).trans
      (MulEquiv.subgroupCongr hi))⟩

end FullSpanClosure

section SourceAssembly
variable [Finite G]
open scoped Pointwise

/-- Discharge the joint block action and the residual-image seed in both
span consumers. Marked binary coordinates are constructed from the source
ranks. All remaining inputs are earlier local identities or clauses of
14.7.55, expressed on their literal quotient; no conclusion of 14.7.56
is an action hypothesis. -/
theorem source_span_image_and_quotient
    (H U V V₁ V₂ Y L₂ T : Subgroup G) [(V₁.subgroupOf U).Normal]
    [IsElementaryAbelian 2 (generatedLineFamily V Y)]
    (hY : Y = localResidual H V₂)
    (hC : centralizer (V₂ : Set G) ≤ H)
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
    (ambientAction _ _ hspan).range = MulAction.stabilizer
      (MulAut (generatedLineFamily V Y)) (V₂.subgroupOf (generatedLineFamily V Y)) ∧
    let N := normalizer (V₂ : Set G)
    let C := centralizer (generatedLineFamily V Y : Set G)
    C ≤ N ∧ ∃ hnormal : (C.subgroupOf N).Normal,
      let := hnormal
      Nonempty ((N ⧸ C.subgroupOf N) ≃*
        MulAction.stabilizer (MulAut (generatedLineFamily V Y))
          (V₂.subgroupOf (generatedLineFamily V Y))) := by
  obtain ⟨hYV,E,hE,hblocks,hseed⟩ := SpanSourceActions.source_span_action_inputs
    H U V V₁ V₂ Y L₂ T hY hV₂ hV₁ hWU hW hD hZ hspan hLT hfull hcomm
    hHU hstar hquot eYT
  exact ⟨source_span_image_of_block_and_residual_actions H V V₂ Y hY hC
      hV₂ hspan hYV E hE hblocks hseed,
    source_span_quotient_of_block_and_residual_actions H V V₂ Y hY hC
      hV₂ hspan hYV E hE hblocks hseed⟩

/-- Full conditional 14.7.56 on the literal pencil preimages. The action
image and the centralizer quotient are the full stabilizer, and fixation
means normalization of each family member. Span invariance, block
surjectivity, the image two-core, and its saturation are proved here.

The geometry is constructed from the actual natural/Weyl module
equivalence using `Models`. The source owner supplies the marked pencil
formulas of 14.7.55 and the earlier local identities. The orders and elementary abelianness remain earlier-source
inputs, as in the contract of `SpanSourceActions`. -/
theorem source_pencil_full_local_deductions
    (H U V V₁ V₂ L L₂ Y T : Subgroup G) [(V₁.subgroupOf U).Normal]
    [IsElementaryAbelian 2 U]
    (hY : Y = localResidual H V₂)
    (hVU : V ≤ U) (hV₁ : V₁ ≤ V₂) (hV₂ : V₂ ≤ V)
    (hHU : H ≤ normalizer U) (hTH : T ≤ H) (hLV : L ≤ normalizer V)
    (htransV : ∀ W : Subgroup G, W ≤ V → Nat.card W = Nat.card V₂ →
      ∃ l : L, conjugate V₂ l = W)
    (hcomm : ⁅V,L₂⁆ = V₂)
    (hcommY : ⁅L₂,Y⁆ ≤ L₂ ⊓ centralizer (V₂ : Set G))
    (hcore : L₂ ⊓ centralizer (V₂ : Set G) = L₂.pCoreIn 2)
    (hLT : L₂ ⊔ T ≤ normalizer (V₂ : Set G))
    (hC : centralizer (V₂ : Set G) = Y ⊔ (T ⊓ centralizer (V₂ : Set G)))
    (hfull : Function.Surjective (ambientAction (L₂ ⊔ T) V₂ hLT))
    (hTV : T ≤ normalizer V) (hTY : T ≤ normalizer Y)
    (action : Y →* MulAut (U ⧸ V₁.subgroupOf U))
    (hact : ∀ y : Y, ∀ u : U,
      ∃ hu : (y : G) * (u : G) * (y : G)⁻¹ ∈ U,
      action y (QuotientGroup.mk' (V₁.subgroupOf U) u) =
        QuotientGroup.mk' (V₁.subgroupOf U) ⟨(y : G) * (u : G) * (y : G)⁻¹,hu⟩)
    (m : ThreeOffenderOrbit.BinaryG2Module)
    (E : Multiplicative m.Space ≃* (U ⧸ V₁.subgroupOf U)) :
    let geom := transportGeometry m.singularMap.geometry E
    ∀ (p : SingularPoints (ZMod 2)) (line : ZeroProductLine (ZMod 2))
    (_hmark : (V.subgroupOf U).map (QuotientGroup.mk' (V₁.subgroupOf U)) = geom.line line)
    (_horbit : ∀ y : Y, (geom.line line).map (action y).toMonoidHom ∈ markedPencil geom p)
    (_htrans : ∀ B ∈ markedPencil geom p,
      ∃ y : Y, (geom.line line).map (action y).toMonoidHom = B)
    (_hW : Nat.card (pencilSpanPreimage U V₁ geom p) = 16)
    (_hD : Nat.card V₂ = 4) (_hZ : Nat.card V₁ = 2)
    (_hcommH : ⁅V₂,H.pCoreIn 2⁆ = V₁)
    (_hstar : ∀ q : H.pCoreIn 2, ∀ u : U,
      QuotientGroup.mk' (V₁.subgroupOf U)
        ⟨(q : G) * (u : G) * (q : G)⁻¹,
          (mem_normalizer_iff.mp (hHU (pCoreIn_le 2 H q.property)) u).mp u.property⟩ =
        QuotientGroup.mk' (V₁.subgroupOf U) u)
    (_hquot : ((⁅pencilSpanPreimage U V₁ geom p,Y⁆).subgroupOf U).map
        (QuotientGroup.mk' (V₁.subgroupOf U)) =
      ((pencilSpanPreimage U V₁ geom p).subgroupOf U).map
        (QuotientGroup.mk' (V₁.subgroupOf U)))
    (_eYT : ((Y ⊔ T : Subgroup G) ⧸ pCore 2 (Y ⊔ T : Subgroup G)) ≃*
      Equiv.Perm (Fin 3)),
    let W := pencilSpanPreimage U V₁ geom p
    let N := normalizer (V₂ : Set G)
    let C := centralizer (W : Set G)
    pencilPreimages U V₁ geom p = conjugateLineFamily V Y ∧
    pencilPreimages U V₁ geom p = ambientConjugatesThrough V V₂ ∧
    W = generatedLineFamily V Y ∧
    N = L₂ ⊔ Y ⊔ T ∧
    ⁅W,L₂⁆ = V₂ ∧
    (∀ P ∈ pencilPreimages U V₁ geom p, L₂ ≤ normalizer P) ∧
    (∃ hYL : Y ≤ normalizer L₂, coreQuotientAction L₂ Y hYL = 1) ∧
    (∃ hspan : N ≤ normalizer (W : Set G),
      (ambientAction N W hspan).ker = C.subgroupOf N ∧
      (ambientAction N W hspan).ker.map N.subtype = C ∧
      (ambientAction N W hspan).range = MulAction.stabilizer (MulAut W) (V₂.subgroupOf W)) ∧
    C ≤ N ∧ ∃ hnormal : (C.subgroupOf N).Normal,
      let := hnormal
      Nonempty ((N ⧸ C.subgroupOf N) ≃*
        MulAction.stabilizer (MulAut W) (V₂.subgroupOf W)) := by
  dsimp only
  intro p line hmark horbit htrans hW hD hZ hcommH hstar hquot eYT
  let geom := transportGeometry m.singularMap.geometry E
  have hYH : Y ≤ H := by
    rw [hY,localResidual]
    exact (map_subtype_le _).trans inf_le_left
  have hYU := hYH.trans hHU
  have hact' : ∀ y : Y, ∀ u : U,
      action y (QuotientGroup.mk' (V₁.subgroupOf U) u) =
        QuotientGroup.mk' (V₁.subgroupOf U)
          ⟨(y : G) * (u : G) * (y : G)⁻¹,
            (mem_normalizer_iff.mp (hYU y.property) u).mp u.property⟩ := by
    intro y u
    obtain ⟨hu,he⟩ := hact y u
    exact he
  obtain ⟨hfamily,hcover,heq,hvertex,hcommW,hfix,htriv,hn,hker,hkerMap⟩ :=
    source_pencil_local_deductions H U V₁ V V₂ L L₂ Y T hY hVU (hV₁.trans hV₂)
      hV₂ hYU hLV htransV hcomm hcommY hcore hLT hC hfull hTV hTY
      action hact' geom p line hmark horbit htrans
  have hWU : generatedLineFamily V Y ≤ U := by
    rw [← heq]
    exact map_subtype_le _
  have hspan : normalizer (V₂ : Set G) ≤ normalizer (generatedLineFamily V Y : Set G) := by
    rwa [heq] at hn
  have hCH : centralizer (V₂ : Set G) ≤ H := by
    rw [hC]
    exact sup_le hYH (inf_le_left.trans hTH)
  let : IsElementaryAbelian 2 (generatedLineFamily V Y) := IsElementaryAbelian.of_le hWU
  have hresult := source_span_image_and_quotient H U V V₁ V₂ Y L₂ T hY hCH
    hV₂ hV₁ hWU (by rwa [heq] at hW) hD hZ hspan hLT hfull hcommH hHU hstar
    (by rwa [heq] at hquot) eYT
  have hresult' :
      (ambientAction _ _ hn).range = MulAction.stabilizer
        (MulAut (pencilSpanPreimage U V₁ geom p)) (V₂.subgroupOf (pencilSpanPreimage U V₁ geom p)) ∧
      centralizer (pencilSpanPreimage U V₁ geom p : Set G) ≤ normalizer (V₂ : Set G) ∧
      ∃ hnormal : ((centralizer (pencilSpanPreimage U V₁ geom p : Set G)).subgroupOf
          (normalizer (V₂ : Set G))).Normal,
        let := hnormal
        Nonempty (((normalizer (V₂ : Set G)) ⧸
            (centralizer (pencilSpanPreimage U V₁ geom p : Set G)).subgroupOf
              (normalizer (V₂ : Set G))) ≃*
          MulAction.stabilizer (MulAut (pencilSpanPreimage U V₁ geom p))
            (V₂.subgroupOf (pencilSpanPreimage U V₁ geom p))) := by
    generalize hw : pencilSpanPreimage U V₁ geom p = W at hn ⊢
    have hW : W = generatedLineFamily V Y := hw.symm.trans heq
    clear hw
    subst W
    exact hresult
  exact ⟨hfamily,hcover,heq,hvertex,hcommW,hfix,htriv,
    ⟨hn,hker,hkerMap,hresult'.1⟩,hresult'.2⟩


end SourceAssembly

end CFSG.Quasithin.Chapter14.Section07.G2Exclusion.MarkedGeometry.LocalParabolics
