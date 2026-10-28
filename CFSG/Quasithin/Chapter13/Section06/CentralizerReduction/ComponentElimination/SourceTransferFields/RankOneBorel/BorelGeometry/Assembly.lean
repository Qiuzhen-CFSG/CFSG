module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceTransferFields.RankOneBorel.BorelGeometry.Placement
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceTransferFields.RankOneBorel.BorelGeometry.ResidualProduct
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceTransferFields.RankOneBorel.BorelGeometry.MarkedAction
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceTransferFields.RankOneBorel.BorelGeometry.CheckedRigidity
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.LocalSetup.Configuration.Flags.Transport

/-!
# Marked Borel geometry from the earlier source inputs

The genuine E.2.3 application supplies Thompson and Baumann normalization
and places the constructed Borel in Mᵥ. The A₅ marking supplies the cubic
conjugation image, and the natural-section argument forces field degree
two. On the same coordinates, the residual has the full component Borel
image, fixes the specified a, and has the same action on V as Lᵥ. The whole
Borel fixes the checked image of a in C_G(v)/⟨v⟩.

Universal E.2.3 and the independent earlier local/minimal-parabolic inputs
remain explicit. This is the geometry branch of 13.6.18. The printed
full-Borel equality and fixation are not asserted: `Diagnostic` records
the obstruction. Instead, `source_component_centralizes` applies checked
rigidity to this geometry. The actual block model descends through the
central quotient, and two-perfectness lifts the resulting fixation to K.
Thus K centralizes the original marked a, with no additional fixation or
coordinate premise. The enclosing 13.6.18 owner supplies the block and
natural section, discharges the earlier inputs, and invokes 13.6.17 for
the final contradiction.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
proof of 13.6.18, printed p.931 (PDF p.948), with the marking on p.926.
-/

@[expose] public section

open Subgroup Stellmacher Matrix.SpecialLinearGroup
open scoped MatrixGroups IsMulCommutative
open Matrix.SpecialLinearGroup.RankOneResidual
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceTransferFields.RankOneBorel.BorelGeometry
open ComponentSelection A5Module Placement
variable {G : Type*} [Group G] [Finite G]
variable {F : Type*} [Field F] [Finite F] [CharP F 2] [Algebra (ZMod 2) F]

/-- The source flag, actual block and universal earlier inputs construct the
marked Borel, its normalizations and placement, degree two, the residual
product equality and residual/checked fixation of the specified a.
No Borel placement, cubic-action cardinality, degree bound or fixation is
assumed. The literal checked fixation supplies the repaired final step in
`source_component_centralizes`. -/
theorem source_geometry
    {T : Sylow 2 G} {L V V₁ V₂ : Subgroup G}
    (d : FlagSource T L V V₁ V₂) (K M : Subgroup G)
    (hL : Tv (T : Subgroup G) (markedV d.module) ≤
      normalizer (Lv L (markedV d.module) : Set G))
    (hz : Tv (T : Subgroup G) (markedV d.module) ≤
      centralizer ({markedZ d.module} : Set G))
    (hK : K ∈ Yz L (T : Subgroup G) (markedZ d.module) (markedV d.module))
    (hnorm : Tv (T : Subgroup G) (markedV d.module) ≤ normalizer (K : Set G))
    [IsElementaryAbelian 2 (WK K L (T : Subgroup G) (markedZ d.module) (markedV d.module))]
    {n : ℕ} (hF : Nat.card F = 2 ^ n) (hb : ChapterC.IsL2EvenBlock K n)
    (s : NaturalSection (F := F)
      (componentRepresentation K L (T : Subgroup G) (markedZ d.module) (markedV d.module) hL hz)
      (movingSpace K L (T : Subgroup G) (markedZ d.module) (markedV d.module)))
    {𝒞 : GroupClass} (hE23 : SourceFactors.SourceImplication 𝒞)
    (hBaum : SourceBaumannImplication 𝒞)
    (hq : IsSQTK 𝒞 (Gv (markedV d.module)))
    (hzOmega : markedZ d.module ∈ omegaOneCenterAmbient (Tv (T : Subgroup G) (markedV d.module)))
    (hpush : HigherFieldParabolics.CharacteristicNormalizerObstruction
      (Tv (T : Subgroup G) (markedV d.module)) K)
    (hSylow : Chapter1.IsSylowIn 2 (Tv (T : Subgroup G) (markedV d.module)) (Gv (markedV d.module)))
    (hf : Theory.GroupTheory.generalizedFitting (Gv (markedV d.module)) =
      pCore 2 (Gv (markedV d.module)))
    (P : Sylow 2 (K ⊔ Tv (T : Subgroup G) (markedV d.module) : Subgroup G))
    (hP : (P : Subgroup (K ⊔ Tv (T : Subgroup G) (markedV d.module) : Subgroup G)) =
      (Tv (T : Subgroup G) (markedV d.module)).subgroupOf
        (K ⊔ Tv (T : Subgroup G) (markedV d.module)))
    (hmin : ChapterB.IsMinimalParabolicOver P ⊤)
    (h1324 : ChapterB.baumann (T : Subgroup G) ≤ Tv (T : Subgroup G) (markedV d.module))
    (h1325 : normalizer (ChapterB.baumann (T : Subgroup G) : Set G) ≤ M)
    (hMV : normalizer (V : Set G) ≤ M)
    (hBV : Mv M (markedV d.module) ≤ normalizer (V : Set G))
    (hlocal : (pResidual 2 (Mv M (markedV d.module))).map (Mv M (markedV d.module)).subtype ≤
      Lv L (markedV d.module) ⊔ (M ⊓ centralizer (V : Set G))) :
    ∃ s' : NaturalSection (F := F)
        (componentRepresentation K L (T : Subgroup G) (markedZ d.module) (markedV d.module) hL hz)
        (movingSpace K L (T : Subgroup G) (markedZ d.module) (markedV d.module)),
      let B := borel K (Tv (T : Subgroup G) (markedV d.module))
      let R := (pResidual 2 B).map B.subtype
      Tv (T : Subgroup G) (markedV d.module) ≤ B ∧
      B ≤ K ⊔ Tv (T : Subgroup G) (markedV d.module) ∧
      B ≤ normalizer (elementaryAbelianMaxJ (Tv (T : Subgroup G) (markedV d.module)) : Set G) ∧
      B ≤ normalizer (ChapterB.baumann (Tv (T : Subgroup G) (markedV d.module)) : Set G) ∧
      B ≤ Mv M (markedV d.module) ∧
      ((B.subgroupOf K).map
        (componentMap K L (T : Subgroup G) (markedZ d.module) (markedV d.module) hL hz)).map
        s'.actor.toMonoidHom = rankOneBorel F ∧ n = 2 ∧
      R ⊔ (M ⊓ centralizer (V : Set G)) =
        Lv L (markedV d.module) ⊔ (M ⊓ centralizer (V : Set G)) ∧
      R ≤ centralizer ({markedA d.module} : Set G) ∧
      ((R.subgroupOf K).map
        (componentMap K L (T : Subgroup G) (markedZ d.module) (markedV d.module) hL hz)).map
        s'.actor.toMonoidHom = rankOneBorel F ∧
      checkedQuotientMap (markedV d.module) (inclusion inf_le_right d.checkedPoint) ∈
        centralizer (checkedImage (markedV d.module) B : Set (Gcheck (markedV d.module))) := by
  have hLV : Lv L (markedV d.module) ≤ normalizer (V : Set G) :=
    (residual_le_L d.module).trans d.module.normalizes
  have hc := marked_residual_conjugation_card d.module hLV
  have hn := local_source_normalizations_and_placement d.module K (T : Subgroup G) M
    d.action_kernel hL hz hK hnorm hF hb s hE23 hBaum hq hzOmega hpush hSylow
    hf P hP hmin h1324 h1325 hBV hMV
  have hzV : markedZ d.module ∈ V := map_mem d.module _
  let a : Gv (markedV d.module) := inclusion inf_le_right d.checkedPoint
  have ha := markedA_mem_centralizer d.module
  obtain ⟨s', hTB, hBK, hBim, hn2, hRa, hRim, hcheck⟩ :=
    local_source_conclusions K L (T : Subgroup G) M V (markedZ d.module) (markedV d.module)
      hL hz hb.1 hF hK hnorm s hn.2.2 hBV hLV hc hzV a ha.1 ha.2
      (marked_checked_central d) hlocal
  refine ⟨s', hTB, hBK, hn.1, hn.2.1, hn.2.2, hBim, hn2, ?_, hRa, hRim, hcheck⟩
  exact residual_product_eq_of_local_source K L (T : Subgroup G) M V _
    (markedZ d.module) (markedV d.module) hL hz hK hnorm s'
    (by rw [hF, hn2]; decide) hBim hn.2.2 hBV hLV hMV hc hzV hlocal

/-- The geometry and checked-rigidity branches of 13.6.18 together force
field degree two and centralization of the specified source a by K.

The block is an input, as supplied by the independent minimal replacement.
The degree and checked-Borel fixation are derived by `source_geometry`;
Y_z membership supplies both K ≤ C_G(v) and the relative Sylow condition.
There is no full-Borel fixation, product equality, quotient-model or
coordinate-compatibility premise. The enclosing source-theorem owner must
still discharge the earlier inputs and contradict this conclusion using
13.6.17. -/
theorem source_component_centralizes
    {T : Sylow 2 G} {L V V₁ V₂ : Subgroup G}
    (d : FlagSource T L V V₁ V₂) (K M : Subgroup G)
    (hL : Tv (T : Subgroup G) (markedV d.module) ≤
      normalizer (Lv L (markedV d.module) : Set G))
    (hz : Tv (T : Subgroup G) (markedV d.module) ≤
      centralizer ({markedZ d.module} : Set G))
    (hK : K ∈ Yz L (T : Subgroup G) (markedZ d.module) (markedV d.module))
    (hnorm : Tv (T : Subgroup G) (markedV d.module) ≤ normalizer (K : Set G))
    [IsElementaryAbelian 2 (WK K L (T : Subgroup G) (markedZ d.module) (markedV d.module))]
    {n : ℕ} (hF : Nat.card F = 2 ^ n) (hb : ChapterC.IsL2EvenBlock K n)
    (s : NaturalSection (F := F)
      (componentRepresentation K L (T : Subgroup G) (markedZ d.module) (markedV d.module) hL hz)
      (movingSpace K L (T : Subgroup G) (markedZ d.module) (markedV d.module)))
    {𝒞 : GroupClass} (hE23 : SourceFactors.SourceImplication 𝒞)
    (hBaum : SourceBaumannImplication 𝒞)
    (hq : IsSQTK 𝒞 (Gv (markedV d.module)))
    (hzOmega : markedZ d.module ∈ omegaOneCenterAmbient (Tv (T : Subgroup G) (markedV d.module)))
    (hpush : HigherFieldParabolics.CharacteristicNormalizerObstruction
      (Tv (T : Subgroup G) (markedV d.module)) K)
    (hSylow : Chapter1.IsSylowIn 2 (Tv (T : Subgroup G) (markedV d.module)) (Gv (markedV d.module)))
    (hf : Theory.GroupTheory.generalizedFitting (Gv (markedV d.module)) =
      pCore 2 (Gv (markedV d.module)))
    (P : Sylow 2 (K ⊔ Tv (T : Subgroup G) (markedV d.module) : Subgroup G))
    (hP : (P : Subgroup (K ⊔ Tv (T : Subgroup G) (markedV d.module) : Subgroup G)) =
      (Tv (T : Subgroup G) (markedV d.module)).subgroupOf
        (K ⊔ Tv (T : Subgroup G) (markedV d.module)))
    (hmin : ChapterB.IsMinimalParabolicOver P ⊤)
    (h1324 : ChapterB.baumann (T : Subgroup G) ≤ Tv (T : Subgroup G) (markedV d.module))
    (h1325 : normalizer (ChapterB.baumann (T : Subgroup G) : Set G) ≤ M)
    (hMV : normalizer (V : Set G) ≤ M)
    (hBV : Mv M (markedV d.module) ≤ normalizer (V : Set G))
    (hlocal : (pResidual 2 (Mv M (markedV d.module))).map (Mv M (markedV d.module)).subtype ≤
      Lv L (markedV d.module) ⊔ (M ⊓ centralizer (V : Set G))) :
    n = 2 ∧ K ≤ centralizer ({markedA d.module} : Set G) := by
  obtain ⟨_, _, _, _, _, _, _, hn2, _, _, _, hcheck⟩ :=
    source_geometry d K M hL hz hK hnorm hF hb s hE23 hBaum hq hzOmega
      hpush hSylow hf P hP hmin h1324 h1325 hMV hBV hlocal
  refine ⟨hn2, ?_⟩
  exact CheckedRigidity.source_marked_centralizes d K hK.1.1 hnorm hK.1.2.2.1
    (hn2 ▸ hb) hcheck


end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceTransferFields.RankOneBorel.BorelGeometry
