module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.CubicLocal
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanGlobalPrimeZeroCoreGeometry
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalRecognitionUnitaryPlane
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGeneric

/-!
# The original cubic Cartan endpoint

For the selected zero-core Cartan pair with actor D of order three,
the earlier source construction proves that the full overlap SB₂ has
index three in DSB₂. Both endpoint markings in the same finite quotient
transport that index to its first standard panel. Its canonical root
therefore has order two. Index-two normality discharges Fong--Seitz (2B)
at this endpoint, and the original root-generated group acts faithfully
as the full symmetric group on the same panel. The remainder pulls back
to the actual first parabolic two-core.

The final theorem applies this to the literal Chapter12 chosen-module
input, retaining D, R, the full Borel and both endpoint markings. The
earlier selected LocalData and the marked split quotient remain supplied
by their source construction and apartment/exchange owners. No seven-row
comparison or recognition of the ambient generated group is asserted.

Source: Aschbacher--Smith 5.2.2, pp.647--648, and Chapter12, p.795;
Fong--Seitz I (2B), p.9, and the binary linear case of (5C)(b), pp.25--26.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary
open Chapter6.Source.RankOneGeneric Chapter6.Source.RankOneGeneric.Prime
variable {G X : Type*} [Group G] [Finite G] [Group X]
  {T : Sylow 2 G} {L W H A B D R : Subgroup G} {n : ℕ} {P : Fin 2 → Subgroup X}
  (d : LocalData T L H B D R) (h : Input KnownSimple.IsKnownSimple T L W n)
  (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
  (c : CartanPair T L H A B) (hd : CartanPrimeActor A H 3 D)
  (hz : (Prime.generated L H D R).pCoreIn 2 = ⊥)
  (Q : MarkedQuotient P)
  (e : RankTwoAmalgam.Iso
    (Global.sourceParabolicAmalgam ![D ⊔ Global.sourceS L H,R] (Global.sourceS L H))
    Q.standardAmalgam)
  (split : SplitData Q.tits)

include d h hH c hd hz e in
/-- The actual first root order comes from the literal source overlap index three. -/
theorem cartan_cubic_root_card : Nat.card (simpleRoot Q split 0) = 2 := by
  have hf := d.hypothesisF11 h hH c hd hz
  have hi := d.zeroCore_left_index h hH c hd hz
  have heindex := index_comap_of_surjective
    (Q.tits.B.subgroupOf (Q.tits.standardParabolic {Q.simple 0}))
    (f := (MarkedLocal.endpoint Q e 0).toMonoidHom)
    (MarkedLocal.endpoint Q e 0).surjective
  change (Q.tits.B.comap (MarkedLocal.endpointMap Q e 0)).index = _ at heindex
  rw [MarkedLocal.endpoint_borel_comap Q e hf 0] at heindex
  change (commonBorel ![D ⊔ Global.sourceS L H,R] (Global.sourceS L H)).relIndex
    (parabolic ![D ⊔ Global.sourceS L H,R] (Global.sourceS L H) 0) = _ at heindex
  rw [d.zeroCore_commonBorel hz,d.zeroCore_parabolic_zero] at heindex
  rw [singleton_parabolic_root_index Q split 0] at heindex
  omega

include d h hH c hd hz e in
/-- Fong--Seitz (2B) at the cubic endpoint of the ORIGINAL selected pair. -/
theorem cartan_cubic_remainder_le_kernel :
    simpleRemainder Q split 0 ≤ localKernel Q 0 :=
  PanelKernel.remainder_le_kernel_of_root_card_two Q split 0
    (cartan_cubic_root_card d h hH c hd hz Q e split)

/-- The original root group acts as S3 on the same marked cubic panel. -/
def cartanCubicRootEquiv : MarkedLocal.originalRankOne Q e split 0 ≃* Equiv.Perm (Panel Q 0) :=
  (MarkedLocal.originalRankOneEquiv Q e split 0).trans
    (PanelKernel.cubicRootEquiv Q split 0 (cartan_cubic_root_card d h hH c hd hz Q e split))

@[simp] theorem cartanCubicRootEquiv_apply (r : MarkedLocal.originalRankOne Q e split 0) :
    cartanCubicRootEquiv d h hH c hd hz Q e split r =
      (MarkedLocal.originalRootProjection Q e split 0 r : Equiv.Perm (Panel Q 0)) := by
  rw [cartanCubicRootEquiv,MulEquiv.trans_apply,PanelKernel.cubicRootEquiv_apply]
  exact (MarkedLocal.originalRootProjection_apply Q e split 0 r).symm

include d h hH c hd hz in
/-- The complementary root intersection pulls back to the actual first parabolic two-core. -/
theorem cartan_cubic_remainder_comap :
    (simpleRemainder Q split 0).comap (MarkedLocal.endpointMap Q e 0) =
      pCore 2 (parabolic ![D ⊔ Global.sourceS L H,R] (Global.sourceS L H) 0) :=
  MarkedLocal.remainder_comap_of_root_card_two Q e split 0
    (cartan_cubic_root_card d h hH c hd hz Q e split)

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary

namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source.RankOneGeneric Chapter6.Source.RankOneGeneric.Prime
open ChapterF.Source ChapterF.Source.FongSeitzBinary
variable {G X : Type*} [Group G] [Finite G] [Group X]
  {T : Sylow 2 G} {L V H A B D R : Subgroup G} {P : Fin 2 → Subgroup X}
  (C : ChosenModule T L V)
include C

/-- The literal Chapter12 cubic Cartan branch, with (2B) and its local cover discharged. -/
theorem rankOne_cartan_cubic_root_recognition
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2^n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (c : CartanPair T L H A B) (hd : CartanPrimeActor A H 3 D)
    (d : LocalData T L H B D R) (hz : (Prime.generated L H D R).pCoreIn 2 = ⊥)
    (Q : MarkedQuotient P)
    (e : RankTwoAmalgam.Iso
      (Global.sourceParabolicAmalgam ![D ⊔ Global.sourceS L H,R] (Global.sourceS L H))
      Q.standardAmalgam)
    (split : SplitData Q.tits) :
    simpleRemainder Q split 0 ≤ localKernel Q 0 ∧
      Nat.card (Panel Q 0) = 3 ∧
      (simpleRemainder Q split 0).comap (MarkedLocal.endpointMap Q e 0) =
        pCore 2 (parabolic ![D ⊔ Global.sourceS L H,R] (Global.sourceS L H) 0) ∧
      ∃ j : MarkedLocal.originalRankOne Q e split 0 ≃* Equiv.Perm (Panel Q 0),
        ∀ r, j r = (MarkedLocal.originalRootProjection Q e split 0 r : Equiv.Perm (Panel Q 0)) := by
  let hi := C.rankOne_generic_input_of_many h hmany hn hpsl
  refine ⟨cartan_cubic_remainder_le_kernel d hi hH c hd hz Q e split,
    PanelKernel.panel_card_three Q split 0 (cartan_cubic_root_card d hi hH c hd hz Q e split),
    cartan_cubic_remainder_comap d hi hH c hd hz Q e split,
    cartanCubicRootEquiv d hi hH c hd hz Q e split, ?_⟩
  exact cartanCubicRootEquiv_apply d hi hH c hd hz Q e split

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
