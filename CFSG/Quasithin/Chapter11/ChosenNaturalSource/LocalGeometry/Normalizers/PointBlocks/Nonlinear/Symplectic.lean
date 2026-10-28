module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.PointBlocks
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.Restriction
public import CFSG.Quasithin.ChapterC.Section01.BlockTypes.Transport

/-!
# The symplectic point as an intrinsic MS input

All intrinsic premises are transported to J=LR₁ using the literal inclusions,
odd-index witness and marked quotient. A block returned on the restricted
component is transported with its actual conjugation model back to L. Thus
only the shared intrinsic nonbinary symplectic classifier remains explicit;
no additional local classification, Sylow, or centrality premise is added.
The final original 11.1.5 assembly remains with this normalizer owner and the
preceding-source discharge remains with the local-geometry owner.
Source: Aschbacher--Smith C.1.31--32 and 11.1.5, pp.135--136,765.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Subgroup Theory.GroupTheory Representation
open CFSG.Quasithin.Chapter12.Section02 CFSG.Quasithin.ChapterB.QuasisimpleSource
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.PointBlocks.Nonlinear
open ChapterC.RankTwo.NonbinarySymplectic
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)

/-- The literal point pair, with all intrinsic C.1.31 premises discharged. -/
def point_symplectic_input
    (m : ActionEquiv D.centralQuotientAction
      (restrictScalars (k := ZMod 2) (symplecticNatural (k := S.field.Carrier) 2)))
    (f : InvariantFlag (.sp4 m)) (hm : NonbinaryMSPair S.field L (f.Ri 0)) :
    Input (L.subgroupOf (L ⊔ f.Ri 0)) ((f.Ri 0).subgroupOf (L ⊔ f.Ri 0))
      S.field.degree S.field.Carrier :=
  Input.of_join hm.nonbinary S.field.card_eq hm.sqtk hm.fitting hm.component
    hm.product hm.radical hm.characteristic m.groupEquiv

/-- The intrinsic quotient marking is the original map on representatives. -/
theorem point_symplectic_input_mk
    (m : ActionEquiv D.centralQuotientAction
      (restrictScalars (k := ZMod 2) (symplecticNatural (k := S.field.Carrier) 2)))
    (f : InvariantFlag (.sp4 m)) (hm : NonbinaryMSPair S.field L (f.Ri 0))
    (l : L.subgroupOf (L ⊔ f.Ri 0)) :
    (point_symplectic_input D S m f hm).quotientEquiv (QuotientGroup.mk' _ l) =
      m.groupEquiv (QuotientGroup.mk' (pCore 2 L) (subgroupOfEquivOfLe le_sup_left l)) := rfl

/-- Only the separately owned intrinsic symplectic classifier remains.
The resulting block retains its whole original conjugation-module model. -/
theorem symplectic_point_recognition_of_intrinsic
    (hintrinsic : ∀ (R : Subgroup G),
      Input (L.subgroupOf (L ⊔ R)) (R.subgroupOf (L ⊔ R)) S.field.degree S.field.Carrier →
        ChapterC.IsSp4FourBlock (L.subgroupOf (L ⊔ R))) :
    SymplecticPointRecognition D S := by
  intro m f hm
  have hb := hintrinsic (f.Ri 0) (point_symplectic_input D S m f hm)
  let e : L.subgroupOf (L ⊔ f.Ri 0) ≃* L := subgroupOfEquivOfLe le_sup_left
  obtain ⟨hs,F,hF,hfinite,hcard,rho,⟨model⟩,haction⟩ := hb
  exact ⟨hs.of_mulEquiv e,F,hF,hfinite,hcard,rho,⟨model.comap e.symm⟩,haction⟩

/-- The actual escaping symplectic point supplies V=V_M as well as the block. -/
theorem symplectic_escaping_point_of_intrinsic
    (hintrinsic : ∀ (R : Subgroup G),
      Input (L.subgroupOf (L ⊔ R)) (R.subgroupOf (L ⊔ R)) S.field.degree S.field.Carrier →
        ChapterC.IsSp4FourBlock (L.subgroupOf (L ⊔ R)))
    (m : ActionEquiv D.centralQuotientAction
      (restrictScalars (k := ZMod 2) (symplecticNatural (k := S.field.Carrier) 2)))
    (f : InvariantFlag (.sp4 m))
    (he : ¬ normalizer (f.Ri 0 : Set G) ≤ normalizer (L : Set G)) :
    V = Source.conjugateSpan (normalizer (L : Set G)) V ∧ ChapterC.IsSp4FourBlock L := by
  have hb := symplectic_point_recognition_of_intrinsic D S hintrinsic m f
    (point_msPair D S f he)
  exact ⟨(point_blocks_with_span D (n := S.field.degree) (Or.inr hb)).1,hb⟩

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.PointBlocks.Nonlinear
