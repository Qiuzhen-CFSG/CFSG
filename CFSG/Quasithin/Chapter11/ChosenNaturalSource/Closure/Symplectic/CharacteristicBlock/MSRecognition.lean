module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic
public import CFSG.Quasithin.ChapterC.Section01.BlockTypes.Transport
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Symplectic.CharacteristicBlock.MSPair

/-!
# The closure MS-pair as an intrinsic symplectic input

The ambient group for C.1.32 is J=L O₂(G₁). All subgroups, characteristic
conditions, and core quotients are restricted to J through their literal
inclusions. The quotient marking is the original marked flag action.
Applying the intrinsic initial reduction gives faithfulness and positive
even critical geometry for this actual closure input. The complete FF
classification also supplies its natural moved layer of the original degree.
The literal graph cover retains its fixed kernel, and whole-core control
supplies shortness and the original conjugation-module model at that degree.

The field-four restriction and whole-core recognition remain to be proved
before discharging `hrecognition` in RootClosure.
Source: Aschbacher--Smith C.1.31--32 and 11.5.7, pp.135--136 and 783.
-/

public noncomputable section
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Symplectic.CharacteristicBlock
open Subgroup Theory.SpecificGroups.SymplecticFour
open Representation Representation.BinaryOffender
open ChapterB.QuasisimpleSource
open scoped IsMulCommutative
open CFSG.Quasithin.Chapter12.Section02
open ChapterC.RankTwo.NonbinarySymplectic
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    {D : ChosenModule T L V} (E : Geometry D) (m : MarkedFlag E)

/-- Every intrinsic premise is obtained from the actual closure MS-pair. -/
def intrinsicMSInput
    (hms : LocalGeometry.Normalizers.PointBlocks.NonbinaryMSPair
      E.input.field L (E.G₁.pCoreIn 2)) :
    Input (L.subgroupOf (L ⊔ E.G₁.pCoreIn 2))
      ((E.G₁.pCoreIn 2).subgroupOf (L ⊔ E.G₁.pCoreIn 2))
      E.input.field.degree E.input.field.Carrier :=
  Input.of_join hms.nonbinary E.input.field.card_eq hms.sqtk hms.fitting
    hms.component hms.product hms.radical hms.characteristic m.action.groupEquiv

/-- The transported marking agrees with the original marked action on representatives. -/
theorem intrinsicMSInput_quotient_mk
    (hms : LocalGeometry.Normalizers.PointBlocks.NonbinaryMSPair
      E.input.field L (E.G₁.pCoreIn 2))
    (l : L.subgroupOf (L ⊔ E.G₁.pCoreIn 2)) :
    (intrinsicMSInput E m hms).quotientEquiv (QuotientGroup.mk' _ l) =
      m.action.groupEquiv (QuotientGroup.mk' (pCore 2 L)
        (subgroupOfEquivOfLe le_sup_left l)) := by
  change m.action.groupEquiv (subgroupOfCoreQuotientEquiv le_sup_left
    (QuotientGroup.mk' _ l)) = _
  rw [subgroupOfCoreQuotientEquiv_mk]

include m

/-- The source MS3 hypothesis supplies the exact kernel on the original closure orbit. -/
theorem msPair_omegaOrbit_centralizer
    (hms : LocalGeometry.Normalizers.PointBlocks.NonbinaryMSPair
      E.input.field L (E.G₁.pCoreIn 2)) :
    centralizer (ChapterC.MSCentralOrbit.omegaOrbit
      ((E.G₁.pCoreIn 2).subgroupOf (L ⊔ E.G₁.pCoreIn 2)) :
        Set (L ⊔ E.G₁.pCoreIn 2 : Subgroup G)) =
      pCore 2 (L ⊔ E.G₁.pCoreIn 2 : Subgroup G) :=
  (intrinsicMSInput E m hms).omegaOrbit_centralizer

/-- The actual full-image branch admits positive even critical geometry. -/
theorem msPair_positive_even_geometry
    (hms : LocalGeometry.Normalizers.PointBlocks.NonbinaryMSPair
      E.input.field L (E.G₁.pCoreIn 2)) :
    ∃ g : ChapterC.BinaryMS.MS93.Geometry
        ((E.G₁.pCoreIn 2).subgroupOf (L ⊔ E.G₁.pCoreIn 2)),
      0 < g.b ((E.G₁.pCoreIn 2).subgroupOf (L ⊔ E.G₁.pCoreIn 2)) ∧
      Even (g.b ((E.G₁.pCoreIn 2).subgroupOf (L ⊔ E.G₁.pCoreIn 2))) :=
  (intrinsicMSInput E m hms).positive_even_geometry

/-- The closure orbit gives the full moved central omega layer in the
literal product group, without assuming field four or closure abelianness. -/
theorem msPair_initialCore_eq
    (hms : LocalGeometry.Normalizers.PointBlocks.NonbinaryMSPair
      E.input.field L (E.G₁.pCoreIn 2)) :
    ⁅ChapterC.MSCentralOrbit.omegaOrbit
        ((E.G₁.pCoreIn 2).subgroupOf (L ⊔ E.G₁.pCoreIn 2)),
      L.subgroupOf (L ⊔ E.G₁.pCoreIn 2)⁆ =
    ⁅omegaCenterIn (pCore 2 (L ⊔ E.G₁.pCoreIn 2 : Subgroup G)),
      L.subgroupOf (L ⊔ E.G₁.pCoreIn 2)⁆ :=
  (intrinsicMSInput E m hms).initialCore_eq

/-- MS3 recognizes the literal closure quotient action on its canonical
moved/fixed section. The degree equals the original marked field degree. -/
theorem msPair_centralOmega_moved_natural
    (hms : LocalGeometry.Normalizers.PointBlocks.NonbinaryMSPair
      E.input.field L (E.G₁.pCoreIn 2)) :
    let h := intrinsicMSInput E m hms
    let J := L ⊔ E.G₁.pCoreIn 2
    let C := (L.subgroupOf J).map (QuotientGroup.mk' (pCore 2 J))
    letI : C.Normal := h.component_image_structure.2.1
    let ρ := NormalElementaryQuotient.representation
      (omegaCenterIn (pCore 2 J)) (QuotientGroup.mk' (pCore 2 J))
      (QuotientGroup.mk'_surjective _)
      ((QuotientGroup.ker_mk' _).trans h.centralOmega_centralizer.symm)
    IsIrrPlus ρ C (subspaceCommutator ρ ⊤ C) ∧
      ∃ F : BinaryField, F.degree = E.input.field.degree ∧
        Nonempty (ActionEquiv ((MovedSection.ofNormal ρ C).action.comp C.subtype)
          (binarySymplectic F)) :=
  (intrinsicMSInput E m hms).centralOmega_moved_natural

open Representation.OneCohomology Representation.SymplecticFourOrthogonalCover in
/-- The whole quotient of the original closure product acts faithfully and
semilinearly on its marked natural quotient; its original projection is a cover. -/
theorem msPair_ambient_initial_cover
    (hms : LocalGeometry.Normalizers.PointBlocks.NonbinaryMSPair
      E.input.field L (E.G₁.pCoreIn 2)) :
    let h := intrinsicMSInput E m hms
    let J := L ⊔ E.G₁.pCoreIn 2
    let C := (L.subgroupOf J).map (QuotientGroup.mk' (pCore 2 J))
    letI : C.Normal := h.component_image_structure.2.1
    let ρ := NormalElementaryQuotient.representation
      (omegaCenterIn (pCore 2 J)) (QuotientGroup.mk' (pCore 2 J))
      (QuotientGroup.mk'_surjective _)
      ((QuotientGroup.ker_mk' _).trans h.centralOmega_centralizer.symm)
    let s := MovedSection.ofNormal ρ C
    ∃ F : BinaryField, F.degree = E.input.field.degree ∧
      ∃ e : ActionEquiv (s.action.comp C.subtype) (binaryNatural (K := F.Carrier)),
        IsCover (MovedSection.coverProjection s e) ∧
        Function.Injective (MovedSection.ambientAction s e) ∧
        (∀ g : J ⧸ pCore 2 J, ∃ σ : F.Carrier ≃+* F.Carrier, ∀ c v,
          MovedSection.ambientAction s e g (c • v) =
            σ c • MovedSection.ambientAction s e g v) := by
  obtain ⟨F,hF,e,hcover,j,hj,hjU,κ,hκ,hκQ,hκC,hκK,hfaith,hsemi,_⟩ :=
    (intrinsicMSInput E m hms).ambient_initial_cover_at_vertex
      (a := ChapterC.BinaryMS.MS93.alpha _) rfl
  exact ⟨F,hF,e,hcover,hfaith,hsemi⟩

open Stellmacher.PushingUp.AmalgamGraph ChapterC.BinaryMS.MS93
open Representation.OneCohomology Representation.SymplecticFourOrthogonalCover in
/-- The intrinsic natural cover is realized on the original closure graph's
moving subgroup. Its kernel is exactly the fixed subgroup of the residual. -/
theorem msPair_initial_subgroup_cover
    (hms : LocalGeometry.Normalizers.PointBlocks.NonbinaryMSPair
      E.input.field L (E.G₁.pCoreIn 2)) :
    let h := intrinsicMSInput E m hms
    let R₀ := (E.G₁.pCoreIn 2).subgroupOf (L ⊔ E.G₁.pCoreIn 2)
    let a := alpha R₀
    letI := h.vertex_moving_elementary (a := a) rfl
    ∃ F : BinaryField, F.degree = E.input.field.degree ∧
      ∃ σ : Representation (ZMod 2)
          (commutator (Matrix.symplecticGroup (Fin 2) F.Carrier)) (Additive (U R₀ a)),
      ∃ p : σ.IntertwiningMap (binaryNatural (K := F.Carrier)), IsCover p ∧
      ∃ f : Ltilde R₀ a →* commutator (Matrix.symplecticGroup (Fin 2) F.Carrier),
        Function.Surjective f ∧
        (∀ (k : Ltilde R₀ a) (u : U R₀ a),
          ((σ (f k) (Additive.ofMul u)).toMul : FreeAmalgam R₀) =
            (k : FreeAmalgam R₀) * u * (k : FreeAmalgam R₀)⁻¹) ∧
        p.toLinearMap.ker.toAddSubgroup.toSubgroup'.map (U R₀ a).subtype =
          U R₀ a ⊓ centralizer (Ltilde R₀ a : Set (FreeAmalgam R₀)) :=
  (intrinsicMSInput E m hms).initial_subgroup_cover_at_vertex rfl

/-- Whole-core control gives every short-group clause and an actual model
of the original L-module, with no prior restriction on the nonbinary degree. -/
theorem msPair_short_and_natural_of_frattini_small
    (hms : LocalGeometry.Normalizers.PointBlocks.NonbinaryMSPair
      E.input.field L (E.G₁.pCoreIn 2))
    (hsmall : ⁅pCore 2 (L ⊔ E.G₁.pCoreIn 2 : Subgroup G),
        L.subgroupOf (L ⊔ E.G₁.pCoreIn 2)⁆ ≤
      (frattini (pCore 2 (L ⊔ E.G₁.pCoreIn 2 : Subgroup G))).map
        (pCore 2 (L ⊔ E.G₁.pCoreIn 2 : Subgroup G)).subtype ⊔
      omegaCenterIn (pCore 2 (L ⊔ E.G₁.pCoreIn 2 : Subgroup G))) :
    ChapterC.IsShort L ∧ ∃ F : BinaryField, F.degree = E.input.field.degree ∧
      ChapterC.IsLinearBlockModel L (binarySymplectic F) := by
  obtain ⟨hs,F,hF,ρ,⟨model⟩,haction⟩ :=
    (intrinsicMSInput E m hms).short_and_natural_of_frattini_small hsmall
  let e : L.subgroupOf (L ⊔ E.G₁.pCoreIn 2) ≃* L := subgroupOfEquivOfLe le_sup_left
  exact ⟨hs.of_mulEquiv e,F,hF,ρ,⟨model.comap e.symm⟩,haction⟩

/-- The conditional Frattini branch returns a block on the original L,
transporting its whole conjugation module through the subgroup equivalence.
The field restriction and commutator bound still require their source proofs. -/
theorem sp4FourBlock_of_field_four_frattini_small
    (hms : LocalGeometry.Normalizers.PointBlocks.NonbinaryMSPair
      E.input.field L (E.G₁.pCoreIn 2))
    (hfour : Nat.card E.input.field.Carrier = 4)
    (hsmall : ⁅pCore 2 (L ⊔ E.G₁.pCoreIn 2 : Subgroup G),
        L.subgroupOf (L ⊔ E.G₁.pCoreIn 2)⁆ ≤
      (frattini (pCore 2 (L ⊔ E.G₁.pCoreIn 2 : Subgroup G))).map
        (pCore 2 (L ⊔ E.G₁.pCoreIn 2 : Subgroup G)).subtype ⊔
      omegaCenterIn (pCore 2 (L ⊔ E.G₁.pCoreIn 2 : Subgroup G))) :
    ChapterC.IsSp4FourBlock L := by
  have hb := (intrinsicMSInput E m hms).block_of_field_four_frattini_small hfour hsmall
  let e : L.subgroupOf (L ⊔ E.G₁.pCoreIn 2) ≃* L := subgroupOfEquivOfLe le_sup_left
  obtain ⟨hs,F,hF,hfinite,hcard,rho,⟨model⟩,haction⟩ := hb
  exact ⟨hs.of_mulEquiv e,F,hF,hfinite,hcard,rho,⟨model.comap e.symm⟩,haction⟩

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Symplectic.CharacteristicBlock
