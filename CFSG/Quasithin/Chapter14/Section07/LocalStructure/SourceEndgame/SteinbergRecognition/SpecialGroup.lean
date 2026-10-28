module

public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame.SteinbergRecognition.Centralization
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame.RuRecords
public import Theory.Representation.PSL3Two.IrreducibleCatalogue.Irreducibility

/-!
# The center from the actual Steinberg section

The image of Z(S) in S/V is an invariant subspace of the marked Steinberg
module. Irreducibility makes it zero or the whole quotient. The latter would
make S abelian, contradicting [S,S] = V ≠ 1. Thus Z(S) = V.

Source: Aschbacher–Smith, proof of 14.7.72, printed p.1076,
combined manuscript of 1 March 2004.
-/

public section
open Subgroup Representation
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame.SteinbergRecognition
open Chapter12.Section08 CriticalFusion.Source
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V : Subgroup G} {F : InvariantFlag T V 3}
  {W : Type u} [AddCommGroup W] [Module (ZMod 2) W] (d : Data T L V F W)

private noncomputable def imageSpace (c : SteinbergCoordinates d) (B : Subgroup G) :
    Submodule (ZMod 2) BinaryLinearThree.Steinberg :=
  AddSubgroup.toZModSubmodule 2 ((B.subgroupOf (S F L)).map c.coordinates).toAddSubgroup'

private theorem mem_imageSpace_iff (c : SteinbergCoordinates d)
    (B : Subgroup G) (v : BinaryLinearThree.Steinberg) :
    v ∈ imageSpace d c B ↔
      ∃ b : S F L, (b : G) ∈ B ∧ (c.coordinates b).toAdd = v := by
  change Multiplicative.ofAdd v ∈ (B.subgroupOf (S F L)).map c.coordinates ↔ _
  constructor
  · rintro ⟨b,hb,he⟩
    exact ⟨b,hb,congrArg Multiplicative.toAdd he⟩
  · rintro ⟨b,hb,he⟩
    exact ⟨b,hb,Multiplicative.toAdd.injective he⟩

/-- Recognition gives the center equality; the center is not an input to recognition. -/
theorem center_eq_of_steinberg
    (s : SteinbergCoordinates d)
    (hcentral : V ≤ (center (S F L)).map (S F L).subtype)
    (hderived : ⁅S F L,S F L⁆ = V) :
    (center (S F L)).map (S F L).subtype = V := by
  let C := (center (S F L)).map (S F L).subtype
  have hCS : C ≤ S F L := map_subtype_le _
  have hNC : L ≤ normalizer (C : Set G) :=
    (L_normalizes_S (F := F) (L := L)).trans (normalizer_le_normalizer_characteristic_image _ (center (S F L)))
  let X : Subrepresentation BinaryLinearThree.S := {
    toSubmodule := imageSpace d s C
    apply_mem_toSubmodule := by
      intro g v hv
      obtain ⟨l,hl⟩ := d.qL_surjective g
      obtain ⟨a,ha,rfl⟩ := (mem_imageSpace_iff d s C v).mp hv
      apply (mem_imageSpace_iff d s C _).mpr
      refine ⟨⟨l * a * (l : G)⁻¹,
        (mem_normalizer_iff.mp (L_normalizes_S (F := F) (L := L) l.property) a).mp a.property⟩,
        (mem_normalizer_iff.mp (hNC l.property) a).mp ha, ?_⟩
      exact (s.equivariant l a).trans (by rw [hl]) }
  let : IsIrreducible BinaryLinearThree.S :=
    BinaryLinearThree.IrreducibleCatalogue.steinberg_irreducible
  rcases eq_bot_or_eq_top X with hX | hX
  · apply le_antisymm ?_ hcentral
    intro c hc
    have hm : (s.coordinates ⟨c,hCS hc⟩).toAdd ∈ X :=
      (mem_imageSpace_iff d s C _).mpr ⟨⟨c,hCS hc⟩,hc,rfl⟩
    rw [hX] at hm
    exact (s.coordinates_eq_one_iff _).mp hm
  · have hSC : S F L ≤ C := by
      intro a ha
      have hm : (s.coordinates ⟨a,ha⟩).toAdd ∈ imageSpace d s C := by
        change _ ∈ X
        rw [hX]
        trivial
      obtain ⟨c,hc,he⟩ := (mem_imageSpace_iff d s C _).mp hm
      have hca : ((c⁻¹ * ⟨a,ha⟩ : S F L) : G) ∈ V := by
        apply (s.coordinates_eq_one_iff _).mp
        rw [map_mul, map_inv, Multiplicative.toAdd.injective he]
        exact inv_mul_cancel (s.coordinates ⟨a,ha⟩)
      have hm := C.mul_mem hc (hcentral hca)
      simpa only [Subgroup.coe_mul, Subgroup.coe_inv, mul_inv_cancel_left] using hm
    have hCC : C ≤ centralizer (S F L : Set G) := by
      rintro c ⟨z,hz,rfl⟩ a ha
      exact congrArg Subtype.val (mem_center_iff.mp hz ⟨a,ha⟩)
    have hbot : ⁅S F L,S F L⁆ = ⊥ :=
      commutator_eq_bot_iff_le_centralizer.mpr (hSC.trans hCC)
    exact (d.natural.chosen.ne_bot (hderived.symm.trans hbot)).elim

/-- Supply the actual Ru1 constructor after the later 14.7.74 inclusion T ≤ L.
The source center equality is derived from the recognized Steinberg action. -/
theorem ruOne_of_recognized_source
    (earlier : d.ModuleSeparation) (hTL : (T : Subgroup G) ≤ L)
    (hS : S F L = L.pCoreIn 2)
    (hcentral : V ≤ (center (S F L)).map (S F L).subtype)
    (hPhi : (frattini (S F L)).map (S F L).subtype = V)
    (hderived : ⁅S F L,S F L⁆ = V)
    (s : SteinbergCoordinates d) :
    Nonempty (ChapterJ.RuOne L V) := by
  have hcenter := center_eq_of_steinberg d s hcentral hderived
  let sec := s.toSection (hS.le.trans (pCoreIn_le 2 L))
  rw [hS] at sec hcenter hPhi hderived
  apply source_ruOne_of_steinberg d earlier hTL hcenter hPhi
    (by simpa only [map_subtype_commutator] using hderived)
    BinaryLinearThree.S sec (Representation.Equiv.refl _)

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame.SteinbergRecognition
