module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearThree.CoreActions.ThreeLayer.Displacement
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.SourceSetup.BinaryFullCover

/-!
The actual moving plane identifies the component parabolic in any natural
layer, including the characteristic derived subgroup of the core. Its genuine
two-residual detects the doubled-dual cover by the two marked matrices.
This supplies whole-core generation without identifying the full center with
the natural layer. Source: Aschbacher--Smith15.3.23, p.1129.
-/

@[expose] public noncomputable section
open Subgroup Representation Representation.OneCohomology
open CFSG.Quasithin.Chapter15.Section04.LocalSetup.CoreElimination.BlockSieve.ExchangedCases.SL3Geometry.SourceCases
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearThree.OriginalSource.FullCover.Plane
open CoreActions CoreActions.ThreeLayer CoreActions.ThreeLayer.Displacement
open RankOneConfiguration.SmallExtension RankOneConfiguration.SmallExtension.CentralCover
open RankOneConfiguration.SmallExtension.CentralCover.LinearThree
variable {G : Type*} [Group G]
local notation "SL" => Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)
local notation "Res" => Matrix.PSL3Two.MarkedAutomorphisms.residual
/-- The actual subgroup of the natural center, in its supplied coordinates. -/
noncomputable def coordinatePlane {L Z : Subgroup G}
    {e : (L ⧸ pCore 2 L) ≃* SL}
    (m : LayerModel L Z ⊥ e (NaturalCopies (ZMod 2) 1)) (U : Subgroup G) :
    Submodule (ZMod 2) W :=
  AddSubgroup.toZModSubmodule 2 ((U.subgroupOf Z).map (naturalCoordinates m).toMonoidHom).toAddSubgroup

private lemma coordinatePlane_mem {L Z U : Subgroup G}
    {e : (L ⧸ pCore 2 L) ≃* SL}
    (m : LayerModel L Z ⊥ e (NaturalCopies (ZMod 2) 1)) (z : Z) :
    (naturalCoordinates m z).toAdd ∈ coordinatePlane m U ↔ (z : G) ∈ U := by
  constructor
  · rintro ⟨w, hw, he⟩
    exact (naturalCoordinates m).injective he ▸ hw
  · intro hz
    exact ⟨z, hz, rfl⟩

private lemma coordinatePlane_card {L Z U : Subgroup G}
    {e : (L ⧸ pCore 2 L) ≃* SL}
    (m : LayerModel L Z ⊥ e (NaturalCopies (ZMod 2) 1)) (hUZ : U ≤ Z) :
    Nat.card (coordinatePlane m U) = Nat.card U := by
  let f : U → coordinatePlane m U := fun u =>
    ⟨(naturalCoordinates m ⟨u, hUZ u.property⟩).toAdd,
      (coordinatePlane_mem m _).mpr u.property⟩
  have hf : Function.Bijective f := by
    constructor
    · intro u v huv
      apply Subtype.ext
      have hh := (naturalCoordinates m).injective
        (congrArg (fun x : coordinatePlane m U => Multiplicative.ofAdd (x : W)) huv)
      exact congrArg (fun z : Z => (z : G)) hh
    · intro v
      obtain ⟨z, hz⟩ := (naturalCoordinates m).surjective (Multiplicative.ofAdd v.val)
      have hzU : (z : G) ∈ U := (coordinatePlane_mem m z).mp (by rw [hz]; exact v.property)
      exact ⟨⟨z, hzU⟩, Subtype.ext (congrArg Multiplicative.toAdd hz)⟩
  exact (Nat.card_congr (Equiv.ofBijective f hf)).symm

variable [Finite G]

private lemma normalizer_image {L Z U : Subgroup G}
    {e : (L ⧸ pCore 2 L) ≃* SL}
    (m : LayerModel L Z ⊥ e (NaturalCopies (ZMod 2) 1)) (hUZ : U ≤ Z) :
    ((L ⊓ normalizer (U : Set G)).subgroupOf L).map (actorMap e) =
      stabilizer (coordinatePlane m U) := by
  have hiff (l : L) : actorMap e l ∈ stabilizer (coordinatePlane m U) ↔
      (l : G) ∈ normalizer (U : Set G) := by
    rw [stabilizer, MulAction.mem_stabilizer_set' (Set.toFinite _)]
    constructor
    · intro h
      apply mem_normalizer_fintype
      intro u hu
      have he := h ((coordinatePlane_mem m ⟨u, hUZ hu⟩).mpr hu)
      change ρ (e (QuotientGroup.mk' _ l)) (naturalCoordinates m ⟨u, hUZ hu⟩).toAdd ∈ coordinatePlane m U at he
      rw [← naturalCoordinates_intertwining m l ⟨u, hUZ hu⟩] at he
      exact (coordinatePlane_mem m _).mp he
    · intro hn v hv
      obtain ⟨z, hz⟩ := (naturalCoordinates m).surjective (Multiplicative.ofAdd v)
      have hu : (z : G) ∈ U := (coordinatePlane_mem m z).mp (by rw [hz]; exact hv)
      have hc := (coordinatePlane_mem m (layerConjugate L Z m.normalized l z)).mpr
        ((hn z).mp hu)
      rw [naturalCoordinates_intertwining, hz] at hc
      exact hc
  ext g
  constructor
  · rintro ⟨l, hl, rfl⟩
    exact (hiff l).mpr hl.2
  · intro hg
    obtain ⟨l, rfl⟩ := (e.surjective.comp (QuotientGroup.mk'_surjective (pCore 2 L))) g
    exact ⟨l, ⟨l.property, (hiff l).mp hg⟩, rfl⟩

/-- The image of the genuine Y_L is the two-residual of the plane stabilizer. -/
theorem YL_residual_image (d : LocalData G) (L : Subgroup G) {Z : Subgroup G}
    {e : (L ⧸ pCore 2 L) ≃* SL}
    (m : LayerModel L Z ⊥ e (NaturalCopies (ZMod 2) 1))
    {U : Subgroup G} (hUZ : U ≤ Z)
    (hSYL : d.S ≤ normalizer (YL d L : Set G))
    (hpar : YL d L ⊔ (d.S ⊓ L) = L ⊓ normalizer (U : Set G)) :
    ((YL d L).subgroupOf L).map (actorMap e) = Res (stabilizer (coordinatePlane m U)) := by
  have hYL : YL d L ≤ L :=
    (ComponentIntersection.intersectionResidual_le _ _).trans inf_le_right
  have hp : IsPPerfect 2 ((YL d L).subgroupOf L) :=
    (ComponentIntersection.intersectionResidual_isPPerfect d.Yplus L).of_surjective
      (subgroupOfEquivOfLe hYL).symm.toMonoidHom (subgroupOfEquivOfLe hYL).symm.surjective
  have hS : IsPGroup 2 ((d.S ⊓ L).subgroupOf L) :=
    (d.T.isPGroup'.to_le (show d.S ⊓ L ≤ (d.T : Subgroup G) from inf_le_left.trans inf_le_left)).comap_subtype
  have hn : (d.S ⊓ L).subgroupOf L ≤ normalizer (((YL d L).subgroupOf L) : Set L) := by
    rw [← subgroupOf_normalizer_eq hYL]
    exact fun s hs => hSYL hs.1
  have hr := embedded_pResidual_join_pGroup ((YL d L).subgroupOf L)
    ((d.S ⊓ L).subgroupOf L) hp hS hn
  rw [← subgroupOf_sup hYL inf_le_right, hpar] at hr
  rw [← hr, map_embedded_pResidual, normalizer_image m hUZ]
  rfl



private theorem detected_conjugate {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    (ρ : Representation (ZMod 2) SL V) (B : Subgroup SL) (a : SL)
    (h : DetectedOn ρ (B.map (MulAut.conj a).toMonoidHom)) : DetectedOn ρ B := by
  apply detectedOn_transport ρ ρ (MulAut.conj a)
    (LinearEquiv.ofBijective (ρ a) (ρ.apply_bijective a)) _ B h
  intro b v
  change ρ a (ρ b v) = ρ (a * b * a⁻¹) (ρ a v)
  rw [map_mul,map_mul]
  simp only [Module.End.mul_apply,inv_self_apply]

/-- The actual natural plane detects doubled-dual covers on the genuine YL,
independently of any identification of the full center with that natural layer. -/
theorem YL_detected (d : LocalData G) (L Z U : Subgroup G)
    {e : (L ⧸ pCore 2 L) ≃* SL}
    (m : LayerModel L Z ⊥ e (NaturalCopies (ZMod 2) 1))
    (hUZ : U ≤ Z) (hc : Nat.card U = 4)
    (hSYL : d.S ≤ normalizer (YL d L : Set G))
    (hpar : YL d L ⊔ (d.S ⊓ L) = L ⊓ normalizer (U : Set G)) :
    DetectedOn ChapterC.BinaryMS.dualPair.dual
      (((YL d L).subgroupOf L).map (actorMap e)) := by
  let V := coordinatePlane m U
  have hd : Module.finrank (ZMod 2) V = 2 :=
    MarkedModelAssembly.plane_dimension V ((coordinatePlane_card m hUZ).trans hc)
  obtain ⟨a,ha⟩ := LinearModels.PlaneGeometry.exists_plane_coordinates V hd
  let B := ((YL d L).subgroupOf L).map (actorMap e)
  have hB : B.map (MulAut.conj a).toMonoidHom = Res Matrix.PSL3Two.lineParabolicSL := by
    rw [show B = Res (stabilizer V) from YL_residual_image d L m hUZ hSYL hpar]
    rw [Matrix.PSL3Two.MarkedAutomorphisms.residual,map_embedded_pResidual]
    have hh := LinearModels.PlaneGeometry.stabilizer_map_conj V a ha
    have hs (V : Submodule (ZMod 2) W) :
        LinearModels.PlaneGeometry.stabilizer V = stabilizer V := by
      ext g
      rw [stabilizer,MulAction.mem_stabilizer_set]
      rfl
    rw [hs V] at hh
    have hcan : LinearModels.PlaneGeometry.stabilizer LinearModels.PlaneGeometry.plane =
        Matrix.PSL3Two.lineParabolicSL := by
      ext g
      rw [Matrix.PSL3Two.lineParabolicSL,MulAction.mem_stabilizer_set]
      rfl
    rw [hh,hcan]
    rfl
  apply detected_conjugate _ B a
  apply ContainedCoreModels.graph_double_dual_detected
  · rw [hB,Matrix.PSL3Two.MarkedAutomorphisms.line_residual]
    decide +kernel
  · rw [hB,Matrix.PSL3Two.MarkedAutomorphisms.line_residual]
    decide +kernel

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearThree.OriginalSource.FullCover.Plane
