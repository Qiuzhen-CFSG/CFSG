module

public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.TwoFactors.SingleOvergroup.Construction
public import CFSG.Quasithin.ChapterF.Section01.GreenBook.LieModels.BinaryLinear
public import Theory.AtlasPort.LinearGroups.G2.BinaryParabolicPair.CoreIdentification
public import Theory.Mathieu.M12.SmallParabolicPair.SylowGeometry
public import Theory.SpecificGroups.SymplecticFour.Binary.PointModel
public import Theory.SpecificGroups.SymplecticFour.Binary.PlaneModel

/-!
# Concrete model checks for the single-factor argument

The actual flag overlap in PSL₃(2) has center order two. The checked
split-octonion and Witt-design models give omega-center order two for the
G₂(2) and M₁₂ overlaps. Isomorphism invariance therefore excludes these
three overlaps when the source `Ω₁(Z(T))` has order four.

For the surviving binary symplectic model, the matrix point and plane
parabolics are explicitly isomorphic to `S₂ × S₄`. Here `S₂` is the
concrete cyclic group of order two. Field transport covers every field of
cardinality two. These identifications use the actual matrix equivalences;
no identification of an arbitrary generator is assumed.

These are the concrete checks for F.1.12 cases (1), (2), (3), and (12)
used in 15.4.15. Cases (8) and (13), and the universal F.6.5 assembly, remain
outside the assertions here. In particular this module does not infer a
classification from the listed examples or from an unconnected family tag.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, combined
1 March 2004 manuscript, F.1.12, printed pp.262–263, and 15.4.15, p.1161.
The cited concrete model modules retain their independent source attribution.
-/

@[expose] public section

open Subgroup
namespace CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.SingleOvergroup
variable {G : Type*} [Group G]

theorem omega_center_card_le_center [Finite G] (T : Subgroup G) :
    Nat.card (Stellmacher.omegaOneCenterAmbient T) ≤ Nat.card (center T) := by
  have hle : Stellmacher.omegaOneCenterAmbient T ≤ (center T).map T.subtype :=
    map_mono (map_subtype_le _)
  exact (card_le_of_le hle).trans_eq
    (Nat.card_congr ((center T).equivMapOfInjective T.subtype T.subtype_injective).toEquiv).symm

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
private theorem linear_binary_center_card : Nat.card (center Matrix.PSL3Two.borelSL) = 2 := by
  rw [Nat.card_eq_fintype_card]
  decide +kernel

/-- The actual binary projective flag overlap has omega-center of order at most two. -/
theorem linear_binary_omega_center_card_le :
    Nat.card (Stellmacher.omegaOneCenterAmbient Matrix.PSL3Two.borel) ≤ 2 := by
  have h := omega_center_card_eq_of_equiv Matrix.PSL3Two.borelSL Matrix.PSL3Two.borel
    (Matrix.PSL3Two.borelSL.equivMapOfInjective Matrix.PSL3Two.project Matrix.PSL3Two.project_injective)
  rw [← h]
  exact (omega_center_card_le_center Matrix.PSL3Two.borelSL).trans_eq linear_binary_center_card

/-- The actual split-octonion G₂(2) overlap has omega-center of order two. -/
theorem g2_binary_omega_center_card :
    Nat.card (Stellmacher.omegaOneCenterAmbient (Atlas.G2.unipotent (K := ZMod 2))) = 2 := by
  change Nat.card (((omega₁ (center (Atlas.G2.unipotent (K := ZMod 2))) (p := 2)).map
    (center (Atlas.G2.unipotent (K := ZMod 2))).subtype).map
      (Atlas.G2.unipotent (K := ZMod 2)).subtype) = 2
  rw [Atlas.G2.BinaryParabolicPair.commonSylow_omega_center]
  exact Atlas.G2.BinaryCore.card_distinguished

/-- The checked degree-twelve Witt-design overlap has omega-center of order two. -/
theorem m12_omega_center_card :
    Nat.card (Stellmacher.omegaOneCenterAmbient Sporadic.Mathieu.M12SmallPair.sylowCandidate) = 2 := by
  change Nat.card (((omega₁ (center Sporadic.Mathieu.M12SmallPair.sylowCandidate) (p := 2)).map
    (center Sporadic.Mathieu.M12SmallPair.sylowCandidate).subtype).map
      Sporadic.Mathieu.M12SmallPair.sylowCandidate.subtype) = 2
  rw [Sporadic.Mathieu.M12SmallPair.omega_center_image]
  exact Sporadic.Mathieu.M12SmallPair.card_distinguished

/-- The first surviving symplectic generator is actually C₂ × S₄. -/
noncomputable def symplectic_point_identification {F : Type*} [Field F] [Finite F]
    (hF : Nat.card F = 2) {A : Type*} [Group A]
    (e : A ≃* Theory.SpecificGroups.SymplecticFour.pointParabolic (F := F)) :
    A ≃* (Equiv.Perm (Fin 2) × Equiv.Perm (Fin 4)) :=
  e.trans ((Theory.SpecificGroups.SymplecticFour.Binary.pointParabolicEquivZModTwo hF).trans
    Theory.SpecificGroups.SymplecticFour.Binary.pointParabolicZModEquivProd)

/-- The second surviving symplectic generator is actually C₂ × S₄. -/
noncomputable def symplectic_plane_identification {F : Type*} [Field F] [Finite F]
    (hF : Nat.card F = 2) {A : Type*} [Group A]
    (e : A ≃* Theory.SpecificGroups.SymplecticFour.planeParabolic (F := F)) :
    A ≃* (Equiv.Perm (Fin 2) × Equiv.Perm (Fin 4)) :=
  e.trans ((Theory.SpecificGroups.SymplecticFour.Binary.planeParabolicEquivZModTwo hF).trans
    Theory.SpecificGroups.SymplecticFour.Binary.planeParabolicZModEquivProd)
/-- F.1.12(1)'s actual binary overlap cannot have the source center order four. -/
theorem not_linear_binary_overlap (T : Subgroup G)
    (hZ : Nat.card (Stellmacher.omegaOneCenterAmbient T) = 4) :
    ¬ Nonempty (T ≃* Matrix.PSL3Two.borel) := by
  rintro ⟨e⟩
  have he := omega_center_card_eq_of_equiv T Matrix.PSL3Two.borel e
  have hb := linear_binary_omega_center_card_le
  omega

/-- F.1.12(3)'s actual binary overlap cannot have the source center order four. -/
theorem not_g2_binary_overlap (T : Subgroup G)
    (hZ : Nat.card (Stellmacher.omegaOneCenterAmbient T) = 4) :
    ¬ Nonempty (T ≃* Atlas.G2.unipotent (K := ZMod 2)) := by
  rintro ⟨e⟩
  have he := omega_center_card_eq_of_equiv T (Atlas.G2.unipotent (K := ZMod 2)) e
  have hb := g2_binary_omega_center_card
  omega

/-- F.1.12(12)'s checked Witt-design overlap cannot have center order four. -/
theorem not_m12_overlap (T : Subgroup G)
    (hZ : Nat.card (Stellmacher.omegaOneCenterAmbient T) = 4) :
    ¬ Nonempty (T ≃* Sporadic.Mathieu.M12SmallPair.sylowCandidate) := by
  rintro ⟨e⟩
  have he := omega_center_card_eq_of_equiv T Sporadic.Mathieu.M12SmallPair.sylowCandidate e
  have hb := m12_omega_center_card
  omega

end CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.SingleOvergroup
