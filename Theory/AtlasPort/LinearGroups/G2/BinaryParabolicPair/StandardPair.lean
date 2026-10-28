module

public import Theory.AtlasPort.LinearGroups.G2.BinaryParabolicPair.MarkedRestriction
public import Theory.AtlasPort.LinearGroups.G2.LieBinaryCompatibility
public import Theory.AtlasPort.LinearGroups.G2.LieShortParabolic.Geometry
public import Theory.GroupTheory.Amalgam.RankTwo

/-!
# The marked geometric pair in G₂(2) and its derived group

The binary root parabolics equal the incident null-plane and point
stabilizers in the split octonions. The common Sylow subgroup is their whole
intersection. Restricting both stabilizers to the actual commutator subgroup
preserves this pair, with its order-32 Sylow subgroup and both inclusion maps.
The compatible isomorphisms use the ambient identity on all three groups.

The natural four-group is exactly the normal closure of the marked root
involution in the second parabolic, in both models. This connects the
explicit coordinates to the conjugate-generated V of the source.

Source: Aschbacher–Smith, Hypothesis 14.2.1 and Lemma 14.2.21, printed
pp.981 and 988, with the geometric pair of F.1.12(I)(3), printed p.263.
The imported octonion and root conventions follow the licensed ATLAS port
(LICENSES/ATLAS.txt).
-/

@[expose] public section
namespace Atlas.G2.BinaryParabolicPair
open BinaryCore LieParabolicSetup Theory.GroupTheory
noncomputable section

theorem firstParabolic_eq_planeStabilizer :
    firstParabolic = shortPlaneStabilizer (F := ZMod 2) :=
  parabolic₁_binary.symm.trans parabolic₁_eq_shortPlaneStabilizer

theorem secondParabolic_eq_pointStabilizer :
    secondParabolic = pointStabilizer (K := ZMod 2) := parabolic_eq_pointStabilizer

/-- Both maps are the original inclusions of the entire intersection. -/
def concreteAmalgam : RankTwoAmalgam firstParabolic
    (commonSylow : Subgroup (Model (ZMod 2))) secondParabolic :=
  .ofSubgroups _ _ _ commonSylow_le_first commonSylow_le_second

def geometricPair : RankTwoAmalgam (shortPlaneStabilizer (F := ZMod 2))
    (shortPlaneStabilizer (F := ZMod 2) ⊓ pointStabilizer : Subgroup (Model (ZMod 2)))
    (pointStabilizer (K := ZMod 2)) :=
  .ofSubgroups _ _ _ inf_le_left inf_le_right

theorem geometric_intersection :
    shortPlaneStabilizer (F := ZMod 2) ⊓ pointStabilizer =
      (commonSylow : Subgroup (Model (ZMod 2))) := by
  rw [← firstParabolic_eq_planeStabilizer, ← secondParabolic_eq_pointStabilizer]
  exact parabolic_intersection

/-- A single ambient identity makes both squares commute. -/
def geometricPairIso : RankTwoAmalgam.Iso concreteAmalgam geometricPair where
  left := MulEquiv.subgroupCongr firstParabolic_eq_planeStabilizer
  middle := MulEquiv.subgroupCongr geometric_intersection.symm
  right := MulEquiv.subgroupCongr secondParabolic_eq_pointStabilizer
  left_commutes _ := by apply Subtype.ext; rfl
  right_commutes _ := by apply Subtype.ext; rfl

theorem derivedFirst_eq_planeStabilizer :
    derivedFirst = (shortPlaneStabilizer (F := ZMod 2)).subgroupOf DerivedModel := by
  rw [derivedFirst, firstParabolic_eq_planeStabilizer]

theorem derivedSecond_eq_pointStabilizer :
    derivedSecond = (pointStabilizer (K := ZMod 2)).subgroupOf DerivedModel := by
  rw [derivedSecond, secondParabolic_eq_pointStabilizer]

def derivedAmalgam : RankTwoAmalgam derivedFirst
    (derivedSylow : Subgroup DerivedModel) derivedSecond :=
  .ofSubgroups _ _ _ derivedSylow_le_first derivedSylow_le_second

def derivedGeometricPair : RankTwoAmalgam
    ((shortPlaneStabilizer (F := ZMod 2)).subgroupOf DerivedModel)
    (((shortPlaneStabilizer (F := ZMod 2)).subgroupOf DerivedModel) ⊓
      ((pointStabilizer (K := ZMod 2)).subgroupOf DerivedModel) : Subgroup DerivedModel)
    ((pointStabilizer (K := ZMod 2)).subgroupOf DerivedModel) :=
  .ofSubgroups _ _ _ inf_le_left inf_le_right

theorem derived_geometric_intersection :
    (shortPlaneStabilizer (F := ZMod 2)).subgroupOf DerivedModel ⊓
      (pointStabilizer (K := ZMod 2)).subgroupOf DerivedModel =
      (derivedSylow : Subgroup DerivedModel) := by
  rw [← derivedFirst_eq_planeStabilizer, ← derivedSecond_eq_pointStabilizer]
  exact derived_parabolic_intersection_in_model

def derivedGeometricPairIso : RankTwoAmalgam.Iso derivedAmalgam derivedGeometricPair where
  left := MulEquiv.subgroupCongr derivedFirst_eq_planeStabilizer
  middle := MulEquiv.subgroupCongr derived_geometric_intersection.symm
  right := MulEquiv.subgroupCongr derivedSecond_eq_pointStabilizer
  left_commutes _ := by apply Subtype.ext; rfl
  right_commutes _ := by apply Subtype.ext; rfl

theorem natural_eq_normalClosure :
    (Subgroup.normalClosure
      ({⟨z, elementary_le_secondParabolic z_mem_elementary⟩} : Set secondParabolic)).map
      secondParabolic.subtype = natural := by
  let N := Subgroup.normalClosure
    ({⟨z, elementary_le_secondParabolic z_mem_elementary⟩} : Set secondParabolic)
  apply le_antisymm
  · have hN : N ≤ natural.subgroupOf secondParabolic :=
      Subgroup.normalClosure_le_normal (by rintro _ rfl; exact z_mem_natural)
    rintro _ ⟨x,hx,rfl⟩
    exact hN hx
  · apply natural_minimal
    · intro g hg
      apply Subgroup.le_normalizer_map secondParabolic.subtype
      exact ⟨⟨g,hg⟩, by rw [Subgroup.normalizer_eq_top]; trivial, rfl⟩
    · exact ⟨⟨z, elementary_le_secondParabolic z_mem_elementary⟩,
        Subgroup.subset_normalClosure (Set.mem_singleton _), rfl⟩

theorem derivedNatural_eq_normalClosure :
    (Subgroup.normalClosure
      ({⟨⟨z, rootA_one_mem_commutator⟩, elementary_le_secondParabolic z_mem_elementary⟩} :
        Set derivedSecond)).map derivedSecond.subtype = derivedNatural := by
  let N := Subgroup.normalClosure
    ({⟨⟨z, rootA_one_mem_commutator⟩, elementary_le_secondParabolic z_mem_elementary⟩} :
      Set derivedSecond)
  apply le_antisymm
  · have hN : N ≤ derivedNatural.subgroupOf derivedSecond :=
      Subgroup.normalClosure_le_normal (by rintro _ rfl; exact z_mem_natural)
    rintro _ ⟨x,hx,rfl⟩
    exact hN hx
  · apply derivedNatural_minimal
    · intro g hg
      apply Subgroup.le_normalizer_map derivedSecond.subtype
      exact ⟨⟨g,hg⟩, by rw [Subgroup.normalizer_eq_top]; trivial, rfl⟩
    · exact ⟨⟨⟨z, rootA_one_mem_commutator⟩, elementary_le_secondParabolic z_mem_elementary⟩,
        Subgroup.subset_normalClosure (Set.mem_singleton _), rfl⟩

theorem commonSylow_index_in_first :
    ((commonSylow : Subgroup (Model (ZMod 2))).subgroupOf firstParabolic).index = 3 := by
  have hc := ((commonSylow : Subgroup (Model (ZMod 2))).subgroupOf firstParabolic).card_mul_index
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe commonSylow_le_first).toEquiv,
    show Nat.card (commonSylow : Subgroup (Model (ZMod 2))) = 64 from card_unipotent_binary,
    card_firstParabolic] at hc
  omega

end
end Atlas.G2.BinaryParabolicPair
