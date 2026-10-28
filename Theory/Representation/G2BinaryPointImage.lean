module
public import Theory.Representation.G2BinaryPlaneKernel
public import Theory.GroupTheory.PCoreImage
public import Theory.AtlasPort.LinearGroups.G2.LieBinaryCompatibility
public import Theory.AtlasPort.LinearGroups.G2.LieLongParabolic.Quotient

/-!
# Elementary actors in an actual point-stabilizer image

If an actor contains the genuine derived G₂ group, its range is normal
in full G₂. A marked point stabilizer therefore maps onto the intersection
of that range with the full point parabolic. An elementary subgroup normal
in this actual image lies in its two-core, hence in the full parabolic
two-core and the unipotent group. The derived point parabolic normalizes it.

Source: Aschbacher–Smith 13.8.27, printed p.963, using B.4.6(3).
The concrete model retains the attribution in LICENSES/ATLAS.txt.
-/

public section

open Subgroup
namespace Atlas.G2.Natural.BinaryPointFlag
open Atlas.G2.Restricted.NaturalCoordinates
variable {D : Type*} [Group D] [Finite D]

omit [Finite D] in
/-- The actual point stabilizer maps onto the full parabolic intersected
with the original actor image. -/
theorem marked_point_image
    (f : D →* Model F) (C : Subgroup D)
    (hC : ∀ a, a ∈ C ↔
      Restricted.NaturalCoordinates.action F (f a) (Pi.single 0 1) = Pi.single 0 1) :
    C.map f = BinaryCore.secondParabolic ⊓ f.range := by
  have hpoint (g : Model F) : g ∈ BinaryCore.secondParabolic ↔
      Restricted.NaturalCoordinates.action F g (Pi.single 0 1) = Pi.single 0 1 := by
    constructor
    · intro hg
      exact pointParabolic_fixes_pointLine g hg _ (by
        rw [mem_pointLine]
        intro i hi
        simp only [Pi.single_eq_of_ne hi])
    · exact fixes_first_mem_parabolic g
  ext g
  constructor
  · rintro ⟨a,ha,rfl⟩
    exact ⟨(hpoint _).mpr ((hC a).mp ha),⟨a,rfl⟩⟩
  · rintro ⟨hg,⟨a,rfl⟩⟩
    exact ⟨a,(hC a).mpr ((hpoint _).mp hg),rfl⟩

omit [Finite D] in
/-- Relative normality in the actual point image supplies both root-marking bounds. -/
theorem marked_point_actor_bounds
    (f : D →* Model F)
    (hrange : commutator (Model F) ≤ f.range)
    (C A : Subgroup D) (hAC : A ≤ C)
    (hn : C ≤ normalizer (A : Set D)) [IsElementaryAbelian 2 A]
    (hC : ∀ a, a ∈ C ↔
      Restricted.NaturalCoordinates.action F (f a) (Pi.single 0 1) = Pi.single 0 1) :
    A.map f ≤ unipotent ∧
      BinaryParabolicPair.derivedSecondAmbient ≤ normalizer (A.map f : Set _) := by
  have hmap := marked_point_image f C hC
  have hnorm : C.map f ≤ normalizer (A.map f : Set _) :=
    (map_mono hn).trans (le_normalizer_map f)
  have hderived : BinaryParabolicPair.derivedSecondAmbient ≤ C.map f := by
    rw [hmap]
    exact inf_le_inf le_rfl hrange
  refine ⟨?_,hderived.trans hnorm⟩
  have hcore : A.map f ≤ (C.map f).pCoreIn 2 :=
    le_pCoreIn_of_normalizes ((IsElementaryAbelian.isPGroup 2 A).map f)
      (map_mono hAC) hnorm
  let : f.range.Normal := Subgroup.Normal.of_commutator_le (Model F) hrange
  have hPnorm : BinaryCore.secondParabolic ≤ normalizer (C.map f : Set _) := by
    rw [hmap]
    exact (le_inf BinaryCore.secondParabolic.le_normalizer
      le_normalizer_of_normal).trans inf_normalizer_le_normalizer_inf
  have hcP := pCoreIn_mono_of_normalizes (p := 2)
    (show C.map f ≤ BinaryCore.secondParabolic from hmap ▸ inf_le_left) hPnorm
  have hPu : BinaryCore.secondParabolic.pCoreIn 2 ≤ unipotent := by
    rw [← LieParabolicSetup.local₂_binary,LieParabolicSetup.local₂_pCoreIn]
    exact LieParabolicSetup.fiveRootSubgroup_le_unipotent 4 (Or.inl rfl)
  exact hcore.trans (hcP.trans hPu)

end Atlas.G2.Natural.BinaryPointFlag
