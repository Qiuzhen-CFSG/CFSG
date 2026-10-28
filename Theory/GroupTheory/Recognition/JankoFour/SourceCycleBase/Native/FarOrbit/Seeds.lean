module
public import Theory.GroupTheory.Recognition.JankoFour.SourceCycleBase.Native.FarOrbit.MaskTools
public import Mathlib.LinearAlgebra.Matrix.Notation
/-!
# Literal near-trio seeds for the sextet stabilizer forest

Six explicit Golay trios and two sextets supply the three near-root witnesses.
Every octad is a checked weight-eight Golay word, and each incidence is given
by its explicit pair of tetrads. These witnesses exclude three forest roots
for a trio coplanar with no incident trio of the standard sextet.

Source: AS91 (3.8); native witnesses from the supplied orbit certificate.
-/
@[expose] public section
open Sporadic.Mathieu Sporadic.Mathieu.M24LocalGeometry
open Sporadic.Mathieu.M24LocalGeometry.PairOvergroups
open scoped Matrix Pointwise
namespace Theory.GroupTheory.Recognition.JankoFour.SourceCycleBase.Native.FarOrbit
def seedMasks : Fin 6 → Fin 3 → BitVec 24 :=
  ![![1950, 256033, 16519232], ![6869, 1753130, 15017216], ![6869, 2704650, 14065696], ![133183, 1626816, 15017216], ![674416, 1085583, 15017216], ![541263, 1218736, 15017216]]
def seedMessage : Fin 6 → Fin 3 → Fin 4096 :=
  ![![926, 3105, 64], ![1749, 42, 2304], ![1749, 266, 2080], ![1087, 704, 2304], ![1648, 143, 2304], ![591, 1200, 2304]]

theorem seed_word (i : Fin 6) (j : Fin 3) :
    support (seedMasks i j) = m24GolayWord (seedMessage i j) := by
  revert i j; decide +kernel

def seedLine (i : Fin 6) : Line where
  parts := parts (seedMasks i)
  card := by revert i; decide +kernel
  octad := by
    intro A hA
    obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hA
    simp only [maskParts,Finset.mem_insert,Finset.mem_singleton] at ha
    rcases ha with rfl|rfl|rfl
    all_goals rw [seed_word]; apply m24GolayWord_mem_blocks_of_card_eq_eight
    all_goals revert i; decide +kernel
  disjoint := by
    intro A hA B hB hne
    obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hA
    obtain ⟨b,hb,rfl⟩ := Finset.mem_image.mp hB
    simp only [maskParts,Finset.mem_insert,Finset.mem_singleton] at ha hb
    rcases ha with rfl|rfl|rfl <;> rcases hb with rfl|rfl|rfl
    all_goals revert i; decide +kernel
  cover := by revert i; decide +kernel
def planeMasks : Fin 2 → Fin 6 → BitVec 24 :=
  ![![2640, 4229, 671776, 1081354, 4203776, 10813440], ![581, 6288, 540682, 1212448, 2163968, 12853248]]
def planeMessage : Fin 2 → Fin 6 → Fin 6 → Fin 4096 :=
  ![![![0, 1749, 1648, 1626, 3920, 1616], ![1749, 0, 165, 143, 2437, 133], ![1648, 165, 0, 42, 2336, 32], ![1626, 143, 42, 0, 2314, 10], ![3920, 2437, 2336, 2314, 0, 2304], ![1616, 133, 32, 10, 2304, 0]], ![![0, 1749, 591, 613, 837, 2629], ![1749, 0, 1178, 1200, 1424, 3216], ![591, 1178, 0, 42, 266, 2058], ![613, 1200, 42, 0, 288, 2080], ![837, 1424, 266, 288, 0, 2304], ![2629, 3216, 2058, 2080, 2304, 0]]]

theorem plane_word (s : Fin 2) (i j : Fin 6) (hij : i ≠ j) :
    support (planeMasks s i) ∪ support (planeMasks s j) =
      m24GolayWord (planeMessage s i j) := by
  revert s i j; decide +kernel

def nearPlane (s : Fin 2) : Plane where
  parts := Finset.univ.image (fun i => support (planeMasks s i))
  card := by revert s; decide +kernel
  tetrad := by
    intro A hA
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hA
    revert s i; decide +kernel
  disjoint := by
    intro A hA B hB hne
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hA
    obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hB
    revert s i j; decide +kernel
  cover := by revert s; decide +kernel
  octad := by
    intro A hA B hB hne
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hA
    obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hB
    have hij : i ≠ j := fun he => hne (he ▸ rfl)
    rw [plane_word s i j hij]
    apply m24GolayWord_mem_blocks_of_card_eq_eight
    revert s i j
    decide +kernel

theorem near_one_incident_standard : Incident (seedLine 4) standardSextet := by
  intro A hA
  obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hA
  simp only [maskParts,Finset.mem_insert,Finset.mem_singleton] at ha
  rcases ha with rfl|rfl|rfl
  · exact ⟨standardTetrad 3,by decide +kernel,standardTetrad 4,by decide +kernel,by decide +kernel,by decide +kernel⟩
  · exact ⟨standardTetrad 0,by decide +kernel,standardTetrad 2,by decide +kernel,by decide +kernel,by decide +kernel⟩
  · exact ⟨standardTetrad 1,by decide +kernel,standardTetrad 5,by decide +kernel,by decide +kernel,by decide +kernel⟩

theorem near_one_incident_plane : Incident (seedLine 4) (nearPlane 0) := by
  intro A hA
  obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hA
  simp only [maskParts,Finset.mem_insert,Finset.mem_singleton] at ha
  rcases ha with rfl|rfl|rfl
  · exact ⟨support (planeMasks 0 0),by decide +kernel,support (planeMasks 0 2),by decide +kernel,by decide +kernel,by decide +kernel⟩
  · exact ⟨support (planeMasks 0 1),by decide +kernel,support (planeMasks 0 3),by decide +kernel,by decide +kernel,by decide +kernel⟩
  · exact ⟨support (planeMasks 0 4),by decide +kernel,support (planeMasks 0 5),by decide +kernel,by decide +kernel,by decide +kernel⟩

theorem seed_one_incident_plane : Incident (seedLine 1) (nearPlane 0) := by
  intro A hA
  obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hA
  simp only [maskParts,Finset.mem_insert,Finset.mem_singleton] at ha
  rcases ha with rfl|rfl|rfl
  · exact ⟨support (planeMasks 0 0),by decide +kernel,support (planeMasks 0 1),by decide +kernel,by decide +kernel,by decide +kernel⟩
  · exact ⟨support (planeMasks 0 2),by decide +kernel,support (planeMasks 0 3),by decide +kernel,by decide +kernel,by decide +kernel⟩
  · exact ⟨support (planeMasks 0 4),by decide +kernel,support (planeMasks 0 5),by decide +kernel,by decide +kernel,by decide +kernel⟩

theorem near_two_incident_standard : Incident (seedLine 5) standardSextet := by
  intro A hA
  obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hA
  simp only [maskParts,Finset.mem_insert,Finset.mem_singleton] at ha
  rcases ha with rfl|rfl|rfl
  · exact ⟨standardTetrad 0,by decide +kernel,standardTetrad 3,by decide +kernel,by decide +kernel,by decide +kernel⟩
  · exact ⟨standardTetrad 2,by decide +kernel,standardTetrad 4,by decide +kernel,by decide +kernel,by decide +kernel⟩
  · exact ⟨standardTetrad 1,by decide +kernel,standardTetrad 5,by decide +kernel,by decide +kernel,by decide +kernel⟩

theorem near_two_incident_plane : Incident (seedLine 5) (nearPlane 1) := by
  intro A hA
  obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hA
  simp only [maskParts,Finset.mem_insert,Finset.mem_singleton] at ha
  rcases ha with rfl|rfl|rfl
  · exact ⟨support (planeMasks 1 0),by decide +kernel,support (planeMasks 1 2),by decide +kernel,by decide +kernel,by decide +kernel⟩
  · exact ⟨support (planeMasks 1 1),by decide +kernel,support (planeMasks 1 3),by decide +kernel,by decide +kernel,by decide +kernel⟩
  · exact ⟨support (planeMasks 1 4),by decide +kernel,support (planeMasks 1 5),by decide +kernel,by decide +kernel,by decide +kernel⟩

theorem seed_two_incident_plane : Incident (seedLine 2) (nearPlane 1) := by
  intro A hA
  obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hA
  simp only [maskParts,Finset.mem_insert,Finset.mem_singleton] at ha
  rcases ha with rfl|rfl|rfl
  · exact ⟨support (planeMasks 1 0),by decide +kernel,support (planeMasks 1 1),by decide +kernel,by decide +kernel,by decide +kernel⟩
  · exact ⟨support (planeMasks 1 2),by decide +kernel,support (planeMasks 1 4),by decide +kernel,by decide +kernel,by decide +kernel⟩
  · exact ⟨support (planeMasks 1 3),by decide +kernel,support (planeMasks 1 5),by decide +kernel,by decide +kernel,by decide +kernel⟩

theorem seed_three_incident_standard : Incident (seedLine 3) standardSextet := by
  intro A hA
  obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hA
  simp only [maskParts,Finset.mem_insert,Finset.mem_singleton] at ha
  rcases ha with rfl|rfl|rfl
  · exact ⟨standardTetrad 0,by decide +kernel,standardTetrad 4,by decide +kernel,by decide +kernel,by decide +kernel⟩
  · exact ⟨standardTetrad 2,by decide +kernel,standardTetrad 3,by decide +kernel,by decide +kernel,by decide +kernel⟩
  · exact ⟨standardTetrad 1,by decide +kernel,standardTetrad 5,by decide +kernel,by decide +kernel,by decide +kernel⟩

theorem seed_one_near : NearPlane standardSextet (seedLine 1) :=
  ⟨seedLine 4,near_one_incident_standard,nearPlane 0,near_one_incident_plane,seed_one_incident_plane⟩

theorem seed_two_near : NearPlane standardSextet (seedLine 2) :=
  ⟨seedLine 5,near_two_incident_standard,nearPlane 1,near_two_incident_plane,seed_two_incident_plane⟩

theorem seed_three_near : NearPlane standardSextet (seedLine 3) :=
  ⟨seedLine 3,seed_three_incident_standard,standardSextet,seed_three_incident_standard,
    seed_three_incident_standard⟩
end Theory.GroupTheory.Recognition.JankoFour.SourceCycleBase.Native.FarOrbit
