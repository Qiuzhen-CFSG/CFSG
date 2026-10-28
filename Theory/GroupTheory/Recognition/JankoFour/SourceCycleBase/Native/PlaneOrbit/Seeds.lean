module
public import Theory.GroupTheory.Recognition.JankoFour.SourceCycleBase.Native.Hitting
/-!
# Four native sextets with near octad pencils

Explicit weight-eight Golay sums certify the four representative sextets.
Their incident trios are identified with entries of the already checked
trio forest. Each representative has a pencil whose three trios belong to
near forest roots. No new group generators or near-plane assumptions enter.

Source: AS91 (3.11.2), p.596.
-/
@[expose] public section
namespace Theory.GroupTheory.Recognition.JankoFour.SourceCycleBase.Native.PlaneOrbit
open Sporadic.Mathieu Sporadic.Mathieu.M24LocalGeometry
open Theory.SpecificGroups.SymmetricSix
open scoped Matrix Pointwise
open FarOrbit (support)
def seedMasks : Fin 4 → Fin 6 → BitVec 24 :=
  ![![15, 133168, 541248, 1085568, 2367744, 12649472], ![38944, 67136, 270346, 1179792, 2097413, 13123584], ![32775, 148736, 329792, 1052808, 4726816, 10486288], ![40994, 132624, 268296, 1114304, 4718597, 10502400]]
def message : Fin 4 → Fin 6 → Fin 6 → Fin 4096 :=
  ![![![0, 1087, 591, 143, 2319, 15], ![1087, 0, 1648, 1200, 3376, 1072], ![591, 1648, 0, 704, 2880, 576], ![143, 1200, 704, 0, 2432, 128], ![2319, 3376, 2880, 2432, 0, 2304], ![15, 1072, 576, 128, 2304, 0]], ![![0, 1632, 3114, 1200, 1317, 1056], ![1632, 0, 2634, 720, 837, 576], ![3114, 2634, 0, 2202, 2319, 2058], ![1200, 720, 2202, 0, 405, 144], ![1317, 837, 2319, 405, 0, 261], ![1056, 576, 2058, 144, 261, 0]], ![![0, 263, 1095, 143, 2087, 535], ![263, 0, 1344, 392, 2336, 784], ![1095, 1344, 0, 1224, 3168, 1616], ![143, 392, 1224, 0, 2216, 664], ![2087, 2336, 3168, 2216, 0, 2608], ![535, 784, 1616, 664, 2608, 0]], ![![0, 2610, 3114, 2274, 2087, 2338], ![2610, 0, 1560, 720, 533, 784], ![3114, 1560, 0, 1224, 1037, 1288], ![2274, 720, 1224, 0, 197, 448], ![2087, 533, 1037, 197, 0, 261], ![2338, 784, 1288, 448, 261, 0]]]
def pencilIndex : Fin 4 → Fin 15 := ![0, 0, 2, 1]
def trioIndex : Fin 4 → Fin 15 → Fin 3795 :=
  ![![375, 377, 379, 1197, 1200, 1202, 1477, 1984, 1986, 1480, 2188, 2583, 1482, 2190, 2585], ![331, 333, 335, 796, 798, 800, 871, 2187, 2188, 873, 2223, 2415, 875, 2224, 2416], ![519, 525, 526, 931, 938, 940, 1111, 1989, 1990, 1118, 2169, 2383, 1120, 2170, 2386], ![491, 496, 499, 796, 803, 805, 1021, 2085, 2086, 1028, 2229, 2383, 1030, 2230, 2385]]

theorem word (r : Fin 4) (i j : Fin 6) (hij : i ≠ j) :
    support (seedMasks r i) ∪ support (seedMasks r j) = m24GolayWord (message r i j) := by
  revert r i j; decide +kernel

def rootPlane (r : Fin 4) : Plane where
  parts := Finset.univ.image (fun i => support (seedMasks r i))
  card := by revert r; decide +kernel
  tetrad := by
    intro A hA
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hA
    revert r i; decide +kernel
  disjoint := by
    intro A hA B hB hne
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hA
    obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hB
    revert r i j; decide +kernel
  cover := by revert r; decide +kernel
  octad := by
    intro A hA B hB hne
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hA
    obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hB
    have hij : i ≠ j := fun he => hne (he ▸ rfl)
    rw [word r i j hij]
    apply m24GolayWord_mem_blocks_of_card_eq_eight
    revert r i j; decide +kernel

noncomputable def labels (r : Fin 4) : Fin 6 ≃ {A // A ∈ (rootPlane r).parts} :=
  Equiv.ofBijective (fun i => ⟨support (seedMasks r i),Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩⟩) ⟨by
    have hi : Function.Injective (fun i => support (seedMasks r i)) := by revert r; decide +kernel
    intro i j he
    exact hi (congrArg Subtype.val he),by
    rintro ⟨A,hA⟩
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hA
    exact ⟨i,rfl⟩⟩

theorem root_trio_parts (r : Fin 4) (s : Syntheme) :
    (synthemeTrio (rootPlane r) (labels r) s).parts =
      FarOrbit.parts (FarOrbit.row (trioIndex r s)).masks := by
  revert r s; decide +kernel

theorem root_near (r : Fin 4) (s : Syntheme) (hs : incident (pencilIndex r) s) :
    NearPlane standardSextet (synthemeTrio (rootPlane r) (labels r) s) := by
  have hnon : (FarOrbit.row (trioIndex r s)).root ≠ 0 := by
    have hc : ∀ (r : Fin 4) (s : Syntheme), incident (pencilIndex r) s →
        (FarOrbit.row (trioIndex r s)).root ≠ 0 := by decide +kernel
    exact hc r s hs
  have he : synthemeTrio (rootPlane r) (labels r) s = FarOrbit.entry (trioIndex r s) := by
    apply line_parts_injective
    rw [FarOrbit.entry_parts,root_trio_parts]
  rw [he]
  exact nearPlane_transport ((FarOrbit.exists_transport _).choose : M24) rfl
    (FarOrbit.exists_transport _).choose.property.symm (FarOrbit.root_ne_zero_near _ hnon)

/-- Every representative has an actual octad pencil all of whose trios are
near the fixed standard sextet. -/
theorem root_pencil (r : Fin 4) : ∃ A, PlaneOctad (rootPlane r) A ∧
    ∀ l, Incident l (rootPlane r) → A ∈ l.parts → NearPlane standardSextet l := by
  let a := pencilIndex r
  refine ⟨duadOctad (rootPlane r) (labels r) a,?_,?_⟩
  · obtain ⟨i,j,hij,ha⟩ := Finset.card_eq_two.mp (duad_is_duad a)
    refine ⟨(labels r i).val,(labels r i).property,(labels r j).val,(labels r j).property,?_,?_⟩
    · intro he
      exact hij ((labels r).injective (Subtype.ext he))
    · simp [duadOctad,tetradUnion,ha]
  · intro l hl hAl
    let s := residueEquiv (rootPlane r) (labels r) ⟨l,hl⟩
    have hs : incident a s := (residueEquiv_incidence _ _ ⟨l,hl⟩ a).mpr hAl
    have he : synthemeTrio (rootPlane r) (labels r) s = l := by
      have he' : (⟨synthemeTrio (rootPlane r) (labels r) s,synthemeTrio_incident _ _ s⟩ :
          {l : Line // Incident l (rootPlane r)}) = ⟨l,hl⟩ :=
        (residueEquiv (rootPlane r) (labels r)).injective (residueSyntheme_synthemeTrio _ _ s)
      exact congrArg Subtype.val he' 
    exact he ▸ root_near r s hs
end Theory.GroupTheory.Recognition.JankoFour.SourceCycleBase.Native.PlaneOrbit
