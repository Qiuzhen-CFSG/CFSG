module
public import Theory.Mathieu.M12.SmallParabolicPair.SylowGeometry.TwoHexads
/-!
# Short-word certificate for the natural-four normalizer

The table lists words in the four quaternion generators and the moving cubic.
Every word belongs to the second parabolic. Two hexads suffice to place every
normalizer coordinate permutation in the table; equality and distinctness are
checked in the kernel. The table was obtained by breadth-first multiplication
of these five explicit permutations, and is independently verified below.
-/
@[expose] public section
namespace Sporadic.Mathieu.M12SmallPair.SylowEnumeration
set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000
noncomputable def localGenerator (i : Fin 5) : M12 :=
  ![leftI,leftJ,rightI,rightJ,movingActor] i

private theorem localGenerator_mem (i : Fin 5) : localGenerator i ∈ secondParabolic := by
  fin_cases i
  · apply core_le_secondParabolic
    exact (mem_core _).mpr ⟨.a 1,.a 0,by decide +kernel⟩
  · apply core_le_secondParabolic
    exact (mem_core _).mpr ⟨.xa 0,.a 0,by decide +kernel⟩
  · apply core_le_secondParabolic
    exact (mem_core _).mpr ⟨.a 0,.a 1,by decide +kernel⟩
  · apply core_le_secondParabolic
    exact (mem_core _).mpr ⟨.a 0,.xa 0,by decide +kernel⟩
  · exact movingActor_mem

noncomputable def localWord : List (Fin 5) → M12
  | [] => 1
  | i :: is => localGenerator i * localWord is

private theorem localWord_mem (w : List (Fin 5)) : localWord w ∈ secondParabolic := by
  induction w with
  | nil => exact secondParabolic.one_mem
  | cons i is ih => exact secondParabolic.mul_mem (localGenerator_mem i) ih

def wordTable : Array (List (Fin 5)) := #[
  [],
  [3,2,4,0,4],
  [2,0,0],
  [2,4,0,4,2],
  [2],
  [4,0,4,3],
  [0,0],
  [4,0,4,2],
  [2,4,0,4],
  [3,0,0],
  [4,3,2,4,0],
  [3],
  [4,0,4],
  [2,3],
  [4,0,4,0,0],
  [3,2],
  [4,4,2],
  [0,4,3],
  [2,3,1,4],
  [0,4,3,0,0],
  [4,4,0,0],
  [0,4,2],
  [4,4],
  [2,0,4,4],
  [0,4],
  [4,4,2,3],
  [0,4,0,0],
  [2,4,1],
  [3,2,4,0],
  [4,4,3],
  [0,4,3,2],
  [3,0,4,0],
  [3,1],
  [2,4,0,4,1],
  [3,2,1],
  [4,0,4,1],
  [2,3,1],
  [1,4,0,4],
  [3,1,0,0],
  [2,1,4,0,4],
  [4,2,3,4,0],
  [1],
  [4,2,1,4,0],
  [1,0,0],
  [4,0,4,3,1],
  [2,1,0,0],
  [1,4,0,4,3],
  [2,1],
  [4,3,1],
  [0,4,4,2,3],
  [4,2,3,1],
  [0,4,4],
  [3,1,4],
  [2,0,4,1],
  [4,3,2,1],
  [3,4,1,0],
  [0,4,4,3],
  [4,2,1],
  [0,4,4,2],
  [4,1,0,0],
  [3,4,3,1,0],
  [2,4,4,1],
  [3,4,2,1,0],
  [4,1],
  [4],
  [3,4,2,0],
  [4,2],
  [1,4,3,0],
  [4,0,0],
  [1,4,2,0],
  [2,4,4],
  [3,4,3,0],
  [3,4,0],
  [4,3,2],
  [2,0,4],
  [4,3],
  [1,4,0],
  [4,2,3],
  [2,0,4,0,0],
  [4,3,0,0],
  [2,4],
  [4,0,4,4],
  [2,4,0,0],
  [0,4,1],
  [4,3,1,4],
  [2,3,4,3,0],
  [2,4,2],
  [3,2,4,1,0],
  [0,4,3,1],
  [2,4,3],
  [3,0,1,4],
  [4,4,2,1],
  [2,1,4,0],
  [2,4,2,3],
  [2,3,4,0],
  [4,4,1],
  [2,4,2,0],
  [3,2,4],
  [3,0,4,1],
  [1,4,4,2],
  [2,4,0],
  [4,1,4],
  [2,4,0,0,0],
  [0,4,0],
  [0,4,2,0],
  [4,4,1,0],
  [2,3,4,1],
  [1,0,4],
  [0,4,3,0],
  [2,4,3,0],
  [1,4,4],
  [4,4,2,1,0],
  [2,0],
  [0,4,0,4,3],
  [0],
  [4,2,1,4],
  [0,0,0],
  [4,2,3,4],
  [2,0,0,0],
  [4,1,4,4,1],
  [0,4,0,4],
  [2,3,0],
  [4,0,4,1,0],
  [3,2,0],
  [4,2,3,4,3],
  [3,0],
  [4,3,2,4,1],
  [3,0,0,0],
  [1,0,4,1],
  [2,3,4],
  [4,4,0],
  [2,1,4],
  [2,3,1,4,0],
  [1,4,4,1],
  [4,4,2,0],
  [3,4,4,3],
  [2,3,4,3],
  [3,0,4],
  [3,2,4,1],
  [0,1,4],
  [0,4,1,0],
  [2,4,1,0],
  [3,4,4],
  [2,4,0,1],
  [3,2,1,0],
  [4,0,4,0],
  [3,0,1],
  [4,1,4,4,2],
  [3,1,0],
  [4,3,2,4],
  [2,3,1,0],
  [4,4,1,4],
  [4,1,4,4],
  [2,1,0],
  [4,0,4,3,0],
  [2,0,1],
  [4,0,4,2,0],
  [1,0],
  [4,2,3,4,1],
  [0,1],
  [4,2,0],
  [3,4,3,1],
  [4,0,0,0],
  [3,4,2,1],
  [2,4,4,0],
  [1,4,3,1],
  [4,0],
  [1,4,2,1],
  [2,0,4,1,0],
  [1,0,4,4],
  [1,4,1],
  [4,3,2,0],
  [2,3,4,4],
  [4,3,0],
  [3,4,1],
  [4,2,3,0],
  [4,3,2,1,0],
  [3,4],
  [4,3,1,0],
  [3,4,3,2],
  [4,2,3,1,0],
  [1,4],
  [3,1,4,0],
  [2,0,4,0],
  [1,4,2],
  [4,0,1],
  [3,4,3],
  [4,2,0,1],
  [3,4,2],
  [4,1,0],
  [1,4,3],
  [4,2,1,0]
]

theorem wordTable_size : wordTable.size = 192 := by decide +kernel
noncomputable def wordElement (i : Fin 192) : M12 :=
  localWord (wordTable[i.val]'(by rw [wordTable_size]; exact i.isLt))
theorem wordElement_mem (i : Fin 192) : wordElement i ∈ secondParabolic := localWord_mem _

noncomputable def wordCarrier : Finset (Equiv.Perm (Fin 12)) :=
  Finset.univ.image (fun i : Fin 192 => (wordElement i).val)

end Sporadic.Mathieu.M12SmallPair.SylowEnumeration
