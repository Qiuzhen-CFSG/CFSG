module

public import CFSG.Quasithin.MainConverse.SporadicLocal.Ru.ThreeSubgroup.Generators

/-!
# Complete enumeration of a nonabelian Rudvalis three-subgroup

The 27 word representatives contain the identity and admit right transitions
by both generators. The transitions have inverse index maps, so closure under
inverse generators will follow by cancellation. A single point separates the
27 representatives. A point also distinguishes the products `x * y` and `y * x`.
Every permutation equality is checked on all 4060 letters by kernel reduction.

Source: ATLAS `RuG1-p4060B0`; GLS3, Table 5.3r, p.279 (3A row).
The untrusted generation procedure and action convention are in `source/`.
-/

namespace CFSG.Quasithin.MainConverse.SporadicLocal.RuRank.ThreeCertificate
open Rudvalis Theory.GroupTheory

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

@[expose] public def generators : Fin 2 → Model := ![x, y]
@[expose] public def P : Subgroup Model := Subgroup.closure (Set.range generators)
@[expose] public def signedGen : Fin 4 → Model := ![x, y, x⁻¹, y⁻¹]
@[expose] public def nfWords : Fin 27 → List (Fin 4) := ![[], [0], [1], [2], [3], [0, 1], [0, 3], [1, 0], [1, 2], [2, 1], [2, 3], [3, 0], [3, 2], [0, 1, 0], [0, 1, 2], [0, 3, 0], [0, 3, 2], [1, 0, 1], [1, 0, 3], [1, 2, 3], [2, 1, 0], [2, 1, 2], [2, 3, 0], [3, 0, 1], [3, 2, 1], [0, 1, 2, 3], [0, 3, 2, 1]]
@[expose] public def reps (i : Fin 27) : Model := evalWord signedGen (nfWords i)
@[expose] public def next : Fin 27 → Fin 2 → Fin 27 := ![![1, 2], ![3, 5], ![7, 4], ![0, 9], ![11, 0], ![13, 6], ![15, 1], ![8, 17], ![2, 15], ![20, 10], ![22, 3], ![12, 23], ![4, 24], ![14, 12], ![5, 22], ![16, 19], ![6, 26], ![10, 18], ![24, 7], ![25, 8], ![21, 16], ![9, 11], ![17, 25], ![19, 21], ![26, 13], ![23, 14], ![18, 20]]
@[expose] public def prev : Fin 27 → Fin 2 → Fin 27 := ![![3, 4], ![0, 6], ![8, 0], ![1, 10], ![12, 2], ![14, 1], ![16, 5], ![2, 18], ![7, 19], ![21, 3], ![17, 9], ![4, 21], ![11, 13], ![5, 24], ![13, 25], ![6, 8], ![15, 20], ![22, 7], ![26, 17], ![23, 15], ![9, 26], ![20, 23], ![10, 14], ![25, 11], ![18, 12], ![19, 22], ![24, 16]]

public theorem transitions (i : Fin 27) (j : Fin 2) :
    reps i * generators j = reps (next i j) := by
  fin_cases i <;> fin_cases j <;>
    apply Subtype.ext <;> apply Equiv.ext <;> apply Data.allFin <;> decide +kernel

public theorem index_inverse : ∀ i j, next (prev i j) j = i := by decide +kernel

@[expose] public def basePoint : Fin 4060 := 1
@[expose] public def point : Fin 27 → Fin 4060 := ![1, 1924, 2717, 614, 2687, 1717, 2264, 2583, 2008, 2937, 3511, 3390, 3080, 1531, 2041, 895, 679, 1902, 107, 2743, 2692, 3289, 2897, 2227, 397, 3386, 803]

public theorem reps_point : ∀ i, (modelSubgroup.subtype (reps i)) basePoint = point i := by
  apply OrderCertificate.allFin
  decide +kernel

public theorem point_injective : Function.Injective point := by decide +kernel

@[expose] public def noncommutePoint : Fin 4060 := 1

public theorem noncommute : x * y ≠ y * x := by
  intro h
  have hn : xMap (yMap noncommutePoint) ≠ yMap (xMap noncommutePoint) := by
    decide +kernel
  exact hn (congrArg (fun g : Model => (modelSubgroup.subtype g) noncommutePoint) h)

end CFSG.Quasithin.MainConverse.SporadicLocal.RuRank.ThreeCertificate
