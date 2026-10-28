module

public import Theory.GroupTheory.PerfectCentralCoverAutomorphisms
public import Theory.GroupTheory.QuasithinBasic

/-!
# Automorphism ranks of perfect central covers

Descent through the whole center is faithful for a perfect group. Thus any
prime-rank bound for the automorphisms of its central quotient also holds
for the cover. This retains the actual covering map and does not identify
the two automorphism groups.

Source application: Aschbacher–Smith, 16.3.9, printed p.1180.
-/

public section

namespace PerfectCentralCovering
open Subgroup Theory.GroupTheory
variable {E B : Type*} [Group E] [Group B] [Finite E] [Finite B]

/-- Faithful descent bounds the prime rank of the covering automorphism group. -/
theorem Cover.automorphism_primeRank_le (f : Cover E B)
    (hk : f.toMonoidHom.ker = center E) (p : ℕ) :
    primeRank p (MulAut E) ≤ primeRank p (MulAut B) :=
  primeRank_le_of_injective p (f.autMap hk) (f.autMap_injective hk)

end PerfectCentralCovering

namespace Theory.GroupTheory
open Subgroup
variable {E : Type*} [Group E] [Finite E] [Group.IsPerfect E]

/-- Specialization to the canonical quotient by the whole center. -/
theorem automorphism_primeRank_le_quotient_center (p : ℕ) :
    primeRank p (MulAut E) ≤ primeRank p (MulAut (E ⧸ center E)) := by
  let f : PerfectCentralCovering.Cover E (E ⧸ center E) := {
    toMonoidHom := QuotientGroup.mk' (center E)
    surjective := QuotientGroup.mk'_surjective _
    isPerfect := inferInstance
    ker_le_center := (QuotientGroup.ker_mk' _).le }
  exact f.automorphism_primeRank_le (QuotientGroup.ker_mk' _) p

end Theory.GroupTheory
