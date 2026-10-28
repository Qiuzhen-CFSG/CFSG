module
public import Theory.GroupTheory.ElementaryThompsonRelative

/-!
# Lifting elementary Thompson normalizers through a contained kernel

If ker(q) lies in S, the full preimage of q(J(S)) lies between J(S) and S.
Thompson heredity recovers J(S) from that preimage. Consequently its full
normalizer is exactly the inverse image of the image normalizer.

Source: Aschbacher–Smith B.2.3(3), used in 5.1.13, printed pp.75,637.
-/

public section
open Subgroup Stellmacher
namespace Stellmacher
variable {G Q : Type*} [Group G] [Finite G] [Group Q]
/-- A kernel contained in S lets the original Thompson subgroup be recovered
from the full preimage of its image. -/
theorem normalizer_maxJ_eq_comap_of_ker_le (S : Subgroup G) (q : G →* Q)
    (hk : q.ker ≤ S) :
    normalizer (elementaryAbelianMaxJ S : Set G) =
      (normalizer ((elementaryAbelianMaxJ S).map q : Set Q)).comap q := by
  let J := elementaryAbelianMaxJ S
  let P := (J.map q).comap q
  have hJP : J ≤ P := le_comap_map q J
  have hPS : P ≤ S := by
    rw [show P = (J.map q).comap q from rfl,comap_map_eq]
    exact sup_le (sSup_le fun _ hA => hA.1) hk
  have he : elementaryAbelianMaxJ P = J := elementaryAbelianMaxJ_eq_of_intermediate S P hJP hPS
  apply le_antisymm
  · exact map_le_iff_le_comap.mp (J.le_normalizer_map q)
  · apply ((J.map q).le_normalizer_comap q).trans
    simpa only [he] using normalizer_le_normalizer_elementaryAbelianMaxJ P
end Stellmacher
