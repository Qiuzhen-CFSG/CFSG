module
public import Theory.GroupTheory.ElementaryThompsonRelative

/-!
# Normalizers of a Thompson image through a kernel in the two-subgroup

If a surjection has kernel contained in R, the inverse image of J(R)'s
image is J(R) ker(q), an intermediate subgroup between J(R) and R. Its
Thompson subgroup is J(R) again. Thus normalizers lift exactly even though
J(R) need not contain the kernel.

Source application: Aschbacher–Smith C.2.7, displayed (*) on printed p.146.
-/

public section
open Subgroup
namespace Stellmacher
variable {G H : Type*} [Group G] [Finite G] [Group H]

theorem normalizer_comap_map_maxJ (R : Subgroup G) (q : G →* H)
    (hq : Function.Surjective q) (hker : q.ker ≤ R) :
    (normalizer ((elementaryAbelianMaxJ R).map q : Set H)).comap q =
      normalizer (elementaryAbelianMaxJ R : Set G) := by
  apply le_antisymm
  · rw [comap_normalizer_eq_of_surjective _ hq, comap_map_eq]
    have he : elementaryAbelianMaxJ (elementaryAbelianMaxJ R ⊔ q.ker) =
        elementaryAbelianMaxJ R :=
      elementaryAbelianMaxJ_eq_of_intermediate R _ le_sup_left
        (sup_le (sSup_le fun _ hA => hA.1) hker)
    simpa only [he] using
      normalizer_le_normalizer_elementaryAbelianMaxJ (elementaryAbelianMaxJ R ⊔ q.ker)
  · exact (map_le_iff_le_comap).mp ((elementaryAbelianMaxJ R).le_normalizer_map q)

theorem normalizer_map_maxJ (R : Subgroup G) (q : G →* H)
    (hq : Function.Surjective q) (hker : q.ker ≤ R) :
    (normalizer (elementaryAbelianMaxJ R : Set G)).map q =
      normalizer ((elementaryAbelianMaxJ R).map q : Set H) := by
  rw [←normalizer_comap_map_maxJ R q hq hker, map_comap_eq_self_of_surjective hq]

end Stellmacher

