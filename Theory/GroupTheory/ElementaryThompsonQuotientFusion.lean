module
public import Stellmacher.ElementaryAbelianMaxDefs
public import Theory.GroupTheory.CentralizerImageConjugation

/-!
# Returning conjugates of maximum elementary subgroups in a quotient

When the kernel of a quotient lies in S, a conjugate of the image of A
contained in the image of S lifts to an actual conjugate of A inside S.
If A has maximum elementary order in S, the lifted conjugate has that
same order and therefore lies in J(S). This retains the whole subgroup;
fusion of an individual involution would not suffice.

Source application: Aschbacher--Smith 6.1.4, printed p.666.
-/

public section
open Subgroup
namespace Stellmacher
variable {G H : Type*} [Group G] [Group H]

/-- A returning conjugate of the image of a maximum elementary subgroup
lies in the image of the original elementary Thompson subgroup. -/
theorem maxFamily_quotient_conjugate_le_maxJ
    (S : Subgroup G) (q : G →* H) (hq : Function.Surjective q)
    (hk : q.ker ≤ S) {A : Subgroup G}
    (hA : A ∈ elementaryAbelianMaxSubgroups S) (y : H)
    (hy : (A.map q).map (MulAut.conj y).toMonoidHom ≤ S.map q) :
    (A.map q).map (MulAut.conj y).toMonoidHom ≤
      (elementaryAbelianMaxJ S).map q := by
  obtain ⟨g,rfl⟩ := hq y
  rw [←Theory.GroupTheory.map_conjugate_image] at hy ⊢
  have hg : A.map (MulAut.conj g).toMonoidHom ≤ S := by
    have hle := map_le_iff_le_comap.mp hy
    rwa [comap_map_eq_self hk] at hle
  apply map_mono
  apply le_sSup
  refine ⟨hg,hA.2.1.map _,?_⟩
  intro B hBS hBe
  rw [card_map_of_injective (MulAut.conj g).injective]
  exact hA.2.2 B hBS hBe

end Stellmacher
