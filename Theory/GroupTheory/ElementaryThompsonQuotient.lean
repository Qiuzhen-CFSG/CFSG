module
public import Theory.GroupTheory.ElementaryThompsonFrattini

/-!
# Thompson normalizers through a quotient with kernel in the Sylow subgroup

The inverse image of the image of J(T) lies between J(T) and T whenever
the kernel lies in T. Thompson heredity identifies its Thompson subgroup
with J(T), so the normalizer of the image lifts to the original normalizer.
This is the normalizer transport in the exceptional A₇ case of
Aschbacher–Smith C.1.23(2), printed pp.129–130.
-/

namespace Stellmacher
open Subgroup
variable {G H : Type*} [Group G] [Finite G] [Group H]

public theorem normalizer_maxJ_map_of_ker_le (T : Subgroup G) (q : G →* H) (hq : Function.Surjective q)
    (hk : q.ker ≤ T) :
    (normalizer (elementaryAbelianMaxJ T : Set G)).map q =
      normalizer ((elementaryAbelianMaxJ T).map q : Set H) := by
  apply le_antisymm ((elementaryAbelianMaxJ T).le_normalizer_map q)
  intro y hy
  obtain ⟨g, rfl⟩ := hq y
  refine ⟨g, ?_, rfl⟩
  let P := ((elementaryAbelianMaxJ T).map q).comap q
  have hJP : elementaryAbelianMaxJ T ≤ P := le_comap_map q _
  have hPT : P ≤ T := by
    rw [show P = ((elementaryAbelianMaxJ T).map q).comap q from rfl, comap_map_eq]
    exact sup_le (sSup_le fun _ hA => hA.1) hk
  have hJ : elementaryAbelianMaxJ P = elementaryAbelianMaxJ T :=
    elementaryAbelianMaxJ_eq_of_intermediate T P hJP hPT
  have hg : g ∈ normalizer (P : Set G) :=
    ((elementaryAbelianMaxJ T).map q).le_normalizer_comap q hy
  change g ∈ normalizer (elementaryAbelianMaxJ T : Set G)
  rw [mem_normalizer_iff_map_conj_eq] at hg ⊢
  change P.map (MulAut.conj g).toMonoidHom = P at hg
  change (elementaryAbelianMaxJ T).map (MulAut.conj g).toMonoidHom = _
  rw [← hJ, ← elementaryAbelianMaxJ_map_equiv, hg]

end Stellmacher
