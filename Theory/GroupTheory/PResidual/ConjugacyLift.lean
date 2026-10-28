module
public import Theory.GroupTheory.PResidual.MapInjectivity

/-!
# Lifting conjugacy of prime-perfect subgroups

A prime-group kernel normalizing two prime-perfect subgroups lets us lift
conjugacy of their images through the same chosen conjugating element.
The full preimage recovers each subgroup as its prime-residual. This is the
lifting step in Aschbacher--Smith 12.6.16(1), printed p.826.
-/

public section
open Subgroup
namespace Subgroup
variable {G D : Type*} [Group G] [Group D] {p : ℕ}

theorem conjugate_eq_of_map_conjugate_eq (f : G →* D) (A B : Subgroup G)
    (hA : IsPPerfect p A) (hB : IsPPerfect p B) (hk : IsPGroup p f.ker)
    (hnA : f.ker ≤ normalizer (A : Set G))
    (hnB : f.ker ≤ normalizer (B : Set G))
    (g : G) (he : (A.map f).map (MulAut.conj (f g)).toMonoidHom = B.map f) :
    A.map (MulAut.conj g).toMonoidHom = B := by
  let c := (MulAut.conj g).toMonoidHom
  have hkmap : f.ker.map c = f.ker :=
    (mem_normalizer_iff_map_conj_eq).mp (show g ∈ normalizer (f.ker : Set G) by
      rw [normalizer_eq_top]; trivial)
  have hn : f.ker ≤ normalizer (A.map c : Set G) := by
    rw [←hkmap]
    exact (map_mono hnA).trans (A.le_normalizer_map c)
  apply eq_of_map_eq_map_of_isPPerfect f
    (hA.of_surjective (A.equivMapOfInjective c (MulAut.conj g).injective).toMonoidHom
      (A.equivMapOfInjective c (MulAut.conj g).injective).surjective) hB hk hn hnB
  rw [map_map] at he ⊢
  have hh : f.comp c = (MulAut.conj (f g)).toMonoidHom.comp f := by
    ext x
    simp [c,MulAut.conj_apply]
  rw [hh]
  exact he

end Subgroup
