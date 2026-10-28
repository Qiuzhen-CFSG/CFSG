module

public import Theory.GroupTheory.AutomorphismTowerSimple
public import Mathlib.GroupTheory.PGroup

/-!
# Prime-power centralizers of inner automorphisms

For a centerless group with p-group outer automorphism group, the full
automorphism centralizer of an inner automorphism is a p-group whenever
the conjugating element has a p-group centralizer. A p-power of each
automorphism is inner; injectivity of conjugation places its conjugator
in the given element centralizer, where another p-power kills it.

Source application: Aschbacher--Smith, 15.1.20(3), printed p.1097,
the inner-involution centralizer in Aut(PSL₃(2)).
-/

public section
open Subgroup
namespace MulAut

/-- A p-group outer quotient and element centralizer control the full
centralizer of the corresponding inner automorphism. -/
theorem isPGroup_centralizer_conj_of_outer
    {H : Type*} [Group H] {p : ℕ} [Fact p.Prime]
    (hz : center H = ⊥) (ho : IsPGroup p (Outer H))
    (t : H) (ht : IsPGroup p (centralizer ({t} : Set H))) :
    IsPGroup p (centralizer ({conj t} : Set (MulAut H))) := by
  intro a
  obtain ⟨n,hn⟩ := ho (QuotientGroup.mk' (innerSubgroup H) a.val)
  rw [←map_pow] at hn
  obtain ⟨g,hg⟩ := (QuotientGroup.eq_one_iff _).mp hn
  have hgc : g ∈ centralizer ({t} : Set H) := by
    apply mem_centralizer_singleton_iff.mpr
    apply conj_injective_of_center_eq_bot hz
    rw [map_mul,map_mul]
    exact hg ▸ mem_centralizer_singleton_iff.mp (a ^ (p^n)).property
  obtain ⟨m,hm⟩ := ht ⟨g,hgc⟩
  have hm' : g ^ (p^m) = 1 := congrArg Subtype.val hm
  refine ⟨n+m,?_⟩
  apply Subtype.ext
  change a.val ^ (p^(n+m)) = 1
  rw [Nat.pow_add,pow_mul,←hg,←map_pow,hm',map_one]

end MulAut
