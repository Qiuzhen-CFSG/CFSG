module

public import Theory.AtlasPort.LinearGroups.G2.EvenLocal.NormalizerCover
public import Theory.AtlasPort.LinearGroups.G2.PerfectSubgroups

/-!
# Perfect subgroups in even-field G₂ two-local normalizers

The normalizer of a nonidentity two-subgroup is conjugate into one of the two
root parabolics. A perfect subgroup of either parabolic has odd-prime rank at
most one. Consequently a faithfully embedded perfect group of odd-prime rank
at least two cannot normalize a nonidentity two-subgroup.

This is the local obstruction used for the actual central-quotient image in
Aschbacher--Smith C.3.5, printed p.150. The two-subgroup need not be radical or
contain a Sylow subgroup. The field-size assumption is the one required by the
proved parabolic residual calculation.
-/

public section

open Subgroup Theory.GroupTheory
namespace Atlas.G2.PerfectSubgroups
variable {F : Type*} [Field F] [Finite F] [CharP F 2]

/-- A faithful perfect group of odd-prime rank at least two cannot normalize
a nonidentity two-subgroup of the actual even-field G₂ model. -/
theorem no_perfect_odd_rank_two_in_two_normalizer
    (P : Subgroup (Model F)) (hp : IsPGroup 2 P) (hne : P ≠ ⊥)
    {A : Type*} [Group A] [Finite A] [Group.IsPerfect A]
    {p : ℕ} [Fact p.Prime] (ho : Odd p) (hr : 2 ≤ primeRank p A)
    (hq : 2 < Nat.card F) (f : A →* Model F) (hf : Function.Injective f)
    (hn : f.range ≤ normalizer (P : Set (Model F))) : False := by
  obtain ⟨g,hg⟩ := EvenLocal.NormalizerCover.normalizer_conjugate_le_parabolic
    P hne hp
  let j := (MulAut.conj g).toMonoidHom.comp f
  have hj : j.range ≤ (normalizer (P : Set (Model F))).map
      (MulAut.conj g).toMonoidHom := by
    rw [MonoidHom.range_comp]
    exact map_mono hn
  exact no_perfect_odd_rank_two_in_parabolic ho hr hq j
    ((MulAut.conj g).injective.comp hf) (hg.imp hj.trans hj.trans)

/-- Every perfect subgroup in the literal two-local normalizer has odd-prime
rank at most one. -/
theorem perfect_subgroup_two_normalizer_odd_rank_le_one
    (P : Subgroup (Model F)) (hp : IsPGroup 2 P) (hne : P ≠ ⊥)
    (hq : 2 < Nat.card F) (A : Subgroup (Model F)) [Group.IsPerfect A]
    (hn : A ≤ normalizer (P : Set (Model F)))
    {p : ℕ} [Fact p.Prime] (ho : Odd p) : primeRank p A ≤ 1 := by
  by_contra! hb
  apply no_perfect_odd_rank_two_in_two_normalizer P hp hne ho (by omega) hq
    A.subtype A.subtype_injective
  simpa only [range_subtype] using hn

end Atlas.G2.PerfectSubgroups
