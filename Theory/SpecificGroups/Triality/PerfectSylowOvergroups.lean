module

public import Theory.SpecificGroups.Triality.PerfectTwoNormalizer
public import Theory.SpecificGroups.Triality.OddSupplement

/-!
# Perfect odd-rank-two subgroups and full Sylow overgroups in triality

Conjugate the full Sylow to the positive subgroup of the genuine graph-field
D₄ carrier. Every proper overgroup lies in a root parabolic, where a perfect
subgroup has odd-prime rank at most one. Thus a full Sylow overgroup containing
a perfect subgroup of odd-prime rank two is the whole carrier. This includes
the field of order two.

Source: Aschbacher–Smith A.3.12, printed pp.47–48; the root-parabolic
construction is from GLS3 §§2.3–2.6.
-/

public section
open Subgroup Theory.GroupTheory
namespace Triality.Standard.PerfectSylowOvergroups
open Parabolics

/-- The genuine binary triality carrier has no proper full-Sylow overgroup
containing a faithful perfect subgroup of odd-prime rank at least two. -/
theorem eq_top_of_perfect_odd_rank_two
    (n : ℕ) (hn : 0 < n)
    (S : Sylow 2 (BinaryCarrier n hn)) (D : Subgroup (BinaryCarrier n hn))
    (hSD : (S : Subgroup _) ≤ D)
    {A : Type*} [Group A] [Finite A] [Group.IsPerfect A]
    (f : A →* BinaryCarrier n hn) (hf : Function.Injective f) (hAD : f.range ≤ D)
    {p : ℕ} [Fact p.Prime] (ho : Odd p) (hr : 2 ≤ primeRank p A) : D = ⊤ := by
  by_contra hD
  let P := binaryParameters n hn
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq (Carrier P) S (unipotentSylow P rfl)
  let c := MulAut.conj g
  have hS : (S : Subgroup (Carrier P)).map c.toMonoidHom = unipotent P :=
    congrArg Sylow.toSubgroup hg
  have hDc : D.map c.toMonoidHom ≠ ⊤ := by
    intro he
    apply hD
    apply map_injective (f := c.toMonoidHom) c.injective
    rw [he,map_top_of_surjective _ c.surjective]
  obtain ⟨a,ha⟩ := OddSupplement.le_parabolic n hn (D.map c.toMonoidHom)
    (hS ▸ map_mono hSD) hDc
  have him : (c.toMonoidHom.comp f).range ≤ D.map c.toMonoidHom := by
    rw [MonoidHom.range_comp]
    exact map_mono hAD
  have hb := PerfectTwoNormalizer.perfect_parabolic_embedding_odd_rank_le_one
    P rfl a (c.toMonoidHom.comp f) (c.injective.comp hf) (him.trans ha) ho
  omega

end Triality.Standard.PerfectSylowOvergroups
