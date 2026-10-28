module
public import Theory.Representation.MathieuCodeRestriction.NormalizedShadowRows.M22CodeFourSpace
public import Theory.GroupTheory.PerfectCentralCoverLocalResidual
public import Theory.GroupTheory.PrimeRankSquareFree

/-!
# Removing the odd covering kernel on the quintet residual

The quintet has order 3840, so its odd-prime ranks are at most one.
An actual perfect subgroup in a central cover with trivial two-core
therefore injects into its quintet image by odd-rank transfer. A preceding
map with a two-group kernel retains exactly such a kernel on this subgroup.
The Chapter 12 application uses the original L/O₂(L) covering map and
its relative normalizer's solvable residual; no full covering center is
silently removed.

Source: Aschbacher--Smith 8.2.6(3), H.16.3(4), and I.1.2, printed
pp.717,403,407, refs/quasithin.pdf. The quintet calculations come from
the existing licensed ATLAS ports; see LICENSES/ATLAS.txt.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open Sporadic.Mathieu MathieuCode
namespace MathieuCode.NormalizedShadowRows.M22CodeFourSpace
open M22Quintet

private theorem quintet_card : Nat.card Q = 3840 := by
  have hk : Nat.card (pCore 2 Q) = 32 :=
    (card_map_of_injective Q.subtype_injective).symm.trans M22ChapterH.Quintet.core_card
  have hq : Nat.card (Q ⧸ pCore 2 Q) = 120 :=
    (Nat.card_congr M22ChapterH.Quintet.quotientEquiv.toEquiv).trans (by simp [Nat.card_eq_fintype_card,Fintype.card_perm,Nat.factorial])
  rw [card_eq_card_quotient_mul_card_subgroup (pCore 2 Q),hq,hk]

private theorem quintet_odd_rank (p : ℕ) (hp : p.Prime) (ho : Odd p) : primeRank p Q ≤ 1 := by
  let : Fact p.Prime := ⟨hp⟩
  apply primeRank_le_one_of_square_not_dvd
  rw [quintet_card]
  intro hs
  have hd : p ∣ 3840 := (dvd_pow_self p (by decide : 2 ≠ 0)).trans hs
  have hfac : 3840 = 2^8*3*5 := by decide
  rw [hfac,hp.dvd_mul,hp.dvd_mul] at hd
  rcases hd with (h2 | h3) | h5
  · have he : p = 2 := (Nat.dvd_prime Nat.prime_two).mp (hp.dvd_of_dvd_pow h2) |>.resolve_left hp.ne_one
    subst p
    exact ho.not_two_dvd_nat (dvd_refl 2)
  · have he : p = 3 := (Nat.dvd_prime Nat.prime_three).mp h3 |>.resolve_left hp.ne_one
    subst p
    norm_num at hs
  · have he : p = 5 := (Nat.dvd_prime (by decide : Nat.Prime 5)).mp h5 |>.resolve_left hp.ne_one
    subst p
    norm_num at hs

/-- A perfect subgroup mapping into the quintet has no residual odd covering kernel. -/
theorem quintet_perfect_kernel_isTwo
    {X Y : Type*} [Group X] [Finite X] [Group.IsPerfect X] [Group Y] [Finite Y]
    (c : PerfectCentralCovering.Cover Y M22) (hY : pCore 2 Y = ⊥)
    (q : X →* Y) (hq : IsPGroup 2 q.ker)
    (t : MathieuCode.m22PairStabilizer)
    (hQ : ∀ x, t*m22ToPairStabilizer (c.toMonoidHom (q x))*t⁻¹ ∈ Q) :
    IsPGroup 2 ((m22ToPairStabilizer.comp c.toMonoidHom).comp q).ker := by
  let P := q.range
  let : Group.IsPerfect P := Group.IsPerfect.ofSurjective q.rangeRestrict_surjective
  let j := m22ToPairStabilizer
  have hj : Function.Injective j := by
    intro x y h
    exact m22Embedding_injective (congrArg Subtype.val h)
  have hr (p : ℕ) (hp : p.Prime) (ho : Odd p) :
      primeRank p (P.map c.toMonoidHom) ≤ 1 := by
    let f : (P.map c.toMonoidHom) →* Q :=
      (((MulAut.conj t).toMonoidHom.comp j).comp (P.map c.toMonoidHom).subtype).codRestrict Q (by
        rintro ⟨a,b,hb,rfl⟩
        obtain ⟨x,rfl⟩ := hb
        exact hQ x)
    have hf : Function.Injective f := by
      intro x y h
      apply Subtype.ext
      apply hj
      apply (MulAut.conj t).injective
      exact congrArg Subtype.val h
    exact (Theory.GroupTheory.primeRank_le_of_injective p f hf).trans (quintet_odd_rank p hp ho)
  have hinj := c.injective_on_perfect_subgroup hY P hr
  have hk : ((m22ToPairStabilizer.comp c.toMonoidHom).comp q).ker = q.ker := by
    ext x
    change j (c.toMonoidHom (q x)) = 1 ↔ q x = 1
    rw [←j.map_one,hj.eq_iff]
    constructor
    · intro hx
      have hh : c.toMonoidHom.subgroupMap P (q.rangeRestrict x) =
          c.toMonoidHom.subgroupMap P 1 := Subtype.ext (hx.trans c.toMonoidHom.map_one.symm)
      exact congrArg Subtype.val (hinj hh)
    · intro hx
      rw [hx,map_one]
  exact hk.symm ▸ hq

end MathieuCode.NormalizedShadowRows.M22CodeFourSpace
