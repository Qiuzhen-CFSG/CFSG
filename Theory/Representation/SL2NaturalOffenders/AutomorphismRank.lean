module
public import Theory.Representation.SL2NaturalOffenders.Semilinear
public import Theory.SpecificGroups.PSL2.BinaryAutomorphismRank
public import Theory.GroupTheory.PrimeRankElementary
public import Theory.ElementaryAbelian.Quotient

/-!
# The two-rank of a faithful extension of natural SL₂

An involution centralizing the natural matrix subgroup is scalar. In
characteristic two that scalar is one. Thus each elementary two-subgroup
embeds by conjugation in Aut(SL₂), whose checked binary rank bound applies.

Source: Aschbacher--Smith, 6.1.10(3), printed p.670, and G.9.3, p.356.
-/

public section
open Subgroup Theory.GroupTheory
namespace Representation.SL2NaturalOffenders
variable {F H : Type*} [Field F] [Finite F] [CharP F 2]
  [Group H] [Finite H] [Algebra (ZMod 2) F]

omit [Finite H] [Finite F] in
theorem centralizing_square_one_eq_one
    (L : Subgroup H) (e : L ≃* Matrix.SpecialLinearGroup (Fin 2) F)
    (ρ : Representation (ZMod 2) H (Fin 2 → F))
    (hfaith : Function.Injective ρ)
    (hnat : ∀ (g : L) v, ρ (g : H) v = Matrix.mulVec (e g).val v)
    {x : H} (hx : x ^ 2 = 1) (hc : x ∈ centralizer (L : Set H)) : x = 1 := by
  obtain ⟨c,hc⟩ := centralizer_scalar (ρ x).toAddMonoidHom (by
    intro g v
    obtain ⟨l,rfl⟩ := e.surjective g
    change ρ x (Matrix.mulVec (e l).val v) = Matrix.mulVec (e l).val (ρ x v)
    rw [←hnat, ←hnat, ←Module.End.mul_apply, ←Module.End.mul_apply,
      ←map_mul, ←map_mul, hc l l.property])
  change ∀ v, ρ x v = c • v at hc
  have hh (v : Fin 2 → F) : c • (c • v) = v := by
    rw [←hc, ←hc, ←Module.End.mul_apply, ←map_mul, ←pow_two, hx, map_one]
    rfl
  have hc2 : c ^ 2 = 1 := by
    have ht := congrFun (hh ![1,0]) 0
    simpa only [Pi.smul_apply, smul_eq_mul, Matrix.cons_val_zero, mul_one, pow_two] using ht
  have hc1 : c = 1 := by
    have ht : (c - 1) ^ 2 = 0 := by
      rw [sub_sq, hc2, one_pow, CharTwo.two_eq_zero, zero_mul, zero_mul, sub_zero,
        CharTwo.add_self_eq_zero]
    exact sub_eq_zero.mp ((sq_eq_zero_iff.mp ht))
  apply hfaith
  apply LinearMap.ext
  intro v
  rw [hc,hc1,one_smul,map_one]
  rfl

theorem faithful_extension_rank_le
    (L : Subgroup H) [L.Normal]
    (e : L ≃* Matrix.SpecialLinearGroup (Fin 2) F)
    (ρ : Representation (ZMod 2) H (Fin 2 → F))
    (hfaith : Function.Injective ρ)
    (hnat : ∀ (g : L) v, ρ (g : H) v = Matrix.mulVec (e g).val v)
    {n : ℕ} (hn : 2 ≤ n) (hF : Nat.card F = 2 ^ n) :
    primeRank 2 H ≤ n := by
  have hr : primeRank 2 (MulAut L) ≤ n := by
    rw [primeRank_equiv 2 (MulAut.congr e)]
    exact Theory.PSL2.BinaryAutomorphismRank.sl2_automorphism_two_rank_le hn hF
  apply (primeRank_le_iff_elementary_card_le H).mpr
  intro A hA
  let := hA
  have hAL : A ≤ normalizer (L : Set H) := by
    rw [normalizer_eq_top]; exact le_top
  let a := L.normalizerMonoidHom.comp (inclusion hAL)
  have ha : Function.Injective a := by
    apply (MonoidHom.ker_eq_bot_iff a).mp
    apply le_bot_iff.mp
    intro x hx
    apply Subtype.ext
    apply centralizing_square_one_eq_one L e ρ hfaith hnat
      (elemPow_eq_one_of_isElementaryAbelian (x : H) x.property)
    change inclusion hAL x ∈ L.normalizerMonoidHom.ker at hx
    rw [normalizerMonoidHom_ker] at hx
    exact hx
  have he : IsElementaryAbelian 2 a.range :=
    IsElementaryAbelian.of_surjective a.rangeRestrict a.rangeRestrict_surjective
  exact (Nat.card_congr (MonoidHom.ofInjective ha).toEquiv).le.trans
    ((primeRank_le_iff_elementary_card_le (MulAut L)).mp hr a.range he)
end Representation.SL2NaturalOffenders
