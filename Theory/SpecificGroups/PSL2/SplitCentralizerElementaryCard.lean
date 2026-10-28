module

public import Theory.SpecificGroups.PSL2.SplitCentralizerElementaryField
public import Theory.SpecificGroups.PSL2.LinearCentralizerSplitTorus
/-!
# The original elementary bound inside the full semilinear involution centralizer

The actual Sylow normality and two-core containment fix all squares of the
normal full torus. The field-coordinate obstruction and the reflected-torus
calculation place the elementary actor in that cyclic torus, giving order
at most two. No torus-fixer or actor-placement assumption is retained.
Source application: Aschbacher–Smith E.2.7, printed pp.218–219.
-/

public section
open Subgroup GorensteinWalter
open scoped MatrixGroups
namespace Theory.PSL2
/-- The literal full quadratic semilinear involution centralizer has no
noncyclic elementary subgroup normal in a Sylow and contained in its two-core. -/
theorem split_centralizer_elementary_card_le_two
    {F : Type*} [Field F] [Finite F] {p : ℕ} [Fact p.Prime]
    (ho : Odd p) (hF : Nat.card F = p ^ 2) (hp : 3 < p) :
    let C := centralizer ({(SemidirectProduct.inl (pGammaL2FullSplitTorus F (-1)) : PGammaL2 F)} : Set (PGammaL2 F))
    ∀ T : Sylow 2 C, ∀ V : Subgroup C, V ≤ pCore 2 C →
      (T : Subgroup C) ≤ normalizer (V : Set C) → (∀ v ∈ V, v ^ 2 = 1) →
      Nat.card V ≤ 2 := by
  intro C T V hV hVN hpow
  let i : Fˣ →* PGammaL2 F := (SemidirectProduct.inl : PGL2 F →* PGammaL2 F).comp (pGammaL2FullSplitTorus F)
  have hodd : IsOddPrimePower (Nat.card F) := ⟨p, 2, Fact.out, ho, by decide, hF⟩
  have hlarge : 9 < Nat.card F := by rw [hF]; nlinarith
  have hle : V.map C.subtype ≤ i.range := by
    rintro x ⟨v, hv, rfl⟩
    have hf := split_centralizer_elementary_field_eq_one ho hF hp T V hV hVN hpow v hv
    apply linear_centralizer_mem_split_torus_of_fourth_fixed hodd hlarge v.val hf
      (mem_centralizer_singleton_iff.mp v.property)
    intro a
    have hh := split_centralizer_elementary_commute_squares ho hF hp T V hV hVN hpow v hv a
    simpa only [← pow_mul] using hh.pow_right 2
  let : IsCyclic i.range := isCyclic_of_surjective i.rangeRestrict i.rangeRestrict_surjective
  let : IsCyclic (V.map C.subtype) := Subgroup.isCyclic_of_le hle
  let : IsCyclic V := (V.equivMapOfInjective C.subtype C.subtype_injective).isCyclic.mpr inferInstance
  have hd : Nat.card V ∣ 2 := by
    rw [← IsCyclic.exponent_eq_card]
    apply Monoid.exponent_dvd_of_forall_pow_eq_one
    intro v
    exact Subtype.ext (hpow v v.property)
  exact Nat.le_of_dvd (by decide : 0 < 2) hd
end Theory.PSL2
