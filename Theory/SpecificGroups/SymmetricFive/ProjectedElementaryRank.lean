module
public import Theory.SpecificGroups.SymmetricFive.WreathElementaryRank
public import Theory.ElementaryAbelian.PrimeRankCard
public import Theory.ElementaryAbelian.Quotient

/-!
# Projected elementary actors on two alternating-five factors

Each projection to S₅ has two-rank at most two. A faithful pair of projections
bounds the actor's rank by the sum of the image ranks. A nonzero image supplies
a nonidentity permutation; a rank-two image meets A₅ nontrivially because the
sign quotient has order two. The witnesses remain elements of the original
actor. An actor exchanging the two factors has rank at most three by the
existing wreath centralizer calculation.

These are the elementary group inputs for the separated homogeneous blocks
in Aschbacher–Smith D.3.9 and D.3.21, pp.199–201 and 204–207.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace Theory.SpecificGroups.SymmetricFive.ProjectedElementaryRank
abbrev Sym := Equiv.Perm (Fin 5)
abbrev Alt := alternatingGroup (Fin 5)
variable {A : Type*} [Group A] [Finite A]

open WreathTwoElementaryRank in
/-- The literal ordered pair of projections of a block-preserving wreath actor. -/
@[expose] def preservedPairHom (f : A →* W Sym) (hb : ∀ a, (f a).right = 1) :
    A →* Sym × Sym :=
  baseEquiv.symm.toMonoidHom.comp (f.codRestrict (base Sym) hb)

open WreathTwoElementaryRank in
omit [Finite A] in
theorem preservedPairHom_injective (f : A →* W Sym)
    (hf : Function.Injective f) (hb : ∀ a, (f a).right = 1) :
    Function.Injective (preservedPairHom f hb) := by
  intro a b h
  apply hf
  have hh := baseEquiv.symm.injective h
  exact congrArg Subtype.val hh

open WreathTwoElementaryRank in
omit [Finite A] in
theorem preservedPairHom_apply (f : A →* W Sym) (hb : ∀ a, (f a).right = 1)
    (a : A) : preservedPairHom f hb a = ((f a).left 1, (f a).left turn) := by
  have hh := baseEquiv.apply_symm_apply ⟨f a, hb a⟩
  have hval := congrArg Subtype.val hh
  rw [baseEquiv_coe] at hval
  change baseHom (preservedPairHom f hb a) = f a at hval
  apply Prod.ext
  · simpa [baseHom] using
      congrArg (fun w : W Sym => w.left 1) hval
  · simpa only [baseHom, MonoidHom.coe_mk, OneHom.coe_mk, if_neg turn_ne_one] using
      congrArg (fun w : W Sym => w.left turn) hval

/-- The rank of a faithful actor is bounded by its two image ranks. -/
theorem rank_le_sum_ranges (f g : A →* Sym) (hf : Function.Injective (f.prod g)) :
    primeRank 2 A ≤ primeRank 2 f.range + primeRank 2 g.range := by
  let j := f.rangeRestrict.prod g.rangeRestrict
  have hj : Function.Injective j := by
    intro a b h
    apply hf
    exact Prod.ext (congrArg (fun x => (x.1 : Sym)) h)
      (congrArg (fun x => (x.2 : Sym)) h)
  have hh := primeRank_le_of_injective 2 j hj
  rwa [primeRank_prod_eq_add] at hh

omit [Finite A] in
theorem range_rank_le_two (f : A →* Sym) : primeRank 2 f.range ≤ 2 :=
  (primeRank_le_of_injective 2 f.range.subtype f.range.subtype_injective).trans
    Sporadic.Mathieu.M22ValueBound.SmallQuotients.symmetricFive_primeRank_le_two

variable [IsElementaryAbelian 2 A]

omit [Finite A] in
/-- Positive projected rank is witnessed by an actual element of the actor. -/
theorem exists_nontrivial_image (f : A →* Sym) (hr : 0 < primeRank 2 f.range) :
    ∃ a : A, f a ≠ 1 := by
  by_contra hn
  push Not at hn
  let : IsElementaryAbelian 2 f.range :=
    IsElementaryAbelian.of_surjective f.rangeRestrict f.rangeRestrict_surjective
  have hc : Nat.card f.range ≤ 1 := by
    have hsub : Subsingleton f.range := ⟨fun x y => by
      apply Subtype.ext
      obtain ⟨a, ha⟩ := x.property
      obtain ⟨b, hb⟩ := y.property
      rw [← ha, ← hb, hn a, hn b]⟩
    let := hsub
    exact (Nat.card_of_subsingleton (1 : f.range)).le
  have hh := IsElementaryAbelian.primeRank_le_of_card_le (p := 2) (n := 0) f.range hc
  omega

omit [Finite A] in
/-- Rank two forces a nonidentity even image without lifting a subgroup. -/
theorem exists_nontrivial_even_image (f : A →* Sym)
    (hr : 2 ≤ primeRank 2 f.range) :
    ∃ a : A, f a ≠ 1 ∧ f a ∈ Alt := by
  by_contra hn
  have hfaith : Function.Injective
      ((Equiv.Perm.sign : Sym →* ℤˣ).comp f.range.subtype) := by
    apply (injective_iff_map_eq_one _).mpr
    intro x hx
    obtain ⟨a, ha⟩ := x.property
    apply Subtype.ext
    by_contra hne
    refine hn ⟨a, ha ▸ hne, ?_⟩
    change Equiv.Perm.sign (f a) = 1
    rw [ha]
    exact hx
  have hc := Nat.card_le_card_of_injective _ hfaith
  have hu : Nat.card ℤˣ = 2 := by simp [Nat.card_eq_fintype_card]
  let : IsElementaryAbelian 2 f.range :=
    IsElementaryAbelian.of_surjective f.rangeRestrict f.rangeRestrict_surjective
  have hh := IsElementaryAbelian.primeRank_le_of_card_le (p := 2) (n := 1) f.range
    (by simpa only [pow_one, hu] using hc)
  omega

open WreathTwoElementaryRank in
/-- A faithful elementary actor which exchanges the blocks has rank at most three. -/
theorem rank_le_three_of_swapping (f : A →* W Sym) (hf : Function.Injective f)
    (hs : ∃ a : A, (f a).right ≠ 1) : primeRank 2 A ≤ 3 := by
  have he : IsElementaryAbelian 2 f.range :=
    IsElementaryAbelian.of_surjective f.rangeRestrict f.rangeRestrict_surjective
  have hb : ¬ f.range ≤ base Sym := by
    rintro h
    obtain ⟨a, ha⟩ := hs
    exact ha (h ⟨a, rfl⟩)
  have hc := elementary_card_le_of_not_le_base f.range he hb
    Sporadic.Mathieu.M22ValueBound.SmallQuotients.symmetricFive_primeRank_le_two
  have hcard : Nat.card A = Nat.card f.range :=
    Nat.card_congr (MonoidHom.ofInjective hf).toEquiv
  exact IsElementaryAbelian.primeRank_le_of_card_le (p := 2) (n := 3) A
    (hcard.symm ▸ hc)

end Theory.SpecificGroups.SymmetricFive.ProjectedElementaryRank
