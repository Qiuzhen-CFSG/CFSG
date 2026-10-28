module

public import Theory.Representation.SymplecticConjugatePair.Ambient.Normalizer.Coordinates

/-!
# Reduction of summand permutation to the derived commutant

If the binary commutant of the actual derived pair consists of the independent
coefficient scalars, its only nontrivial idempotents are the two coordinate
projections. Normalizer conjugation permutes them. This proves permutation of
the marked summands, with the literal commutant computation still an explicit
premise. The same premise gives the scalar commutant of the natural module.

The graph swap squares to Frobenius; the argument uses its actual inverse
rather than treating it as an involution.

Source: the paired normalizer used in Aschbacher–Smith H.7, printed pp.388–389,
and the paired setup on printed p.696 of `refs/quasithin.pdf`.
-/

@[expose] public section
open Representation BinaryOffender Theory.SpecificGroups.SymplecticFour
open Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms
open Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms.ExceptionalGraph
namespace SymplecticConjugatePair.Ambient.Normalizer
variable {F : Type*} [Field F] [Algebra (ZMod 2) F] [Finite F] [CharP F 2]

variable (hcomm : ∀ q : Space F →ₗ[ZMod 2] Space F,
  (∀ (x : commutator (Sp F)) v, q (derivedPair graphAut x v) = derivedPair graphAut x (q v)) →
  ∃ a b : F, q = blockScalar a b)

include hcomm in
lemma natural_commutant_of_pair (q : Vector F →ₗ[ZMod 2] Vector F)
    (hq : ∀ (x : commutator (Sp F)) v,
      q (naturalDerivedAction x v) = naturalDerivedAction x (q v)) :
    ∃ a : F, ∀ v, q v = a • v := by
  obtain ⟨a, b, he⟩ := hcomm (q.prodMap 0) (by
    intro x v
    apply Prod.ext
    · exact hq x v.1
    · change 0 = symplecticNatural 2 (graphAut x.val) 0
      exact (map_zero _).symm)
  exact ⟨a, fun v => congrArg Prod.fst (LinearMap.congr_fun he (v, 0))⟩

include hcomm in
lemma commutant_idempotents (q : Space F →ₗ[ZMod 2] Space F)
    (hq : ∀ (x : commutator (Sp F)) v,
      q (derivedPair graphAut x v) = derivedPair graphAut x (q v))
    (hi : q * q = q) :
    q = 0 ∨ q = 1 ∨ q = blockScalar 1 0 ∨ q = blockScalar 0 1 := by
  obtain ⟨a, b, rfl⟩ := hcomm q hq
  have ha : a^2 = a := by
    have h := congrArg (fun z : Space F => z.1 (Sum.inl 0))
      (LinearMap.congr_fun hi ((Pi.single (Sum.inl 0) 1 : Vector F), 0))
    simpa [Module.End.mul_apply, sq] using h
  have hb : b^2 = b := by
    have h := congrArg (fun z : Space F => z.2 (Sum.inl 0))
      (LinearMap.congr_fun hi (0, (Pi.single (Sum.inl 0) 1 : Vector F)))
    simpa [Module.End.mul_apply, sq] using h
  rcases eq_zero_or_one_of_sq_eq_self ha with rfl | rfl <;>
    rcases eq_zero_or_one_of_sq_eq_self hb with rfl | rfl
  · exact Or.inl (by apply LinearMap.ext; intro v; simp)
  · exact Or.inr (Or.inr (Or.inr rfl))
  · exact Or.inr (Or.inr (Or.inl rfl))
  · exact Or.inr (Or.inl (by apply LinearMap.ext; intro v; simp))

lemma normalizer_conj_commutes
    (f : Space F ≃ₗ[ZMod 2] Space F) (hf : f ∈ pairedNormalizer graphAut)
    (q : Space F →ₗ[ZMod 2] Space F)
    (hq : ∀ (x : commutator (Sp F)) v,
      q (derivedPair graphAut x v) = derivedPair graphAut x (q v)) :
    ∀ (x : commutator (Sp F)) v,
      f.conjRingEquiv q (derivedPair graphAut x v) =
      derivedPair graphAut x (f.conjRingEquiv q v) := by
  intro x v
  obtain ⟨y, hy⟩ := normalizer_intertwines graphAut f.symm
    ((pairedNormalizer graphAut).inv_mem hf) x
  have he (w : Space F) : f (derivedPair graphAut y w) = derivedPair graphAut x (f w) := by
    apply f.symm.injective
    rw [LinearEquiv.symm_apply_apply, hy, LinearEquiv.symm_apply_apply]
  change f (q (f.symm (derivedPair graphAut x v))) =
    derivedPair graphAut x (f (q (f.symm v)))
  rw [hy, hq, he]

include hcomm in
lemma normalizer_summand_dichotomy (f : Space F ≃ₗ[ZMod 2] Space F)
    (hf : f ∈ pairedNormalizer graphAut) :
    PreservesCoordinates f ∨ PreservesCoordinates (f * graphSwap) := by
  let p := blockScalar (1 : F) 0
  have hp : p * p = p := by apply LinearMap.ext; intro v; simp [p, Module.End.mul_apply]
  have hp0 : p ≠ 0 := by
    intro h
    have he := congrArg (fun v : Space F => v.1 (Sum.inl 0))
      (LinearMap.congr_fun h ((Pi.single (Sum.inl 0) 1 : Vector F), 0))
    simp [p] at he
  have hp1 : p ≠ 1 := by
    intro h
    have he := congrArg (fun v : Space F => v.2 (Sum.inl 0))
      (LinearMap.congr_fun h (0, (Pi.single (Sum.inl 0) 1 : Vector F)))
    simp [p] at he
  have hc := commutant_idempotents hcomm (f.conjRingEquiv p)
    (normalizer_conj_commutes f hf p (blockScalar_commutes graphAut 1 0))
    (by rw [← map_mul, hp])
  have hc0 : f.conjRingEquiv p ≠ 0 := by
    intro h
    exact hp0 (f.conjRingEquiv.injective (h.trans (map_zero f.conjRingEquiv).symm))
  have hc1 : f.conjRingEquiv p ≠ 1 := by
    intro h
    exact hp1 (f.conjRingEquiv.injective (h.trans (map_one f.conjRingEquiv).symm))
  rcases hc.resolve_left hc0 |>.resolve_left hc1 with h | h
  · left
    have he (v : Space F) : f (v.1, 0) = ((f v).1, 0) := by
      have hh := LinearMap.congr_fun h (f v)
      change f (p (f.symm (f v))) = blockScalar 1 0 (f v) at hh
      simpa [p] using hh
    constructor
    · intro w
      exact congrArg Prod.snd (he (w, 0))
    · intro w
      have hh := congrArg Prod.fst (he (0, w))
      simpa only [← Prod.zero_eq_mk, map_zero, Prod.fst_zero] using hh.symm
  · right
    have he (v : Space F) : f (v.1, 0) = (0, (f v).2) := by
      have hh := LinearMap.congr_fun h (f v)
      change f (p (f.symm (f v))) = blockScalar 0 1 (f v) at hh
      simpa [p] using hh
    constructor
    · intro w
      change (f (0, fieldVector (frobeniusEquiv F 2) w)).2 = 0
      have hh := congrArg Prod.snd (he (0, fieldVector (frobeniusEquiv F 2) w))
      simpa only [← Prod.zero_eq_mk, map_zero, Prod.snd_zero] using hh.symm
    · intro w
      change (f (w, fieldVector (frobeniusEquiv F 2) 0)).1 = 0
      rw [map_zero]
      exact congrArg Prod.fst (he (w, 0))

lemma swaps_of_preserves_mul_graphSwap (f : Space F ≃ₗ[ZMod 2] Space F)
    (hf : f ∈ pairedNormalizer graphAut) (hp : PreservesCoordinates (f * graphSwap)) :
    SwapsSummands (normalizerAction graphAut) ⟨f, hf⟩ := by
  constructor
  · rintro _ ⟨v, rfl⟩
    apply (mem_secondSummand _).mpr
    change (f (v, 0)).1 = 0
    have h := hp.2 v
    change (f (v, fieldVector (frobeniusEquiv F 2) 0)).1 = 0 at h
    simpa only [map_zero] using h
  · rintro _ ⟨v, rfl⟩
    apply (mem_firstSummand _).mpr
    change (f (0, v)).2 = 0
    have h := hp.1 ((fieldVector (frobeniusEquiv F 2)).symm v)
    change (f (0, fieldVector (frobeniusEquiv F 2)
      ((fieldVector (frobeniusEquiv F 2)).symm v))).2 = 0 at h
    simpa only [LinearEquiv.apply_symm_apply] using h

include hcomm in
lemma permutesSummands_of_commutant :
    PermutesSummands (normalizerAction (graphAut (F := F))) := by
  intro f
  rcases normalizer_summand_dichotomy hcomm f.val f.property with hp | hp
  · exact Or.inl ((preservesCoordinates_iff graphAut f).mp hp)
  · exact Or.inr (swaps_of_preserves_mul_graphSwap f.val f.property hp)

end SymplecticConjugatePair.Ambient.Normalizer
