module

public import Theory.Representation.SL3FourNaturalDual.QuadraticActors.NormalizerReduction.Centralizer
public import Theory.Representation.SL3FourNaturalDual.QuadraticActors.NormalizerReduction.Model

/-!
# The two summands of a binary SL₃(4) normalizer

The computed commutant has exactly two nontrivial idempotents, the coordinate
projections. Conjugation by an element normalizing the actual component image
permutes these projections. Thus every such element either preserves both
summands or becomes preserving after composition with the concrete graph swap.
The swap itself normalizes the component by inverse transpose.

For a preserving operator, both diagonal blocks are genuine invertible binary
maps. They implement the same conjugation on the natural and dual actions.
These results supply the coordinate reduction for the remaining field and
matrix calculations, without assuming an automorphism classification.

Source: Aschbacher--Smith, combined manuscript of 1 March 2004, proof of
13.8.20, printed p.955 (PDF p.972), natural-plus-dual SL₃(4) case.
-/

@[expose] public section
noncomputable section
namespace Representation.SL3FourNaturalDual.QuadraticActors.NormalizerReduction

/-- The two actual coordinate summands are individually invariant. -/
def PreservesSummands (f : BinaryGL) : Prop :=
  (∀ w : W, (f (w, 0)).2 = 0) ∧ (∀ w : W, (f (0, w)).1 = 0)

/-- Normalizer membership supplies an actual matrix intertwining every component element. -/
theorem normalizer_intertwines (f : BinaryGL) (hf : f ∈ normalizer) (g : SL) :
    ∃ h : SL, ∀ v : V, f (representation g v) = representation h (f v) := by
  have hm : f * linearAction g * f⁻¹ ∈ component :=
    (Subgroup.mem_normalizer_iff.mp hf (linearAction g)).mp ⟨g, rfl⟩
  obtain ⟨h, hh⟩ := hm
  refine ⟨h, fun v => ?_⟩
  have he := congrArg (fun e : BinaryGL => e (f v)) hh
  change representation h (f v) = f (representation g (f.symm (f v))) at he
  simpa only [LinearEquiv.symm_apply_apply] using he.symm

/-- Conjugation by a normalizer element preserves the computed endomorphism commutant. -/
theorem normalizer_conj_commutes (f : BinaryGL) (hf : f ∈ normalizer)
    (q : V →ₗ[ZMod 2] V)
    (hq : ∀ (g : SL) v, q (representation g v) = representation g (q v)) :
    ∀ (g : SL) v, f.conjRingEquiv q (representation g v) =
      representation g (f.conjRingEquiv q v) := by
  intro g v
  obtain ⟨h, hh⟩ := normalizer_intertwines f.symm (normalizer.inv_mem hf) g
  have he (w : V) : f (representation h w) = representation g (f w) := by
    apply f.symm.injective
    rw [LinearEquiv.symm_apply_apply, hh, LinearEquiv.symm_apply_apply]
  change f (q (f.symm (representation g v))) = representation g (f (q (f.symm v)))
  rw [hh, hq, he]

/-- A normalizer either preserves the coordinate summands or becomes preserving
by exchanging them in the domain. -/
theorem normalizer_summand_dichotomy (f : BinaryGL) (hf : f ∈ normalizer) :
    PreservesSummands f ∨ PreservesSummands (f * graphSwap) := by
  let p := blockScalar 1 0
  have hp : p * p = p := by
    apply LinearMap.ext
    intro v
    simp [p, Module.End.mul_apply, blockScalar_apply]
  have hp0 : p ≠ 0 := by
    intro h
    have he := congrArg (fun v : V => v.1 0)
      (LinearMap.congr_fun h ((Pi.single 0 1 : W), 0))
    simp [p, blockScalar_apply] at he
  have hp1 : p ≠ 1 := by
    intro h
    have he := congrArg (fun v : V => v.2 0)
      (LinearMap.congr_fun h (0, (Pi.single 0 1 : W)))
    simp [p, blockScalar_apply] at he
  have hc := centralizer_idempotents (f.conjRingEquiv p)
    (normalizer_conj_commutes f hf p (blockScalar_commutes 1 0))
    (by rw [← map_mul, hp])
  have hc0 : f.conjRingEquiv p ≠ 0 := by
    intro h
    exact hp0 (f.conjRingEquiv.injective (h.trans (map_zero f.conjRingEquiv).symm))
  have hc1 : f.conjRingEquiv p ≠ 1 := by
    intro h
    exact hp1 (f.conjRingEquiv.injective (h.trans (map_one f.conjRingEquiv).symm))
  rcases hc.resolve_left hc0 |>.resolve_left hc1 with h | h
  · left
    have he (v : V) : f (v.1, 0) = ((f v).1, 0) := by
      have hh := LinearMap.congr_fun h (f v)
      change f (p (f.symm (f v))) = blockScalar 1 0 (f v) at hh
      simpa [p, blockScalar_apply] using hh
    constructor
    · intro w
      exact congrArg Prod.snd (he (w, 0))
    · intro w
      have hh := congrArg Prod.fst (he (0, w))
      simpa only [← Prod.zero_eq_mk, map_zero, Prod.fst_zero] using hh.symm
  · right
    have he (v : V) : f (v.1, 0) = (0, (f v).2) := by
      have hh := LinearMap.congr_fun h (f v)
      change f (p (f.symm (f v))) = blockScalar 0 1 (f v) at hh
      simpa [p, blockScalar_apply] using hh
    constructor
    · intro w
      change (f (0, w)).2 = 0
      have hh := congrArg Prod.snd (he (0, w))
      simpa only [← Prod.zero_eq_mk, map_zero, Prod.snd_zero] using hh.symm
    · intro w
      change (f (w, 0)).1 = 0
      exact congrArg Prod.fst (he (w, 0))

/-- The concrete graph involution normalizes the actual component image. -/
theorem graphSwap_mem_normalizer : graphSwap ∈ normalizer := by
  have hc (g : SL) : graphSwap * linearAction g * graphSwap⁻¹ =
      linearAction (Matrix.SpecialLinearGroup.inverseTranspose g) := by
    apply LinearEquiv.ext
    intro v
    change graphSwap (representation g (graphSwap v)) = _
    rw [graphSwap_equivariant]
    rfl
  apply Subgroup.mem_normalizer_iff.mpr
  intro x
  constructor
  · rintro ⟨g, rfl⟩
    exact ⟨Matrix.SpecialLinearGroup.inverseTranspose g, (hc g).symm⟩
  · rintro ⟨g, hg⟩
    refine ⟨Matrix.SpecialLinearGroup.inverseTranspose g, ?_⟩
    rw [← hc, hg]
    apply LinearEquiv.ext
    intro v
    rfl

/-- The full action of a preserving map is determined by its diagonal blocks. -/
theorem preservesSummands_apply (f : BinaryGL) (hp : PreservesSummands f) (v : V) :
    f v = ((f (v.1, 0)).1, (f (0, v.2)).2) := by
  have hv : v = (v.1, 0) + (0, v.2) := by simp
  rw [hv, map_add]
  exact Prod.ext (by simpa using hp.2 v.2) (by simpa using hp.1 v.1)

/-- Restriction to the first coordinate, defined even before invariance is known. -/
def firstBlock (f : BinaryGL) : W →ₗ[ZMod 2] W :=
  (LinearMap.fst (ZMod 2) W W).comp
    (f.toLinearMap.comp (LinearMap.inl (ZMod 2) W W))

/-- Restriction to the second coordinate. -/
def secondBlock (f : BinaryGL) : W →ₗ[ZMod 2] W :=
  (LinearMap.snd (ZMod 2) W W).comp
    (f.toLinearMap.comp (LinearMap.inr (ZMod 2) W W))

lemma firstBlock_apply (f : BinaryGL) (w : W) : firstBlock f w = (f (w, 0)).1 := rfl
lemma secondBlock_apply (f : BinaryGL) (w : W) : secondBlock f w = (f (0, w)).2 := rfl

lemma firstBlock_fst (f : BinaryGL) (hp : PreservesSummands f) (v : V) :
    firstBlock f v.1 = (f v).1 := (congrArg Prod.fst (preservesSummands_apply f hp v)).symm

lemma secondBlock_snd (f : BinaryGL) (hp : PreservesSummands f) (v : V) :
    secondBlock f v.2 = (f v).2 := (congrArg Prod.snd (preservesSummands_apply f hp v)).symm

lemma firstBlock_bijective (f : BinaryGL) (hp : PreservesSummands f) :
    Function.Bijective (firstBlock f) := by
  constructor
  · intro u v huv
    have he : f (u, 0) = f (v, 0) :=
      Prod.ext huv ((hp.1 u).trans (hp.1 v).symm)
    exact congrArg Prod.fst (f.injective he)
  · intro w
    refine ⟨(f.symm (w, 0)).1, ?_⟩
    rw [firstBlock_fst f hp, LinearEquiv.apply_symm_apply]

lemma secondBlock_bijective (f : BinaryGL) (hp : PreservesSummands f) :
    Function.Bijective (secondBlock f) := by
  constructor
  · intro u v huv
    have he : f (0, u) = f (0, v) :=
      Prod.ext ((hp.2 u).trans (hp.2 v).symm) huv
    exact congrArg Prod.snd (f.injective he)
  · intro w
    refine ⟨(f.symm (0, w)).2, ?_⟩
    rw [secondBlock_snd f hp, LinearEquiv.apply_symm_apply]

/-- The natural block of a preserving operator is an actual binary equivalence. -/
def firstBlockEquiv (f : BinaryGL) (hp : PreservesSummands f) : W ≃ₗ[ZMod 2] W :=
  LinearEquiv.ofBijective (firstBlock f) (firstBlock_bijective f hp)

/-- The dual block of a preserving operator is an actual binary equivalence. -/
def secondBlockEquiv (f : BinaryGL) (hp : PreservesSummands f) : W ≃ₗ[ZMod 2] W :=
  LinearEquiv.ofBijective (secondBlock f) (secondBlock_bijective f hp)

lemma firstBlockEquiv_apply (f : BinaryGL) (hp : PreservesSummands f) (w : W) :
    firstBlockEquiv f hp w = (f (w, 0)).1 := rfl

lemma secondBlockEquiv_apply (f : BinaryGL) (hp : PreservesSummands f) (w : W) :
    secondBlockEquiv f hp w = (f (0, w)).2 := rfl

lemma preservesSummands_symm (f : BinaryGL) (hp : PreservesSummands f) :
    PreservesSummands f.symm := by
  constructor
  · intro w
    apply (secondBlock_bijective f hp).1
    rw [secondBlock_snd f hp, LinearEquiv.apply_symm_apply, map_zero]
  · intro w
    apply (firstBlock_bijective f hp).1
    rw [firstBlock_fst f hp, LinearEquiv.apply_symm_apply, map_zero]

/-- Both diagonal blocks implement the same conjugation on the actual component. -/
theorem normalizer_blocks_intertwine (f : BinaryGL) (hf : f ∈ normalizer)
    (g : SL) :
    ∃ h : SL, (∀ w : W, firstBlock f (natural g w) = natural h (firstBlock f w)) ∧
      (∀ w : W, secondBlock f (dualCoordinates g w) = dualCoordinates h (secondBlock f w)) := by
  obtain ⟨h, hh⟩ := normalizer_intertwines f hf g
  refine ⟨h, ?_, ?_⟩
  · intro w
    have he := congrArg Prod.fst (hh (w, 0))
    simpa [firstBlock_apply, secondBlock_apply, representation, Representation.prod] using he
  · intro w
    have he := congrArg Prod.snd (hh (0, w))
    simpa [firstBlock_apply, secondBlock_apply, representation, Representation.prod] using he

end Representation.SL3FourNaturalDual.QuadraticActors.NormalizerReduction
