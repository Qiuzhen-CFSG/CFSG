module
public import Theory.Representation.BinaryPermutation.FiveBorelFixed
public import Theory.Representation.BinaryAlternatingFiveFlag.Borel
public import Theory.SpecificGroups.Alternating.FiveBorelOvergroups
public import Theory.GroupTheory.PResidual.Quotient
public import Theory.GroupTheory.SylowNormalizerCommutingFamily

/-!
# Two-group actions and fixed vectors of an A₅ Borel

Every Sylow normalizer in A₅ is two-perfect, by transport from the actual
point stabilizer A₄. Consequently any two-group action factoring through
that marked normalizer is trivial, including actions of a cover with its
full kernel retained. On the binary deleted five-point module the Sylow
fixed space has order at most two; on two copies it has order at most four.
The fixed-space bounds reuse the unique nonzero Sylow-fixed vector.

Source application: Aschbacher--Smith 5.1.13, printed pp.635--638,
refs/quasithin.pdf, the original local Cartan retained-kernel analysis.
-/

public noncomputable section
open Subgroup
namespace BinaryPermutation.FiveBorelTwoAction
abbrev A := alternatingGroup (Fin 5)

/-- Every A₅ Sylow normalizer has no nontrivial two-group quotient. -/
theorem normalizer_twoPerfect (P : Sylow 2 A) :
    IsPPerfect 2 (normalizer (P : Set A)) := by
  obtain ⟨i,hi⟩ := Theory.SpecificGroups.Alternating.FiveBorelOvergroups.sylow_normalizer_eq_stabilizer P
  rw [hi]
  have ht : ∀ i : Fin 5, ∃ g : A, g • (4 : Fin 5) = i := by decide +kernel
  obtain ⟨g,hg⟩ := ht i
  let e := MulAction.stabilizerEquivStabilizer hg.symm
  have hp : IsPPerfect 2 AlternatingFiveBorel.B :=
    (pResidual_eq_top_iff 2 _).mp AlternatingFiveFlag.borel_twoResidual
  exact hp.of_surjective e.toMonoidHom e.surjective

/-- A two-group action through the marked A₅ Borel is trivial. -/
theorem trivial_of_two_image
    {J D : Type*} [Group J] [Finite J] [Group D]
    (q : J →* A) (hq : Function.Surjective q) (P : Sylow 2 J)
    (f : normalizer (P : Set J) →* D)
    (hk : (q.comp (normalizer (P : Set J)).subtype).ker ≤ f.ker)
    (hf : IsPGroup 2 f.range) : ∀ x, f x = 1 := by
  let B := normalizer (P : Set J)
  let S := P.mapSurjective hq
  have he : B.map q = normalizer (S : Set A) := P.normalizer_map_surjective q hq
  have hp : IsPPerfect 2 (B.map q) := he ▸ normalizer_twoPerfect S
  have hm : (pResidual 2 B).map (q.subgroupMap B) = ⊤ := by
    rw [map_pResidual_of_surjective 2 _ (q.subgroupMap_surjective B),
      (pResidual_eq_top_iff 2 _).mpr hp]
  have hr : pResidual 2 B ≤ f.ker := by
    intro y hy
    exact congrArg Subtype.val (pResidual_le_ker_of_isPGroup 2 f.rangeRestrict hf hy)
  intro x
  obtain ⟨y,hy,hxy⟩ := show q.subgroupMap B x ∈ (pResidual 2 B).map (q.subgroupMap B) by rw [hm]; trivial
  have hz : x*y⁻¹ ∈ (q.comp B.subtype).ker := by
    change q ((x : J) * (y : J)⁻¹) = 1
    rw [map_mul,map_inv,show q (x : J) = q (y : J) from (congrArg Subtype.val hxy).symm,mul_inv_cancel]
  have hfy : f y = 1 := hr hy
  have hfx : f (x*y⁻¹) = 1 := hk hz
  simpa only [map_mul,map_inv,hfy,inv_one,mul_one] using hfx

/-- A Sylow four-group fixes at most two vectors of the binary A₅ module. -/
theorem sylow_fixed_card_le_two (P : Sylow 2 A) :
    Nat.card (Representation.BinaryOffender.fixedSpace
      (alternatingNaturalRepresentation (Ω := Fin 5)) P) ≤ 2 := by
  classical
  let F := Representation.BinaryOffender.fixedSpace
    (alternatingNaturalRepresentation (Ω := Fin 5)) P
  let e := coreEquivNatural (Fin 5) (by decide)
  have unique (v w : F) (hv : v ≠ 0) (hw : w ≠ 0) : v = w := by
    apply Subtype.ext
    apply e.symm.injective
    apply FiveBorelFixed.sylow_fixed_unique P
    · intro hz
      apply hv
      apply Subtype.ext
      exact e.symm.injective (hz.trans (map_zero _).symm)
    · intro hz
      apply hw
      apply Subtype.ext
      exact e.symm.injective (hz.trans (map_zero _).symm)
    · intro g
      apply e.injective
      change e (coreRepresentation (Fin 5) g.val.val (e.symm v.val)) = e (e.symm v.val)
      rw [coreEquivNatural_equivariant,e.apply_symm_apply]
      exact v.property g
    · intro g
      apply e.injective
      change e (coreRepresentation (Fin 5) g.val.val (e.symm w.val)) = e (e.symm w.val)
      rw [coreEquivNatural_equivariant,e.apply_symm_apply]
      exact w.property g
  have hi : Function.Injective (fun v : F => decide (v = 0)) := by
    intro v w he
    by_cases hv : v = 0
    · have hw : w = 0 := by simpa [hv] using he.symm
      exact hv.trans hw.symm
    · have hw : w ≠ 0 := by simpa [hv] using he.symm
      exact unique v w hv hw
  exact (Nat.card_le_card_of_injective _ hi).trans (by simp)
end BinaryPermutation.FiveBorelTwoAction

namespace BinaryPermutation.FiveBorelTwoAction
/-- On two copies the fixed subgroup has order at most four. -/
theorem sylow_fixed_pair_card_le_four (P : Sylow 2 A) :
    Nat.card (Representation.BinaryOffender.fixedSpace
      ((alternatingNaturalRepresentation (Ω := Fin 5)).prod
        (alternatingNaturalRepresentation (Ω := Fin 5))) P) ≤ 4 := by
  let F := Representation.BinaryOffender.fixedSpace
    (alternatingNaturalRepresentation (Ω := Fin 5)) P
  let F2 := Representation.BinaryOffender.fixedSpace
    ((alternatingNaturalRepresentation (Ω := Fin 5)).prod
      (alternatingNaturalRepresentation (Ω := Fin 5))) P
  let f : F2 → F × F := fun x =>
    (⟨x.val.1, fun g => congrArg Prod.fst (x.property g)⟩,
      ⟨x.val.2, fun g => congrArg Prod.snd (x.property g)⟩)
  have hf : Function.Injective f := by
    intro x y he
    exact Subtype.ext (Prod.ext (congrArg (fun z : F × F => z.1.val) he)
      (congrArg (fun z : F × F => z.2.val) he))
  apply (Nat.card_le_card_of_injective f hf).trans
  rw [Nat.card_prod]
  exact Nat.mul_le_mul (sylow_fixed_card_le_two P) (sylow_fixed_card_le_two P)
end BinaryPermutation.FiveBorelTwoAction
