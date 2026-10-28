module
public import Theory.Representation.BinaryPermutationNaturalStructure
public import Theory.Representation.BinaryNaturalDual.Transport
public import Theory.Alternating.PrimeRank
public import Theory.GroupTheory.PrimeRankProduct
public import Mathlib.Logic.Equiv.Set

/-!
# Three-rank of alternating natural point stabilizers

The alternating groups on the zero and one supports of a binary vector
embed as a direct product in its full-permutation stabilizer. Their exact
three-ranks give the lower bound floor(z/3)+floor(o/3). With at least eight
letters this is at least two, independently of the vector. Fixing a core
representative also fixes its class in the actual natural deleted-permutation
section, so the same lower bound holds there, including in even degree.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), §B.3 and
the point-stabilizer argument in 13.7.6(3), printed pp.938–939.
-/

@[expose] public section
open Theory.GroupTheory BinaryNaturalDual.VectorStabilizers
namespace BinaryPermutation.PointStabilizerRank
variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]

private noncomputable def split (v : Full Ω) :
    {i : Ω // v i = 0} ⊕ {i : Ω // v i ≠ 0} ≃ Ω := Equiv.sumCompl (fun i => v i = 0)

private noncomputable def splitAction (v : Full Ω) :
    alternatingGroup {i : Ω // v i = 0} × alternatingGroup {i : Ω // v i ≠ 0} →*
      alternatingGroup Ω where
  toFun g := ⟨(Equiv.permCongr (split v)) (Equiv.sumCongr g.1.val g.2.val), by
    change Equiv.Perm.sign ((Equiv.permCongr (split v)) (Equiv.sumCongr g.1.val g.2.val)) = 1
    rw [Equiv.Perm.sign_permCongr, Equiv.Perm.sign_sumCongr,
      Equiv.Perm.mem_alternatingGroup.mp g.1.property,
      Equiv.Perm.mem_alternatingGroup.mp g.2.property, mul_one]⟩
  map_one' := by apply Subtype.ext; ext i; simp
  map_mul' g h := by apply Subtype.ext; ext i; simp

private theorem splitAction_injective (v : Full Ω) : Function.Injective (splitAction v) := by
  intro g h he
  have hh := (Equiv.permCongr (split v)).injective (congrArg Subtype.val he)
  have hh' := Equiv.Perm.sumCongrHom_injective (α := {i : Ω // v i = 0})
    (β := {i : Ω // v i ≠ 0}) (a₁ := (g.1.val, g.2.val)) (a₂ := (h.1.val, h.2.val)) hh
  exact Prod.ext (Subtype.ext (congrArg Prod.fst hh')) (Subtype.ext (congrArg Prod.snd hh'))

private theorem splitAction_fixes (v : Full Ω)
    (g : alternatingGroup {i : Ω // v i = 0} × alternatingGroup {i : Ω // v i ≠ 0}) :
    alternatingRepresentation Ω (splitAction v g) v = v := by
  funext i
  have hz : ∀ x : ZMod 2, x ≠ 0 → x = 1 := by decide
  obtain ⟨i,rfl⟩ := (split v).surjective i
  change v (((split v).permCongr (Equiv.sumCongr g.1.val g.2.val)).symm ((split v) i)) = _
  change v ((split v) ((Equiv.sumCongr g.1.val g.2.val).symm ((split v).symm ((split v) i)))) = _
  rw [Equiv.symm_apply_apply]
  rcases i with i | i
  · change v ((split v) (Sum.inl (g.1.val.symm i))) = v ((split v) (Sum.inl i))
    exact (g.1.val.symm i).property.trans i.property.symm
  · change v ((split v) (Sum.inr (g.2.val.symm i))) = v ((split v) (Sum.inr i))
    exact (hz _ (g.2.val.symm i).property).trans (hz _ i.property).symm

private theorem alternating_rank (X : Type*) [Fintype X] [DecidableEq X] :
    primeRank 3 (alternatingGroup X) = Fintype.card X / 3 := by
  rw [primeRank_equiv 3 ((Fintype.equivFin X).altCongrHom)]
  exact GLS3.Chapter5.PRank.alternating_primeRank_of_odd_prime _ _ (by decide) (by decide)

/-- Cubics on the zero and one supports give this exact lower bound for the
stabilizer of a binary full-permutation vector. -/
theorem full_stabilizer_lower (v : Full Ω) :
    Fintype.card {i : Ω // v i = 0} / 3 + Fintype.card {i : Ω // v i ≠ 0} / 3 ≤
      primeRank 3 (representationStabilizer (alternatingRepresentation Ω) v) := by
  let f := (splitAction v).codRestrict
    (representationStabilizer (alternatingRepresentation Ω) v) (splitAction_fixes v)
  have hf : Function.Injective f := by
    intro g h he
    exact splitAction_injective v (congrArg Subtype.val he)
  have h := Theory.GroupTheory.primeRank_le_of_injective 3 f hf
  rwa [primeRank_prod_eq_add, alternating_rank, alternating_rank] at h

/-- Every full binary vector on at least eight letters is fixed by an
actual elementary nine-subgroup of the alternating actor. -/
theorem two_le_full_stabilizer (hΩ : 8 ≤ Fintype.card Ω) (v : Full Ω) :
    2 ≤ primeRank 3 (representationStabilizer (alternatingRepresentation Ω) v) := by
  have hc := Fintype.card_congr (split v)
  rw [Fintype.card_sum] at hc
  have h := full_stabilizer_lower v
  omega

/-- The same rank bound on the actual natural deleted-permutation section. -/
theorem two_le_natural_stabilizer (hΩ : 8 ≤ Fintype.card Ω) (v : natural Ω) :
    2 ≤ primeRank 3 (representationStabilizer (alternatingNaturalRepresentation Ω) v) := by
  obtain ⟨u,rfl⟩ := coreToNatural_surjective v
  have hi : representationStabilizer (alternatingRepresentation Ω) u.val ≤
      representationStabilizer (alternatingNaturalRepresentation Ω) (coreToNatural Ω u) := by
    intro g hg
    apply Subtype.ext
    change (constants Ω).mkQ (representation Ω g.val u.val) = (constants Ω).mkQ u.val
    change representation Ω g.val u.val = u.val at hg
    rw [hg]
  exact (two_le_full_stabilizer hΩ u.val).trans
    (Theory.GroupTheory.primeRank_le_of_injective 3 (Subgroup.inclusion hi) (Subgroup.inclusion_injective hi))
end BinaryPermutation.PointStabilizerRank
