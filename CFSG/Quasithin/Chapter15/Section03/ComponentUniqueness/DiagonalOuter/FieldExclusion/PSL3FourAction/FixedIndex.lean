module

public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.DiagonalOuter.FieldExclusion.ModelAction
public import Theory.GroupTheory.CardFourAutomorphismStabilizer

/-!
# Fixed centralizers for a TI four-group

If a nonidentity member of a TI four-group U commutes with k, then k
normalizes U. Conjugation by its centralizer therefore acts on U while fixing
that member. The automorphism image has order at most two, and its kernel is
the centralizer of the entire plane. Applied inside an invariant subgroup K,
this proves relative normality and the index bound for the actual fixed
subgroups in K.

This retains more of the local geometry than `FixesTwoPerfectSubgroups`.
In particular, it concerns the genuine central cover, before passage to its
simple quotient. It is an input to the PSL₃(4) calculation in the last
paragraph of Aschbacher--Smith 15.3.38, printed p.1137, combined manuscript
of 1 March 2004. No model classification is asserted here.
-/

public section

open Subgroup
namespace CFSG.Quasithin.Chapter15.Section03.DiagonalOuter.FieldExclusion.PSL3FourAction
variable {A K : Type*} [Group A] [Group K]

/-- The subgroup fixed by one specified actor. -/
@[expose] def elementFixedSubgroup (φ : A →* MulAut K) (a : A) : Subgroup K :=
  (φ a).toMonoidHom.eqLocus (MonoidHom.id K)

/-- The full-plane fixer is normal of index at most two in every
nonidentity actor's fixer. -/
@[expose] def FixedCentralizerControl (φ : A →* MulAut K) : Prop :=
  ∀ a : A, a ≠ 1 →
    ((fixedSubgroupOfAction φ).subgroupOf (elementFixedSubgroup φ a)).Normal ∧
    (fixedSubgroupOfAction φ).relIndex (elementFixedSubgroup φ a) ≤ 2

variable {G : Type*} [Group G]

/-- Ambient TI gives both the relative normality and the index bound
inside each element centralizer in the invariant subgroup. -/
theorem conjugation_fixedCentralizerControl (U K : Subgroup G) [IsKleinFour U]
    (hU : CFSG.Quasithin.ChapterI.Section06To08.IsTISubgroup U)
    (hUN : U ≤ normalizer (K : Set G)) :
    FixedCentralizerControl (K.normalizerMonoidHom.comp (inclusion hUN)) := by
  let φ := K.normalizerMonoidHom.comp (inclusion hUN)
  intro a ha
  let C := elementFixedSubgroup φ a
  have hCN : ∀ k : C, ((k : K) : G) ∈ normalizer (U : Set G) := by
    intro k
    apply hU.centralizer_le_normalizer a.property
      (fun h => ha (Subtype.ext h))
    apply mem_centralizer_singleton_iff.mpr
    have he := congrArg Subtype.val k.property
    change (a : G) * ((k : K) : G) * (a : G)⁻¹ = ((k : K) : G) at he
    exact (mul_inv_eq_iff_eq_mul.mp he).symm
  let j : C →* normalizer (U : Set G) :=
    (K.subtype.comp C.subtype).codRestrict _ hCN
  let ψ := U.normalizerMonoidHom.comp j
  have hker : ψ.ker = (fixedSubgroupOfAction φ).subgroupOf C := by
    ext k
    change ψ k = 1 ↔ ∀ u : U, φ u (k : K) = (k : K)
    constructor
    · intro h u
      apply Subtype.ext
      have he := congrArg Subtype.val (MulEquiv.congr_fun h u)
      change ((k : K) : G) * (u : G) * ((k : K) : G)⁻¹ = (u : G) at he
      change (u : G) * ((k : K) : G) * (u : G)⁻¹ = ((k : K) : G)
      rw [mul_inv_eq_iff_eq_mul] at he ⊢
      exact he.symm
    · intro h
      ext u
      have he := congrArg Subtype.val (h u)
      change (u : G) * ((k : K) : G) * (u : G)⁻¹ = ((k : K) : G) at he
      change ((k : K) : G) * (u : G) * ((k : K) : G)⁻¹ = (u : G)
      rw [mul_inv_eq_iff_eq_mul] at he ⊢
      exact he.symm
  constructor
  · rw [← hker]
    infer_instance
  · change ((fixedSubgroupOfAction φ).subgroupOf C).index ≤ 2
    rw [← hker, index_ker]
    let : Finite U := Nat.finite_of_card_ne_zero (by simp)
    apply card_mulAut_subgroup_le_two_of_fixed_point IsKleinFour.card_four a ha ψ.range
    rintro _ ⟨k, rfl⟩
    apply Subtype.ext
    have he := congrArg Subtype.val k.property
    change (a : G) * ((k : K) : G) * (a : G)⁻¹ = ((k : K) : G) at he
    change ((k : K) : G) * (a : G) * ((k : K) : G)⁻¹ = (a : G)
    rw [mul_inv_eq_iff_eq_mul] at he ⊢
    exact he.symm
end CFSG.Quasithin.Chapter15.Section03.DiagonalOuter.FieldExclusion.PSL3FourAction
