module

public import Theory.Representation.SymplecticFourOrthogonalCover.Roots
public import Theory.Representation.SymplecticFourOrthogonalCover.SylowFlag.Geometry
public import Theory.Representation.BinaryOffender.QuadraticSection
public import Theory.Representation.QuadraticDuality
public import Theory.ElementaryAbelian.Injective

/-!
# Dual quadratic bounds for natural symplectic central covers

For a binary central cover of the natural Sp₄(K)′ module, with |K| > 2,
use the long-root subgroup of order |K|. Its commutator space is the
preimage of the first natural line and is fixed by the root subgroup.
The explicit universal orthogonal cover bounds that preimage by twice
the binary degree of K. The same root subgroup therefore gives quadratic
ratio at most two on the contragredient of every such central cover.

These are the commutator-generated cover cases of Aschbacher–Smith B.5.13,
printed pp.110–112. A module with a further trivial top quotient requires
the separate six-dimensional orthogonal envelope used in the source.
-/

public section

open Representation Representation.OneCohomology Representation.BinaryOffender
open Theory.SpecificGroups.SymplecticFour
open Representation.OneCohomology.SymplecticFour
namespace Representation.SymplecticFourOrthogonalCover.Roots
variable {K : Type*} [Field K] [Finite K] [CharP K 2] [Algebra (ZMod 2) K]

/-- The literal derived root subgroup has the additive field as parameter. -/
noncomputable def parameterEquiv (hcard : 2 < Nat.card K) :
    Multiplicative K ≃* group (K := K) := by
  let f : Multiplicative K →* group (K := K) :=
    { toFun := fun t => ⟨element hcard t.toAdd, element_mem_group hcard t.toAdd⟩
      map_one' := by
        apply Subtype.ext
        apply Subtype.ext
        exact RootSubgroup.element_zero 0
      map_mul' := by
        intro s t
        apply Subtype.ext
        apply Subtype.ext
        exact (RootSubgroup.element_add 0 s.toAdd t.toAdd).symm }
  exact MulEquiv.ofBijective f ⟨by
      intro s t h
      have hs : rootElement 0 s.toAdd = rootElement 0 t.toAdd :=
        congrArg (fun x : group (K := K) => x.val.val) h
      change s.toAdd = t.toAdd
      exact RootSubgroup.element_injective (F := K) 0 hs,
    by
      intro g
      obtain ⟨t, ht⟩ := (mem_group hcard g.val).mp g.property
      exact ⟨Multiplicative.ofAdd t, Subtype.ext ht⟩⟩

/-- The root group has binary rank equal to the degree of the field. -/
theorem group_rank (hcard : 2 < Nat.card K) :
    rank (group (K := K)) = Module.finrank (ZMod 2) K := by
  have hc : Nat.card (group (K := K)) = Nat.card K :=
    (Nat.card_congr (parameterEquiv hcard).toEquiv).symm
  rw [rank, hc, Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod,
    Nat.log_pow (by decide : 1 < 2)]

/-- The root subgroup is a nontrivial elementary abelian two-group. -/
theorem group_elementary (hcard : 2 < Nat.card K) :
    IsElementaryTwo (group (K := K)) := by
  let _ : IsElementaryAbelian 2 (Multiplicative K) := {
    exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr (by
      intro x
      change (2 : ℕ) • x.toAdd = 0
      rw [← Nat.cast_smul_eq_nsmul (ZMod 2)]
      exact zero_smul (ZMod 2) x.toAdd) }
  refine ⟨?_, IsElementaryAbelian.of_injective (parameterEquiv hcard).symm.toMonoidHom
    (parameterEquiv hcard).symm.injective⟩
  intro he
  have hc : Nat.card (group (K := K)) = Nat.card K :=
    (Nat.card_congr (parameterEquiv hcard).toEquiv).symm
  rw [he, Subgroup.card_bot] at hc
  omega

/-- The same root group acts quadratically on every cover and moves at most twice its rank. -/
theorem cover_root_bound (hcard : 2 < Nat.card K)
    {W : Type*} [AddCommGroup W] [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W]
    {σ : Representation (ZMod 2) (L (K := K)) W}
    (p : σ.IntertwiningMap (binaryNatural (K := K))) (hp : IsCover p) :
    IsQuadratic σ group ∧
      Module.finrank (ZMod 2) (Coinvariants.ker (σ.comp group.subtype)) ≤
        2 * rank (group (K := K)) := by
  obtain ⟨_, hcomm, hfixed⟩ := cover_root_geometry hcard p hp
  constructor
  · intro a ha b hb w
    exact hfixed (hcomm.symm ▸ Coinvariants.sub_mem_ker
      (ρ := σ.comp group.subtype) ⟨b, hb⟩ w) ⟨a, ha⟩
  · obtain ⟨f, hf, hover⟩ := exists_cover_quotient p hp
    have hm := map_preimage_of_surjective binaryProjection p f hf hover
      (firstLine.restrictScalars (ZMod 2))
    rw [← hcomm, ← hm]
    apply (Submodule.finrank_map_le _ _).trans
    have he : (firstLine.restrictScalars (ZMod 2)).comap
        (binaryProjection (K := K)).toLinearMap = firstPreimage.restrictScalars (ZMod 2) := rfl
    rw [he]
    rw [((Submodule.restrictScalarsEquiv (ZMod 2) K _ firstPreimage).restrictScalars
      (ZMod 2)).finrank_eq, ← Module.finrank_mul_finrank (ZMod 2) K,
      group_rank hcard]
    have hd : Module.finrank K (firstPreimage (K := K)) = 2 :=
      SylowFlag.first_preimage_finrank
    rw [hd, Nat.mul_comm]

/-- The contragredient of every natural central cover has quadratic ratio at most two. -/
theorem dual_cover_ratio_le_two (hcard : 2 < Nat.card K)
    {W : Type*} [AddCommGroup W] [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W]
    {σ : Representation (ZMod 2) (L (K := K)) W}
    (p : σ.IntertwiningMap (binaryNatural (K := K))) (hp : IsCover p) :
    quadraticRatio σ.dual ≤ 2 := by
  obtain ⟨hq, hd⟩ := cover_root_bound hcard p hp
  apply (quadraticRatio_le_two_iff σ.dual).mpr
  refine ⟨group, group_elementary hcard, ?_, ?_⟩
  · have hc : Coinvariants.ker (σ.comp group.subtype) ≤
        Representation.invariants (σ.comp group.subtype) :=
      (commutator_le_invariants_iff _).mpr (fun a b w => hq a.val a.property b.val b.property w)
    have hdual := (commutator_le_invariants_iff_dual (σ.comp group.subtype)).mp hc
    intro a ha b hb w
    exact (commutator_le_invariants_iff _).mp hdual ⟨a, ha⟩ ⟨b, hb⟩ w
  · change Module.finrank (ZMod 2)
      (Module.Dual (ZMod 2) W ⧸ Representation.invariants
        (Representation.dual (σ.comp group.subtype))) ≤ _
    rw [finrank_dual_quotient_invariants]
    exact hd

end Representation.SymplecticFourOrthogonalCover.Roots
