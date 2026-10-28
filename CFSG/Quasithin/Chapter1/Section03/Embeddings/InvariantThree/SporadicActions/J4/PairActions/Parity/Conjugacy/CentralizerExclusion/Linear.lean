module

public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreNormalizer.LinearNormalizer.CoreRecognition
public import Theory.GroupTheory.PrimeCyclicCoverage
public import Theory.GroupTheory.PrimeOrderLift
public import Mathlib.GroupTheory.Perm.Centralizer

/-!
# Order 35 is absent from the certified binary local model

An order-five element of the concrete M₂₂ has cycle type 5⁴1². Its
centralizer in S₂₂ has order 30000, prime to seven. Sylow conjugacy for
order-five subgroups excludes order 35 in M₂₂. The proved central-quotient
isomorphism transports this exclusion to the derived subgroup of the
fixed twelve-dimensional binary model, since its center is a three-group.
Every square in the full linear model belongs to that derived subgroup,
which gives the same exclusion for the full model.

These are intrinsic calculations for the actual carriers. Applying them to
J₄ requires the separate action and kernel comparison in `Local`.
Source motivation: GLS3, Table 5.3i, printed p.270,
`refs/KGroup/GLS3/Chapter5(sec3-).tex`. The matrix and permutation provenance
is retained in the imported `CoreRecognition` development.
-/

public section

open Subgroup Sporadic.Mathieu

namespace CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.SporadicActions.J4Reduction.Max4Conjugacy.CentralizerExclusion

private def fivePerm : Equiv.Perm (Fin 22) := m22GeneratorA * m22GeneratorB ^ 2

private noncomputable def five : M22 :=
  (⟨m22GeneratorA, m22GeneratorA_mem_M22⟩ : M22) *
    (⟨m22GeneratorB, m22GeneratorB_mem_M22⟩ : M22) ^ 2

private theorem five_order : orderOf five = 5 := by
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  rw [← Subgroup.orderOf_coe]
  change orderOf fivePerm = 5
  apply orderOf_eq_prime
  · decide +kernel
  · decide +kernel

private theorem centralizer_five_card :
    Nat.card (centralizer ({fivePerm} : Set (Equiv.Perm (Fin 22)))) = 30000 := by
  rw [Equiv.Perm.nat_card_centralizer]
  have ht : fivePerm.cycleType = {5, 5, 5, 5} := by decide +kernel
  rw [ht]
  decide +kernel

/-- The concrete M₂₂ permutation group has no element of order 35. -/
theorem m22_orderOf_ne_thirtyFive (x : M22) : orderOf x ≠ 35 := by
  intro hx
  have hu : orderOf (x ^ 7) = 5 := by norm_num [orderOf_pow, hx]
  obtain ⟨k, g, hg⟩ :=
    PrimeCyclicCoverage.exists_conjugate_pow_of_prime_sq_not_dvd
      (by decide : Nat.Prime 5) (by rw [m22_order]; decide) hu five_order
  have hcomm : Commute (g * x * g⁻¹) five := by
    rw [hg]
    have h := (Commute.self_pow x (7 * k)).map (MulAut.conj g).toMonoidHom
    simpa only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, ← pow_mul] using h
  let y : centralizer ({fivePerm} : Set (Equiv.Perm (Fin 22))) :=
    ⟨(g * x * g⁻¹ : M22), mem_centralizer_singleton_iff.mpr (hcomm.map M22.subtype).eq⟩
  have hy : orderOf y = 35 := by
    rw [← Subgroup.orderOf_coe]
    exact (orderOf_injective M22.subtype M22.subtype_injective _).trans
      (((MulAut.conj g).orderOf_eq x).trans hx)
  have hd := orderOf_dvd_natCard y
  rw [hy, centralizer_five_card] at hd
  norm_num at hd

open Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreLinearModel

/-- The literal derived matrix group has no element of order 35. -/
theorem derived_orderOf_ne_thirtyFive (x : derivedGroup) : orderOf x ≠ 35 := by
  intro hx
  let f := derivedQuotientEquivM22.toMonoidHom.comp
    (QuotientGroup.mk' (center derivedGroup))
  have hk : f.ker = center derivedGroup := by
    ext y
    change derivedQuotientEquivM22 (QuotientGroup.mk' _ y) = 1 ↔ _
    rw [map_eq_one_iff _ derivedQuotientEquivM22.injective]
    exact QuotientGroup.eq_one_iff y
  have hp : IsPGroup 3 f.ker := by
    rw [hk]
    intro z
    refine ⟨1, ?_⟩
    apply Subtype.ext
    change (z : derivedGroup) ^ 3 = 1
    rcases (mem_center_derivedGroup_iff z).mp z.property with h | h | h
    · rw [h, one_pow]
    · rw [h, coreScalar_pow_three]
    · rw [h, ← pow_mul, show 2 * 3 = 3 * 2 from rfl, pow_mul, coreScalar_pow_three, one_pow]
  exact m22_orderOf_ne_thirtyFive (f x)
    ((f.orderOf_map_eq_of_coprime_of_isPGroup_ker hp x (by rw [hx]; decide)).trans hx)

private def c : actionGroup := ⟨unitC, unitC_mem_actionGroup⟩
private def d : actionGroup := ⟨unitD, unitD_mem_actionGroup⟩

private theorem generators : closure {c, d} = ⊤ := by
  apply Subgroup.map_injective actionGroup.subtype_injective
  rw [MonoidHom.map_closure, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  simp only [Set.image_pair]
  rfl

private theorem sq_mem_commutator (x : actionGroup) : x ^ 2 ∈ _root_.commutator actionGroup := by
  let f : actionGroup →* Abelianization actionGroup := Abelianization.of
  have hd : d ^ 2 ∈ _root_.commutator actionGroup := by
    have h := coreB_mem_derivedGroup
    rw [derivedGroup, ← Subgroup.map_subtype_commutator] at h
    obtain ⟨y, hy, he⟩ := h
    exact (show y = d ^ 2 from Subtype.ext he) ▸ hy
  have he : (powMonoidHom 2).comp f = 1 := by
    apply MonoidHom.eq_of_eqOn_dense generators
    rintro z (rfl | rfl)
    · change f c ^ 2 = 1
      rw [← map_pow, show c ^ 2 = 1 from Subtype.ext unitC_pow_two, map_one]
    · change f d ^ 2 = 1
      rw [← map_pow]
      exact (show d ^ 2 ∈ f.ker by rwa [Abelianization.ker_of])
  rw [← Abelianization.ker_of]
  change f (x ^ 2) = 1
  rw [map_pow]
  exact DFunLike.congr_fun he x

/-- The full certified twelve-dimensional matrix model omits order 35. -/
theorem linear_orderOf_ne_thirtyFive (x : actionGroup) : orderOf x ≠ 35 := by
  intro hx
  have hxs : (x : Matrix12ˣ) ^ 2 ∈ derivedGroup := by
    rw [derivedGroup, ← Subgroup.map_subtype_commutator]
    exact ⟨x ^ 2, sq_mem_commutator x, rfl⟩
  let y : derivedGroup := ⟨(x : Matrix12ˣ) ^ 2, hxs⟩
  apply derived_orderOf_ne_thirtyFive y
  rw [← Subgroup.orderOf_coe]
  have hx' : orderOf (x : Matrix12ˣ) = 35 :=
    (orderOf_injective actionGroup.subtype actionGroup.subtype_injective x).trans hx
  norm_num [y, orderOf_pow, hx']

end CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.SporadicActions.J4Reduction.Max4Conjugacy.CentralizerExclusion
