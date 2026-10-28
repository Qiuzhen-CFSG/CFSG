module
public import Theory.SpecificGroups.BinaryLinear.OuterCyclic
public import Theory.SpecificGroups.BinaryLinear.SmallCubicRank
public import Theory.SpecificGroups.AlternatingSix.OuterSolvable
public import Theory.Alternating.PrimeRank
public import Theory.AtlasPort.LinearGroups.G2.LieAutomorphismExtensions.BinaryAutomorphismGroup
public import Theory.AtlasPort.LinearGroups.G2.EvenThreeRank
public import Theory.AtlasPort.LinearGroups.G2.BinaryDerivedSimplicity
public import Theory.SpecificGroups.FFG2DerivedCenter
public import Theory.GroupTheory.AutomorphismOvergroupCore
public import Theory.Quasithin.Rank

/-!
# Ordinary cubic-residual facts for the surviving binary component models

The genuine A₆, SL₄(2), SL₅(2), and G₂(2)′ carriers have trivial center,
three-rank at least two and two-group outer automorphisms. The outer-two
bounds use actual automorphism coverage, including the full G₂(2)
conjugation map on its derived subgroup.
Source: Aschbacher–Smith13.5.21(1), p.924, ordinary case of A.3.18.
-/
public section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace Theory.SpecificGroups.BinaryComponentResidual

/-- The graph representative has square one in the actual outer quotient. -/
theorem linear_outer_two {n : ℕ} (hn : n = 4 ∨ n = 5) :
    IsPGroup 2 (MulAut.Outer SL(n,ZMod 2)) := by
  have h : IsPGroup 2 (MulAut.Outer (BinaryLinear.OuterCyclic.LinearGroup n)) := by
    let q := QuotientGroup.mk' (MulAut.innerSubgroup (BinaryLinear.OuterCyclic.LinearGroup n))
    intro x
    obtain ⟨a,rfl⟩ := QuotientGroup.mk'_surjective (MulAut.innerSubgroup _) x
    refine ⟨1,?_⟩
    change (q a)^2=1
    obtain ⟨g,hg⟩ := BinaryLinear.OuterCyclic.inner_graph hn a
    have hi : q (MulAut.conj g)=1 := (QuotientGroup.eq_one_iff _).mpr ⟨g,rfl⟩
    rcases hg with rfl | rfl
    · rw [hi,one_pow]
    · rw [map_mul,hi,mul_one,←map_pow,BinaryLinear.OuterCyclic.graphLinear_sq,map_one]
  exact h.of_injective (MulAut.outerCongr (BinaryLinear.OuterCyclic.slEquivLinear n)).toMonoidHom
    (MulAut.outerCongr (BinaryLinear.OuterCyclic.slEquivLinear n)).injective

/-- The full octonion group is the actual automorphism group, with index-two inners. -/
theorem g2_outer_two : IsPGroup 2 (MulAut.Outer (commutator (Atlas.G2.Model (ZMod 2)))) := by
  let A := commutator (Atlas.G2.Model (ZMod 2))
  have hz : center A=⊥ := Theory.SpecificGroups.g2_derived_two_center_eq_bot
  have hi : Function.Injective (MulAut.conj : A →* MulAut A) :=
    Theory.GroupTheory.conj_injective_of_center_eq_bot hz
  have hinner : Nat.card (MulAut.innerSubgroup A)=6048 := by
    rw [←Nat.card_congr (MonoidHom.ofInjective hi).toEquiv]
    exact Atlas.G2.LieAutomorphismExtensions.card_binaryDerived
  have haut : Nat.card (MulAut A)=12096 :=
    (Nat.card_congr Atlas.G2.LieAutomorphismExtensions.binaryAutomorphismEquiv.toEquiv).symm.trans
      Atlas.G2.LieAutomorphismExtensions.card_binaryFull
  have hc := (MulAut.innerSubgroup A).card_mul_index
  rw [hinner,haut] at hc
  apply IsPGroup.of_card (n:=1)
  change (MulAut.innerSubgroup A).index=2
  omega

/-- Three concrete facts needed by the ordinary source residual deduction. -/
@[expose] def Facts (E : Type*) [Group E] : Prop :=
  center E=⊥ ∧ 2≤primeRank 3 E ∧ IsPGroup 2 (MulAut.Outer E)

theorem Facts.of_equiv {E M : Type*} [Group E] [Finite E] [Group M] [Finite M]
    (e : E ≃* M) (h : Facts M) : Facts E := by
  refine ⟨?_,?_,h.2.2.of_injective (MulAut.outerCongr e).toMonoidHom
    (MulAut.outerCongr e).injective⟩
  · apply le_bot_iff.mp
    intro x hx
    exact e.map_eq_one_iff.mp (h.1.le ((centerCongr e) ⟨x,hx⟩).property)
  · rw [primeRank_congr 3 e]; exact h.2.1

theorem alternatingSix : Facts (alternatingGroup (Fin 6)) := by
  refine ⟨alternatingGroup.center_eq_bot (by simp),?_,?_⟩
  · rw [GLS3.Chapter5.PRank.alternating_primeRank_of_odd_prime 6 3 Nat.prime_three (by decide)]
  · exact IsPGroup.of_card (n:=2) AlternatingSix.ShadowLocal.outer_card

theorem linear {n : ℕ} (hn : n=4 ∨ n=5) : Facts SL(n,ZMod 2) :=
  ⟨BinaryLinear.OuterCyclic.binary_center_eq_bot (by omega),
    BinaryLinear.SmallCubicRank.four_or_five hn,linear_outer_two hn⟩

theorem g2 : Facts (commutator (Atlas.G2.Model (ZMod 2))) :=
  ⟨Theory.SpecificGroups.g2_derived_two_center_eq_bot,
    Atlas.G2.EvenThreeRank.two_le_primeRank_derived,g2_outer_two⟩
end Theory.SpecificGroups.BinaryComponentResidual
