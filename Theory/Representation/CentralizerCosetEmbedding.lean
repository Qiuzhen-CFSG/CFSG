module
public import Theory.GroupTheory.CentralizerGeneratorIndexTwo
public import Theory.ElementaryAbelian.VectorSpace
public import Theory.Representation.BinaryCosetFunctional
public import Mathlib.GroupTheory.SpecificGroups.Cyclic

/-!
# Functionals on literal seed-centralizer quotients

An index-two centralizer of u in Q defines a binary functional on
Q/C_Q(U). If the point parabolic has representatives centralizing u,
this functional is invariant under its actual image. Generation of U by
conjugates of u together with a Q-centralized subgroup makes the orbit
of the functional separate the entire quotient.

Relative normality of C_Q(U) and its elementary quotient are explicit
inputs. The original source application supplies both from the five
seed centralizers. No action kernel or constant line is discarded.
Source: Aschbacher--Smith 13.8.33, printed pp.967--968.
-/

public section
open Subgroup Representation
open scoped commutatorElement IsMulCommutative
namespace Representation.CentralizerCosetEmbedding
variable {G A : Type*} [Group G] [Group A]

/-- The seed centralizer is the exact kernel of a binary functional. -/
theorem exists_functional (Q U : Subgroup G) (u : U)
    (hi : (centralizer ({(u : G)} : Set G)).relIndex Q = 2)
    [((Q ⊓ centralizer (U : Set G)).subgroupOf Q).Normal]
    [IsElementaryAbelian 2 (Q ⧸ (Q ⊓ centralizer (U : Set G)).subgroupOf Q)] :
    ∃ f : Additive (Q ⧸ (Q ⊓ centralizer (U : Set G)).subgroupOf Q) →ₗ[ZMod 2] ZMod 2,
      ∀ q : Q, f (Additive.ofMul (QuotientGroup.mk' _ q)) = 0 ↔
        (q : G) ∈ centralizer ({(u : G)} : Set G) := by
  let C := (Q ⊓ centralizer (U : Set G)).subgroupOf Q
  let D := (centralizer ({(u : G)} : Set G)).subgroupOf Q
  let _ : D.Normal := normal_of_index_eq_two hi
  let _ : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let E : (Q ⧸ D) ≃* Multiplicative (ZMod 2) :=
    mulEquivOfPrimeCardEq hi (by exact Nat.card_zmod 2)
  let φ := E.toMonoidHom.comp (QuotientGroup.mk' D)
  have hk : C ≤ φ.ker := by
    intro q hq
    have hqD : q ∈ D := mem_centralizer_singleton_iff.mpr (hq.2 u u.property).symm
    change E (QuotientGroup.mk' D q) = 1
    exact (congrArg E ((QuotientGroup.eq_one_iff q).mpr hqD)).trans (map_one E)
  let ψ := QuotientGroup.lift C φ hk
  let f : Additive (Q ⧸ C) →ₗ[ZMod 2] ZMod 2 :=
    ((AddEquiv.additiveMultiplicative (ZMod 2)).toAddMonoidHom.comp
      (MonoidHom.toAdditive ψ)).toZModLinearMap 2
  refine ⟨f,fun q => ?_⟩
  change E (QuotientGroup.mk' D q) = 1 ↔ q ∈ D
  rw [map_eq_one_iff E E.injective]
  exact QuotientGroup.eq_one_iff q

/-- The actual parabolic fixes the functional and its orbit separates the quotient. -/
theorem exists_separating_functional {ι : Type*}
    (P Q U V R : Subgroup G) (π : P →* A)
    [((Q ⊓ centralizer (U : Set G)).subgroupOf Q).Normal]
    [IsElementaryAbelian 2 (Q ⧸ (Q ⊓ centralizer (U : Set G)).subgroupOf Q)]
    (hn : P ≤ normalizer (Q : Set G))
    (ρ : Representation (ZMod 2) A (Additive (Q ⧸ (Q ⊓ centralizer (U : Set G)).subgroupOf Q)))
    (hρ : ∀ (p : P) (q : Q),
      ρ (π p) (Additive.ofMul (QuotientGroup.mk' _ q)) =
        Additive.ofMul (QuotientGroup.mk' _
          ⟨(p : G) * (q : G) * (p : G)⁻¹,
            (mem_normalizer_iff.mp (hn p.property) q).mp q.property⟩))
    (u : U) (hi : (centralizer ({(u : G)} : Set G)).relIndex Q = 2)
    (him : ((R ⊓ centralizer ({(u : G)} : Set G)).subgroupOf P).map π =
      (R.subgroupOf P).map π)
    (g : ι → P) (hgen : U = V ⊔ closure (Set.range fun i => MulAut.conj (g i : G) (u : G)))
    (hQV : Q ≤ centralizer (V : Set G)) :
    ∃ f : Additive (Q ⧸ (Q ⊓ centralizer (U : Set G)).subgroupOf Q) →ₗ[ZMod 2] ZMod 2,
      (∀ q : Q, f (Additive.ofMul (QuotientGroup.mk' _ q)) = 0 ↔
        (q : G) ∈ centralizer ({(u : G)} : Set G)) ∧
      (∀ a ∈ (R.subgroupOf P).map π, ∀ x, f (ρ a x) = f x) ∧
      (∀ x, (∀ a, f (ρ a x) = 0) → x = 0) := by
  obtain ⟨f,hf⟩ := exists_functional Q U u hi
  refine ⟨f,hf,?_,?_⟩
  · intro a ha x
    obtain ⟨p,hp,hpa⟩ := (him.symm ▸ ha)
    obtain ⟨q,hqx⟩ := QuotientGroup.mk'_surjective
      ((Q ⊓ centralizer (U : Set G)).subgroupOf Q) x.toMul
    change Additive.ofMul (QuotientGroup.mk' _ q) = x at hqx
    rw [← hqx, ← hpa, hρ]
    apply (show ∀ a b : ZMod 2, (a = 0 ↔ b = 0) → a = b by decide)
    rw [hf,hf]
    exact (mem_normalizer_iff.mp ((centralizer ({(u : G)} : Set G)).le_normalizer hp.2) q).symm
  · intro x hx
    obtain ⟨q,hqx⟩ := QuotientGroup.mk'_surjective
      ((Q ⊓ centralizer (U : Set G)).subgroupOf Q) x.toMul
    change Additive.ofMul (QuotientGroup.mk' _ q) = x at hqx
    rw [← hqx] at hx ⊢
    apply (QuotientGroup.eq_one_iff q).mpr
    change (q : G) ∈ Q ⊓ centralizer (U : Set G)
    rw [inf_centralizer_eq_of_generated V Q U _ hgen hQV]
    refine ⟨q.property,mem_iInf.mpr fun i => ?_⟩
    have hz := hx (π (g i)⁻¹)
    rw [hρ] at hz
    have hc := (hf _).mp hz
    have hh : Commute ((g i : G)⁻¹ * (q : G) * (g i : G)) (u : G) := by
      change _ * _ = _ * _
      simpa only [Subgroup.coe_inv,inv_inv] using mem_centralizer_singleton_iff.mp hc
    have hm := hh.map (MulAut.conj (g i : G))
    apply mem_centralizer_singleton_iff.mpr
    simpa only [MulAut.conj_apply, mul_assoc, mul_inv_cancel_left,
      inv_mul_cancel_left, mul_inv_cancel_right, mul_inv_cancel, mul_one] using hm.eq

end Representation.CentralizerCosetEmbedding
