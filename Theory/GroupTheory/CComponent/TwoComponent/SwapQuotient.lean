module
public import Theory.GroupTheory.CComponent.TwoComponent.PairQuotient
public import Theory.GroupTheory.InvolutiveFactorSwap
public import Theory.GroupAction.AutomorphismFixedTransport

/-!
# Involutions swapping two component quotients

The source core is characteristic, so automorphisms descend to its quotient.
The marked product coordinates force a swapping automorphism to exchange
the two quotient factors. The fixed-subgroup equivalence is then the
existing full-diagonal theorem `fixedSubgroupEquivLeftOfSwapsFactors`,
transported back along the constructed product equivalence.

We also retain the literal map from the original fixed subgroup to the
fixed subgroup of the quotient. Component preservation under this map is
a separate balance assertion, not assumed in the product or diagonal proof.

Source: Aschbacher–Smith I.3.2, printed p.415 (1 March 2004 manuscript).
-/

@[expose] public section
open Subgroup Theory.GroupTheory
namespace MulAut
variable {G : Type*} [Group G]

/-- The induced automorphism on the literal source quotient. -/
def oddTwoCoreQuotientAut (σ : MulAut G) : MulAut (G ⧸ oddTwoCore G) :=
  QuotientGroup.congr _ _ σ (oddTwoCore_map_equiv σ)

theorem oddTwoCoreQuotientAut_mk (σ : MulAut G) (g : G) :
    oddTwoCoreQuotientAut σ (QuotientGroup.mk' (oddTwoCore G) g) =
      QuotientGroup.mk' (oddTwoCore G) (σ g) := rfl

theorem oddTwoCoreQuotientAut_involutive (σ : MulAut G) (hσ : Function.Involutive σ) :
    Function.Involutive (oddTwoCoreQuotientAut σ) := by
  intro x
  obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective (oddTwoCore G) x
  simp only [oddTwoCoreQuotientAut_mk]
  exact congrArg (QuotientGroup.mk' (oddTwoCore G)) (hσ g)

/-- The marked component embeddings force the induced action to exchange coordinates. -/
theorem oddTwoCoreQuotient_swap_coordinates {L K : Subgroup G} (σ : MulAut G)
    (hLK : L.map σ.toMonoidHom = K) (hKL : K.map σ.toMonoidHom = L)
    (e : (G ⧸ oddTwoCore G) ≃* (L ⧸ oddTwoCore L) × (K ⧸ oddTwoCore K))
    (heL : ∀ l : L, e (QuotientGroup.mk' (oddTwoCore G) l.val) =
      (QuotientGroup.mk' (oddTwoCore L) l, 1))
    (heK : ∀ k : K, e (QuotientGroup.mk' (oddTwoCore G) k.val) =
      (1, QuotientGroup.mk' (oddTwoCore K) k)) :
    (∀ a : L ⧸ oddTwoCore L,
      (MulAut.congr e (oddTwoCoreQuotientAut σ) (a, 1)).1 = 1) ∧
    (∀ b : K ⧸ oddTwoCore K,
      (MulAut.congr e (oddTwoCoreQuotientAut σ) (1, b)).2 = 1) := by
  constructor
  · intro a
    obtain ⟨l, rfl⟩ := QuotientGroup.mk'_surjective (oddTwoCore L) a
    have hl : σ l.val ∈ K := hLK ▸ mem_map_of_mem σ.toMonoidHom l.property
    change (e (oddTwoCoreQuotientAut σ
      (e.symm (QuotientGroup.mk' (oddTwoCore L) l, 1)))).1 = 1
    rw [← heL l, e.symm_apply_apply, oddTwoCoreQuotientAut_mk]
    exact congrArg Prod.fst (heK ⟨σ l.val, hl⟩)
  · intro b
    obtain ⟨k, rfl⟩ := QuotientGroup.mk'_surjective (oddTwoCore K) b
    have hk : σ k.val ∈ L := hKL ▸ mem_map_of_mem σ.toMonoidHom k.property
    change (e (oddTwoCoreQuotientAut σ
      (e.symm (1, QuotientGroup.mk' (oddTwoCore K) k)))).2 = 1
    rw [← heK k, e.symm_apply_apply, oddTwoCoreQuotientAut_mk]
    exact congrArg Prod.snd (heL ⟨σ k.val, hk⟩)

/-- The literal map from the original fixed subgroup to the quotient fixed subgroup. -/
def oddTwoCoreFixedMap (σ : MulAut G) :
    σ.fixedSubgroup →* (oddTwoCoreQuotientAut σ).fixedSubgroup where
  toFun x := ⟨QuotientGroup.mk' (oddTwoCore G) x.val, by
    rw [mem_fixedSubgroup]
    rw [oddTwoCoreQuotientAut_mk, (mem_fixedSubgroup σ x.val).mp x.property]⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' x y := Subtype.ext (map_mul _ x.val y.val)

theorem oddTwoCoreFixedMap_apply (σ : MulAut G) (x : σ.fixedSubgroup) :
    (oddTwoCoreFixedMap σ x : G ⧸ oddTwoCore G) =
      QuotientGroup.mk' (oddTwoCore G) x.val := rfl

variable [Finite G]

/-- The source quotient centralizer of a swapped pair is its full simple diagonal.
The product equivalence and its coordinate equations are constructed from the components. -/
noncomputable def fixedOddTwoCoreQuotientEquivLeftOfSwap
    {L K : Subgroup G} (hL : L.IsTwoComponent) (hK : K.IsTwoComponent)
    (hne : L ≠ K) (hgen : L ⊔ K = ⊤)
    [Group.IsSolvable (pPrimeCore 2 G)]
    [Group.IsSolvable (pPrimeCore 2 L)] [Group.IsSolvable (pPrimeCore 2 K)]
    (σ : MulAut G) (hσ : Function.Involutive σ)
    (hLK : L.map σ.toMonoidHom = K) (hKL : K.map σ.toMonoidHom = L) :
    (oddTwoCoreQuotientAut σ).fixedSubgroup ≃* (L ⧸ oddTwoCore L) := by
  classical
  let hex := exists_oddTwoCore_quotient_prod_of_sup_eq_top hL hK hne hgen
  let e := Classical.choose hex
  have heL := (Classical.choose_spec hex).1
  have heK := (Classical.choose_spec hex).2
  let β := oddTwoCoreQuotientAut σ
  let τ := MulAut.congr e β
  have hτ : Function.Involutive τ := by
    intro x
    change e (β (e.symm (e (β (e.symm x))))) = x
    rw [e.symm_apply_apply]
    exact (congrArg e (oddTwoCoreQuotientAut_involutive σ hσ (e.symm x))).trans
      (e.apply_symm_apply x)
  obtain ⟨hA, hB⟩ := oddTwoCoreQuotient_swap_coordinates σ hLK hKL e heL heK
  have hf : τ.fixedSubgroup = τ.toMonoidHom.eqLocus (MonoidHom.id _) := by
    ext x
    exact mem_fixedSubgroup τ x
  exact (fixedSubgroupCongr e β).trans ((MulEquiv.subgroupCongr hf).trans
    (fixedSubgroupEquivLeftOfSwapsFactors τ hτ hA hB))

end MulAut

namespace MulAut
variable {G : Type*} [Group G]

/-- Restrict an ambient swapping involution to the actual join, retaining
both component markings and the original action on each element. -/
theorem exists_involutive_swap_on_join (σ : MulAut G) (hσ : Function.Involutive σ)
    {A B : Subgroup G} (hAB : A.map σ.toMonoidHom = B) :
    ∃ τ : MulAut ↥(A ⊔ B), Function.Involutive τ ∧
      (A.subgroupOf (A ⊔ B)).map τ.toMonoidHom = B.subgroupOf (A ⊔ B) ∧
      (B.subgroupOf (A ⊔ B)).map τ.toMonoidHom = A.subgroupOf (A ⊔ B) ∧
      ∀ x : ↥(A ⊔ B), (τ x : G) = σ x.val := by
  have hcomp : σ.toMonoidHom.comp σ.toMonoidHom = MonoidHom.id G :=
    MonoidHom.ext hσ
  have hBA : B.map σ.toMonoidHom = A := by
    rw [← hAB, map_map, hcomp, map_id]
  have hsup : (A ⊔ B).map σ.toMonoidHom = A ⊔ B := by
    rw [Subgroup.map_sup, hAB, hBA, sup_comm]
  let τ : MulAut ↥(A ⊔ B) :=
    (σ.subgroupMap (A ⊔ B)).trans (MulEquiv.subgroupCongr hsup)
  have hτx (x : ↥(A ⊔ B)) : (τ x : G) = σ x.val := rfl
  have he : (A ⊔ B).subtype.comp τ.toMonoidHom =
      σ.toMonoidHom.comp (A ⊔ B).subtype := rfl
  refine ⟨τ, ?_, ?_, ?_, hτx⟩
  · intro x
    apply Subtype.ext
    exact hσ x.val
  · apply map_injective (A ⊔ B).subtype_injective
    rw [map_map, he, ← map_map, map_subgroupOf_eq_of_le le_sup_left,
      hAB, map_subgroupOf_eq_of_le le_sup_right]
  · apply map_injective (A ⊔ B).subtype_injective
    rw [map_map, he, ← map_map, map_subgroupOf_eq_of_le le_sup_right,
      hBA, map_subgroupOf_eq_of_le le_sup_left]

end MulAut
