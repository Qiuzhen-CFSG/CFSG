module
public import Glauberman.MaximumAbelianReplacement
public import Glauberman.PushingUpQuadraticOffender
public import Theory.SpecificGroups.SL2.MainHypothesisPair

/-!
# Maximum abelian replacement in the original rank-one group

The arbitrary original PSL2(4) quotient identifies S/O₂(H) as an elementary
four-group. Apply the sharp counting theorem to the actual central omega
V=Ω₁(Z(O₂(H))). The source natural-module lower bound therefore forces
A O₂(H)=S and makes (A intersect O₂(H))V a maximum abelian subgroup of both
S and O₂(H), of the same order as A. Its fixed-space index is exactly four.

The no-characteristic-normal condition provides a maximum abelian subgroup
outside O₂(H). The natural-module lower bound remains the explicit theorem2.9
input, owned independently. These literal conclusions feed Niles7.5's maximum
intersection selection and the initial pair in4.3.

Source: Niles, *Pushing-up in finite groups* (1979), Lemmas4.3 and7.4,
printed pp.44 and60–61.
-/

public section
open Subgroup Theory.GroupTheory
namespace Glauberman
variable {H F : Type*} [Group H] [Finite H] [Field F] [Finite F]

/-- Literal original-group specialization of Niles4.3/7.4. The marked natural
section supplies only the displayed lower fixed-space index. -/
theorem pushingUp_maximum_abelian_replacement
    (hF : Nat.card F = 4) (S : Sylow 2 H)
    (hu : Order.HasUniqueMaximalOver (S : Subgroup H) ⊤)
    (K : Subgroup H) [K.Normal]
    (e : (H ⧸ K) ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) F)
    (A : Subgroup H) (hA : A ∈ thompsonAbelianSubgroups (S : Subgroup H))
    (hlower : 4 ≤ (omegaCenterIn (pCore 2 H) ⊓ centralizer (A : Set H)).relIndex
      (omegaCenterIn (pCore 2 H))) :
    A ⊔ pCore 2 H = (S : Subgroup H) ∧
    (A ⊓ pCore 2 H) ⊔ omegaCenterIn (pCore 2 H) ∈
      thompsonAbelianSubgroups (S : Subgroup H) ∧
    (A ⊓ pCore 2 H) ⊔ omegaCenterIn (pCore 2 H) ∈
      thompsonAbelianSubgroups (pCore 2 H) ∧
    Nat.card ↥((A ⊓ pCore 2 H) ⊔ omegaCenterIn (pCore 2 H)) = Nat.card A ∧
    (A ⊓ omegaCenterIn (pCore 2 H)).relIndex (omegaCenterIn (pCore 2 H)) = 4 ∧
    ¬ omegaCenterIn (pCore 2 H) ≤ A ∧
    thompsonAbelianSubgroups (pCore 2 H) ⊆ thompsonAbelianSubgroups (S : Subgroup H) := by
  have hi : (pCore 2 H).relIndex (S : Subgroup H) = 4 := by
    rw [relIndex,index_eq_card]
    exact (Theory.SpecificGroups.SL2.sylow_twoCore_quotient_elementary_four hF S hu K e).2
  have hQS : pCore 2 H ≤ (S : Subgroup H) := pCore_isPGroup.le_sylow_of_normal S
  have hVQ : omegaCenterIn (pCore 2 H) ≤ pCore 2 H :=
    fun _ hx => ((mem_omegaCenterIn_iff _ _).mp hx).1
  have hVc : omegaCenterIn (pCore 2 H) ≤ centralizer (pCore 2 H : Set H) :=
    fun _ hx => ((mem_omegaCenterIn_iff _ _).mp hx).2.1
  obtain ⟨hgen,hS,hQ,hcard,hfix,hfamily⟩ := maximum_abelian_replacement_of_fixedIndex
    hA hQS hVQ inferInstance hVc
      (by rw [normalizer_eq_top]; exact le_top) (hi ▸ hlower)
  rw [hi] at hfix
  refine ⟨hgen,hS,hQ,hcard,hfix,?_,hfamily⟩
  intro hVA
  rw [inf_eq_right.mpr hVA,relIndex_self] at hfix
  exact (by decide : (1 : ℕ) ≠ 4) hfix

/-- The original characteristic-subgroup hypothesis supplies an outside
maximum abelian subgroup; every such subgroup has the exact replacement
needed in Niles7.5. -/
theorem pushingUp_exists_maximum_abelian_replacement
    (hF : Nat.card F = 4) (S : Sylow 2 H)
    (hu : Order.HasUniqueMaximalOver (S : Subgroup H) ⊤)
    (K : Subgroup H) [K.Normal]
    (e : (H ⧸ K) ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) F)
    (hno : NoCharacteristicNormal (S : Subgroup H))
    (hlower : ∀ A : Subgroup H, A ∈ thompsonAbelianSubgroups (S : Subgroup H) →
      ¬ A ≤ pCore 2 H →
      4 ≤ (omegaCenterIn (pCore 2 H) ⊓ centralizer (A : Set H)).relIndex
        (omegaCenterIn (pCore 2 H))) :
    (∃ A : Subgroup H, A ∈ thompsonAbelianSubgroups (S : Subgroup H) ∧ ¬ A ≤ pCore 2 H) ∧
    (∀ A : Subgroup H, A ∈ thompsonAbelianSubgroups (S : Subgroup H) → ¬ A ≤ pCore 2 H →
      A ⊔ pCore 2 H = (S : Subgroup H) ∧
      (A ⊓ pCore 2 H) ⊔ omegaCenterIn (pCore 2 H) ∈
        thompsonAbelianSubgroups (S : Subgroup H) ∧
      Nat.card ↥((A ⊓ pCore 2 H) ⊔ omegaCenterIn (pCore 2 H)) = Nat.card A ∧
      (A ⊓ omegaCenterIn (pCore 2 H)).relIndex (omegaCenterIn (pCore 2 H)) = 4 ∧
      ¬ omegaCenterIn (pCore 2 H) ≤ A) := by
  have hi : (pCore 2 H).relIndex (S : Subgroup H) = 4 := by
    rw [relIndex,index_eq_card]
    exact (Theory.SpecificGroups.SL2.sylow_twoCore_quotient_elementary_four hF S hu K e).2
  have hS : (S : Subgroup H) ≠ ⊥ := by
    intro he
    rw [he,relIndex_bot_right] at hi
    exact (by decide : (1 : ℕ) ≠ 4) hi
  have hJ := allAbelianThompson_not_le_normal (S : Subgroup H) (pCore 2 H)
    (pCore_isPGroup.le_sylow_of_normal S) hS hno
  constructor
  · by_contra hn
    apply hJ
    apply sSup_le
    intro A hA
    by_contra hout
    exact hn ⟨A,hA,hout⟩
  · intro A hA hout
    obtain ⟨hg,hS,_,hc,hi,hV,_⟩ :=
      pushingUp_maximum_abelian_replacement hF S hu K e A hA (hlower A hA hout)
    exact ⟨hg,hS,hc,hi,hV⟩
end Glauberman
