module
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantLarge.A315Source.OrderSieve
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantLarge.A315Source.EvenSource


/-!
# The remaining actual models for the invariant large-prime branch

Genuine Theorem C is applied to the original simple normal component in the
faithful SQTK ambient group. The nonbinary even action calculations and
certified order sieve eliminate every completed row and retain exactly the
odd linear/unitary families and seven exceptional finite possibilities.
The surviving symplectic row already has the actual plane, whole component,
parameter restrictions and cyclic automizer. Its output is transported to
the original complement and normalizer action in SylowInput.

The remaining constructors are literal group models, not assumed local
classification conclusions. Their odd-characteristic and exceptional finite
source proofs are separate leaves used by the final p > 3 assembly.
Source: Aschbacher–Smith A.3.15, pp.50–51, and 1.3.4, pp.510–511.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter1.XiEmbedding.InvariantLarge.A315Source
open Section02.LocalModels ClassificationModels
universe u v

section SmallEndpoints
variable {J : Type*} [Group J] {D B : Subgroup J} {S : Sylow 2 J} {p : ℕ}
/-- The small rank-two dispatch leaves only genuine triality(2) and Tits. -/
theorem small_rankTwo_triality_or_tits
    (hA : OddCartan.AmbientInput KnownSimple.IsKnownSimple D B S p)
    (hB : SourceTransport.PairAction p (S : Subgroup J) B)
    (hm : SmallRankTwoModel D) :
    Triality.Standard.IsTrialityGroupAt 2 D ∨ Nonempty (D ≃* Tits.ParrottGroup) := by
  rcases hm with hm | hm | hm | hm | hm
  · exact (not_binary_linear hA hB 3 (Or.inl rfl) hm).elim
  · exact Or.inl hm
  · exact (not_symplectic_derived hA hB hm).elim
  · exact (not_g2_derived hA hB hm).elim
  · exact Or.inr hm

end SmallEndpoints

/-- The unproved rows are retained as actual models, not as local action assumptions. -/
inductive RemainingModels (D : Type*) [Group D] : Prop
  | linearTwo (q e : ℕ) (hq : q.Prime) (ho : Odd q)
      (he : e=1 ∨ e=2) (hs : 4 ≤ q^e) (hm : ClassicalGroup.IsPSL D 2 (q^e))
  | oddThree (q : ℕ) (hq : q.Prime) (ho : Odd q) (unitary : Bool)
      (hm : IsPSLSign D unitary 3 q)
  | sporadic (name : SporadicName)
      (hname : name=.j2 ∨ name=.j4 ∨ name=.hs ∨ name=.he ∨ name=.ru)
      (hm : Nonempty (D ≃* name.Carrier))
  | triality (hm : Triality.Standard.IsTrialityGroupAt 2 D)
  | tits (hm : Nonempty (D ≃* Tits.ParrottGroup))

/-- The genuine full Theorem C catalogue, with all nonbinary even and
order-square exclusions discharged in the original ambient action. -/
theorem alternative_or_remaining
    (hC : ∀ (Y : Type u) [Group Y] [Finite Y],
      ChapterA.Section02.TheoremC KnownSimple.IsKnownSimple Y)
    {J : Type u} [Group J] [Finite J]
    {Q : Type v} [Group Q] [Finite Q] [Group.IsPerfect Q]
    {D B : Subgroup J} [D.Normal] {S : Sylow 2 J} {p : ℕ}
    (eQ : Q ⧸ center Q ≃* D)
    (hA : OddCartan.AmbientInput KnownSimple.IsKnownSimple D B S p)
    (hB : SourceTransport.PairAction p (S : Subgroup J) B)
    (hcent : centralizer (D : Set J) = ⊥) :
    (Nonempty (B ≃* Plane p) ∧ SymplecticModel p Q ∧ IsCyclic (automizer S B)) ∨
      RemainingModels D := by
  let : IsSimpleGroup D := hA.simple
  let : Group.IsPerfect (Q ⧸ center Q) :=
    Group.IsPerfect.ofSurjective (QuotientGroup.mk'_surjective _)
  let : Group.IsPerfect D := Group.IsPerfect.ofSurjective (f := eQ.toMonoidHom) eQ.surjective
  have hna := Group.IsPerfect.not_isMulCommutative D
  have hD := hA.sqtk.subgroup D
  have hm := ChapterA.Section03.SourceComponents.sourceTheoremC_to_local hna
    ((hC D) inferInstance hna hD.stronglyQuasithin hD.isKGroup)
  cases hm with
  | alternating n hn he => exact (not_alternating hA hB n hn he).elim
  | linear_odd q e hq ho he hs hm => exact Or.inr (.linearTwo q e hq ho he hs hm)
  | three_odd q hq ho unitary hm => exact Or.inr (.oddThree q hq ho unitary hm)
  | rank_one hm => exact (not_rank_one hA hB hna hm).elim
  | rank_two hm =>
    rcases rankTwo_alternative_or_small eQ hA hB hcent hm with ha | hm
    · exact Or.inl ha
    · rcases small_rankTwo_triality_or_tits hA hB hm with ht | ht
      · exact Or.inr (.triality ht)
      · exact Or.inr (.tits ht)
  | binary_linear n hn hm =>
    exact (not_binary_linear hA hB n (Or.inr hn) hm).elim
  | sporadic name hne hm =>
    cases name with
    | m11 => exact (not_mathieu hA hB .m11 (by tauto) hm).elim
    | m12 => exact (not_mathieu hA hB .m12 (by tauto) hm).elim
    | m22 => exact (not_mathieu hA hB .m22 (by tauto) hm).elim
    | m23 => exact (not_mathieu hA hB .m23 (by tauto) hm).elim
    | m24 => exact (not_mathieu hA hB .m24 (by tauto) hm).elim
    | j2 => exact Or.inr (.sporadic .j2 (by tauto) hm)
    | j3 => exact (hne rfl).elim
    | j4 => exact Or.inr (.sporadic .j4 (by tauto) hm)
    | hs => exact Or.inr (.sporadic .hs (by tauto) hm)
    | he => exact Or.inr (.sporadic .he (by tauto) hm)
    | ru => exact Or.inr (.sporadic .ru (by tauto) hm)
  | janko_one hm => exact (not_janko_one hA hB hm).elim
end CFSG.Quasithin.Chapter1.XiEmbedding.InvariantLarge.A315Source

namespace CFSG.Quasithin.Chapter1.XiEmbedding.InvariantLarge
universe u
variable
    (hA : ∀ (Y : Type u) [Group Y] [Finite Y],
      ChapterA.Section02.TheoremA KnownSimple.IsKnownSimple Y)
    (hC : ∀ (Y : Type u) [Group Y] [Finite Y],
      ChapterA.Section02.TheoremC KnownSimple.IsKnownSimple Y)
variable {G : Type u} [Group G] [Finite G]
variable {p : ℕ} {T X P H L : Subgroup G}
include hA hC

/-- The actual quotient action from the original invariant component has the
full symplectic conclusion or one of the remaining explicit source models. -/
theorem SylowInput.alternatives_or_remaining_models
    (h : SylowInput KnownSimple.IsKnownSimple p T X P H L) (hp : 3 < p) :
    Alternatives p T P L ∨ A315Source.RemainingModels (SourceTransport.component h) := by
  let hi := h.a315Input hA hC hp
  let : (SourceTransport.component h).Normal := SourceTransport.component_normal h
  let : IsQuasisimple (XiQuotient L) := h.component_quasisimple
  rcases A315Source.alternative_or_remaining hC
      (SourceTransport.simpleComponentEquiv h) hi
      (SourceTransport.complement_pairAction h hA hC hp)
      (SourceTransport.component_centralizer h) with ⟨hplane, hmodel, hcyc⟩ | hm
  · left
    let hf := SourceTransport.complementMap_injective h hA hC hp
    let eB := SourceTransport.complementEquiv (SourceTransport.ambientMap h)
      (h.complement_le_component.trans le_sup_left) hf
    refine ⟨hplane.map (fun j => eB.trans j), Or.inr ⟨h.component_invariant,
      Or.inr (Or.inl ⟨hmodel, ?_⟩)⟩⟩
    rw [SourceTransport.sylow_eq_image] at hcyc
    exact SourceTransport.automizer_cyclic_of_image (SourceTransport.ambientMap h)
      (h.complement_le_component.trans le_sup_left) le_sup_right hf hcyc
  · exact Or.inr hm
end CFSG.Quasithin.Chapter1.XiEmbedding.InvariantLarge
