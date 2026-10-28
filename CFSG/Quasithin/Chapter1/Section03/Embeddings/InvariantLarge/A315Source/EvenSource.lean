module
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantLarge.A315Source.EvenConsequences
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantLarge.Source


/-!
# Actual rank-two source dispatch without A.3.15 case existence

The complete Theorem C rank-two list is reduced to the surviving full
symplectic model and its five literal field-two endpoints. Every nonbinary
row uses the original permuting product and Frattini action, with no Cartan
or automorphism output premise. The final theorem applies the symplectic
result to the original LocalInput, detected normal component and Sylow,
returning the original Proposition 1.3.4 Conclusion with plane, whole
component, parameter restrictions and cyclic automizer.

The field-two endpoints remain explicit actual model alternatives here;
this file does not claim the full A.3.15 catalogue. Genuine earlier A/C
supply the component quotient and faithful action transport.
Source: Aschbacher–Smith 1.3.4, pp.510–511, using A.3.15, pp.50–51.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter1.XiEmbedding.InvariantLarge.A315Source
open Section02.LocalModels

/-- The five field-two endpoints left after the nonbinary rank-two argument. -/
@[expose] def SmallRankTwoModel (D : Type*) [Group D] : Prop :=
  ClassicalGroup.IsPSL D 3 2 ∨ Triality.Standard.IsTrialityGroupAt 2 D ∨
    Nonempty (D ≃* commutator (ClassicalGroup.PSp 2 (ZMod 2))) ∨
    Nonempty (D ≃* commutator (Atlas.G2.Model (ZMod 2))) ∨
    Nonempty (D ≃* Tits.ParrottGroup)

/-- The complete rank-two catalogue reduces to its symplectic result or the
literal field-two endpoints, without a raw A.3.15 configuration. -/
theorem rankTwo_alternative_or_small
    {J Q : Type*} [Group J] [Finite J] [Group Q] [Finite Q] [Group.IsPerfect Q]
    {D B : Subgroup J} [D.Normal] {S : Sylow 2 J} {p : ℕ}
    (eQ : Q ⧸ center Q ≃* D)
    (hA : OddCartan.AmbientInput KnownSimple.IsKnownSimple D B S p)
    (hB : SourceTransport.PairAction p (S : Subgroup J) B)
    (hC : centralizer (D : Set J) = ⊥)
    (hm : RankTwoTheoremC D) :
    (Nonempty (B ≃* Plane p) ∧ SymplecticModel p Q ∧ IsCyclic (automizer S B)) ∨
      SmallRankTwoModel D := by
  let : IsSimpleGroup D := hA.simple
  let : Group.IsPerfect (Q ⧸ center Q) :=
    Group.IsPerfect.ofSurjective (QuotientGroup.mk'_surjective _)
  let : Group.IsPerfect D := Group.IsPerfect.ofSurjective (f := eQ.toMonoidHom) eQ.surjective
  have hna := Group.IsPerfect.not_isMulCommutative D
  cases hm with
  | linear n hn hm =>
    by_cases hsmall : n = 1
    · right; left; simpa [hsmall] using hm
    · obtain ⟨F, _, _, hF, ⟨e⟩⟩ := hm
      exact (not_linear_even hA hB hF (by omega) e).elim
  | symplectic n hn hm =>
    obtain ⟨F, _, _, hF, ⟨e⟩⟩ := hm
    let : CharP F 2 := Theory.SpecificGroups.SymplecticFour.EvenProjective.charTwo_of_card hF
    exact Or.inl (symplectic_alternative eQ hA hB hC hF hn
      (e.trans Theory.SpecificGroups.SymplecticFour.EvenProjective.equiv.symm))
  | g2 n hn hm =>
    obtain ⟨F, _, _, hF, ⟨e⟩⟩ := hm
    exact (not_g2_even hA hB hF hn e).elim
  | triality n hn hm =>
    by_cases hsmall : n = 1
    · right; right; left; simpa [hsmall] using hm
    · obtain ⟨P, hq, ⟨e⟩⟩ := hm
      exact (not_triality_even hA hB hna P (by omega) hq e).elim
  | ree m hm he =>
    obtain ⟨d, ⟨e⟩⟩ := he
    exact (not_ree_even hA hB hna m hm (e.trans d.modelEquiv)).elim
  | symplectic_derived he => exact Or.inr (Or.inr (Or.inr (Or.inl he)))
  | g2_derived he => exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl he))))
  | tits he => exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr he))))
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

/-- A concrete symplectic central quotient gives the original large-prime
alternative with every A.3.15 placement premise discharged. -/
theorem SylowInput.alternatives_of_symplectic_source
    (h : SylowInput KnownSimple.IsKnownSimple p T X P H L) (hp : 3 < p)
    {n : ℕ} (hn : 1 < n)
    (hm : ClassicalGroup.IsPSp ((XiQuotient L) ⧸ center (XiQuotient L)) 2 (2^n)) :
    Alternatives p T P L := by
  let hi := h.a315Input hA hC hp
  let : (SourceTransport.component h).Normal := SourceTransport.component_normal h
  let : IsQuasisimple (XiQuotient L) := h.component_quasisimple
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := hm
  let : CharP F 2 := Theory.SpecificGroups.SymplecticFour.EvenProjective.charTwo_of_card hF
  let eD := (SourceTransport.simpleComponentEquiv h).symm.trans
    (e.trans Theory.SpecificGroups.SymplecticFour.EvenProjective.equiv.symm)
  obtain ⟨hplane, hmodel, hcyc⟩ := A315Source.symplectic_alternative
    (SourceTransport.simpleComponentEquiv h) hi (SourceTransport.complement_pairAction h hA hC hp)
    (SourceTransport.component_centralizer h) hF hn eD
  let hf := SourceTransport.complementMap_injective h hA hC hp
  let eB := SourceTransport.complementEquiv (SourceTransport.ambientMap h)
    (h.complement_le_component.trans le_sup_left) hf
  refine ⟨hplane.map (fun j => eB.trans j), Or.inr ⟨h.component_invariant,
    Or.inr (Or.inl ⟨hmodel, ?_⟩)⟩⟩
  rw [SourceTransport.sylow_eq_image] at hcyc
  exact SourceTransport.automizer_cyclic_of_image (SourceTransport.ambientMap h)
    (h.complement_le_component.trans le_sup_left) le_sup_right hf hcyc

/-- Literal original-source conclusion for a detected normal symplectic component. -/
theorem conclusion_of_detected_normal_symplectic
    (h : LocalInput p T X P H) (hH : IsSQTK KnownSimple.IsKnownSimple H)
    (hT : IsSylowIn 2 T H) (hL : ComponentDetection P H L)
    (hn : (L.subgroupOf H).Normal) (hp : 3 < p)
    {n : ℕ} (hdegree : 1 < n)
    (hm : ClassicalGroup.IsPSp ((XiQuotient L) ⧸ center (XiQuotient L)) 2 (2^n)) :
    Conclusion p T X P H := by
  refine Or.inr ⟨L, hL.mem, hL.quasisimple, ?_, ?_⟩
  · exact (h.complement_and_X_le_normal_component hA hC hH hL hn).2.trans (le_componentOrbit L T)
  · exact (sourceInput_of_detected_normal hA hC h hH hT hL hn).alternatives_of_symplectic_source
      hA hC hp hdegree hm
end CFSG.Quasithin.Chapter1.XiEmbedding.InvariantLarge
