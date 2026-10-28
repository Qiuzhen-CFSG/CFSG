module

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.LinearReduction.Orthogonal.Quotient.Selection
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.LinearReduction.Orthogonal.Quotient.B4Extraction.ComponentInputs
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.LinearReduction.Orthogonal.Quotient.B4Extraction.IndexTwo
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.LinearReduction.Orthogonal.Quotient.B4Extraction.SplitActor
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.LinearReduction.Orthogonal.Quotient.B4Extraction.SplitModels
public import Theory.Representation.BinaryOffender.QuadraticQuotient
public import Theory.Representation.BinaryOffender.CodimensionSieve
public import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple

/-!
# Preparing the literal quotient for B.4 in 13.8.25

The rank-two image of V₃/V₁, with its L₁ commutator equality, forces the
marked A₈ component to act nontrivially. The normal-subgroup theorem for S₈
then proves faithfulness. The original Uγ* actor remains elementary and
quadratic on the literal maximal quotient, with no increase of fixed
codimension. Selection uses the genuine conjugation action on Source.Utilde.

The component-irreducible branch can use the exact universal B.4 input.
The other branch has the two exchanged summands constructed in IndexTwo;
passing the quadratic bound to a faithful constituent and identifying the
resulting natural-plus-dual model are remaining obligations. Thus this module
does not yet assert the requested complete representation alternatives.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), 13.8.8(2),
13.8.21(1) and the proof of 13.8.25, printed pp.949,955,959–960;
B.4.2 and B.4.5, printed pp.86–87.
-/

@[expose] public section

namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.LinearReduction.OrthogonalQuotient.B4Extraction
open Representation Representation.BinaryOffender
open FourStructure FourStructure.ChiefFactors

universe v
variable {H : Type*} {U : Type v} [Group H] [AddCommGroup U] [Module (ZMod 2) U]

/-- The marked alternating component has index two in the actual actor. -/
theorem marked_component_index_two (eH : H ≃* Equiv.Perm (Fin 8))
    (K : Subgroup H) (hK : K.map eH.toMonoidHom = alternatingGroup (Fin 8)) :
    K.index = 2 := by
  rw [← K.index_map_equiv eH]
  change (K.map eH.toMonoidHom).index = 2
  rw [hK]
  exact alternatingGroup.index_eq_two

/-- Normality is in H*, and no source monolith assumption is added. -/
theorem marked_component_monolith (eH : H ≃* Equiv.Perm (Fin 8))
    (K : Subgroup H) (hK : K.map eH.toMonoidHom = alternatingGroup (Fin 8))
    (N : Subgroup H) (hn : N.Normal) (hne : N ≠ ⊥) : K ≤ N := by
  let : (N.map eH.toMonoidHom).Normal := hn.map eH.toMonoidHom eH.surjective
  have hne' : N.map eH.toMonoidHom ≠ ⊥ := by
    intro he
    exact hne ((N.map_eq_bot_iff_of_injective eH.injective).mp he)
  have hle := Equiv.Perm.alternatingGroup_le_of_normal (α := Fin 8) (by simp)
    ((N.map eH.toMonoidHom).nontrivial_iff_ne_bot.mpr hne')
  intro k hk
  obtain ⟨n, hn, he⟩ := hle (hK ▸ Subgroup.mem_map_of_mem eH.toMonoidHom hk)
  exact eH.injective he ▸ hn

/-- A nonzero commutator seed forces faithfulness of the S₈ action. -/
theorem faithful_of_marked_seed (ρ : Representation (ZMod 2) H U)
    (eH : H ≃* Equiv.Perm (Fin 8)) (K L : Subgroup H)
    (hK : K.map eH.toMonoidHom = alternatingGroup (Fin 8)) (hLK : L ≤ K)
    (S : Submodule (ZMod 2) U) (hdim : Module.finrank (ZMod 2) S = 2)
    (hcomm : subspaceCommutator ρ S L = S) : Function.Injective ρ := by
  apply faithful_of_nontrivial_on_monolith ρ K (marked_component_monolith eH K hK)
  by_contra! hn
  have hzero : subspaceCommutator ρ S L = ⊥ :=
    (subspaceCommutator_eq_bot_iff ρ S L).mpr (fun v _ l => hn l (hLK l.property) v)
  rw [hcomm] at hzero
  rw [hzero, finrank_bot] at hdim
  omega

/-- Quadraticity descends without replacing the actor by a different subgroup. -/
theorem quadratic_quotient (ρ : Representation (ZMod 2) H U)
    (W : Subrepresentation ρ) (A : Subgroup H) (hq : IsQuadratic ρ A) :
    IsQuadratic W.quotientRepresentation A :=
  quadratic_of_equivariant_surjection ρ W.quotientRepresentation
    W.toSubmodule.mkQ W.toSubmodule.mkQ_surjective (fun _ _ => rfl) A hq

/-- The original actor's small fixed-codimension bound survives the quotient. -/
theorem quotient_bound [FiniteDimensional (ZMod 2) U]
    (ρ : Representation (ZMod 2) H U) (W : Subrepresentation ρ) (A : Subgroup H)
    (hb : fixedCodim ρ A ≤ 2 * rank A) :
    fixedCodim W.quotientRepresentation A ≤ 2 * rank A :=
  (fixedCodim_le_of_equivariant_surjection ρ W.quotientRepresentation
    W.toSubmodule.mkQ W.toSubmodule.mkQ_surjective (fun _ _ => rfl) A).trans hb

/-- B.4 is applied only in its component-irreducible case. Otherwise the
restriction is genuinely split, rather than assumed irreducible. Identifying
the exchanged summands with natural and dual remains a separate obligation. -/
theorem natural_or_restrictionSplit [FiniteDimensional (ZMod 2) U]
    (ρ : Representation (ZMod 2) H U)
    (eH : H ≃* Equiv.Perm (Fin 8)) (K : Subgroup H)
    (hK : K.map eH.toMonoidHom = alternatingGroup (Fin 8))
    (hf : Function.Injective ρ) (hi : IsIrreducible ρ)
    (A : Subgroup H) (hA : IsElementaryTwo A) (hq : IsQuadratic ρ A)
    (hb : fixedCodim ρ A ≤ 2 * rank A) (hB4 : SymmetricB4.{v} K eH) :
    IsEightNatural ρ eH ∨ Nonempty (RestrictionSplit ρ K) := by
  classical
  by_cases hr : IsIrreducible (ρ.comp K.subtype)
  · exact Or.inl (hB4 U ρ hf hr A hA hq hb)
  · have hk := marked_component_index_two eH K hK
    let : K.Normal := K.normal_of_index_eq_two hk
    exact Or.inr (exists_restrictionSplit ρ K hk hi hr)

/-- The complete B.4 alternative for an irreducible ambient module.  In the
split branch the original actor is first placed inside the marked component;
only then is B.4 applied to the literal irreducible constituent.  The
constituent's model is assembled back across the two exchanged summands. -/
theorem representation_alternatives [Finite H] [FiniteDimensional (ZMod 2) U]
    (ρ : Representation (ZMod 2) H U)
    (eH : H ≃* Equiv.Perm (Fin 8)) (K : Subgroup H)
    (hK : K.map eH.toMonoidHom = alternatingGroup (Fin 8))
    (eK : K ≃* BinaryLinear.GL FourSpace)
    (hf : Function.Injective ρ) (hi : IsIrreducible ρ)
    (A : Subgroup H) (hA : IsElementaryTwo A) (hq : IsQuadratic ρ A)
    (hb : fixedCodim ρ A ≤ 2 * rank A)
    (hSym : SymmetricB4.{v} K eH)
    (hComp : ComponentB4.{v} K eH eK) :
    IsEightNatural ρ eH ∨ IsNaturalDualRestriction ρ K eK := by
  rcases natural_or_restrictionSplit ρ eH K hK hf hi A hA hq hb hSym with h | h
  · exact Or.inl h
  · obtain ⟨d⟩ := h
    have hp := d.actor_prerequisites ρ K eH hK hf A hA hq hb
    have hleft : IsIrreducible d.left.toRepresentation :=
      (Subrepresentation.irreducible_iff_isAtom _).mpr d.left_atom
    have hc := hComp (E := d.left.toSubmodule) d.left.toRepresentation hp.2.2.1 hleft
      (A.subgroupOf K) hp.2.2.2.1 hp.2.2.2.2.1 hp.2.2.2.2.2
    exact Or.inr (SplitModels.naturalDualRestriction_of_constituent_alternatives
      d hi eH hK eK hc)

open scoped IsMulCommutative

/-- The selected literal quotient has every ambient B.4 action hypothesis,
and retains the seed needed by the parent's marked obstruction. The A₈
restriction still needs the case distinction in natural_or_restrictionSplit. -/
theorem exists_source_faithful_quadratic_quotient
    {G : Type*} [Group G] [Finite G] (H V₃ V₁ Uγ : Subgroup G)
    [(V₁.subgroupOf (Source.UH H V₃)).Normal]
    [IsElementaryAbelian 2 (Source.Utilde H V₃ V₁)]
    (τ : Representation (ZMod 2) (Source.Hstar H) (SourceSpace H V₃ V₁))
    (hτ : IsSourceAction H V₃ V₁ τ)
    (eH : Source.Hstar H ≃* Equiv.Perm (Fin 8))
    (K P T L₁ : Subgroup (Source.Hstar H))
    (hK : K.map eH.toMonoidHom = alternatingGroup (Fin 8)) (hLK : L₁ ≤ K)
    (hTP : T ≤ P) (hT : IsPGroup 2 T)
    (hstable : ∀ g : P, ∀ v ∈ sourceSeedSpace H V₃ V₁, τ g v ∈ sourceSeedSpace H V₃ V₁)
    (hirr : IsAtom (⟨sourceSeedSpace H V₃ V₁, hstable⟩ : Subrepresentation (τ.comp P.subtype)))
    (hdim : Module.finrank (ZMod 2) (sourceSeedSpace H V₃ V₁) = 2)
    (hcomm : subspaceCommutator τ (sourceSeedSpace H V₃ V₁) L₁ = sourceSeedSpace H V₃ V₁)
    (hA : IsElementaryTwo (Source.starImage H Uγ))
    (hq : IsQuadratic τ (Source.starImage H Uγ))
    (hb : fixedCodim τ (Source.starImage H Uγ) ≤ 2 * rank (Source.starImage H Uγ)) :
    ∃ W : Subrepresentation τ, IsCoatom W ∧ W.quotientRepresentation.IsIrreducible ∧
      Function.Injective W.quotientRepresentation ∧
      IsElementaryTwo (Source.starImage H Uγ) ∧
      IsQuadratic W.quotientRepresentation (Source.starImage H Uγ) ∧
      fixedCodim W.quotientRepresentation (Source.starImage H Uγ) ≤
        2 * rank (Source.starImage H Uγ) ∧
      Module.finrank (ZMod 2) ((sourceSeedSpace H V₃ V₁).map W.toSubmodule.mkQ) = 2 ∧
      (∀ g : P, ∀ v ∈ (sourceSeedSpace H V₃ V₁).map W.toSubmodule.mkQ,
        W.quotientRepresentation g v ∈ (sourceSeedSpace H V₃ V₁).map W.toSubmodule.mkQ) ∧
      subspaceCommutator W.quotientRepresentation
        ((sourceSeedSpace H V₃ V₁).map W.toSubmodule.mkQ) L₁ =
        (sourceSeedSpace H V₃ V₁).map W.toSubmodule.mkQ := by
  obtain ⟨W, hW, hi, hd, hs, hc⟩ := exists_source_maximal_quotient
    H V₃ V₁ τ hτ P T L₁ hTP hT hstable hirr hdim hcomm
  exact ⟨W, hW, hi,
    faithful_of_marked_seed W.quotientRepresentation eH K L₁ hK hLK _ hd hc,
    hA, quadratic_quotient τ W _ hq, quotient_bound τ W _ hb, hd, hs, hc⟩

/-- Apply the two B.4 inputs to the literal maximal quotient selected from the
source conjugation action. The displayed disjunction is still before the
marked middle-node obstruction, so the natural-plus-dual branch is retained. -/
theorem exists_source_representation_alternatives
    {G : Type v} [Group G] [Finite G] (H V₃ V₁ Uγ : Subgroup G)
    [(V₁.subgroupOf (Source.UH H V₃)).Normal]
    [IsElementaryAbelian 2 (Source.Utilde H V₃ V₁)]
    (τ : Representation (ZMod 2) (Source.Hstar H) (SourceSpace H V₃ V₁))
    (hτ : IsSourceAction H V₃ V₁ τ)
    (eH : Source.Hstar H ≃* Equiv.Perm (Fin 8))
    (K P T L₁ : Subgroup (Source.Hstar H))
    (hK : K.map eH.toMonoidHom = alternatingGroup (Fin 8)) (hLK : L₁ ≤ K)
    (hTP : T ≤ P) (hT : IsPGroup 2 T)
    (hstable : ∀ g : P, ∀ v ∈ sourceSeedSpace H V₃ V₁,
      τ g v ∈ sourceSeedSpace H V₃ V₁)
    (hirr : IsAtom (⟨sourceSeedSpace H V₃ V₁, hstable⟩ :
      Subrepresentation (τ.comp P.subtype)))
    (hdim : Module.finrank (ZMod 2) (sourceSeedSpace H V₃ V₁) = 2)
    (hcomm : subspaceCommutator τ (sourceSeedSpace H V₃ V₁) L₁ =
      sourceSeedSpace H V₃ V₁)
    (hA : IsElementaryTwo (Source.starImage H Uγ))
    (hq : IsQuadratic τ (Source.starImage H Uγ))
    (hb : fixedCodim τ (Source.starImage H Uγ) ≤
      2 * rank (Source.starImage H Uγ))
    (eK : K ≃* BinaryLinear.GL FourSpace)
    (hSym : SymmetricB4.{v} K eH)
    (hComp : ComponentB4.{v} K eH eK) :
    ∃ W : Subrepresentation τ, IsCoatom W ∧
      W.quotientRepresentation.IsIrreducible ∧
      Function.Injective W.quotientRepresentation ∧
      IsElementaryTwo (Source.starImage H Uγ) ∧
      IsQuadratic W.quotientRepresentation (Source.starImage H Uγ) ∧
      fixedCodim W.quotientRepresentation (Source.starImage H Uγ) ≤
        2 * rank (Source.starImage H Uγ) ∧
      Module.finrank (ZMod 2)
          ((sourceSeedSpace H V₃ V₁).map W.toSubmodule.mkQ) = 2 ∧
      (∀ g : P, ∀ v ∈ (sourceSeedSpace H V₃ V₁).map W.toSubmodule.mkQ,
        W.quotientRepresentation g v ∈
          (sourceSeedSpace H V₃ V₁).map W.toSubmodule.mkQ) ∧
      subspaceCommutator W.quotientRepresentation
          ((sourceSeedSpace H V₃ V₁).map W.toSubmodule.mkQ) L₁ =
        (sourceSeedSpace H V₃ V₁).map W.toSubmodule.mkQ ∧
      (IsEightNatural W.quotientRepresentation eH ∨
        IsNaturalDualRestriction W.quotientRepresentation K eK) := by
  obtain ⟨W, hW, hi, hf, hA', hq', hb', hd, hs, hc⟩ :=
    exists_source_faithful_quadratic_quotient H V₃ V₁ Uγ τ hτ eH K P T L₁
      hK hLK hTP hT hstable hirr hdim hcomm hA hq hb
  refine ⟨W, hW, hi, hf, hA', hq', hb', hd, hs, hc, ?_⟩
  exact representation_alternatives W.quotientRepresentation eH K hK eK hf hi
    (Source.starImage H Uγ) hA' hq' hb' hSym hComp

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.LinearReduction.OrthogonalQuotient.B4Extraction
