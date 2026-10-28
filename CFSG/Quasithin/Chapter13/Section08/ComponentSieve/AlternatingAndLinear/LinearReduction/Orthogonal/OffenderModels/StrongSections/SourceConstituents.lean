module

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.LinearReduction.Orthogonal.OffenderModels.StrongSections.Constituents
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.LinearReduction.Orthogonal.OffenderModels.StrongSections.SourceConstituents.ChiefFlag
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.LinearReduction.Orthogonal.OffenderModels.StrongSections.SourceConstituents.ExchangedFactors
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.LinearReduction.Orthogonal.Quotient.B4Extraction
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.LinearReduction.Orthogonal.OffenderModels.StrongSections.SourceConstituents.PairedObstruction
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.LinearReduction.Orthogonal.Quotient.B4Extraction.SplitActor
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.LinearReduction.Orthogonal.Quotient.B4Extraction.SplitModels
public import Theory.Representation.BinaryOffender.QuadraticSection

/-!
# Constructing constituents in the strong orthogonal branches

In the strong-quotient branch of 13.8.25, B.3.2 marks the entire critical actor
as the disjoint-transposition group and bounds its fixed codimension on W by
five. A chief flag in W has central factors or faithful H-actions. Quadraticity
and the bound pass to these literal sections. The mixed even/odd actor excludes
a reducible K-restriction; the universal component-irreducible B.4 input then
identifies every noncentral factor with the actual natural S₈ module.
Perfectness of K ensures that at least one factor is natural.

In the strong-submodule branch, a contained quadratic strong offender remains
strong on every literal section. Each noncentral H-chief factor is faithful.
If its K-restriction splits, the actor preserves the two summands, and B.4
applies to a faithful irreducible constituent. The compatible split-model
identification gives natural plus dual, where the quadratic displacement bound
excludes strong offenders. Thus this branch also has only central or natural
factors, and perfectness again supplies an actual natural factor.

Both universal B.4 inputs retain component irreducibility explicitly. The
source quotient and critical-action witnesses are supplied independently;
the second source specialization retains the exact 13.8.22(2) branch conditions.
No series, natural-factor occurrence or uniqueness is assumed. Recognition of
the commutator extension remains with the parent assembly.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), 13.8.21–23 and
13.8.25, printed pp.957–960; B.4.2 and B.4.5, printed pp.86–87.
-/

public section

namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.LinearReduction.OffenderModels.StrongSections.SourceConstituents
open Representation Representation.BinaryOffender BinaryPermutation
open CFSG.Quasithin.ChapterB.Offenders
open OrthogonalQuotient.B4Extraction
universe v
variable {H : Type*} {U : Type v} [Group H] [AddCommGroup U] [Module (ZMod 2) U]

/-- A noncentral factor is faithful, using normality in the actual S₈ actor. -/
theorem faithful_of_noncentral (ρ : Representation (ZMod 2) H U)
    (eH : H ≃* Perm) (K : Subgroup H)
    (hK : K.map eH.toMonoidHom = alternatingGroup (Fin 8))
    (hn : ¬ ∀ k ∈ K, ∀ v, ρ k v = v) : Function.Injective ρ := by
  apply faithful_of_nontrivial_on_monolith ρ K (marked_component_monolith eH K hK)
  simpa only [not_forall, exists_prop] using hn

variable [FiniteDimensional (ZMod 2) U]

private theorem natural_of_mixed_actor (ρ : Representation (ZMod 2) H U)
    (eH : H ≃* Perm) (K : Subgroup H)
    (hK : K.map eH.toMonoidHom = alternatingGroup (Fin 8))
    (hf : Function.Injective ρ) (hi : IsIrreducible ρ)
    (A : Subgroup H) (hA : IsElementaryTwo A) (hq : IsQuadratic ρ A)
    (hb : fixedCodim ρ A ≤ 2 * rank A) (ho : ¬ A ≤ K) (he : A ⊓ K ≠ ⊥)
    (hB4 : SymmetricB4.{v} K eH) : IsEightNatural ρ eH := by
  let : IsElementaryAbelian 2 A := hA.2
  have hk := marked_component_index_two eH K hK
  let : K.Normal := K.normal_of_index_eq_two hk
  rcases natural_or_restrictionSplit ρ eH K hK hf hi A hA hq hb hB4 with h | h
  · exact h
  · exact (not_restrictionSplit_of_mixed_actor ρ K A hk hf hq ho he h).elim

private theorem section_central_or_natural (ρ : Representation (ZMod 2) H U)
    (eH : H ≃* Perm) (K : Subgroup H)
    (hK : K.map eH.toMonoidHom = alternatingGroup (Fin 8))
    (A : Subgroup H) (hA : IsElementaryTwo A) (hq : IsQuadratic ρ A)
    (hb : fixedCodim ρ A ≤ 2 * rank A) (ho : ¬ A ≤ K) (he : A ⊓ K ≠ ⊥)
    (hB4 : SymmetricB4.{v} K eH)
    (L N : Subrepresentation ρ) (hi : IsIrreducible (sectionRepresentation ρ L N)) :
    (∀ k ∈ K, ∀ v, sectionRepresentation ρ L N k v = v) ∨
      IsEightNatural (sectionRepresentation ρ L N) eH := by
  classical
  by_cases hc : ∀ k ∈ K, ∀ v, sectionRepresentation ρ L N k v = v
  · exact Or.inl hc
  · exact Or.inr (natural_of_mixed_actor _ eH K hK
      (faithful_of_noncentral _ eH K hK hc) hi A hA
      (quadratic_section ρ L N hq) ((fixedCodim_section_le ρ L N A).trans hb) ho he hB4)

/-- Construct the flag and classify every factor under the mixed actor.
The universal B.4 input retains component irreducibility as a hypothesis. -/
theorem naturalCentralSeries_of_mixed_actor (ρ : Representation (ZMod 2) H U)
    (eH : H ≃* Perm) (K : Subgroup H)
    (hK : K.map eH.toMonoidHom = alternatingGroup (Fin 8))
    (hn : ¬ (⊤ : Submodule (ZMod 2) U) ≤ fixedSpace ρ K)
    (A : Subgroup H) (hA : IsElementaryTwo A) (hq : IsQuadratic ρ A)
    (hb : fixedCodim ρ A ≤ 2 * rank A) (ho : ¬ A ≤ K) (he : A ⊓ K ≠ ⊥)
    (hB4 : SymmetricB4.{v} K eH) : Nonempty (NaturalCentralSeries ρ K eH) := by
  obtain ⟨n, c, hm, hf, hl, hi⟩ := exists_chief_flag ρ
  exact ⟨NaturalCentralSeries.of_nontrivial ρ K eH hK hn n c hm hf hl
    (fun i hit => section_central_or_natural ρ eH K hK A hA hq hb ho he hB4
      (c i) (c (i + 1)) (hi i hit))⟩

/-- The contained strong quotient offender constructs the requested series
on W, along with the whole-actor marking and its bound of five. -/
theorem strong_quotient_series (ρ : Representation (ZMod 2) H U)
    (W : Subrepresentation ρ) (eH : H ≃* Perm) (K : Subgroup H)
    (hK : K.map eH.toMonoidHom = alternatingGroup (Fin 8))
    (hQ : IsEightNatural W.quotientRepresentation eH)
    (hn : ¬ (⊤ : Submodule (ZMod 2) W.toSubmodule) ≤ fixedSpace W.toRepresentation K)
    (A : Subgroup H) (hA : IsElementaryTwo A) (hq : IsQuadratic ρ A)
    (hb : fixedCodim ρ A ≤ 2 * rank A)
    (hstrong : ∃ B ≤ A, IsStrongOffender W.quotientRepresentation B)
    (hB4 : SymmetricB4.{v} K eH) :
    Nonempty (NaturalCentralSeries W.toRepresentation K eH) ∧
      ∃ g : Perm, A.map (conjugateMarking eH g).toMonoidHom = D 8 ∧
        rank A = 4 ∧ fixedCodim W.toRepresentation A ≤ 5 := by
  obtain ⟨g, hg, _, hr, _, hw⟩ :=
    strong_quotient_marking_and_bounds ρ W eH hQ A hA hb hstrong
  have hKg := alternating_marking_conjugate eH K hK g
  obtain ⟨ho, he⟩ := marked_D_mixed_actor (conjugateMarking eH g) K A hKg hg
  exact ⟨naturalCentralSeries_of_mixed_actor W.toRepresentation eH K hK hn A hA
    (quadratic_subrepresentation ρ W hq) (by omega) ho he hB4, g, hg, hr, hw⟩

/-- The actual noncentral sections in the second branch have faithful,
quadratic and strong actions of the same contained offender. No constituent
model or irreducibility of the restricted component action is assumed. -/
theorem strong_noncentral_section_data (ρ : Representation (ZMod 2) H U)
    (eH : H ≃* Perm) (K : Subgroup H)
    (hK : K.map eH.toMonoidHom = alternatingGroup (Fin 8))
    (A B : Subgroup H) (hBA : B ≤ A) (hq : IsQuadratic ρ A)
    (hB : IsStrongOffender ρ B) (L N : Subrepresentation ρ)
    (hn : ¬ ∀ k ∈ K, ∀ v, sectionRepresentation ρ L N k v = v) :
    Function.Injective (sectionRepresentation ρ L N) ∧
      IsQuadratic (sectionRepresentation ρ L N) B ∧
      IsStrongOffender (sectionRepresentation ρ L N) B := by
  have hqB : IsQuadratic ρ B := fun a ha b hb v => hq a (hBA ha) b (hBA hb) v
  exact ⟨faithful_of_noncentral _ eH K hK hn, quadratic_section ρ L N hqB,
    strong_on_section ρ L N B hB⟩

private theorem natural_of_strong_actor (ρ : Representation (ZMod 2) H U)
    (eH : H ≃* Perm) (K : Subgroup H)
    (hK : K.map eH.toMonoidHom = alternatingGroup (Fin 8))
    (eK : K ≃* BinaryLinear.GL OrthogonalQuotient.FourSpace)
    (hf : Function.Injective ρ) (hi : IsIrreducible ρ)
    (B : Subgroup H) (hq : IsQuadratic ρ B) (hs : IsStrongOffender ρ B)
    (hS : SymmetricB4.{v} K eH) (hC : ComponentB4.{v} K eH eK) :
    IsEightNatural ρ eH := by
  let : Finite H := Finite.of_injective eH eH.injective
  have hb : fixedCodim ρ B ≤ 2 * rank B := by
    have := hs.2
    omega
  rcases natural_or_restrictionSplit ρ eH K hK hf hi B hs.1 hq hb hS with h | hsplit
  · exact h
  · obtain ⟨d⟩ := hsplit
    obtain ⟨hBK, _, hfaith, helem, hquad, hbound⟩ :=
      d.actor_prerequisites ρ K eH hK hf B hs.1 hq hb
    have hmodel := hC d.left.toSubmodule d.left.toRepresentation hfaith
      ((Subrepresentation.irreducible_iff_isAtom d.left).mpr d.left_atom)
      (B.subgroupOf K) helem hquad hbound
    have hpair := SplitModels.naturalDualRestriction_of_constituent_alternatives
      d hi eH hK eK hmodel
    exact (not_strong_of_naturalDualRestriction ρ K B eK hpair hBK hq hs).elim

/-- A quadratic strong offender classifies all noncentral factors of a
constructed chief flag. The same offender acts faithfully on each such factor;
no irreducibility of its component restriction is assumed. -/
theorem naturalCentralSeries_of_strong_offender (ρ : Representation (ZMod 2) H U)
    (eH : H ≃* Perm) (K : Subgroup H)
    (hK : K.map eH.toMonoidHom = alternatingGroup (Fin 8))
    (eK : K ≃* BinaryLinear.GL OrthogonalQuotient.FourSpace)
    (hn : ¬ (⊤ : Submodule (ZMod 2) U) ≤ fixedSpace ρ K)
    (A B : Subgroup H) (hBA : B ≤ A) (hq : IsQuadratic ρ A)
    (hB : IsStrongOffender ρ B)
    (hS : SymmetricB4.{v} K eH) (hC : ComponentB4.{v} K eH eK) :
    Nonempty (NaturalCentralSeries ρ K eH) := by
  classical
  obtain ⟨n, c, hm, hf, hl, hi⟩ := exists_chief_flag ρ
  refine ⟨NaturalCentralSeries.of_nontrivial ρ K eH hK hn n c hm hf hl ?_⟩
  intro i hit
  by_cases hc : ∀ k ∈ K, ∀ v, sectionRepresentation ρ (c i) (c (i + 1)) k v = v
  · exact Or.inl hc
  · obtain ⟨hfaith, hquad, hstrong⟩ := strong_noncentral_section_data ρ eH K hK
      A B hBA hq hB (c i) (c (i + 1)) hc
    exact Or.inr (natural_of_strong_actor _ eH K hK eK hfaith (hi i hit)
      B hquad hstrong hS hC)

/-- Construct the series on W from a contained strong offender on W.
The classification uses the actual constituent actions and both universal
component-irreducible B.4 inputs. -/
theorem strong_submodule_series (ρ : Representation (ZMod 2) H U)
    (W : Subrepresentation ρ) (eH : H ≃* Perm) (K : Subgroup H)
    (hK : K.map eH.toMonoidHom = alternatingGroup (Fin 8))
    (eK : K ≃* BinaryLinear.GL OrthogonalQuotient.FourSpace)
    (hn : ¬ (⊤ : Submodule (ZMod 2) W.toSubmodule) ≤ fixedSpace W.toRepresentation K)
    (A : Subgroup H) (hq : IsQuadratic ρ A)
    (hstrong : ∃ B ≤ A, IsStrongOffender W.toRepresentation B)
    (hS : SymmetricB4.{v} K eH) (hC : ComponentB4.{v} K eH eK) :
    Nonempty (NaturalCentralSeries W.toRepresentation K eH) := by
  obtain ⟨B, hBA, hB⟩ := hstrong
  exact naturalCentralSeries_of_strong_offender W.toRepresentation eH K hK eK hn
    A B hBA (quadratic_subrepresentation ρ W hq) hB hS hC

open FourStructure.ChiefFactors
open scoped IsMulCommutative

/-- Specialization to the supplied conjugation action on U_H/V₁ and the
chosen maximal proper W. Neither quotient selection nor critical-pair
transport is used to manufacture these independent source witnesses. -/
theorem source_strong_quotient_series
    {G : Type v} [Group G] [Finite G] (H V₃ V₁ Uγ : Subgroup G)
    [(V₁.subgroupOf (Source.UH H V₃)).Normal]
    [IsElementaryAbelian 2 (Source.Utilde H V₃ V₁)]
    (τ : Representation (ZMod 2) (Source.Hstar H) (SourceSpace H V₃ V₁))
    (_hτ : IsSourceAction H V₃ V₁ τ)
    (W : Subrepresentation τ) (_hW : IsCoatom W)
    (eH : Source.Hstar H ≃* Perm) (Kstar : Subgroup (Source.Hstar H))
    (hK : Kstar.map eH.toMonoidHom = alternatingGroup (Fin 8))
    (hQ : IsEightNatural W.quotientRepresentation eH)
    (hKW : ∃ k ∈ Kstar, ∃ w : W.toSubmodule, W.toRepresentation k w ≠ w)
    (hA : IsElementaryTwo (Source.starImage H Uγ))
    (hq : IsQuadratic τ (Source.starImage H Uγ))
    (hb : fixedCodim τ (Source.starImage H Uγ) ≤ 2 * rank (Source.starImage H Uγ))
    (hstrong : ∃ B ≤ Source.starImage H Uγ, IsStrongOffender W.quotientRepresentation B)
    (hB4 : SymmetricB4.{v} Kstar eH) :
    Nonempty (NaturalCentralSeries W.toRepresentation Kstar eH) := by
  have hn : ¬ (⊤ : Submodule (ZMod 2) W.toSubmodule) ≤
      fixedSpace W.toRepresentation Kstar := by
    intro h
    obtain ⟨k, hk, w, hw⟩ := hKW
    exact hw (h Submodule.mem_top ⟨k, hk⟩)
  exact (strong_quotient_series τ W eH Kstar hK hQ hn
    (Source.starImage H Uγ) hA hq hb hstrong hB4).1

/-- The second strong branch on the literal source module U_H/V₁. We retain
A₁ noncontainment in the subgroup preimage of W, the absence of a contained
strong FF*-offender on the quotient, and the contained strong FF*-offender
on W supplied by 13.8.22(2). These source branch conditions are stronger than
the hypotheses needed for constituent classification alone. -/
theorem source_strong_submodule_series
    {G : Type v} [Group G] [Finite G] (H V₃ V₁ Uγ A₁ : Subgroup G)
    [(V₁.subgroupOf (Source.UH H V₃)).Normal]
    [IsElementaryAbelian 2 (Source.Utilde H V₃ V₁)]
    (τ : Representation (ZMod 2) (Source.Hstar H) (SourceSpace H V₃ V₁))
    (_hτ : IsSourceAction H V₃ V₁ τ)
    (W : Subrepresentation τ) (_hW : IsCoatom W)
    (eH : Source.Hstar H ≃* Perm) (Kstar : Subgroup (Source.Hstar H))
    (hK : Kstar.map eH.toMonoidHom = alternatingGroup (Fin 8))
    (eK : Kstar ≃* BinaryLinear.GL OrthogonalQuotient.FourSpace)
    (_hQ : IsEightNatural W.quotientRepresentation eH)
    (hKW : ∃ k ∈ Kstar, ∃ w : W.toSubmodule, W.toRepresentation k w ≠ w)
    (_hA : IsElementaryTwo (Source.starImage H Uγ))
    (hq : IsQuadratic τ (Source.starImage H Uγ))
    (_hb : fixedCodim τ (Source.starImage H Uγ) ≤ 2 * rank (Source.starImage H Uγ))
    (_hA₁ : ¬ A₁ ≤ ((Subgroup.toAddSubgroup.symm W.toSubmodule.toAddSubgroup).comap
      (sourceProjection H V₃ V₁)).map (Source.UH H V₃).subtype)
    (_hnoQ : ¬ ∃ B ≤ Source.starImage H Uγ, IsBestOffender W.quotientRepresentation B ∧
      IsStrongOffender W.quotientRepresentation B)
    (hstrong : ∃ B ≤ Source.starImage H Uγ, IsBestOffender W.toRepresentation B ∧
      IsStrongOffender W.toRepresentation B)
    (hS : SymmetricB4.{v} Kstar eH) (hC : ComponentB4.{v} Kstar eH eK) :
    Nonempty (NaturalCentralSeries W.toRepresentation Kstar eH) := by
  have hn : ¬ (⊤ : Submodule (ZMod 2) W.toSubmodule) ≤
      fixedSpace W.toRepresentation Kstar := by
    intro h
    obtain ⟨k, hk, w, hw⟩ := hKW
    exact hw (h Submodule.mem_top ⟨k, hk⟩)
  apply strong_submodule_series τ W eH Kstar hK eK hn (Source.starImage H Uγ) hq
    _ hS hC
  obtain ⟨B, hBA, _, hB⟩ := hstrong
  exact ⟨B, hBA, hB⟩


end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.LinearReduction.OffenderModels.StrongSections.SourceConstituents
