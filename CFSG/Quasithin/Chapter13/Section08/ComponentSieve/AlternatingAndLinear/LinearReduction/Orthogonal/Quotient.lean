module

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.LinearReduction.Orthogonal.Quotient.Selection
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.LinearReduction.Orthogonal.Quotient.CentralKernel
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.LinearReduction.Orthogonal.Quotient.B4Extraction
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.LinearReduction.Orthogonal.Quotient.CentralAction

/-!
# The natural maximal quotient and nontrivial component action in 13.8.25

We select a maximal proper H*-subrepresentation W of the actual U_H/V₁.
The literal quotient is irreducible and retains the rank-two V₃ image, its
L₁T-invariance and its L₁-commutator equality. The B.4 extraction gives actual
compatible equivariant models. Restricting the seed to the marked middle-node
parabolic excludes the natural-plus-dual alternative, leaving the natural
six-dimensional S₈ module with the specified permutation marking.

If K centralized W, the central-kernel bridge and U_H=[U_H,K] would identify
the literal Ũ_K/C_{Ũ_K}(K) with the natural A₈ module. Universal 13.7.6(3)
permits only degrees six and seven, so an element of K* moves a vector of W.
The normal-subgroup structure of S₈ then also proves faithfulness on W.

`exists_source_quotient` assembles this segment conditionally on the preceding
marked parabolic outcome, the exact earlier seed and quadratic-actor facts,
and the universal B.4 and 13.7.6 inputs. These inputs do not assert a model for
the chosen quotient or nontrivial action on W. The parent owns their source
instantiation and the remaining full orthogonal exclusion. All quotient and
component normality remains relative to the indicated local subgroup.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), proof of 13.8.25,
printed pp.959–960, PDF pp.976–977; B.4.2 and B.4.5, printed pp.86–87;
13.7.6(3), printed pp.938–939.
-/

@[expose] public section

namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.LinearReduction.OrthogonalQuotient
open Representation Representation.BinaryOffender BinaryLinear
open FourStructure FourStructure.ChiefFactors

/-- The literal maximal quotient, its marked natural model and surviving source
seed, together with the nontrivial component action below that quotient. -/
structure QuotientWitness {J U : Type*} [Group J] [AddCommGroup U] [Module (ZMod 2) U]
    (ρ : Representation (ZMod 2) J U) (eH : J ≃* Equiv.Perm (Fin 8))
    (K P L A : Subgroup J) (S : Submodule (ZMod 2) U) (W : Subrepresentation ρ) : Prop where
  maximal : IsCoatom W
  irreducible : W.quotientRepresentation.IsIrreducible
  faithful : Function.Injective W.quotientRepresentation
  natural : IsEightNatural W.quotientRepresentation eH
  actor_elementary : IsElementaryTwo A
  actor_quadratic : IsQuadratic W.quotientRepresentation A
  actor_bound : fixedCodim W.quotientRepresentation A ≤ 2 * rank A
  seed_finrank : Module.finrank (ZMod 2) ((S).map W.toSubmodule.mkQ) = 2
  seed_stable : ∀ g : P, ∀ v ∈ (S).map W.toSubmodule.mkQ,
    W.quotientRepresentation g v ∈ (S).map W.toSubmodule.mkQ
  seed_commutator : subspaceCommutator W.quotientRepresentation
    ((S).map W.toSubmodule.mkQ) L = (S).map W.toSubmodule.mkQ
  submodule_faithful : Function.Injective W.toRepresentation
  component_moves : ∃ k ∈ K, ∃ w : W.toSubmodule, W.toRepresentation k w ≠ w

private theorem commutator_subgroupOf {J U : Type*} [Group J] [AddCommGroup U]
    [Module (ZMod 2) U] (ρ : Representation (ZMod 2) J U)
    (S : Submodule (ZMod 2) U) (K L : Subgroup J) (hLK : L ≤ K) :
    subspaceCommutator (ρ.comp K.subtype) S (L.subgroupOf K) =
      subspaceCommutator ρ S L := by
  unfold subspaceCommutator
  congr 1
  ext v
  constructor
  · rintro ⟨l, hl, w, hw, rfl⟩
    exact ⟨l, hl, w, hw, rfl⟩
  · rintro ⟨l, hl, w, hw, rfl⟩
    exact ⟨⟨l, hLK hl⟩, hl, w, hw, rfl⟩

open scoped IsMulCommutative

universe v
variable {G : Type v} [Group G] [Finite G]
  (H V₃ V₁ L L₁ T G₁ M K Uγ : Subgroup G)
  [(V₁.subgroupOf (Source.UH H V₃)).Normal]
  [IsElementaryAbelian 2 (Source.Utilde H V₃ V₁)]

local notation "Kstar" => Source.starImage H K
local notation "Lstar" => Source.starImage H L₁
local notation "Tstar" => Source.starImage H T
local notation "Pstar" => (Lstar ⊔ Tstar : Subgroup (Source.Hstar H))
local notation "Astar" => Source.starImage H Uγ
local notation "S" => sourceSeedSpace H V₃ V₁

/-- The maximal-quotient and noncentral-kernel steps of 13.8.25. The preceding
parabolic outcome is supplied by the compatible S₈ and GL₄(2) markings and the
middle-node flag identity. The earlier source seed facts, quadratic actor,
13.8.21 generation equality and universal B.4/13.7.6 inputs remain explicit.
Neither a quotient model nor nontrivial action on W is assumed. -/
theorem exists_source_quotient
    (τ : Representation (ZMod 2) (Source.Hstar H) (SourceSpace H V₃ V₁))
    (hτ : IsSourceAction H V₃ V₁ τ)
    (hH : H ∈ Source.Hz L₁ T G₁ M) (hV₁ : V₁ ≤ Source.UH H V₃)
    (hKH : K ≤ H) (hK : (K.subgroupOf H).IsCComponent) (hL₁K : L₁ ≤ K)
    (hgen : Source.UH H V₃ = ⁅Source.UH H V₃, K⁆)
    (eH : Source.Hstar H ≃* Equiv.Perm (Fin 8))
    (hKalt : (Kstar).map eH.toMonoidHom = alternatingGroup (Fin 8))
    (eK : Kstar ≃* BinaryLinear.GL FourSpace)
    (A F : Submodule (ZMod 2) FourSpace) (hAF : A ≤ F)
    (hA : Module.finrank (ZMod 2) A = 1)
    (hF : Module.finrank (ZMod 2) F + 1 = Module.finrank (ZMod 2) FourSpace)
    (hmiddle : ((Lstar ⊔ (Kstar ⊓ Tstar)).subgroupOf Kstar).map eK.toMonoidHom =
      parabolic A ⊓ parabolic F)
    (hT : IsPGroup 2 Tstar)
    (hstable : ∀ g : Pstar, ∀ v ∈ S, τ g v ∈ S)
    (hirr : IsAtom (⟨S, hstable⟩ : Subrepresentation (τ.comp (Pstar).subtype)))
    (hdim : Module.finrank (ZMod 2) S = 2)
    (hcomm : subspaceCommutator τ S Lstar = S)
    (hactor : IsElementaryTwo Astar) (hq : IsQuadratic τ Astar)
    (hb : fixedCodim τ Astar ≤ 2 * rank Astar)
    (hSym : B4Extraction.SymmetricB4.{v} Kstar eH)
    (hComp : B4Extraction.ComponentB4.{v} Kstar eH eK)
    (h1376 : Seven.PairsBranch.CentralAction.AlternatingNaturalImplication L L₁ T G₁ M τ) :
    ∃ W : Subrepresentation τ, QuotientWitness τ eH Kstar Pstar Lstar Astar S W := by
  have hLK : Lstar ≤ Kstar := by
    rintro x ⟨h, hh, rfl⟩
    exact ⟨h, hL₁K hh, rfl⟩
  obtain ⟨W, hW, hi, hf, ha, hq', hb', hd, hs, hc, halt⟩ :=
    B4Extraction.exists_source_representation_alternatives H V₃ V₁ Uγ τ hτ eH
      Kstar Pstar Tstar Lstar hKalt hLK le_sup_right hT hstable hirr hdim hcomm
      hactor hq hb eK hSym hComp
  have hnatural : IsEightNatural W.quotientRepresentation eH := by
    apply natural_of_marked_alternatives W.quotientRepresentation eH Kstar eK
      ((Lstar ⊔ (Kstar ⊓ Tstar)).subgroupOf Kstar) ((Lstar).subgroupOf Kstar)
      (fun _ hl => (show Lstar ≤ Lstar ⊔ (Kstar ⊓ Tstar) from le_sup_left) hl) A F hAF hA hF hmiddle
      ((S).map W.toSubmodule.mkQ) hd
    · intro g hg v hv
      have hPP : Lstar ⊔ (Kstar ⊓ Tstar) ≤ Pstar :=
        sup_le le_sup_left (inf_le_right.trans le_sup_right)
      have hP : (g : Source.Hstar H) ∈ Pstar := hPP hg
      exact hs ⟨g, hP⟩ v hv
    · rw [commutator_subgroupOf _ _ _ _ hLK]
      exact hc
    · exact halt
  have hmoves := CentralAction.nontrivial_on_submodule L L₁ T G₁ M K τ
    hH hV₁ hτ hKH hK hgen eH hKalt W hnatural h1376
  have hfaithful := faithful_of_nontrivial_on_monolith W.toRepresentation Kstar
    (B4Extraction.marked_component_monolith eH Kstar hKalt) hmoves
  exact ⟨W, hW, hi, hf, hnatural, ha, hq', hb', hd, hs, hc, hfaithful, hmoves⟩

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.LinearReduction.OrthogonalQuotient
