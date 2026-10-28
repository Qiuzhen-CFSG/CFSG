module

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.ExceptionalFields.LinearThreeFour.AutomorphismModule.Constructions
public import Theory.Representation.SL3FourNaturalDual.CentralSections
public import Theory.Representation.SL3FourNaturalDual.GraphSeparation
public import Theory.Representation.BinaryOffender.ConjugationGeneration

/-!
# Lifting the hatted natural pair to the literal source module

The identity U_H=[U_H,K] gives full linear commutator generation on the
specified quotient action. For an Irr⁺ member with natural central quotient,
the scalar norm removes its fixed space and lifts its natural coordinates.
A complementary pair in the hatted quotient then becomes a complementary
pair in U_H/V₁. The original marking of K* and the prescribed translate t*
are retained exactly. The graph relation, including its GL₃ correction,
also proves that the chosen natural section is not t*-invariant; this is the
exclusion of F.9.18(4i) after naturality has been established.

`naturalPairOfHatted` is the final lifting step, not a proof that its hatted
premises hold. The source deduction still needs the T-homogeneous choice,
B.4.5 on faithful irreducible action images and exclusion of F.9.18(4ii),
and the no-FF premise and saturation in F.9.18(7). Neither a record projection
nor this conditional lifting lemma establishes those classification steps.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
13.8.20, printed p.955 (PDF p.972); F.9.18(4),(7), pp.325–326.
-/

@[expose] public noncomputable section
open Subgroup Representation Representation.BinaryOffender Representation.SL3FourNaturalDual
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.ExceptionalFields.LinearThreeFour.AutomorphismModule
open ComponentSieve.AlternatingAndLinear.FourStructure.ChiefFactors
variable {G : Type*} [Group G] {H V₃ V₁ : Subgroup G}
  [(V₁.subgroupOf (Source.UH H V₃)).Normal]
  [IsElementaryAbelian 2 (Source.Utilde H V₃ V₁)]

/-- The literal action carries the source group identity to linear commutator generation. -/
theorem LiteralAction.commutator_eq_top (d : LiteralAction H V₃ V₁)
    (K : Subgroup G) (hKH : K ≤ H)
    (hgen : Source.UH H V₃ = ⁅Source.UH H V₃, K⁆) :
    subspaceCommutator d.representation ⊤ (Source.starImage H K) = ⊤ := by
  let f : K →* Source.Hstar H := (QuotientGroup.mk' (pCore 2 H)).comp (inclusion hKH)
  have hr : f.range = Source.starImage H K := by
    ext g
    constructor
    · rintro ⟨k, rfl⟩
      exact ⟨inclusion hKH k, k.property, rfl⟩
    · rintro ⟨k, hk, rfl⟩
      exact ⟨⟨k, hk⟩, rfl⟩
  have hn : K ≤ normalizer (Source.UH H V₃ : Set G) :=
    hKH.trans (le_normalizer_conjugateSpanBy V₃ H)
  have hc : ⁅K, Source.UH H V₃⁆ = Source.UH H V₃ := by
    rw [commutator_comm]
    exact hgen.symm
  have hm := commutator_eq_top_of_conjugation d.representation (Source.UH H V₃) K hn
    f (sourceProjection H V₃ V₁) (QuotientGroup.mk'_surjective _)
    (fun k u => d.conjugation (inclusion hKH k) u) hc
  rwa [hr] at hm

/-- After natural recognition, the prescribed graph actor excludes the invariant case.
The marking of K* is exactly the one used in the graph relation. -/
theorem natural_section_moved (d : LiteralAction H V₃ V₁)
    (K : Subgroup G) (eK : Source.starImage H K ≃* SL) (t : Source.Hstar H)
    (I : Submodule (ZMod 2) (SourceSpace H V₃ V₁))
    (hI : IsIrrPlus d.representation (Source.starImage H K) I)
    (n : NaturalCentralSection d.representation (Source.starImage H K) eK I)
    (c : Matrix.GeneralLinearGroup (Fin 3) F)
    (ht : ∀ g, sourceActor H K eK g * t = t * sourceActor H K eK
      (Matrix.PSL3.OuterSolvable.linearConjSL F c
        (Matrix.SpecialLinearGroup.inverseTranspose g))) : I.map (d.representation t) ≠ I :=
  graph_moves_natural_section d.representation (sourceActor H K eK) t I
    (n.lift hI.choose_spec.1) c (n.lift_symm_equivariant hI.choose_spec.1) ht

/-- The completed algebraic lift. The central-quotient splitting and its saturation
remain conclusions for the representation-theoretic source deduction to prove. -/
def naturalPairOfHatted (d : LiteralAction H V₃ V₁)
    (K : Subgroup G) (eK : Source.starImage H K ≃* SL) (t : Source.Hstar H)
    (hKH : K ≤ H) (hgen : Source.UH H V₃ = ⁅Source.UH H V₃, K⁆)
    (I : Submodule (ZMod 2) (SourceSpace H V₃ V₁))
    (hI : IsIrrPlus d.representation (Source.starImage H K) I)
    (ht : t ∈ normalizer (Source.starImage H K : Set (Source.Hstar H)))
    (n : NaturalCentralSection d.representation (Source.starImage H K) eK I)
    (hdis : Disjoint (I.map (fixedSpace d.representation (Source.starImage H K)).mkQ)
      ((I.map (d.representation t)).map
        (fixedSpace d.representation (Source.starImage H K)).mkQ))
    (hspan : I.map (fixedSpace d.representation (Source.starImage H K)).mkQ ⊔
      (I.map (d.representation t)).map
        (fixedSpace d.representation (Source.starImage H K)).mkQ = ⊤) :
    NaturalPair d K eK t where
  space := I
  coordinates := n.lift hI.choose_spec.1
  natural_action := n.lift_symm_equivariant hI.choose_spec.1
  complementary := isCompl_of_centralQuotient d.representation (Source.starImage H K)
    I (I.map (d.representation t)) n.stable (hI.map_normalizer d.representation ht).choose
    (d.commutator_eq_top K hKH hgen) (n.disjoint_fixedSpace hI.choose_spec.1) hdis hspan

/-- The internal summand is the one chosen before removing fixed spaces. -/
lemma naturalPairOfHatted_space (d : LiteralAction H V₃ V₁)
    (K : Subgroup G) (eK : Source.starImage H K ≃* SL) (t : Source.Hstar H)
    (hKH : K ≤ H) (hgen : Source.UH H V₃ = ⁅Source.UH H V₃, K⁆)
    (I : Submodule (ZMod 2) (SourceSpace H V₃ V₁))
    (hI : IsIrrPlus d.representation (Source.starImage H K) I)
    (ht : t ∈ normalizer (Source.starImage H K : Set (Source.Hstar H)))
    (n : NaturalCentralSection d.representation (Source.starImage H K) eK I)
    (hdis : Disjoint (I.map (fixedSpace d.representation (Source.starImage H K)).mkQ)
      ((I.map (d.representation t)).map
        (fixedSpace d.representation (Source.starImage H K)).mkQ))
    (hspan : I.map (fixedSpace d.representation (Source.starImage H K)).mkQ ⊔
      (I.map (d.representation t)).map
        (fixedSpace d.representation (Source.starImage H K)).mkQ = ⊤) :
    (naturalPairOfHatted d K eK t hKH hgen I hI ht n hdis hspan).space = I := rfl

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.ExceptionalFields.LinearThreeFour.AutomorphismModule
