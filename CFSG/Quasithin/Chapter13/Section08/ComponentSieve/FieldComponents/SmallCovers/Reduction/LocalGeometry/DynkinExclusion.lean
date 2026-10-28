module

public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.Components.Basic
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.SmallCovers.Reduction.Quotient
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.SmallCovers.Reduction.ModuleRecognition.Inputs
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.SmallCovers.Reduction.ModuleRecognition.CubicAction
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.SmallCovers.Reduction.LocalGeometry.DynkinExclusion.Recognition
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents
public import Theory.Representation.HexacodeAction.NaturalConjugation
public import Theory.SpecificGroups.AlternatingSix.ShadowLocal.InvolutionGeometry.FourNormalizers.SixParabolicTypes

/-!
# The actual central-quotient action in the covered A₆ branch

The conjugation homomorphism on K*/Z(K*) is transported through the canonical
componentStarEquiv and the supplied intrinsic central-quotient identification.
It is therefore the action of the actual H/O₂(H), rather than an unrelated
automorphism of an abstract A₆. A recognized invariant hexacode section puts
this action in the natural S₆, independently of the chosen identification.
The four-group criterion distinguishes that subgroup from the exceptional
class-swapping automorphisms, including outer automorphisms in both cases.

The section passage now uses A.1.42 and all three F.9.18(4) alternatives.
The actual ambient quadratic bound passes to the faithful invariant section;
B.4.5 is applied only after proving irreducibility of its component restriction.
The source theorem below retains H = KT, the actual Sylow image, relative
normality, C-component membership, the genuine cover, and the conjugation
equation on U_H/V₁. In the contrary Y = L₁ branch, the earlier seed identity
with L₁ supplies the cubic polynomial. No Y = L₁,+ or Y ≠ L₁ is assumed.
The parabolic-type criterion uses the literal duad and syntheme stabilizers,
not just the distinction between inner and outer automorphisms.

This is conditional source assembly: the universal irreducible B.4 input
and the F.9 alternatives still require their earlier source proofs. In
particular this module does not claim to prove B.4.5 or F.9.18 from the
definitions of their interfaces. Only B.4's small-ratio field is used here;
the FF ratio-one field belongs to the separate later recognition argument.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, 13.8.21(2),
printed p.956 (PDF p.973); A.1.40–42, pp.31–32; B.4.2(8), B.4.5,
pp.86–87; F.9.18(3–4), pp.325–326; I.5, pp.419–422.
-/

@[expose] public section

open Subgroup Representation Representation.BinaryOffender Atlas.Codes AlternatingSix.ShadowLocal
open scoped IsMulCommutative

namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.SmallCovers.Reduction.LocalGeometry.DynkinExclusion

universe u
variable {G : Type u} [Group G] [Finite G]
variable (H K : Subgroup G) (hKH : K ≤ H)
  (hK : (K.subgroupOf H).IsCComponent)

/-- The given intrinsic central quotient is identified with the actual K*.
This uses the canonical component quotient map, including its kernel. -/
noncomputable def sourceCentralEquiv
    (e : ((K ⧸ pCore 2 K) ⧸ center (K ⧸ pCore 2 K)) ≃* A6) :
    (Source.starImage H K ⧸ center (Source.starImage H K)) ≃* A6 := by
  let c := (Components.componentStarEquiv H K hKH hK).symm
  have hc : (center (Source.starImage H K)).map c.toMonoidHom =
      center (K ⧸ pCore 2 K) := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact (centerCongr c ⟨y, hy⟩).property
    · intro hx
      exact ⟨c.symm x, (centerCongr c.symm ⟨x, hx⟩).property, c.apply_symm_apply x⟩
  exact (QuotientGroup.congr _ _ c hc).trans e

/-- The canonical comparison commutes with the intrinsic quotient map. -/
theorem sourceCentralEquiv_mk
    (e : ((K ⧸ pCore 2 K) ⧸ center (K ⧸ pCore 2 K)) ≃* A6)
    (k : Source.starImage H K) :
    sourceCentralEquiv H K hKH hK e (QuotientGroup.mk' _ k) =
      e (QuotientGroup.mk' _ ((Components.componentStarEquiv H K hKH hK).symm k)) := rfl

/-- The Sylow subgroup used for the orbit is the image of the actual source T. -/
theorem exists_starSylow (T : Subgroup G) (hT : Chapter1.IsSylowIn 2 T H) :
    ∃ P : Sylow 2 (Source.Hstar H), (P : Subgroup (Source.Hstar H)) =
      Source.starImage H T := by
  obtain ⟨P₀, hP₀⟩ := hT
  let P := P₀.mapSurjective (QuotientGroup.mk'_surjective (pCore 2 H))
  refine ⟨P, ?_⟩
  change (P₀ : Subgroup H).map (QuotientGroup.mk' (pCore 2 H)) = _
  have he : T.subgroupOf H = (P₀ : Subgroup H) := by
    rw [← hP₀, ← comap_subtype, comap_map_eq, H.ker_subtype, sup_bot_eq]
  exact congrArg (Subgroup.map (QuotientGroup.mk' (pCore 2 H))) he.symm

omit [Finite G] in
/-- H = KT gives generation in the literal quotient, for this same Sylow image. -/
theorem star_sylow_generation (T : Subgroup G) (hH : H = K ⊔ T)
    (P : Sylow 2 (Source.Hstar H))
    (hP : (P : Subgroup (Source.Hstar H)) = Source.starImage H T) :
    Source.starImage H K ⊔ (P : Subgroup (Source.Hstar H)) = ⊤ := by
  have hTH : T ≤ H := hH ▸ le_sup_right
  have hKH : K ≤ H := hH ▸ le_sup_left
  rw [hP]
  unfold Source.starImage
  rw [← Subgroup.map_sup, ← subgroupOf_sup hKH hTH, ← hH, subgroupOf_self,
    Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _)]

variable [(K.subgroupOf H).Normal]

local instance starNormal : (Source.starImage H K).Normal :=
  (inferInstance : (K.subgroupOf H).Normal).map
    (QuotientGroup.mk' (pCore 2 H)) (QuotientGroup.mk'_surjective _)

/-- Actual conjugation, followed by the central quotient and the source marking. -/
noncomputable def sourceAction
    (e : ((K ⧸ pCore 2 K) ⧸ center (K ⧸ pCore 2 K)) ≃* A6) :
    Source.Hstar H →* AutA6 :=
  Hexacode.centralSixAction (Source.starImage H K) (sourceCentralEquiv H K hKH hK e)

/-- The action equation on representatives of K*/Z(K*). -/
theorem sourceAction_mk
    (e : ((K ⧸ pCore 2 K) ⧸ center (K ⧸ pCore 2 K)) ≃* A6)
    (h : Source.Hstar H) (k : Source.starImage H K) :
    sourceAction H K hKH hK e h
        (sourceCentralEquiv H K hKH hK e (QuotientGroup.mk' _ k)) =
      sourceCentralEquiv H K hKH hK e
        (QuotientGroup.mk' _ (MulAut.conjNormal h k)) :=
  Hexacode.centralSixAction_mk _ _ h k

/-- A faithful hexacode actor marking controls the actual central quotient.
Existence of the actor is a separate representation-theoretic obligation. -/
theorem sourceAction_natural_of_actor
    (e : ((K ⧸ pCore 2 K) ⧸ center (K ⧸ pCore 2 K)) ≃* A6)
    (φ : Source.Hstar H →* HexAutomorphisms) (hf : Function.Injective φ)
    (hc : (Source.starImage H K).map φ = hexSign.ker) (h : Source.Hstar H) :
    sourceAction H K hKH hK e h ∈ natural :=
  Hexacode.centralSixAction_mem_natural _ _ φ hf hc h

/-- Naturality is precisely preservation of the marked four-group's inner
conjugacy class; it is not the condition that the automorphism is inner. -/
theorem sourceAction_natural_iff
    (e : ((K ⧸ pCore 2 K) ⧸ center (K ⧸ pCore 2 K)) ≃* A6)
    (h : Source.Hstar H) :
    sourceAction H K hKH hK e h ∈ natural ↔ ∃ g : A6,
      FourNormalizers.standardFour.map (sourceAction H K hKH hK e h).toMonoidHom =
        FourNormalizers.standardFour.map (MulAut.conj g).toMonoidHom :=
  FourNormalizers.natural_iff_standard_conjugate _

variable (V₃ V₁ : Subgroup G)
  [(V₁.subgroupOf (Source.UH H V₃)).Normal]
  [IsMulCommutative (Source.Utilde H V₃ V₁)]
  [Module (ZMod 2) (Additive (Source.Utilde H V₃ V₁))]

/-- A recognized invariant section of the literal conjugation module supplies
the actor used above. This is conditional transport, not section existence. -/
theorem sourceAction_natural_of_invariant_model
    (act : QuotientAction H V₃ V₁)
    (e : ((K ⧸ pCore 2 K) ⧸ center (K ⧸ pCore 2 K)) ≃* A6)
    (I : Subrepresentation act.representation)
    (m : ModuleRecognition.HexacodeModel (Source.starImage H K) I.toRepresentation)
    (h : Source.Hstar H) : sourceAction H K hKH hK e h ∈ natural :=
  sourceAction_natural_of_actor H K hKH hK e m.actor m.faithful m.component_image h

/-- The actual ambient bound gives natural central-quotient conjugation once
the universal earlier representation inputs are supplied. The cubic action
and faithful irreducible section are constructed, not assumed. -/
theorem sourceAction_natural_of_small_ratio
    (act : QuotientAction H V₃ V₁)
    (T : Subgroup G) (hH : H = K ⊔ T)
    (P : Sylow 2 (Source.Hstar H))
    (hP : (P : Subgroup (Source.Hstar H)) = Source.starImage H T)
    (eK : (K ⧸ pCore 2 K) ≃* HexEvenAutomorphisms)
    (e : ((K ⧸ pCore 2 K) ⧸ center (K ⧸ pCore 2 K)) ≃* A6)
    (hcent : centralizer (Source.starImage H K : Set (Source.Hstar H)) ≤
      Source.starImage H K)
    (hseed : subspaceCommutator act.representation (seedSpace H V₃ V₁)
      (Source.starImage H (coverResidualIn K)) = seedSpace H V₃ V₁)
    (hdim : Module.finrank (ZMod 2) (seedSpace H V₃ V₁) = 2)
    (src : Recognition.Alternatives act.representation (Source.starImage H K) P
      (star_sylow_generation H K T hH P hP))
    (inputs : Recognition.SmallInput.{u,u} (Source.starImage H K))
    (hq : quadraticRatio act.representation ≤ 2) (h : Source.Hstar H) :
    sourceAction H K hKH hK e h ∈ natural := by
  let : Nontrivial (seedSpace H V₃ V₁) := Module.nontrivial_of_finrank_eq_succ hdim
  let : Nontrivial (Additive (Source.Utilde H V₃ V₁)) :=
    Function.Injective.nontrivial (seedSpace H V₃ V₁).subtype_injective
  let c := (Components.componentStarEquiv H K hKH hK).symm.trans eK
  obtain ⟨z, _, ho, hz, hp⟩ :=
    exists_residual_cubic_polynomial H K V₃ V₁ act hKH hK eK hseed
  have hc : Nat.card (center (K ⧸ pCore 2 K)) = 3 :=
    (Nat.card_congr (centerCongr eK).toEquiv).trans Hexacode.even_center_card
  have hzcenter : zpowers z =
      (center (Source.starImage H K)).map (Source.starImage H K).subtype :=
    hz.trans (ModuleRecognition.residual_star_eq_center H K hKH hK hc)
  obtain ⟨J, _, ⟨m⟩⟩ := Recognition.exists_model act.representation
    (Source.starImage H K) P (star_sylow_generation H K T hH P hP)
    c hcent z ho hzcenter hp src inputs hq
  exact sourceAction_natural_of_invariant_model H K hKH hK V₃ V₁ act e J m h

/-- In the contrary branch Y = L₁, the L₁ seed identity supplies exactly
the cubic action needed above. No identification with L₁,+ is required. -/
theorem sourceAction_natural_in_contrary_branch
    (act : QuotientAction H V₃ V₁)
    (L₁ T : Subgroup G) (hH : H = K ⊔ T) (hY : coverResidualIn K = L₁)
    (P : Sylow 2 (Source.Hstar H))
    (hP : (P : Subgroup (Source.Hstar H)) = Source.starImage H T)
    (eK : (K ⧸ pCore 2 K) ≃* HexEvenAutomorphisms)
    (e : ((K ⧸ pCore 2 K) ⧸ center (K ⧸ pCore 2 K)) ≃* A6)
    (hcent : centralizer (Source.starImage H K : Set (Source.Hstar H)) ≤
      Source.starImage H K)
    (hseed : subspaceCommutator act.representation (seedSpace H V₃ V₁)
      (Source.starImage H L₁) = seedSpace H V₃ V₁)
    (hdim : Module.finrank (ZMod 2) (seedSpace H V₃ V₁) = 2)
    (src : Recognition.Alternatives act.representation (Source.starImage H K) P
      (star_sylow_generation H K T hH P hP))
    (inputs : Recognition.SmallInput.{u,u} (Source.starImage H K))
    (hq : quadraticRatio act.representation ≤ 2) (h : Source.Hstar H) :
    sourceAction H K hKH hK e h ∈ natural := by
  apply sourceAction_natural_of_small_ratio H K hKH hK V₃ V₁ act T hH P hP eK e
    hcent _ hdim src inputs hq h
  rwa [hY]

omit [IsMulCommutative (Source.Utilde H V₃ V₁)]
  [Module (ZMod 2) (Additive (Source.Utilde H V₃ V₁))]
  [(V₁.subgroupOf (Source.UH H V₃)).Normal] in
/-- This is the literal source Dynkin criterion: both parabolic types are
preserved up to inner conjugacy, including by natural outer automorphisms. -/
theorem sourceAction_natural_iff_preserves_parabolic_types
    (e : ((K ⧸ pCore 2 K) ⧸ center (K ⧸ pCore 2 K)) ≃* A6)
    (h : Source.Hstar H) :
    sourceAction H K hKH hK e h ∈ natural ↔
      (∃ g : A6,
        Theory.SpecificGroups.SymmetricSix.a6DuadStabilizer.map
            (sourceAction H K hKH hK e h).toMonoidHom =
          Theory.SpecificGroups.SymmetricSix.a6DuadStabilizer.map
            (MulAut.conj g).toMonoidHom) ∧
      (∃ g : A6,
        Theory.SpecificGroups.SymmetricSix.a6SynthemeStabilizer.map
            (sourceAction H K hKH hK e h).toMonoidHom =
          Theory.SpecificGroups.SymmetricSix.a6SynthemeStabilizer.map
            (MulAut.conj g).toMonoidHom) :=
  FourNormalizers.SixParabolics.natural_iff_preserves_source_parabolic_types _

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.SmallCovers.Reduction.LocalGeometry.DynkinExclusion
