module

public import CFSG.Quasithin.Chapter13.Section08.SourceDefs
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure.ChiefFactors.SourceSeed
public import Theory.Representation.SL3FourNaturalDual.GraphSum
public import Theory.GroupTheory.PResidual.NormalityLift

/-!
# Source coordinates and the normalizer step in the SL₃(4) branch

`LiteralAction` retains the actual quotient U_H/V₁ and its conjugation action.
`sourceActor` is the inclusion of K* composed with the inverse of the actual
SL₃(4) model equivalence. Given a natural internal summand and its complementary
graph translate, `sourceMarking` constructs equivariant coordinates by summing
the two embeddings. `NaturalPair` is an intermediate conclusion still to be
constructed from B.4.5 and F.9.18, not a standing source hypothesis.

For the graph-field exclusion, normality of L₀* lifts to normality of L₀
because L₀ is two-perfect and Q_H normalizes it. The latter follows from the
actual overlap identities and M = N_G(L₀). Thus a central image gives the
required chain H ≤ N_G(L₀) ≤ M. The central-image equality itself must still
be proved, retaining the Borel two-core and the source B = O²(B₀).

These are conditional assembly tools. They do not classify the automorphism
of K* or select the natural summand, and hence do not yet complete the SL₃(4)
paragraph of 13.8.20.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
13.8.20, printed pp.954–955 (PDF pp.971–972); 13.2.2(9), 13.7.3(6),(9),
B.4.5, and F.9.18(4),(7).
-/

@[expose] public section
noncomputable section
open Subgroup Representation.SL3FourNaturalDual
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.ExceptionalFields.LinearThreeFour.AutomorphismModule
open ComponentSieve.AlternatingAndLinear.FourStructure.ChiefFactors
variable {G : Type*} [Group G]

/-- The model acts through the actual subgroup K* of H*. -/
def sourceActor (H K : Subgroup G) (eK : Source.starImage H K ≃* SL) :
    SL →* Source.Hstar H := (Source.starImage H K).subtype.comp eK.symm.toMonoidHom

lemma sourceActor_injective (H K : Subgroup G) (eK : Source.starImage H K ≃* SL) :
    Function.Injective (sourceActor H K eK) :=
  (Source.starImage H K).subtype_injective.comp eK.symm.injective

lemma sourceActor_range (H K : Subgroup G) (eK : Source.starImage H K ≃* SL) :
    (sourceActor H K eK).range = Source.starImage H K := by
  apply le_antisymm
  · rintro _ ⟨g, rfl⟩
    exact (eK.symm g).property
  · intro g hg
    exact ⟨eK ⟨g, hg⟩, congrArg Subtype.val (eK.symm_apply_apply _)⟩

/-- Relative normality lifts using the normalizing two-core and two-perfectness. -/
theorem normalizes_of_normal_starImage (H L₀ : Subgroup G) (hL : L₀ ≤ H)
    (hp : IsPPerfect 2 L₀) (hQ : Source.QH H ≤ normalizer (L₀ : Set G))
    [(Source.starImage H L₀).Normal] : H ≤ normalizer (L₀ : Set G) := by
  apply (normal_subgroupOf_iff_le_normalizer hL).mp
  have hperf : IsPPerfect 2 (L₀.subgroupOf H) :=
    hp.of_surjective (subgroupOfEquivOfLe hL).symm.toMonoidHom
      (subgroupOfEquivOfLe hL).symm.surjective
  let : ((L₀.subgroupOf H).map (QuotientGroup.mk' (pCore 2 H))).Normal :=
    ‹(Source.starImage H L₀).Normal›
  apply normal_of_map_normal_of_pPerfect (QuotientGroup.mk' (pCore 2 H))
    (L₀.subgroupOf H) hperf
  · rw [QuotientGroup.ker_mk']
    exact pCore_isPGroup
  · rw [QuotientGroup.ker_mk']
    apply le_normalizer_iff.mpr
    intro q hq l hl
    exact le_normalizer_iff.mp hQ q.val (mem_map_of_mem H.subtype hq) l.val hl

/-- The center of the normal component is normal in H*, so its lift is normalized. -/
theorem normalizes_of_central_starImage (H K L₀ : Subgroup G)
    [(Source.starImage H K).Normal] (hL : L₀ ≤ H) (hp : IsPPerfect 2 L₀)
    (hQ : Source.QH H ≤ normalizer (L₀ : Set G))
    (hz : Source.starImage H L₀ =
      (center (Source.starImage H K)).map (Source.starImage H K).subtype) :
    H ≤ normalizer (L₀ : Set G) := by
  have hn : (Source.starImage H L₀).Normal := by rw [hz]; infer_instance
  let := hn
  exact normalizes_of_normal_starImage H L₀ hL hp hQ

/-- The actual normalizer chain rules out a central L₀* image. -/
theorem graph_field_contradiction (H K L₀ M : Subgroup G)
    [(Source.starImage H K).Normal] (hL : L₀ ≤ H) (hp : IsPPerfect 2 L₀)
    (hQ : Source.QH H ≤ normalizer (L₀ : Set G))
    (hz : Source.starImage H L₀ =
      (center (Source.starImage H K)).map (Source.starImage H K).subtype)
    (hNM : normalizer (L₀ : Set G) ≤ M) (hHM : ¬ H ≤ M) : False :=
  hHM ((normalizes_of_central_starImage H K L₀ hL hp hQ hz).trans hNM)

/-- Recover the kernel-normalization premise from the earlier overlap identities. -/
theorem graph_field_contradiction_of_source_overlap (H K L₀ M V V₃ : Subgroup G)
    [(Source.starImage H K).Normal] (hL : L₀ ≤ H) (hp : IsPPerfect 2 L₀)
    (hV₃ : V₃ ≤ V) (hcomm : ⁅V, Source.QH H⁆ = V₃)
    (hN : H ⊓ normalizer (V : Set G) = H ⊓ M)
    (hM : M = normalizer (L₀ : Set G))
    (hz : Source.starImage H L₀ =
      (center (Source.starImage H K)).map (Source.starImage H K).subtype)
    (hHM : ¬ H ≤ M) : False := by
  have hQV : Source.QH H ≤ normalizer (V : Set G) := by
    apply le_normalizer_iff_commutator_le_left.mpr
    rw [hcomm]
    exact hV₃
  have hQM : Source.QH H ≤ M := by
    have h := le_inf (pCoreIn_le 2 H) hQV
    rw [hN] at h
    exact h.trans inf_le_right
  exact graph_field_contradiction H K L₀ M hL hp (hM ▸ hQM) hz
    hM.ge hHM

variable (H V₃ V₁ : Subgroup G)
  [(V₁.subgroupOf (Source.UH H V₃)).Normal]
  [IsElementaryAbelian 2 (Source.Utilde H V₃ V₁)]

/-- An action on the literal source carrier, specified on every representative. -/
structure LiteralAction where
  representation : Representation (ZMod 2) (Source.Hstar H) (SourceSpace H V₃ V₁)
  conjugation : IsSourceAction H V₃ V₁ representation

variable {H V₃ V₁}

/-- The internal natural pair to be constructed from the earlier representation results.
This contains no coordinates on the full module. -/
structure NaturalPair (d : LiteralAction H V₃ V₁)
    (K : Subgroup G) (eK : Source.starImage H K ≃* SL) (t : Source.Hstar H) where
  space : Submodule (ZMod 2) (SourceSpace H V₃ V₁)
  coordinates : space ≃ₗ[ZMod 2] W
  natural_action : ∀ g w, d.representation (sourceActor H K eK g)
    (coordinates.symm w : SourceSpace H V₃ V₁) = coordinates.symm (natural g w)
  complementary : IsCompl space (space.map (d.representation t))

/-- Construct the complete marking; the supplied actor is preserved exactly. -/
def sourceMarking (d : LiteralAction H V₃ V₁)
    (K : Subgroup G) (eK : Source.starImage H K ≃* SL) (t : Source.Hstar H)
    (p : NaturalPair d K eK t) (c : Matrix.GeneralLinearGroup (Fin 3) F)
    (ht : ∀ g, sourceActor H K eK g * t = t * sourceActor H K eK
      (Matrix.PSL3.OuterSolvable.linearConjSL F c
        (Matrix.SpecialLinearGroup.inverseTranspose g))) :
    LinearMarking d.representation :=
  graphSumMarking d.representation (sourceActor H K eK) t p.space p.coordinates c
    p.complementary p.natural_action ht

lemma sourceMarking_actor (d : LiteralAction H V₃ V₁)
    (K : Subgroup G) (eK : Source.starImage H K ≃* SL) (t : Source.Hstar H)
    (p : NaturalPair d K eK t) (c : Matrix.GeneralLinearGroup (Fin 3) F)
    (ht : ∀ g, sourceActor H K eK g * t = t * sourceActor H K eK
      (Matrix.PSL3.OuterSolvable.linearConjSL F c
        (Matrix.SpecialLinearGroup.inverseTranspose g))) :
    (sourceMarking d K eK t p c ht).actor =
      (Source.starImage H K).subtype.comp eK.symm.toMonoidHom := rfl

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.ExceptionalFields.LinearThreeFour.AutomorphismModule
