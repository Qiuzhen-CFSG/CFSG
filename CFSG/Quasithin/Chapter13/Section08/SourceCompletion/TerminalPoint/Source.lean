module
public import CFSG.Quasithin.Chapter13.Section08.SourceCompletion.TerminalPoint
public import CFSG.Quasithin.Chapter13.Section08.SourceCompletion.TerminalPoint.Nonfixed
public import CFSG.Quasithin.Chapter13.Section08.SourceCompletion.TerminalPoint.Coordinates
public import CFSG.Quasithin.Chapter13.Section08.A6Endgame.PointNormalizer.CoreFixed
/-!
# The terminal point hypotheses from the original strict source pair

The critical quotient point is not fixed by H*: otherwise its point
centralizer would have index at most two in both conjugate endpoint groups,
forcing D_H=U_H. The O₂(H)-fixed subgroup has proper image in the natural
module or its full augmentation cover. Such an invariant subspace is fixed
by H*, so the critical point must be moved by O₂(H).

These two deductions construct the actual point-parabolic model and remove
both point callbacks from the terminal contradiction. A recognized natural
component section constructs the whole-module coordinates, including the
alternating branch. The same-marked version uses the supplied intrinsic
component marking; the general version also works with a separately marked
base edge, since both actions are literal conjugation on the same quotient.

The surviving ordinary component/section setup of 13.8.21/26/27 and the
strict denominators from 13.8.33 remain explicit earlier-source inputs.
Their producers are the six/G₂ and case-one-exclusion assemblies. No result
here asserts the unconditional source theorem before those inputs are supplied.
Source: Aschbacher--Smith, printed pp.957,962--969, especially the final
paragraph of 13.8.1.
-/
public section
open Subgroup Representation.BinaryOffender Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section08.SourceCompletion.TerminalPoint
open CriticalGeometry TransvectionRecognition.Component.ModelExtension
open TransvectionRecognition TransvectionRecognition.Component
open A6Endgame A6Endgame.PointNormalizer TerminalRanks
open Theory.SpecificGroups.SymmetricSix
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ M G₁ H K : Subgroup G}

/-- Every nonidentity critical point is moved by the actual two-core. -/
theorem critical_point_moved
    (d : LocalSetup T L V V₁ V₂ V₃ M G₁)
    (hHz : H ∈ Source.Hz (sourceOne L T V₁) (T : Subgroup G) G₁ M)
    (hF9 : (Section07.ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    (c : CriticalPair L (T : Subgroup G) H V) (hH : H = G₁)
    (hs : Source.DH (Source.UH H V₃) (c.Ugamma V₃) (c.Aone V₁) < Source.UH H V₃)
    (a : letI := d.uh_elementary hHz
      SolvableExclusion.Five.StarAction H (Source.UH H V₃) V₁)
    (coords : letI := d.uh_elementary hHz
      (∃ e : Source.Hstar H ≃* A6, LinearCoordinates a (A6.subtype.comp e.toMonoidHom)) ∨
      (∃ e : Source.Hstar H ≃* S6, LinearCoordinates a e.toMonoidHom))
    (hcomm : ⁅V₃, G₁.pCoreIn 2⁆ ≠ ⊥)
    (u : Source.UH H V₃) (hu : (u : G) ∈ c.Aone V₁) (hu1 : (u : G) ≠ 1) :
    ∃ n ∈ Source.QH H, n * (u : G) ≠ (u : G) * n := by
  let : IsElementaryAbelian 2 (Source.UH H V₃) := d.uh_elementary hHz
  by_contra! hm
  have hproper : ¬ Source.UH H V₃ ≤ centralizer (Source.QH H : Set G) := by
    intro hc
    apply hcomm
    rw [← hH]
    exact commutator_eq_bot_iff_le_centralizer.mpr ((le_conjugateSpanBy V₃ H).trans hc)
  have huC : (u : G) ∈ centralizer (Source.QH H : Set G) := mem_centralizer_iff.mpr hm
  obtain ⟨g,hg⟩ := critical_point_nonfixed d hHz hF9 c hH hs a u hu hu1
  exact hg (core_fixed_image_fixed a (d.line_le_uh H) hF9.H_centralizes
    hproper coords u huC g)

theorem contradiction_of_linear_models
    (d : LocalSetup T L V V₁ V₂ V₃ M G₁)
    (hHz : H ∈ Source.Hz (sourceOne L T V₁) (T : Subgroup G) G₁ M)
    (hF9 : (Section07.ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    (c : CriticalPair L (T : Subgroup G) H V)
    (hH : H = G₁)
    (hgen : H = K ⊔ (sourceOne L T V₁ ⊔ (T : Subgroup G)))
    (hK : (K.subgroupOf H).IsCComponent) (hN : (K.subgroupOf H).Normal)
    (hqs : IsQuasisimple (Source.starImage H K))
    (hcentral : centralizer (V₃ : Set G) ≤ M ⊓ normalizer (V : Set G))
    (hcomm : ⁅V₃, G₁.pCoreIn 2⁆ ≠ ⊥)
    (hstrict : Source.DH (Source.UH H V₃) (c.Ugamma V₃) (c.Aone V₁) < Source.UH H V₃)
    (hDstrict : Source.Dgamma (c.Ugamma V₃) (Source.UH H V₃) V₁ < c.Ugamma V₃)
    (models : letI := d.uh_elementary hHz
      MarkedModels H ((L ⊔ (T : Subgroup G)) ⊓ H) V₃ V₁)
    (a : letI := d.uh_elementary hHz
      SolvableExclusion.Five.StarAction H (Source.UH H V₃) V₁)
    (coords : letI := d.uh_elementary hHz
      (∃ e : Source.Hstar H ≃* A6, LinearCoordinates a (A6.subtype.comp e.toMonoidHom)) ∨
      (∃ e : Source.Hstar H ≃* S6, LinearCoordinates a e.toMonoidHom))
 : False := by
  let : IsElementaryAbelian 2 (Source.UH H V₃) := d.uh_elementary hHz
  have hline := (rank_and_lines_of_source d hHz hF9 hgen hK hN hqs hcentral hcomm
    models c hstrict hDstrict).1.1
  apply contradiction_of_linear_source d hHz hF9 c hH hgen hK hN hqs hcentral hcomm
    hstrict hDstrict models a coords
  · intro u hu hu1
    exact critical_point_moved d hHz hF9 c hH hstrict a coords hcomm ⟨u,hline hu⟩ hu hu1
  · exact critical_point_nonfixed d hHz hF9 c hH hstrict a

theorem contradiction_of_marked_models
    (d : LocalSetup T L V V₁ V₂ V₃ M G₁)
    (hHz : H ∈ Source.Hz (sourceOne L T V₁) (T : Subgroup G) G₁ M)
    (hF9 : (Section07.ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    (c : CriticalPair L (T : Subgroup G) H V)
    (hH : H = G₁)
    (hgen : H = K ⊔ (sourceOne L T V₁ ⊔ (T : Subgroup G)))
    (hK : (K.subgroupOf H).IsCComponent) (hN : (K.subgroupOf H).Normal)
    (hqs : IsQuasisimple (Source.starImage H K))
    (hcentral : centralizer (V₃ : Set G) ≤ M ⊓ normalizer (V : Set G))
    (hcomm : ⁅V₃, G₁.pCoreIn 2⁆ ≠ ⊥)
    (hstrict : Source.DH (Source.UH H V₃) (c.Ugamma V₃) (c.Aone V₁) < Source.UH H V₃)
    (hDstrict : Source.Dgamma (c.Ugamma V₃) (Source.UH H V₃) V₁ < c.Ugamma V₃)
    (a : letI := d.uh_elementary hHz
      SolvableExclusion.Five.StarAction H (Source.UH H V₃) V₁)
    (models : letI := d.uh_elementary hHz
      (∃ e : Source.Hstar H ≃* A6,
        (Source.starImage H ((L ⊔ (T : Subgroup G)) ⊓ H)).map e.toMonoidHom =
          a6SynthemeStabilizer ∧ LinearCoordinates a (A6.subtype.comp e.toMonoidHom)) ∨
      (∃ e : Source.Hstar H ≃* S6,
        (Source.starImage H ((L ⊔ (T : Subgroup G)) ⊓ H)).map e.toMonoidHom =
          BinaryFlags.H2 ∧ IntersectionBalance.CompatibleModel H V₃ V₁ a e))
 : False := by
  let : IsElementaryAbelian 2 (Source.UH H V₃) := d.uh_elementary hHz
  have marked : MarkedModels H ((L ⊔ (T : Subgroup G)) ⊓ H) V₃ V₁ := by
    refine ⟨a,?_⟩
    rcases models with ⟨e,hE,_⟩ | ⟨e,hE,he⟩
    · exact Or.inl ⟨e,hE⟩
    · exact Or.inr ⟨e,hE,he⟩
  have coords :
      (∃ e : Source.Hstar H ≃* A6, LinearCoordinates a (A6.subtype.comp e.toMonoidHom)) ∨
      (∃ e : Source.Hstar H ≃* S6, LinearCoordinates a e.toMonoidHom) := by
    rcases models with ⟨e,_,he⟩ | ⟨e,_,he⟩
    · exact Or.inl ⟨e,he⟩
    · exact Or.inr ⟨e,IntersectionBalance.CompatibleModel.action_cases H V₃ V₁ a e he⟩
  have hline := (rank_and_lines_of_source d hHz hF9 hgen hK hN hqs hcentral hcomm
    marked c hstrict hDstrict).1.1
  apply contradiction_of_marked_linear_source d hHz hF9 c hH hgen hK hN hqs hcentral
    hcomm hstrict hDstrict a models
  · intro u hu hu1
    exact critical_point_moved d hHz hF9 c hH hstrict a coords hcomm ⟨u,hline hu⟩ hu hu1
  · exact critical_point_nonfixed d hHz hF9 c hH hstrict a

/-- Terminal assembly from the actual recognized component section. There
 are no movement, nonfixedness, whole-module coordinate, or point-model premises. -/
theorem contradiction_of_component_section
    (d : LocalSetup T L V V₁ V₂ V₃ M G₁)
    (hHz : H ∈ Source.Hz (sourceOne L T V₁) (T : Subgroup G) G₁ M)
    (hF9 : (Section07.ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    (c : CriticalPair L (T : Subgroup G) H V)
    (hH : H = G₁)
    (hgen : H = K ⊔ (sourceOne L T V₁ ⊔ (T : Subgroup G)))
    (hK : (K.subgroupOf H).IsCComponent) (hN : (K.subgroupOf H).Normal)
    (hqs : IsQuasisimple (Source.starImage H K))
    (hcentral : centralizer (V₃ : Set G) ≤ M ⊓ normalizer (V : Set G))
    (hcomm : ⁅V₃, G₁.pCoreIn 2⁆ ≠ ⊥)
    (hstrict : Source.DH (Source.UH H V₃) (c.Ugamma V₃) (c.Aone V₁) < Source.UH H V₃)
    (hDstrict : Source.Dgamma (c.Ugamma V₃) (Source.UH H V₃) V₁ < c.Ugamma V₃)
    (models : letI := d.uh_elementary hHz
      MarkedModels H ((L ⊔ (T : Subgroup G)) ⊓ H) V₃ V₁)
    (a : letI := d.uh_elementary hHz
      SolvableExclusion.Five.StarAction H (Source.UH H V₃) V₁)
    (hUK : Source.UH H V₃ = ⁅Source.UH H V₃,K⁆)
    (eK : (K ⧸ pCore 2 K) ≃* A6)
    (hs : letI := d.uh_elementary hHz
      HasSectionModel H V₃ V₁ (IntersectionBalance.tildeRepresentation H (Source.UH H V₃) V₁ a)
        K (show K ≤ H from hgen ▸ le_sup_left) (BinaryPermutation.alternatingNaturalRepresentation (Fin 6)) eK) :
    False := by
  let : IsElementaryAbelian 2 (Source.UH H V₃) := d.uh_elementary hHz
  have hk : commutatorPreimage H (Source.UH H V₃) V₁ ≤ Source.QH H :=
    (f9_commutatorPreimage_eq _ hF9 H le_rfl).le.trans inf_le_right
  have coords := coordinates_of_component_section a (show K ≤ H from hgen ▸ le_sup_left)
    hK hN hk hUK eK hs
  exact contradiction_of_linear_models d hHz hF9 c hH hgen hK hN hqs hcentral hcomm
    hstrict hDstrict models a coords

/-- The same-marked source consumer constructs the alternating whole module
 before applying the terminal contradiction. The symmetric comparison is retained
 with its original plane marking from the earlier source alternative. -/
theorem contradiction_of_marked_component_section
    (d : LocalSetup T L V V₁ V₂ V₃ M G₁)
    (hHz : H ∈ Source.Hz (sourceOne L T V₁) (T : Subgroup G) G₁ M)
    (hF9 : (Section07.ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    (c : CriticalPair L (T : Subgroup G) H V)
    (hH : H = G₁)
    (hgen : H = K ⊔ (sourceOne L T V₁ ⊔ (T : Subgroup G)))
    (hK : (K.subgroupOf H).IsCComponent) (hN : (K.subgroupOf H).Normal)
    (hqs : IsQuasisimple (Source.starImage H K))
    (hcentral : centralizer (V₃ : Set G) ≤ M ⊓ normalizer (V : Set G))
    (hcomm : ⁅V₃, G₁.pCoreIn 2⁆ ≠ ⊥)
    (hstrict : Source.DH (Source.UH H V₃) (c.Ugamma V₃) (c.Aone V₁) < Source.UH H V₃)
    (hDstrict : Source.Dgamma (c.Ugamma V₃) (Source.UH H V₃) V₁ < c.Ugamma V₃)
    (a : letI := d.uh_elementary hHz
      SolvableExclusion.Five.StarAction H (Source.UH H V₃) V₁)
    (hUK : Source.UH H V₃ = ⁅Source.UH H V₃,K⁆)
    (models : letI := d.uh_elementary hHz
      (∃ e : Source.Hstar H ≃* A6,
        (Source.starImage H ((L ⊔ (T : Subgroup G)) ⊓ H)).map e.toMonoidHom =
          a6SynthemeStabilizer ∧
        ∃ eK : (K ⧸ pCore 2 K) ≃* A6,
          (∀ k : K, e (QuotientGroup.mk' (pCore 2 H)
            (inclusion (show K ≤ H from hgen ▸ le_sup_left) k)) = eK (QuotientGroup.mk' (pCore 2 K) k)) ∧
          HasSectionModel H V₃ V₁ (IntersectionBalance.tildeRepresentation H (Source.UH H V₃) V₁ a)
            K (show K ≤ H from hgen ▸ le_sup_left) (BinaryPermutation.alternatingNaturalRepresentation (Fin 6)) eK) ∨
      (∃ e : Source.Hstar H ≃* S6,
        (Source.starImage H ((L ⊔ (T : Subgroup G)) ⊓ H)).map e.toMonoidHom =
          BinaryFlags.H2 ∧ IntersectionBalance.CompatibleModel H V₃ V₁ a e)) : False := by
  let : IsElementaryAbelian 2 (Source.UH H V₃) := d.uh_elementary hHz
  apply contradiction_of_marked_models d hHz hF9 c hH hgen hK hN hqs hcentral hcomm
    hstrict hDstrict a
  rcases models with ⟨e,hE,eK,hm,hs⟩ | hs
  · exact Or.inl ⟨e,hE,alternating_coordinates_of_component_section a
      (show K ≤ H from hgen ▸ le_sup_left) hK hUK e eK hm hs⟩
  · exact Or.inr hs

/-- The actual point-parabolic model for any critical pair, suitable for the
 final source case split. Both point conditions are proved on its literal image. -/
theorem point_models_of_component_section
    (d : LocalSetup T L V V₁ V₂ V₃ M G₁)
    (hHz : H ∈ Source.Hz (sourceOne L T V₁) (T : Subgroup G) G₁ M)
    (hF9 : (Section07.ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    (c : CriticalPair L (T : Subgroup G) H V) (hH : H = G₁)
    (hstrict : Source.DH (Source.UH H V₃) (c.Ugamma V₃) (c.Aone V₁) < Source.UH H V₃)
    (hcomm : ⁅V₃, G₁.pCoreIn 2⁆ ≠ ⊥)
    (a : letI := d.uh_elementary hHz
      SolvableExclusion.Five.StarAction H (Source.UH H V₃) V₁)
    (hKH : K ≤ H) (hK : (K.subgroupOf H).IsCComponent) (hN : (K.subgroupOf H).Normal)
    (hUK : Source.UH H V₃ = ⁅Source.UH H V₃,K⁆)
    (eK : (K ⧸ pCore 2 K) ≃* A6)
    (hs : letI := d.uh_elementary hHz
      HasSectionModel H V₃ V₁ (IntersectionBalance.tildeRepresentation H (Source.UH H V₃) V₁ a)
        K hKH (BinaryPermutation.alternatingNaturalRepresentation (Fin 6)) eK)
    (hline : c.Aone V₁ ≤ Source.UH H V₃) :
    Nonempty (Source.starImage H (normalizer (c.Aone V₁ : Set G)) ≃* a6DuadStabilizer) ∨
      Nonempty (Source.starImage H (normalizer (c.Aone V₁ : Set G)) ≃* duadStabilizer) := by
  let : IsElementaryAbelian 2 (Source.UH H V₃) := d.uh_elementary hHz
  have hk : commutatorPreimage H (Source.UH H V₃) V₁ ≤ Source.QH H :=
    (f9_commutatorPreimage_eq _ hF9 H le_rfl).le.trans inf_le_right
  have coords := coordinates_of_component_section a hKH hK hN hk hUK eK hs
  have hA : Nat.card (c.Aone V₁) = 2 := by
    rw [CriticalPair.Aone,card_map_of_injective (MulAut.conj _).injective,d.line_card]
  obtain ⟨u,hu,_⟩ := (Nat.card_eq_two_iff' (1 : c.Aone V₁)).mp hA
  have hu1 : (u : G) ≠ 1 := fun he => hu (Subtype.ext he)
  let v : Source.UH H V₃ := ⟨u,hline u.property⟩
  have hm := critical_point_moved d hHz hF9 c hH hstrict a coords hcomm v u.property hu1
  have hnf := critical_point_nonfixed d hHz hF9 c hH hstrict a v u.property hu1
  rcases coords with ⟨e,he⟩ | ⟨e,he⟩
  · exact Or.inl (alternating_model_of_linear_coordinates a _ hA v u.property hu1
      d.line_card hF9.commutator_UH_QH_le_point hm e he hnf)
  · exact Or.inr (symmetric_model_of_linear_coordinates a _ hA v u.property hu1
      d.line_card hF9.commutator_UH_QH_le_point hm e he hnf)

end CFSG.Quasithin.Chapter13.Section08.SourceCompletion.TerminalPoint
