module

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.SixAndG2.SixRecognition.Constituents.Source
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.TransvectionModules.Recognition
public import Theory.GroupTheory.Commutator.PerfectLocalReduction

/-!
# The transvection branch retains the original A₆ component

The full 13.8.5 alternatives concern the entire actor H*. A normal component
of order 360 excludes both the S₇ and L₄(2) rows: the former would give a
proper nontrivial normal subgroup of A₇, and L₄(2) is the actual simple A₈.
In the remaining S₆ row, the image of the original K* has index two and is
therefore the literal alternating subgroup. The natural module projects to
itself; the five-dimensional augmentation module projects onto its natural
quotient with fixed kernel. These maps reconstruct HasSectionModel for the
original K/O₂(K), without replacing K by the component selected in 13.8.5.

The last theorem feeds SourceSix.source_alternative_of_section and retains
both full actions and the L₁ chief-factor statement. The earlier 13.8.5 inputs
remain with qt-d-1381-source and its source owners; the critical-pair equality
case supplies the transvection. The strict case and its constituent selection
remain with qt-d-138-six-section-recognition.

Source: Aschbacher–Smith 13.8.26, first sentence, printed p.962, using
13.8.5, printed pp.947–948. The actual L₄(2)–A₈ comparison retains the ATLAS
attribution and license in its imported model.
-/

public section

open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open scoped IsMulCommutative Pointwise
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.SixAndG2.SixRecognition.Constituents
open NaturalSix TransvectionRecognition TransvectionRecognition.Component
open TransvectionRecognition.Component.ModelExtension TransvectionRecognition.Component.RecognitionStep

private theorem six_card {J : Type*} [Group J] (e : J ≃* Alternating) : Nat.card J = 360 := by
  rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup]
  norm_num

private theorem symmetric_component {J : Type*} [Group J]
    (C : Subgroup J) (e : C ≃* Alternating) (f : J ≃* Symmetric) :
    ∃ e' : C ≃* Alternating, ∀ c : C, (e' c).val = f c := by
  have hc : Nat.card (C.map f.toMonoidHom) = 360 :=
    (card_map_of_injective f.injective).trans (six_card e)
  have hi : (C.map f.toMonoidHom).index = 2 := by
    have hh := (C.map f.toMonoidHom).index_mul_card
    rw [hc, Nat.card_perm, Nat.card_fin] at hh
    norm_num [Nat.factorial] at hh
    simpa using (show C.index = 2 by omega)
  let e' := (f.subgroupMap C).trans
    (MulEquiv.subgroupCongr (Equiv.Perm.eq_alternatingGroup_of_index_eq_two hi))
  exact ⟨e', fun _ => rfl⟩

private theorem no_symmetric_seven {J : Type*} [Group J]
    (C : Subgroup J) [C.Normal] [Group.IsPerfect C]
    (e : C ≃* Alternating) (f : J ≃* Equiv.Perm (Fin 7)) : False := by
  let N := C.map f.toMonoidHom
  let : N.Normal := Normal.map inferInstance _ f.surjective
  let : Group.IsPerfect N := Group.IsPerfect.ofSurjective
    (f := (f.subgroupMap C).toMonoidHom) (f.subgroupMap C).surjective
  have hN : N ≤ alternatingGroup (Fin 7) :=
    le_of_isPerfect_of_index_eq_two N _ alternatingGroup.index_eq_two
  let D := N.subgroupOf (alternatingGroup (Fin 7))
  let : D.Normal := inferInstance
  let : IsSimpleGroup (alternatingGroup (Fin 7)) := alternatingGroup.isSimpleGroup (by simp)
  have hd : Nat.card D = 360 :=
    (Nat.card_congr (subgroupOfEquivOfLe hN).toEquiv).trans
      ((card_map_of_injective f.injective).trans (six_card e))
  rcases (inferInstance : D.Normal).eq_bot_or_eq_top with hb | ht
  · rw [hb] at hd
    norm_num [Nat.factorial] at hd
  · rw [ht, Nat.card_congr Subgroup.topEquiv.toEquiv, nat_card_alternatingGroup] at hd
    norm_num [Nat.factorial] at hd

private theorem no_projective_four {J : Type*} [Group J]
    (C : Subgroup J) [C.Normal]
    (e : C ≃* Alternating)
    (f : J ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 4) (ZMod 2)) : False := by
  let g := f.trans Atlas.Comparisons.Exceptional.psl4TwoEquivAlt8
  let N := C.map g.toMonoidHom
  let : N.Normal := Normal.map inferInstance _ g.surjective
  let : IsSimpleGroup (alternatingGroup (Fin 8)) := alternatingGroup.isSimpleGroup (by simp)
  have hn : Nat.card N = 360 := (card_map_of_injective g.injective).trans (six_card e)
  rcases (inferInstance : N.Normal).eq_bot_or_eq_top with hb | ht
  · rw [hb] at hn
    norm_num [Nat.factorial] at hn
  · rw [ht, Nat.card_congr Subgroup.topEquiv.toEquiv, nat_card_alternatingGroup] at hn
    norm_num [Nat.factorial] at hn

private theorem symmetric_projection {J E : Type*} [Group J]
    [AddCommGroup E] [Module (ZMod 2) E]
    (ρ : Representation (ZMod 2) J E)
    (hm : HasActionModel ρ symmetricAction ∨ HasActionModel ρ (BinaryPermutation.coreRepresentation (Fin 6))) :
    ∃ (f : J ≃* Symmetric) (p : E →ₗ[ZMod 2] Natural),
      Function.Surjective p ∧
      (∀ j v, p (ρ j v) = symmetricAction (f j) (p v)) ∧
      p.ker ≤ fixedSpace ρ ⊤ := by
  rcases hm with ⟨f, E', hE⟩ | ⟨f, E', hE⟩
  · refine ⟨f, E'.toLinearMap, E'.surjective, hE, ?_⟩
    intro v hv j
    have hz : v = 0 := E'.injective (hv.trans (map_zero E').symm)
    rw [hz, map_zero]
  · let q := BinaryPermutation.coreToNatural (Fin 6)
    refine ⟨f, q.comp E'.toLinearMap, (BinaryPermutation.coreToNatural_surjective).comp E'.surjective,
      ?_, ?_⟩
    · intro j v
      change q (E' (ρ j v)) = symmetricAction (f j) (q (E' v))
      rw [hE]
      exact BinaryPermutation.coreToNatural_equivariant (f j) (E' v)
    · intro v hv j
      apply E'.injective
      change E' (ρ j.val v) = E' v
      rw [hE]
      have hc : (E' v).val ∈ BinaryPermutation.constants (Fin 6) :=
        (Submodule.Quotient.mk_eq_zero _).mp (congrArg Subtype.val hv)
      obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp hc
      apply Subtype.ext
      change BinaryPermutation.representation (Fin 6) (f j) (E' v).val = (E' v).val
      rw [← ha, map_smul, BinaryPermutation.permute_allOne]

universe u
variable {G : Type u} [Group G] [Finite G] {H K V₃ V₁ : Subgroup G}
  [(V₁.subgroupOf (Source.UH H V₃)).Normal]
  [IsElementaryAbelian 2 (Source.Utilde H V₃ V₁)]

/-- Recover the original component section from either of the two S₆ modules. -/
theorem section_of_full_symmetric_action
    (hKH : K ≤ H) (hK : (K.subgroupOf H).IsCComponent)
    (e₀ : (K ⧸ pCore 2 K) ≃* Alternating)
    (ρ : Representation (ZMod 2) (Source.Hstar H) (Additive (Source.Utilde H V₃ V₁)))
    (hρ : IsConjugation H V₃ V₁ ρ)
    (hgen : Source.UH H V₃ = ⁅Source.UH H V₃, K⁆)
    (hm : HasActionModel ρ symmetricAction ∨ HasActionModel ρ (BinaryPermutation.coreRepresentation (Fin 6))) :
    ∃ eK : (K ⧸ pCore 2 K) ≃* Alternating,
      HasSectionModel H V₃ V₁ ρ K hKH alternatingAction eK := by
  obtain ⟨f, p, hp, he, hk⟩ := symmetric_projection ρ hm
  let j := Components.componentStarEquiv H K hKH hK
  obtain ⟨eC, hc⟩ := symmetric_component (Source.starImage H K) (j.symm.trans e₀) f
  refine ⟨j.trans eC, section_of_natural_quotient hKH ρ hρ hgen _ p hp ?_ ?_⟩
  · intro k v
    have hh := he (QuotientGroup.mk' (pCore 2 H) (inclusion hKH k)) v
    have heq := hc (j (QuotientGroup.mk' (pCore 2 K) k))
    rw [Components.componentStarEquiv_mk] at heq
    change p (ρ (QuotientGroup.mk' (pCore 2 H) (inclusion hKH k)) v) =
      symmetricAction ((eC (j (QuotientGroup.mk' (pCore 2 K) k))).val) (p v)
    rwa [heq]
  · exact hk.trans (fixedSpace_antitone ρ le_top)

/-- The original A₆ component excludes both other rows of the full 13.8.5 conclusion. -/
theorem section_of_full_alternatives
    (hKH : K ≤ H) (hK : (K.subgroupOf H).IsCComponent)
    (e₀ : (K ⧸ pCore 2 K) ≃* Alternating)
    (hfit : Source.starImage H K = generalizedFitting (Source.Hstar H))
    (ρ : Representation (ZMod 2) (Source.Hstar H) (Additive (Source.Utilde H V₃ V₁)))
    (hρ : IsConjugation H V₃ V₁ ρ)
    (hgen : Source.UH H V₃ = ⁅Source.UH H V₃, K⁆)
    (L L₁ : Subgroup G) (hL : L₁ ≤ H) [IsElementaryAbelian 2 (Source.UH H V₃)]
    (hm : FullAlternatives H L L₁ V₃ V₁ hL ρ) :
    ∃ eK : (K ⧸ pCore 2 K) ≃* Alternating,
      HasSectionModel H V₃ V₁ ρ K hKH alternatingAction eK := by
  rcases hm with ⟨hn | ⟨hn, _⟩, _⟩ | ⟨hn | hn, _⟩
  · exact section_of_full_symmetric_action hKH hK e₀ ρ hρ hgen (Or.inl hn)
  · exact section_of_full_symmetric_action hKH hK e₀ ρ hρ hgen (Or.inr hn)
  · obtain ⟨f, _⟩ := hn
    let : (Source.starImage H K).Normal := hfit ▸ inferInstance
    let e := (Components.componentStarEquiv H K hKH hK).symm.trans e₀
    let : IsQuasisimple (Source.starImage H K) := (component_properties _ hfit e).1
    exact (no_symmetric_seven (Source.starImage H K) e f).elim
  · obtain ⟨f, _⟩ := hn
    let : (Source.starImage H K).Normal := hfit ▸ inferInstance
    let e := (Components.componentStarEquiv H K hKH hK).symm.trans e₀
    exact (no_projective_four (Source.starImage H K) e f).elim

/-- Apply the proved 13.8.5 theorem and keep the prescribed component K. -/
theorem section_of_transvection
    (T : Sylow 2 G) {L V V₂ M G₁ : Subgroup G}
    (d : LocalSetup T L V V₁ V₂ V₃ M G₁)
    (earlier : EarlierInputs T L V V₁ V₂ V₃ M G₁)
    (localEarlier : Solvable.EarlierLocalInputs (G := G))
    (hB18 : ∀ (B E : Type u) [Group B] [Finite B] [Group.IsSolvable B]
      [AddCommGroup E] [Module (ZMod 2) E] [Finite E]
      (σ : Representation (ZMod 2) B E),
      pCore 2 B = ⊥ → Function.Injective σ → IsFFModule σ →
        Nonempty (ChapterB.SolvableFFFactors σ))
    (hG64 : G64SourceTheorem.{u} KnownSimple.IsKnownSimple)
    (hH : H ∈ Source.Hz (sourceOne L T V₁) (T : Subgroup G) G₁ M)
    (hKH : K ≤ H) (hK : (K.subgroupOf H).IsCComponent)
    (e₀ : (K ⧸ pCore 2 K) ≃* Alternating)
    (hfit : Source.starImage H K = generalizedFitting (Source.Hstar H))
    (hgen : Source.UH H V₃ = ⁅Source.UH H V₃, K⁆)
    (ρ : Representation (ZMod 2) (Source.Hstar H) (Additive (Source.Utilde H V₃ V₁)))
    (hρ : IsConjugation H V₃ V₁ ρ)
    (ht : ∃ t : Source.Hstar H, IsTransvection ρ t) :
    ∃ eK : (K ⧸ pCore 2 K) ≃* Alternating,
      HasSectionModel H V₃ V₁ ρ K hKH alternatingAction eK := by
  let := d.uh_elementary hH
  have hm := (lemma_13_8_5 T d earlier localEarlier hB18 hG64 hH ρ hρ ht).2
  exact section_of_full_alternatives hKH hK e₀ hfit ρ hρ hgen L
    (sourceOne L T V₁) (le_sup_left.trans hH.1.2) hm

/-- The transvection branch with its literal full-module and L₁ consumer. -/
theorem source_alternative_of_transvection
    (T : Sylow 2 G) {L V V₂ M G₁ : Subgroup G}
    (d : LocalSetup T L V V₁ V₂ V₃ M G₁)
    (earlier : EarlierInputs T L V V₁ V₂ V₃ M G₁)
    (localEarlier : Solvable.EarlierLocalInputs (G := G))
    (hB18 : ∀ (B E : Type u) [Group B] [Finite B] [Group.IsSolvable B]
      [AddCommGroup E] [Module (ZMod 2) E] [Finite E]
      (σ : Representation (ZMod 2) B E),
      pCore 2 B = ⊥ → Function.Injective σ → IsFFModule σ →
        Nonempty (ChapterB.SolvableFFFactors σ))
    (hG64 : G64SourceTheorem.{u} KnownSimple.IsKnownSimple)
    (hH : H ∈ Source.Hz (sourceOne L T V₁) (T : Subgroup G) G₁ M)
    (hKH : K ≤ H) (hK : (K.subgroupOf H).IsCComponent)
    (e₀ : (K ⧸ pCore 2 K) ≃* Alternating)
    (hfit : Source.starImage H K = generalizedFitting (Source.Hstar H))
    (hgen : Source.UH H V₃ = ⁅Source.UH H V₃, K⁆)
    (ρ : Representation (ZMod 2) (Source.Hstar H) (Additive (Source.Utilde H V₃ V₁)))
    (hρ : IsConjugation H V₃ V₁ ρ)
    (ht : ∃ t : Source.Hstar H, IsTransvection ρ t) :
    let := d.uh_elementary hH
    ∃ eK : (K ⧸ pCore 2 K) ≃* Alternating,
      HasSectionModel H V₃ V₁ ρ K hKH alternatingAction eK ∧
      (H : Set G) = (K : Set G) * (T : Set G) ∧
      Nonempty ((L ⧸ pCore 2 L) ≃* Alternating) ∧
      SourceSix.MarkedFullAction hKH eK ρ ∧
      CriticalGeometry.Reorientation.TwoNoncentralChiefFactors
        (ChiefQuotient.loneQuotientRepresentation H V₃ V₁ (sourceOne L T V₁)
          (le_sup_left.trans hH.1.2) ρ) := by
  let := d.uh_elementary hH
  obtain ⟨eK, hs⟩ := section_of_transvection T d earlier localEarlier hB18 hG64 hH
    hKH hK e₀ hfit hgen ρ hρ ht
  exact ⟨eK, hs, SourceSix.source_alternative_of_section T d earlier hH hKH hK ρ hρ eK hs⟩

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.SixAndG2.SixRecognition.Constituents
