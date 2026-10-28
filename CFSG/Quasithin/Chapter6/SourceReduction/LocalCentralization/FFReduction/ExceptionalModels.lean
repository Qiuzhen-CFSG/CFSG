module
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.ExceptionalOvercomponents
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.ExceptionalOvercomponentsAlternatingSeven
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.ExceptionalOvercomponentsAlternatingSevenEven
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.ExceptionalOvercomponentsAlternatingSevenSporadic
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.ExceptionalOvercomponentsJankoFour
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.ExceptionalOvercomponentsAlternatingSevenBinary
public import CFSG.Quasithin.Chapter6.SourceReduction.LocalCentralization.FFReduction

/-!
# Proved branches of exceptional local enlargement in the Cartan construction

The J₂ branch is unconditional. The M₂₃ branch is reduced to the restricted
intrinsic J₄ Sylow-overgroup input, with all local quotient transports
discharged. The A₇ branch has a quasisimple containing quotient; the
even-rank-two, binary higher-linear and three unwanted sporadic rows
have the explicit consequences below.

These results apply to the actual LocalCartanWitness and the same maximal
K used by localCartan_maximal_models_of_earlier_inputs. They do not yet
establish ExceptionalLocalOvercomponentModels: the remaining A₇ inspection
and the intrinsic J₄ input remain with its assembly owner.

Source: Aschbacher–Smith 1.2.8, pp.506–507, and 5.1.13, p.637.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric
universe u
variable {G : Type u} [Group G] [Finite G]

/-- The J₂ branch of the actual maximal local Cartan construction, with only
the independently owned earlier Baumann theorem left explicit. -/
theorem localCartan_maximal_models_of_jankoTwo
    (hbaum : RankOneBaumannNormalizerControl G)
    {T : Sylow 2 G} {L W H A Y X D : Subgroup G} {n : ℕ}
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hY : Y ∈ Chapter1.HOver G (H : Set G))
    (d : LocalCartanWitness T H A Y X D) (hXC : ¬ X ≤ omegaCentralizer T)
    (hJ : Nonempty ((X ⧸ pCore 2 X) ≃* Sporadic.LeechRelated.J2.Carrier)) :
    ∃ K : Subgroup G,
      X ≤ K ∧ K ∈ Chapter1.LStar G (T : Subgroup G) ∧
      (T : Subgroup G) ≤ normalizer (K : Set G) ∧
      LocalExceptionalQuotient K ∧
      ¬ K ≤ normalizer (ChapterB.baumann (T : Subgroup G) : Set G) ∧
      localOmegaModule T K ∈ reducedFamily (K ⊔ (T : Subgroup G)) ∧
      localOmegaModule T K ≠ ⊥ ∧
      conjugateSpanBy (Stellmacher.omegaOneCenterAmbient (T : Subgroup G)) K =
        localOmegaModule T K ⊔
          (Stellmacher.omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (K : Set G)) := by
  obtain ⟨K,hXK,hK,hn,_,hU,hUne,hspan⟩ :=
    localCartan_maximal_reduced_configuration h hH hY d hXC
  have he := Chapter1.Section02.eq_of_jankoTwo_local_overcomponent h.qtke T
    (d.mem_localFamily hH.1.1.2 hY) (d.sylow_normalizes hH.1.1.2 hY.2) hK.1 hXK hJ
  refine ⟨K,hXK,hK,hn,Or.inr (Or.inl (he ▸ hJ)),?_,hU,hUne,hspan⟩
  intro hKB
  exact d.component_escape hH.1.1.2 h.sylow_normalizes hH.1.2
    (hXK.trans (hKB.trans (hbaum T L W n h)))

/-- On the actual M₂₃ witness, the checked catalogue leaves only the J₄ row
in addition to the required exceptional quotient list. -/
theorem localCartan_mathieuTwentyThree_overcomponent_models_or_jankoFour
    {T : Sylow 2 G} {H A Y X D K : Subgroup G}
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hTH : (T : Subgroup G) ≤ H) (hY : Y ∈ Chapter1.HOver G (H : Set G))
    (d : LocalCartanWitness T H A Y X D)
    (hK : K ∈ Chapter1.LStar G (T : Subgroup G)) (hXK : X ≤ K)
    (hM : Nonempty ((X ⧸ pCore 2 X) ≃* Sporadic.Mathieu.M23)) :
    LocalExceptionalQuotient K ∨ Nonempty ((K ⧸ pCore 2 K) ≃* Janko4.Model) := by
  rcases Chapter1.Section02.mathieuTwentyThree_local_overcomponent_or_jankoFour
    hG T (d.mem_localFamily hTH hY) (d.sylow_normalizes hTH hY.2) hK.1 hXK hM with h | h
  · exact Or.inl (Or.inr (Or.inr h))
  · exact Or.inr h
/-- The A₇ witness makes the actual maximal local quotient quasisimple.
The further carrier inspection is not asserted by this theorem. -/
theorem localCartan_alternatingSeven_overcomponent_quasisimple
    {T : Sylow 2 G} {H A Y X D K : Subgroup G}
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hTH : (T : Subgroup G) ≤ H) (hY : Y ∈ Chapter1.HOver G (H : Set G))
    (d : LocalCartanWitness T H A Y X D)
    (hK : K ∈ Chapter1.LStar G (T : Subgroup G)) (hXK : X ≤ K)
    (hA : Nonempty ((X ⧸ pCore 2 X) ≃* alternatingGroup (Fin 7))) :
    IsQuasisimple (K ⧸ pCore 2 K) :=
  Chapter1.Section02.ExceptionalOvercomponents.alternatingSeven_local_overcomponent_quotient_quasisimple
    hG T (d.mem_localFamily hTH hY) hK.1 hXK hA


/-- The actual A₇ witness excludes the three large unwanted sporadic
quotients of its maximal local overcomponent. -/
theorem localCartan_alternatingSeven_overcomponent_not_otherSporadic
    {T : Sylow 2 G} {H A Y X D K : Subgroup G}
    (hTH : (T : Subgroup G) ≤ H) (hY : Y ∈ Chapter1.HOver G (H : Set G))
    (d : LocalCartanWitness T H A Y X D)
    (hK : K ∈ Chapter1.LStar G (T : Subgroup G)) (hXK : X ≤ K)
    (hA : Nonempty ((X ⧸ pCore 2 X) ≃* alternatingGroup (Fin 7))) :
    ¬ Nonempty ((K ⧸ pCore 2 K) ≃* Sporadic.LeechRelated.HS.Carrier) ∧
    ¬ Nonempty ((K ⧸ pCore 2 K) ≃* Held.He) ∧
    ¬ Nonempty ((K ⧸ pCore 2 K) ≃* Rudvalis.Model) :=
  Chapter1.Section02.ExceptionalOvercomponents.AlternatingSevenModels.local_overcomponent_not_otherSporadic
    T (d.mem_localFamily hTH hY) (d.sylow_normalizes hTH hY.2) hK.1 hXK hA


/-- On the actual A₇ witness, the simple even-rank-two branch of the
containing-model inspection preserves the required quotient list. -/
theorem localCartan_alternatingSeven_overcomponent_models_of_rankTwo
    {T : Sylow 2 G} {H A Y X D K : Subgroup G}
    (hTH : (T : Subgroup G) ≤ H) (hY : Y ∈ Chapter1.HOver G (H : Set G))
    (d : LocalCartanWitness T H A Y X D)
    (hK : K ∈ Chapter1.LStar G (T : Subgroup G)) (hXK : X ≤ K)
    (hA : Nonempty ((X ⧸ pCore 2 X) ≃* alternatingGroup (Fin 7)))
    (hsimple : IsSimpleGroup (K ⧸ pCore 2 K))
    {n : ℕ} (hmodel : ChapterA.Section02.IsTheoremCRankTwoModel (K ⧸ pCore 2 K) n) :
    LocalExceptionalQuotient K :=
  Or.inl (Chapter1.Section02.ExceptionalOvercomponents.AlternatingSevenEven.local_overcomponent_of_rankTwo
    T (d.mem_localFamily hTH hY) (d.sylow_normalizes hTH hY.2) hK.1 hXK hA hsimple hmodel)

/-- The M₂₃ branch of the actual Cartan construction. The independent
Baumann theorem and the intrinsic J₄ placement remain explicit. -/
theorem localCartan_maximal_models_of_mathieuTwentyThree
    (hcover : Chapter1.Section02.ExceptionalOvercomponents.JankoFourTwentyThreeOvergroups)
    (hbaum : RankOneBaumannNormalizerControl G)
    {T : Sylow 2 G} {L W H A Y X D : Subgroup G} {n : ℕ}
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hY : Y ∈ Chapter1.HOver G (H : Set G))
    (d : LocalCartanWitness T H A Y X D) (hXC : ¬ X ≤ omegaCentralizer T)
    (hM : Nonempty ((X ⧸ pCore 2 X) ≃* Sporadic.Mathieu.M23)) :
    ∃ K : Subgroup G,
      X ≤ K ∧ K ∈ Chapter1.LStar G (T : Subgroup G) ∧
      (T : Subgroup G) ≤ normalizer (K : Set G) ∧
      LocalExceptionalQuotient K ∧
      ¬ K ≤ normalizer (ChapterB.baumann (T : Subgroup G) : Set G) ∧
      localOmegaModule T K ∈ reducedFamily (K ⊔ (T : Subgroup G)) ∧
      localOmegaModule T K ≠ ⊥ ∧
      conjugateSpanBy (Stellmacher.omegaOneCenterAmbient (T : Subgroup G)) K =
        localOmegaModule T K ⊔
          (Stellmacher.omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (K : Set G)) := by
  obtain ⟨K,hXK,hK,hn,_,hU,hUne,hspan⟩ :=
    localCartan_maximal_reduced_configuration h hH hY d hXC
  have hm := Chapter1.Section02.ExceptionalOvercomponents.mathieuTwentyThree_local_overcomponent_of_jankoFour_overgroups
    hcover h.qtke T (d.mem_localFamily hH.1.1.2 hY)
    (d.sylow_normalizes hH.1.1.2 hY.2) hK.1 hXK hM
  refine ⟨K,hXK,hK,hn,Or.inr (Or.inr hm),?_,hU,hUne,hspan⟩
  intro hKB
  exact d.component_escape hH.1.1.2 h.sylow_normalizes hH.1.2
    (hXK.trans (hKB.trans (hbaum T L W n h)))

/-- The original A₇ witness excludes both binary higher-linear quotients. -/
theorem localCartan_alternatingSeven_overcomponent_not_binaryFour_or_Five
    {T : Sylow 2 G} {H A Y X D K : Subgroup G}
    (hTH : (T : Subgroup G) ≤ H) (hY : Y ∈ Chapter1.HOver G (H : Set G))
    (d : LocalCartanWitness T H A Y X D)
    (hK : K ∈ Chapter1.LStar G (T : Subgroup G)) (hXK : X ≤ K)
    (hA : Nonempty ((X ⧸ pCore 2 X) ≃* alternatingGroup (Fin 7)))
    {n : ℕ} (hn : n = 4 ∨ n = 5) :
    ¬ ClassicalGroup.IsPSL (K ⧸ pCore 2 K) n 2 :=
  Chapter1.Section02.ExceptionalOvercomponents.AlternatingSevenBinary.local_overcomponent_not_binaryFour_or_Five
    T (d.mem_localFamily hTH hY) (d.sylow_normalizes hTH hY.2) hK.1 hXK hA hn

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric
