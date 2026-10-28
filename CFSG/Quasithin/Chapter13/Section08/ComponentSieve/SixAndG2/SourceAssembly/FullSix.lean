module
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.SixAndG2.SourceAssembly.Six
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.SixAndG2.SourceAssembly.RankOne
public import CFSG.Quasithin.Chapter13.Section08.SourceCompletion.SolvableB18

/-!
# Both original A₆ component-section cases

Split on rank-one displacement in the actual H* action on U_H/V₁.
In its absence, the selected critical geometry and literal index-three
parabolic give strict recognition. In its presence, a binary rank-one
operator is a transvection, and the proved B.1.8 and full G.6.4 theorems
give the recognized component section. Both branches construct the same
full-module alternatives with their intrinsic component marking and the
original L₁ chief factors.
Source: Aschbacher–Smith, 13.8.5 and 13.8.26, printed pp.947,962.
-/

public section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open scoped IsMulCommutative Pointwise
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.SixAndG2.SourceAssembly
open TransvectionRecognition TransvectionRecognition.Component
open TransvectionRecognition.Component.ModelExtension
open CriticalGeometry SourceCompletion
private theorem rank_one_transvection
    {D E : Type*} [Group D] [AddCommGroup E] [Module (ZMod 2) E]
    [FiniteDimensional (ZMod 2) E]
    (ρ : Representation (ZMod 2) D E) (g : D)
    (hr : Module.finrank (ZMod 2) (LinearMap.range (ρ g - LinearMap.id)) = 1) :
    IsTransvection ρ g := by
  let t := LinearEquiv.ofBijective (ρ g) (ρ.apply_bijective g)
  obtain ⟨f, v, he⟩ := LinearEquiv.mem_dilatransvections_iff_finrank.mpr
    (show Module.finrank (ZMod 2) (LinearMap.range (t.toLinearMap - LinearMap.id)) ≤ 1 from hr.le)
  have hact (w : E) : ρ g w = w + f w • v := LinearMap.congr_fun he w
  have hne : ρ g ≠ LinearMap.id := by
    intro h
    rw [h, sub_self, LinearMap.range_zero, finrank_bot] at hr
    contradiction
  have hf : f ≠ 0 := by
    intro h
    apply hne
    ext w
    simpa [h] using hact w
  have hv : v ≠ 0 := by
    intro h
    apply hne
    ext w
    simpa [h] using hact w
  have hfv : f v = 0 := by
    rcases (by decide : ∀ x : ZMod 2, x = 0 ∨ x = 1) (f v) with h | h
    · exact h
    · have htv : t v = 0 := by
        change ρ g v = 0
        rw [hact, h, one_smul, ZModModule.add_self]
      exact (hv (t.map_eq_zero_iff.mp htv)).elim
  exact ⟨f, v, hf, hv, hfv, hact⟩

universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L H V V₁ V₂ V₃ M G₁ : Subgroup G}
  [IsElementaryAbelian 2 (Source.UH H V₃)]

/-- Both critical cases of original 13.8.26, with every local section,
parabolic and selected-pair premise constructed. The genuine full G.6.4
and B.1.8 theorems supply the transvection branch's appendix inputs. -/
theorem six_source_alternative
    {K : Subgroup G}
    (d : LocalSetup T L V V₁ V₂ V₃ M G₁)
    (earlier : EarlierInputs T L V V₁ V₂ V₃ M G₁)
    (localEarlier : Solvable.EarlierLocalInputs (G := G))
    (hHz : H ∈ Source.Hz (sourceOne L T V₁) (T : Subgroup G) G₁ M)
    (hF9 : (Section07.ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    (hKH : K ≤ H) (hK : (K.subgroupOf H).IsCComponent)
    (hN : (K.subgroupOf H).Normal) (hgen : H = K ⊔ (T : Subgroup G))
    (hfit : generalizedFitting (Source.Hstar H) = Source.starImage H K)
    (hUK : Source.UH H V₃ = ⁅Source.UH H V₃, K⁆)
    (hcentral : centralizer (V₃ : Set G) ≤ M ⊓ normalizer (V : Set G))
    (hcomm : ⁅V₃, G₁.pCoreIn 2⁆ ≠ ⊥)
    (eK : (K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 6))
    (ρ : Representation (ZMod 2) (Source.Hstar H) (Additive (Source.Utilde H V₃ V₁)))
    (hρ : IsConjugation H V₃ V₁ ρ) :
    ∃ eK' : (K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 6),
      HasSectionModel H V₃ V₁ ρ K hKH
        (BinaryPermutation.alternatingNaturalRepresentation (Fin 6)) eK' ∧
      (H : Set G) = (K : Set G) * (T : Set G) ∧
      Nonempty ((L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6)) ∧
      SourceSix.MarkedFullAction hKH eK' ρ ∧
      Reorientation.TwoNoncentralChiefFactors
        (ChiefQuotient.loneQuotientRepresentation H V₃ V₁ (sourceOne L T V₁)
          (le_sup_left.trans hHz.1.2) ρ) := by
  by_cases hno : ∀ g, Module.finrank (ZMod 2) (LinearMap.range (ρ g - LinearMap.id)) ≠ 1
  · exact six_alternative_of_no_rank_one d earlier hHz hF9 hKH hK hN hgen hfit hUK
      hcentral hcomm eK ρ hρ hno
  · obtain ⟨a, ha⟩ := not_forall.mp hno
    have hr := Classical.not_not.mp ha
    exact SixRecognition.Constituents.source_alternative_of_transvection T d earlier
      localEarlier solvable_ff_factors RankOneSource.source_theorem hHz
      hKH hK eK hfit.symm hUK ρ hρ ⟨a, rank_one_transvection ρ a hr⟩

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.SixAndG2.SourceAssembly
