module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components.Triangle.MaximalSieve

/-!
# The remaining maximality row for the literal symplectic third vertex

The original common-Q construction gives I = K₀ ∨ L₂, both marked A₅
sections, Cartan containment, faithfulness and cubic rank two. The maximal
envelope comparison excludes all Lie rows, and MaximalSieve excludes all
exceptional rows except J₂, J₄ and Rudvalis. The original L₂ and its order-nine
normalizing Cartan exclude J₂ and Rudvalis in the containing group as well.
Thus a strict faithful maximal envelope has actual two-core quotient J₄.

This is checked progress toward 1.2.8(4)'s use in 11.1.2, not maximality or
source 11.1.2 itself. The J₄ comparison, common-normal existence, reselected
natural action, source SL₃(4) exclusion and both orientations remain with
qt-d-1222-natural-relative-components. Earlier flag and Cartan premises retain
their original producers and final discharge by qt-d-1222-natural-local-geometry.
Source: Aschbacher--Smith, 11.1.2, printed pp.762--764.
-/

open Subgroup Theory.GroupTheory
open CFSG.Quasithin.Chapter12.Section02
open CFSG.Quasithin.ChapterB.QuasisimpleSource Representation
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components.Triangle
public noncomputable section

variable {G : Type*} [Group G] [Finite G]
    {T : Sylow 2 G} {L V : Subgroup G}
    (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)
    (m : ActionEquiv D.centralQuotientAction
      (restrictScalars (k := ZMod 2) (symplecticNatural (k := S.field.Carrier) 2)))
    (f : InvariantFlag (.sp4 m))

/-- The literal common-Q join is faithful maximal unless its normalized
faithful maximal envelope has quotient J₄. Every other exceptional row is
excluded using its actual quotient and the two original marked local groups. -/
theorem sp4_triangle_maximal_or_janko_four_of_common_normal
    (hu : f.IsInnerUnique)
    (hm₁ : ClassicalGroup.IsPSL (f.Li 0 ⧸ pCore 2 (f.Li 0)) 2 (2^S.field.degree))
    (hm₂ : ClassicalGroup.IsPSL (f.Li 1 ⧸ pCore 2 (f.Li 1)) 2 (2^S.field.degree))
    (hfour : S.field.degree = 2)
    (hfix : f.Li 0 ≤ centralizer (f.Vi 0 : Set G))
    {K K₀ X Q : Subgroup G} (hX : IsCartan T L X)
    (hK : Source.NormalComponentIn (normalizer (f.Vi 0 : Set G)) K)
    (hLK : f.Li 0 < K) (hK₀ : K₀ ∈ Chapter1.L G T) (hK₀K : K₀ < K)
    (hTK₀ : (T : Subgroup G) ≤ normalizer (K₀ : Set G))
    (hk : ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 3 4)
    (hp : IsPGLThreeFour ((K ⊔ X : Subgroup G) ⧸ pCore 2 (K ⊔ X : Subgroup G)))
    (hcard : Nat.card (X ⊓ Closure.coreQuotientCentralizer (f.Li 1) : Subgroup G) = 3)
    (hmove : ¬ X ⊓ Closure.coreQuotientCentralizer (f.Li 1) ≤ centralizer (f.Vi 0 : Set G))
    (hQ : Q ≠ ⊥) (hQT : Q ≤ (T : Subgroup G))
    (hTQ : (T : Subgroup G) ≤ normalizer (Q : Set G))
    (hKQ : K₀ ≤ normalizer (Q : Set G)) (hLQ : f.Li 1 ≤ normalizer (Q : Set G)) :
    let I := K₀ ⊔ f.Li 1
    (∃ W : Subgroup G, Nonempty (ChosenModule T I W)) ∧
      (FaithfulMaximalLocal T I ∨
        ∃ J : Subgroup G, I < J ∧
          (T : Subgroup G) ≤ normalizer (J : Set G) ∧
          Hypothesis1223 KnownSimple.IsKnownSimple T J ∧
          Nonempty ((J ⧸ pCore 2 J) ≃* Janko4.Model) ∧
          ∃ W : Subgroup G, Nonempty (ChosenModule T J W)) := by
  intro I
  obtain ⟨hchosen,hmax | ⟨J,hIJ,hTJ,hsource,hmJ,hchosenJ⟩⟩ :=
    sp4_triangle_reselection_of_common_normal D S m f hu hm₁ hm₂ hfour hfix
      hX hK hLK hK₀ hK₀K hTK₀ hk hp hcard hmove hQ hQT hTQ hKQ hLQ
  · exact ⟨hchosen,.inl hmax⟩
  obtain ⟨_,hmI⟩ := sp4_triangle_join_three_models_of_common_normal
    D S m f hu hm₁ hm₂ hfour hfix hX hK hLK hK₀ hK₀K hTK₀ hk hp hcard hmove
    hQ hQT hTQ hKQ hLQ
  obtain ⟨_,_,_,_,hXI,hr,_⟩ := sp4_triangle_join_faithful_of_common_normal
    D S m f hu hm₁ hm₂ hfour hfix hX hK hLK hK₀ hK₀K hTK₀ hk hp hcard hmove
    hQ hQT hTQ hKQ hLQ
  have hJ := hsource.maximal_faithful.1.1
  have hrJ : 2 ≤ primeRank 3 (J ⧸ pCore 2 J) := by
    rw [primeRank_quotient_eq_of_isTwoGroup 3 (by decide) _ pCore_isPGroup]
    exact hr.ge.trans (primeRank_mono 3 hIJ.le)
  have hB := flag_mem_local_of_model D S f 1 hm₂
  have hm₂four : ClassicalGroup.IsPSL (f.Li 1 ⧸ pCore 2 (f.Li 1)) 2 4 := by
    simpa only [hfour,show (2:ℕ)^2 = 4 by decide] using hm₂
  obtain ⟨_,_,_,hm₀,_,_⟩ :=
    (sp4_triangle_marked_locals_of_common_normal D S m f hu hm₁ hm₂ hfour hfix
      hX hK hLK hK₀ hK₀K hTK₀ hk hp hcard hmove hQ hQT hTQ hKQ hLQ).2.2.2.2.2.2 K₀ (.inl rfl)
  have hXN : X ≤ normalizer (f.Li 1 : Set G) := by
    have hx : X ≤ L ⊓ normalizer (f.Vi 1 : Set G) :=
      le_inf (hX.1.trans inf_le_left) (f.cartan_normalizes hu hX 1)
    exact (hx.trans (L ⊓ normalizer (f.Vi 1 : Set G)).le_normalizer).trans
      (normalizer_le_normalizer_characteristic_image _ (solvableResidual _))
  have hXcard : Nat.card X = 9 := by
    rw [(Coordinates.sp4 m).cartan_card hX,hfour]
    norm_num
  have hspor := local_quotient_not_three_sporadics T hB.1 hJ.1
    (lt_of_le_of_lt (show f.Li 1 ≤ I from le_sup_right) hIJ)
    (f.sylow_normalizes_Li 1) (hXI.trans hIJ.le) hXN hXcard hm₂four
  have hcover := triangle_join_overcomponent_not_m22_cover T hK₀.1 hB.1 hJ.1
    ((show K₀ ≤ I from le_sup_left).trans hIJ.le)
    ((show f.Li 1 ≤ I from le_sup_right).trans hIJ.le)
    hTK₀ (f.sylow_normalizes_Li 1) hm₀ hm₂four hmI
  refine ⟨hchosen,.inr ⟨J,hIJ,hTJ,hsource,?_,hchosenJ⟩⟩
  rcases triangle_exceptional_overcomponent_sieve hIJ.le hrJ hsource.quasisimple hmI hmJ
      with hm | hm | hm | hm
  · exact (hcover hm).elim
  · exact (hspor (.inl hm)).elim
  · exact hm
  · exact (hspor (.inr (.inr hm))).elim

end
end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components.Triangle
