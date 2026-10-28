module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components.Triangle.MaximalJankoFour

/-!
# Faithful maximal placement of the literal symplectic third vertex

The original common-Q construction and both marked local sections exclude
every strict faithful maximal envelope of I = K₀ ∨ L₂, including J₄.
Thus I itself is faithful maximal, inherits the original Hypothesis 12.2.3,
and admits a chosen module on the literal R₂(IT). No natural action on the
new module or quotient orientation is assumed here.

Common-normal existence, reselected naturality, the source SL₃(4) exclusion
and both final orientations remain with qt-d-1222-natural-relative-components.
The earlier flag/Cartan premises retain their original producers and final
discharge by qt-d-1222-natural-local-geometry.
Source: Aschbacher--Smith, 11.1.2, printed pp.762--764, especially the
application of 1.2.8(4) on p.764.
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

/-- The original common-Q third vertex is faithful maximal. The same
ambient source exclusions and the literal chosen-module construction apply
to I itself, with no naturality or triangle orientation assumed. -/
theorem sp4_triangle_maximal_faithful_of_common_normal
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
    FaithfulMaximalLocal T I ∧ Hypothesis1223 KnownSimple.IsKnownSimple T I ∧
      ∃ W : Subgroup G, Nonempty (ChosenModule T I W) := by
  intro I
  obtain ⟨hchosen,hcases⟩ := sp4_triangle_maximal_or_janko_four_of_common_normal
    D S m f hu hm₁ hm₂ hfour hfix hX hK hLK hK₀ hK₀K hTK₀ hk hp hcard hmove
    hQ hQT hTQ hKQ hLQ
  obtain ⟨hqI,hmI⟩ := sp4_triangle_join_three_models_of_common_normal
    D S m f hu hm₁ hm₂ hfour hfix hX hK hLK hK₀ hK₀K hTK₀ hk hp hcard hmove
    hQ hQT hTQ hKQ hLQ
  have hmax : FaithfulMaximalLocal T I := by
    rcases hcases with hmax | ⟨J,hIJ,_,hsource,hmJ,_⟩
    · exact hmax
    have hB := flag_mem_local_of_model D S f 1 hm₂
    have hm₂four : ClassicalGroup.IsPSL (f.Li 1 ⧸ pCore 2 (f.Li 1)) 2 4 := by
      simpa only [hfour,show (2:ℕ)^2 = 4 by decide] using hm₂
    obtain ⟨_,_,_,hm₀,_,_⟩ :=
      (sp4_triangle_marked_locals_of_common_normal D S m f hu hm₁ hm₂ hfour hfix
        hX hK hLK hK₀ hK₀K hTK₀ hk hp hcard hmove hQ hQT hTQ hKQ hLQ).2.2.2.2.2.2 K₀ (.inl rfl)
    exact (triangle_join_overcomponent_not_j4 T hK₀.1 hB.1 hsource.maximal_faithful.1.1.1
      ((show K₀ ≤ I from le_sup_left).trans hIJ.le)
      ((show f.Li 1 ≤ I from le_sup_right).trans hIJ.le)
      hTK₀ (f.sylow_normalizes_Li 1) hm₀ hm₂four hmI hmJ).elim
  refine ⟨hmax,?_,hchosen⟩
  exact {
    simpleQTKE := S.source.simpleQTKE
    maximal_faithful := hmax
    quasisimple := hqI
    no_rankTwo := S.source.no_rankTwo
    no_M22 := S.source.no_M22
    no_M23 := S.source.no_M23
    no_J4 := S.source.no_J4 }

end
end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components.Triangle
