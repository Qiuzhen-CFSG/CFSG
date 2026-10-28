module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components.Triangle.ThirdVertexQuasisimpleSp4
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components.Triangle.ThirdVertexM23

/-!
# The three quotient models of the actual symplectic third vertex

The previous sieve left M₂₃ beside SL₃(4), Sp₄(4) and G₂(4). The native
marked comparison removes M₂₃ using the two original local A₅ sections
normalized by the same order-nine Cartan inside I = K₀ ∨ L₂. Thus the
actual join, with its original two-core, has the three models on p.763.

This proves that comparison conditionally on the explicit nontrivial common
normal Q. It does not prove its existence, the source SL₃(4) exclusion,
maximal-faithful placement, or either final triangle orientation. Those
remain with qt-d-1222-natural-relative-components. The original full flag,
module, relative normality and quotient markings remain in the hypotheses;
qt-d-1222-natural-local-geometry retains discharge of the preceding inputs.
Source: Aschbacher--Smith, 11.1.2, printed pp.762--764, especially p.763.
-/

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components.Triangle
public noncomputable section

open CFSG.Quasithin.Chapter12.Section02
open CFSG.Quasithin.ChapterB.QuasisimpleSource Representation
variable {G : Type*} [Group G] [Finite G]
    {T : Sylow 2 G} {L V : Subgroup G}
    (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)
    (m : ActionEquiv D.centralQuotientAction
      (restrictScalars (k := ZMod 2) (symplecticNatural (k := S.field.Carrier) 2)))
    (f : InvariantFlag (.sp4 m))

/-- The actual common-Q join has exactly the three quotient alternatives
on p.763. Both original local markings and the common Cartan discharge the
last M₂₃ row; Q remains the explicit independent source premise. -/
theorem sp4_triangle_join_three_models_of_common_normal
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
    let A := I ⧸ pCore 2 I
    IsQuasisimple A ∧
      (Source.IsSL A 3 4 ∨ Source.IsSp A 2 4 ∨ ClassificationModels.IsG2At A 4) := by
  intro I A
  obtain ⟨hq,hm⟩ := sp4_triangle_join_reduced_models_of_common_normal
    D S m f hu hm₁ hm₂ hfour hfix hX hK hLK hK₀ hK₀K hTK₀ hk hp hcard hmove
    hQ hQT hTQ hKQ hLQ
  refine ⟨hq,?_⟩
  rcases hm with hm | hm | hm | hm
  · exact .inl hm
  · exact .inr (.inl hm)
  · exact .inr (.inr hm)
  obtain ⟨_,hIL,_,_,_,_,hmark⟩ := sp4_triangle_marked_locals_of_common_normal
    D S m f hu hm₁ hm₂ hfour hfix hX hK hLK hK₀ hK₀K hTK₀ hk hp hcard hmove
    hQ hQT hTQ hKQ hLQ
  obtain ⟨hb,hbX,hXb,hmb,_,_⟩ := hmark K₀ (.inl rfl)
  obtain ⟨hc,_,hXc,hmc,_,_⟩ := hmark (f.Li 1) (.inr rfl)
  have hXcard : Nat.card X = 9 := by
    rw [(Coordinates.sp4 m).cartan_card hX,hfour]
    norm_num
  exact (local_join_not_m23_of_marked_cartan T hK₀.1
    (flag_mem_local_of_model D S f 1 hm₂).1 hIL.1 hb.le hc.le hTK₀
    (f.sylow_normalizes_Li 1) rfl hmb hmc (le_sup_right.trans hbX)
    hXb hXc hXcard hm).elim

end
end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components.Triangle
