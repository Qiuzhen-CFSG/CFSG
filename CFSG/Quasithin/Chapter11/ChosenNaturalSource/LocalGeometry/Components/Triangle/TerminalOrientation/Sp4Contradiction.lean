module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components.Triangle.TerminalOrientation.Sp4Cartan
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components.Triangle.TerminalOrientation.ProjectiveKernels
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components.Triangle.ReselectedComponentSp4

/-!
# Excluding the original Sp₄/Sp₄ triangle

Reselect the natural module at the literal I = K₀ ∨ L₂ using the common
normal Q and the earlier 7.0.1/3.2.5 inputs. The two flags have the same
plane residual and X ∩ L₁ = X ∩ K₀. Their four action characters therefore
identify the original cubic X₁ with C_X(K₀/O₂(K₀)). This contradicts the
action of the same cubic in the original full PSL₃(4) quotient. No opposite
orientation or subsequent triangle exclusion is assumed.
Source: Aschbacher--Smith, 11.1.2, printed p.764, final i=1 paragraph.
-/

open Subgroup Theory.GroupTheory Representation
open scoped IsMulCommutative
open CFSG.Quasithin.Chapter12.Section02 CFSG.Quasithin.ChapterB.QuasisimpleSource
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components
open Triangle Triangle.TerminalOrientation
public noncomputable section
variable {G : Type*} [Group G] [Finite G]
    {T : Sylow 2 G} {L V : Subgroup G}
    (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)
    (m : ActionEquiv D.centralQuotientAction
      (restrictScalars (k := ZMod 2) (symplecticNatural (k := S.field.Carrier) 2)))
    (f : InvariantFlag (.sp4 m))

/-- The original and reselected symplectic rows cannot both occur:
their literal cubic kernels agree, contrary to the same projective action. -/
theorem sp4_canonical_common_normal_not_sp4
    (hu : f.IsInnerUnique)
    (hm₁ : ClassicalGroup.IsPSL (f.Li 0 ⧸ pCore 2 (f.Li 0)) 2 (2^S.field.degree))
    (hm₂ : ClassicalGroup.IsPSL (f.Li 1 ⧸ pCore 2 (f.Li 1)) 2 (2^S.field.degree))
    (hfour : S.field.degree = 2)
    (hfix : f.Li 0 ≤ centralizer (f.Vi 0 : Set G))
    {K K₀ X Q : Subgroup G} (hX : IsCartan T L X)
    (hK : Source.NormalComponentIn (normalizer (f.Vi 0 : Set G)) K)
    (hLK : f.Li 0 < K) (hK₀ : K₀ ∈ Chapter1.L G T) (hK₀K : K₀ < K)
    (hne₀ : K₀ ≠ f.Li 0)
    (hTK₀ : (T : Subgroup G) ≤ normalizer (K₀ : Set G))
    (hk : ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 3 4)
    (hp : IsPGLThreeFour ((K ⊔ X : Subgroup G) ⧸ pCore 2 (K ⊔ X : Subgroup G)))
    (hcard : Nat.card (X ⊓ Closure.coreQuotientCentralizer (f.Li 1) : Subgroup G) = 3)
    (hmove : ¬ X ⊓ Closure.coreQuotientCentralizer (f.Li 1) ≤ centralizer (f.Vi 0 : Set G))
    (hQ : Q ≠ ⊥) (hQT : Q ≤ (T : Subgroup G))
    (hTQ : (T : Subgroup G) ≤ normalizer (Q : Set G))
    (hKQ : K₀ ≤ normalizer (Q : Set G)) (hLQ : f.Li 1 ≤ normalizer (Q : Set G))
    (hpre : ∀ (J W : Subgroup G) (D_J : ChosenModule T J W),
      Hypothesis1223 KnownSimple.IsKnownSimple T J →
      Chapter7.NormalizedSource.Alternatives G D_J.orbitRepresentation D_J.orbitComponent ∧
        D_J.Source325Alternatives) :
    ¬ Source.IsSp
      ((K₀ ⊔ f.Li 1 : Subgroup G) ⧸ pCore 2 (K₀ ⊔ f.Li 1 : Subgroup G)) 2 4 := by
  intro hmI
  obtain ⟨_,_,U,D_I,hcases⟩ :=
    sp4_triangle_reselected_component_of_common_normal_and_source701325
      D S m f hu hm₁ hm₂ hfour hfix hX hK hLK hK₀ hK₀K hTK₀ hk hp hcard hmove
      hQ hQT hTQ hKQ hLQ hpre
  have hnot : ¬ Source.IsSL
      ((K₀ ⊔ f.Li 1 : Subgroup G) ⧸ pCore 2 (K₀ ⊔ f.Li 1 : Subgroup G)) 3 4 := by
    rintro ⟨F,_,_,hF,⟨e⟩⟩
    obtain ⟨E,_,_,hE,⟨g⟩⟩ := hmI
    have hc := Nat.card_congr (e.symm.trans g).toEquiv
    rw [Matrix.PSL3.LinearThree.DefiningSylow.card_specialLinear,
      Theory.SpecificGroups.SymplecticFour.card_sp,hF,hE] at hc
    norm_num at hc
  obtain ⟨S_I,hd,_,_,hcartan,f_I,_,_,hfirst,hsecond,_⟩ := hcases.resolve_left hnot
  obtain ⟨_,h₁,h₀⟩ := first_triangle_cartan_intersections D S f hu hm₁ hfour
    hX hK hLK hK₀ hK₀K hk hp
  have hfirstX : X ⊓ f.Li 0 = X ⊓ f_I.Li 0 := by
    rw [hfirst]
    exact h₁.symm.trans h₀
  have hker := sp4_point_kernel_eq_of_reselected_sp4 S m hfour f hX
    S_I hd f_I hcartan hmI hfirstX hsecond.symm
  rw [hfirst] at hker
  have hcard₁ := sp4_point_kernel_card S m hfour f hX
  exact first_projective_cubic_not_in_other_kernel D S f hu hm₁ hfour hX hK hLK
    hK₀ hK₀K hne₀ hk inf_le_left hcard₁ inf_le_right (hker.le.trans inf_le_right)

end
end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components
