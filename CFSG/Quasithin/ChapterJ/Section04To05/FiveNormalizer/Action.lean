module

public import CFSG.Quasithin.ChapterJ.Section04To05.FiveNormalizer.Intersection
public import CFSG.Quasithin.ChapterJ.Section04To05.SecondQuotient.Kernel

/-!
# The actual complement acts on the five-hyperplane

The complement A constructed in the second quotient normalizes Q₅S₂.
Using the proved W=S₂ and (Q₅W)∩Q=Q₀Q₅ therefore makes A normalize the
original hyperplane. Its genuine normalizer residual then proves that A
normalizes B₅Q₅ and Q₅. The same original A defines F₁=AQ₅B₅.

Source: Aschbacher–Smith, J.4.4(3–4), printed p.441.
-/

public section
noncomputable section
open Subgroup
namespace CFSG.Quasithin.ChapterJ.RuSubgroup
open Centralizers.Choices
variable {G:Type*} [Group G] [Finite G] {d:LocalSetup G} (p:Plane d)

theorem Plane.A_le_H (B5:Sylow 5 d.toTypeRuSetup.H) : p.A B5≤d.toTypeRuSetup.H :=
  (p.A_le_R₂ B5).trans (p.R₂_le_T.trans d.toTypeRuSetup.T_le_H)

theorem SourceChoice.A_normalizes_fiveHyperplane (s:SourceChoice p)
    (B5:Sylow 5 d.toTypeRuSetup.H) (hi:∀a∈B5Image B5,s.v*a*s.v⁻¹=a⁻¹) :
    p.A B5≤normalizer (fiveHyperplane d B5:Set G) := by
  have h := (le_inf (s.A_normalizes_Q₅S₂ p B5 hi)
    ((p.A_le_H B5).trans d.ru2.six.normalized)).trans inf_normalizer_le_normalizer_inf
  rwa [←p.W_eq_S₂,s.Q₅_sup_W_inf_Q B5 hi] at h

theorem SourceChoice.A_normalizes_fiveProduct (s:SourceChoice p)
    (B5:Sylow 5 d.toTypeRuSetup.H) (hi:∀a∈B5Image B5,s.v*a*s.v⁻¹=a⁻¹) :
    p.A B5≤normalizer ((B5Image B5⊔Q₅ d B5:Subgroup G):Set G) :=
  normalizes_fiveProduct_of_normalizes_fiveHyperplane d B5 _ (p.A_le_H B5)
    (s.A_normalizes_fiveHyperplane p B5 hi)

theorem SourceChoice.A_normalizes_Q₅ (s:SourceChoice p)
    (B5:Sylow 5 d.toTypeRuSetup.H) (hi:∀a∈B5Image B5,s.v*a*s.v⁻¹=a⁻¹) :
    p.A B5≤normalizer (Q₅ d B5:Set G) :=
  normalizes_Q₅_of_normalizes_fiveHyperplane d B5 _ (p.A_le_H B5)
    (s.A_normalizes_fiveHyperplane p B5 hi)

abbrev Plane.F₁ (B5:Sylow 5 d.toTypeRuSetup.H) : Subgroup G :=
  (p.A B5⊔Q₅ d B5)⊔B5Image B5

theorem Plane.F₁_le_H (B5:Sylow 5 d.toTypeRuSetup.H) : p.F₁ B5≤d.toTypeRuSetup.H :=
  sup_le (sup_le (p.A_le_H B5) ((Q₅_le_Q d B5).trans (pCoreIn_le 2 _))) (map_subtype_le _)

theorem Plane.fiveHyperplane_le_F₁ (B5:Sylow 5 d.toTypeRuSetup.H) :
    fiveHyperplane d B5≤p.F₁ B5 :=
  sup_le ((p.Q₀_le_S₂.trans (p.S₂_le_A B5)).trans (le_sup_left.trans le_sup_left))
    (le_sup_right.trans le_sup_left)

theorem SourceChoice.A_sup_Q₅_sup_S (s:SourceChoice p)
    (B5:Sylow 5 d.toTypeRuSetup.H) (hi:∀a∈B5Image B5,s.v*a*s.v⁻¹=a⁻¹) :
    (p.A B5⊔Q₅ d B5)⊔d.toTypeRuSetup.S=(d.T:Subgroup G) := by
  rw [sup_right_comm,s.A_sup_S p B5 hi,p.R₂_sup_Q₅]

theorem SourceChoice.F₁_normalizes_fiveHyperplane (s:SourceChoice p)
    (B5:Sylow 5 d.toTypeRuSetup.H) (hi:∀a∈B5Image B5,s.v*a*s.v⁻¹=a⁻¹) :
    p.F₁ B5≤normalizer (fiveHyperplane d B5:Set G) := by
  refine sup_le (sup_le (s.A_normalizes_fiveHyperplane p B5 hi)
    ((Q₅_le_Q d B5).trans (Q_normalizes_fiveHyperplane d B5))) ?_
  rintro _ ⟨b,hb,rfl⟩
  exact five_normalizer_le_fiveHyperplaneNormalizer d B5 ((B5:Subgroup d.toTypeRuSetup.H).le_normalizer hb)

end CFSG.Quasithin.ChapterJ.RuSubgroup
