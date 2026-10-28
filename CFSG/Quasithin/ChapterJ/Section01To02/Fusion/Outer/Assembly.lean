module

public import CFSG.Quasithin.ChapterJ.Section01To02.Fusion.Outer.SourceGeometry
public import CFSG.Quasithin.ChapterJ.Section01To02.Fusion.Outer.Lifting
public import CFSG.Quasithin.ChapterJ.Section01To02.Fusion.Outer.Semidihedral

/-!
# Assembly of the exact J.2.5 and J.2.6 conclusions

The source conjugate geometry first supplies a z-fused outer involution.
Freeness on the two actual Ru2 sections gives the count 640 and an involution
in C_H(B), representing all outer involutions up to multiplication by z.
Only then do quaternion displacement and semidihedral recognition apply.
The explicit quaternion conjugator merges the two lifts. Parabolic transport
and the natural head finish fusion in L outside S and in all of Q.

The sole additional premise is CentralProductData, produced independently
by the commutator branch and discharged by the parent Fusion assembly.
All earlier J.2.1–3, action, transport, seed, count and orbit inputs used here
are proved in their named component modules.

Source: Aschbacher–Smith J.2.5–6, printed pp.434–435 of `refs/quasithin.pdf`.
-/

public section
noncomputable section

open Subgroup Representation
namespace CFSG.Quasithin.ChapterJ.Fusion.Outer
variable {G : Type*} [Group G] [Finite G]

private theorem transitive_of_two_lifts (d : TypeRuSetup G) (B : Sylow 3 d.L₁)
    (i : CB d B) (z : G)
    (hlifts : ∀ x ∈ involutionsOutside d.H d.K,
      ∃ h : d.H, (h : G) * x * (h : G)⁻¹ = i ∨
        (h : G) * x * (h : G)⁻¹ = (i : G) * z)
    (q : HB d B) (hq : (q : G) * i * (q : G)⁻¹ = (i : G) * z) :
    TransitiveOn d.H (involutionsOutside d.H d.K) := by
  let qH : d.H := ⟨q, d.ru2.six.section_le q.property.1⟩
  have hone (x : G) (hx : x ∈ involutionsOutside d.H d.K) :
      ∃ h : d.H, (h : G) * x * (h : G)⁻¹ = i := by
    obtain ⟨h, he | he⟩ := hlifts x hx
    · exact ⟨h, he⟩
    · refine ⟨qH⁻¹ * h, ?_⟩
      change ((q : G)⁻¹ * h) * x * ((q : G)⁻¹ * h)⁻¹ = i
      calc
        _ = (q : G)⁻¹ * ((h : G) * x * (h : G)⁻¹) * q := by group
        _ = (q : G)⁻¹ * ((i : G) * z) * q := by rw [he]
        _ = i := by rw [← hq]; group
  intro x y hx hy
  obtain ⟨h, hh⟩ := hone x hx
  obtain ⟨k, hk⟩ := hone y hy
  refine ⟨k⁻¹ * h, ?_⟩
  change ((k : G)⁻¹ * h) * x * ((k : G)⁻¹ * h)⁻¹ = y
  calc
    _ = (k : G)⁻¹ * ((h : G) * x * (h : G)⁻¹) * k := by group
    _ = (k : G)⁻¹ * (i : G) * k := by rw [hh]
    _ = y := by rw [← hk]; group

/-- The exact J.2.5–6 conclusions from the genuine setup and the independently
produced central product. The centralizing involution is constructed before
semidihedral recognition is used. -/
theorem sourceJ25_sourceJ26_of_centralProduct (d : LocalSetup G)
    (B : Sylow 3 d.toTypeRuSetup.L₁) (cp : CentralProductData d.toTypeRuSetup B)
    {z : G} (hz : z ∈ d.toTypeRuSetup.Z) (hz1 : z ≠ 1) :
    SourceJ25 d.toTypeRuSetup B ∧ SourceJ26 d.toTypeRuSetup z := by
  let D := d.toTypeRuSetup
  obtain ⟨j, hj, hjz⟩ := exists_fused_outer_seed d hz hz1
  have hQR : D.Q ≤ D.R₁ := by
    rw [← d.parabolic_core_eq_R₁, ← d.Q_sup_S_eq_parabolic_core]
    exact le_sup_left
  have actions := outerActionData_of_centralProduct d B cp
  obtain ⟨hcard, i, hiK, hi, hlifts⟩ := involution_lifting d B hQR d.card_Z hz hz1
    ⟨j, hj.1⟩ hj.2.1 hj.2.2 actions.natural_free actions.six_free
  have h25 := sourceJ25_of_centralizing_involution d B cp hz hz1 i hiK hi
  obtain ⟨-, -, -, -, q, hq⟩ := quaternion_rotation d B cp hz hz1 i hiK hi
  have htrans := transitive_of_two_lifts D B i z hlifts q hq
  have houter : ∀ x ∈ involutionsOutside D.H D.K, IsConj x z := by
    intro x hx
    obtain ⟨h, hh⟩ := htrans hx hj
    exact (isConj_iff.mpr ⟨(h : G), hh⟩).trans hjz
  have hL : ∀ x ∈ involutionsOutside D.L D.S, IsConj x z := by
    intro x hx
    obtain ⟨y, hy, hxy⟩ := transport_involutions d x hx
    exact hxy.trans (houter y hy)
  have he := elementaryFusion_of_centralProduct D B cp d.card_Z
    (d.center_eq.le.trans inf_le_left) hz hz1
  exact ⟨h25, ⟨⟨htrans, hcard, houter⟩, hL,
    fusion_Q_of_fusion_L D d.fusionNaturalHead d.Q_le_L (source_HC_le_S d)
      d.not_Q_le_S he hL, he⟩⟩

/-- J.2.5, with no outer-involution, action, count or recognition premise. -/
theorem sourceJ25_of_centralProduct (d : LocalSetup G)
    (B : Sylow 3 d.toTypeRuSetup.L₁) (cp : CentralProductData d.toTypeRuSetup B) :
    SourceJ25 d.toTypeRuSetup B := by
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := d.toTypeRuSetup.Z) 2
    (by rw [d.card_Z])
  exact (sourceJ25_sourceJ26_of_centralProduct d B cp z.property
    (by intro h; have h1 : z = 1 := Subtype.ext h; simp [h1] at hz)).1

/-- J.2.6, including all four source clauses, from the independent central product. -/
theorem sourceJ26_of_centralProduct (d : LocalSetup G)
    (B : Sylow 3 d.toTypeRuSetup.L₁) (cp : CentralProductData d.toTypeRuSetup B)
    {z : G} (hz : z ∈ d.toTypeRuSetup.Z) (hz1 : z ≠ 1) :
    SourceJ26 d.toTypeRuSetup z :=
  (sourceJ25_sourceJ26_of_centralProduct d B cp hz hz1).2

end CFSG.Quasithin.ChapterJ.Fusion.Outer
