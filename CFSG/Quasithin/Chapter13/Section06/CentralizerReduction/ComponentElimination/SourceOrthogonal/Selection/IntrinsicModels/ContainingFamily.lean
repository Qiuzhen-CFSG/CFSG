module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceOrthogonal.Selection.Actions
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.FFSelection.Existence.FittingCenter
public import Theory.GroupTheory.CComponent.FittingCentralizer
public import Theory.GroupTheory.CComponent.NonquasisimpleAction

/-!
# The actual containing component belongs to Y_z

The universal commutator assertion 13.6.16(3) puts the star image of the
containing C-component in J(G_v)*. It remains a C-component under the star
map: movement of z excludes the trivial image. The already proved equality
F(J(G_v)*) = Z(J(G_v)*) then makes that image quasisimple. This uses only
the central Fitting equality, not a component-product assertion for J(G_v)*.

Normality relative to G_v supplies T_v-invariance, and containment of L_v
supplies movement. The final application constructs all clauses of the
literal Y_z definition using the sibling Actions module.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
the paragraph after 13.6.13, 13.6.16(3), and 13.6.23, pp.929–933.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceOrthogonal.Selection
open ComponentSelection
universe u
variable {G : Type u} [Group G] [Finite G]

/-- Thompson generation places the literal star image in the global Thompson image. -/
theorem starImage_le_JGstar_of_generated (D T : Subgroup G) (z v : G)
    (hD : D ≤ Gv v)
    (hSyl : Chapter1.IsSylowIn 2 (Tv T v) (Gv v))
    (hgen : ⁅D, Stellmacher.elementaryAbelianMaxJ (Tv T v)⁆ = D) :
    starImage z v D ≤ JGstar z v := by
  let := JGstar_normal z v
  have hJ : Stellmacher.elementaryAbelianMaxJ (Tv T v) ≤ Gv v :=
    (sSup_le fun _ h => h.1).trans inf_le_right
  have hJS : starImage z v (Stellmacher.elementaryAbelianMaxJ (Tv T v)) ≤
      JGstar z v := by
    rw [JGstar_eq_conjugateSpan T z v hSyl]
    exact le_conjugateSpanBy _ _
  rw [← hgen, starImage_commutator z v D _ hD hJ]
  exact (commutator_mono le_rfl hJS).trans (commutator_le_right _ _)

/-- The star image of a moving ambient C-component is itself a C-component.
No solvability hypothesis on the whole star kernel is imposed. -/
theorem starImage_isCComponent_of_moving (D : Subgroup G) (z v : G)
    (hD : D ∈ Chapter1.cComponentsIn (Gv v))
    (hmove : ¬ D ≤ centralizer ({z} : Set G)) :
    (starImage z v D).IsCComponent := by
  rcases NonquasisimpleAction.ccomponent_image_or_bot hD.2
      (starMk z v) (starMk_surjective z v) with hb | hc
  · exact (hmove (((starImage_eq_bot_iff z v D hD.1).mp hb).trans
      (centralizer_le (Set.singleton_subset_iff.mpr (z_mem_Uv z v))))).elim
  · exact hc

/-- The central Fitting equality after 13.6.13 supplies star-quasisimplicity
for every moving, Thompson-generated ambient C-component. -/
theorem containing_star_quasisimple (D T : Subgroup G) (z v : G)
    (hD : D ∈ Chapter1.cComponentsIn (Gv v))
    (hmove : ¬ D ≤ centralizer ({z} : Set G))
    (hSyl : Chapter1.IsSylowIn 2 (Tv T v) (Gv v))
    (hgen : ⁅D, Stellmacher.elementaryAbelianMaxJ (Tv T v)⁆ = D)
    (hfit : fittingSubgroup (JGstar z v) = center (JGstar z v)) :
    IsQuasisimple (starImage z v D) := by
  have hC := starImage_isCComponent_of_moving D z v hD hmove
  have hDJ := starImage_le_JGstar_of_generated D T z v hD.1 hSyl hgen
  let E := (starImage z v D).subgroupOf (JGstar z v)
  have hE : E.IsCComponent := hC.subgroupOf hDJ
  let : IsQuasisimple E := hE.isQuasisimple_of_fitting_centralizes (by
    rw [hfit]
    intro x hx y _
    exact mem_center_iff.mp hx y)
  exact IsQuasisimple.of_mulEquiv (subgroupOfEquivOfLe hDJ)

/-- Membership of the containing component in the exact source family.
The earlier commutator theorem is applied to the actual local subgroup D. -/
theorem containing_mem_Yz (K D L T : Subgroup G) (z v : G)
    (hD : D ∈ Chapter1.cComponentsIn (Gv v)) (hKD : K ≤ D)
    (hDn : Gv v ≤ normalizer (D : Set G))
    (hcore : Gv v ∈ Chapter1.H G)
    (hSyl : Chapter1.IsSylowIn 2 (Tv T v) (Gv v))
    (hLK : Lv L v ≤ K)
    (hmove : ¬ Lv L v ≤ centralizer ({z} : Set G))
    (h16 : ∀ B ∈ Chapter1.LIn (Gv v) (Tv T v),
      Tv T v ≤ normalizer (B : Set G) → ¬ B ≤ centralizer ({z} : Set G) →
      ⁅B, Stellmacher.elementaryAbelianMaxJ (Tv T v)⁆ = B)
    (hstarCore : pCore 2 (Gstar z v) = ⊥)
    (hfit : fittingSubgroup (JGstar z v) = center (JGstar z v)) :
    D ∈ Yz L T z v := by
  have hlocal : D ∈ Chapter1.LIn (Gv v) (Tv T v) :=
    ⟨hD.1, Chapter1.mem_L_of_cComponent hcore hSyl hD.1 hD.2⟩
  have hDnT : Tv T v ≤ normalizer (D : Set G) := inf_le_right.trans hDn
  have hLD : Lv L v ≤ D := hLK.trans hKD
  have hm : ¬ D ≤ centralizer ({z} : Set G) := fun h => hmove (hLD.trans h)
  let := containing_star_quasisimple D T z v hD hm hSyl
    (h16 D hlocal hDnT hm) hfit
  have hq : IsQuasisimple (starImage z v D ⧸ pCore 2 (starImage z v D)) := by
    have he : pCore 2 (starImage z v D) = ⊥ := by
      rw [pCore_subnormal_eq_comap 2
        (starImage_isCComponent_of_moving D z v hD hm).subnormal, hstarCore]
      exact (starImage z v D).ker_subtype
    exact IsQuasisimple.of_mulEquiv
      ((QuotientGroup.quotientMulEquivOfEq he).trans QuotientGroup.quotientBot).symm
  exact mem_Yz_of_source_commutator D L T z v h16 hlocal hDnT hLD hq hmove

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceOrthogonal.Selection
