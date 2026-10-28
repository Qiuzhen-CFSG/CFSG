module

public import Theory.SpecificGroups.PSL3Even.AutomorphismTwoRank.Coverage.RootOrientation.Geometry

/-!
# Intrinsic permutation of the two elementary abelian planes

An automorphism preserving a marked UT₃(F) subgroup in characteristic two
carries an elementary abelian plane into one of its two coordinate planes.
Each plane has order |F|², so containment is equality. Injectivity forces the
second plane to have the other image. We apply this both to the actual upper
unipotent embedding and to its inverse-transpose image.

Source: the root-plane geometry of Aschbacher–Smith §5.3.5–7, printed p.660,
as the characteristic-two normalization step toward GLS3 Theorem 2.5.12(a).
The matrix conventions are in §2.7 of `refs/KGroup/GLS3/chapter2.tex`.
-/

public section

open scoped MatrixGroups
open Matrix Matrix.PSL3 Matrix.PSL3.LinearThree Matrix.PSL3Even.UnipotentGeometry
open Matrix.PSL3.OuterSolvable Matrix.PSL3.OuterSolvable.OddPrimeCoverage
open Matrix.PSL3.RootPlaneGeometry
namespace Matrix.PSL3Even.AutomorphismCoverage.RootOrientation
variable (F : Type*) [Field F] [Finite F] [CharP F 2]
local instance : Fact (Nat.Prime 2) := ⟨by decide⟩

omit [Finite F] in
private theorem marked_plane_image {G : Type*} [Group G] [Finite G]
    (S : Subgroup G) (e : U F ≃* S) (α : MulAut G)
    (hS : S.map α.toMonoidHom = S) (b : Bool) :
    ∃ c : Bool, ((if b then V₁ F else V₂ F).map (markedHom F S e)).map α.toMonoidHom =
      (if c then V₁ F else V₂ F).map (markedHom F S e) := by
  let P : Bool → Subgroup G := fun b => (if b then V₁ F else V₂ F).map (markedHom F S e)
  have helem (b : Bool) : IsElementaryAbelian 2 (P b) := by
    cases b
    · exact marked_plane₂_elementary F S e
    · exact marked_plane₁_elementary F S e
  have hcard (b : Bool) : Nat.card (P b) = Nat.card F ^ 2 := by
    cases b
    · exact marked_card_plane₂ F S e
    · exact marked_card_plane₁ F S e
  let := helem b
  let : IsElementaryAbelian 2 ((P b).map α.toMonoidHom) := IsElementaryAbelian.map α.toMonoidHom
  have hle : (P b).map α.toMonoidHom ≤ S := by
    rw [← hS]
    apply Subgroup.map_mono
    rw [← range_markedHom F S e]
    exact Subgroup.map_le_range _ _
  have hsize : Nat.card ((P b).map α.toMonoidHom) = Nat.card F ^ 2 := by
    rw [Subgroup.card_map_of_injective α.injective, hcard]
  rcases marked_elementary_le_plane F S e ((P b).map α.toMonoidHom) hle with h | h
  · refine ⟨true, Subgroup.eq_of_le_of_card_ge h ?_⟩
    rw [hsize]
    exact (hcard true).le
  · refine ⟨false, Subgroup.eq_of_le_of_card_ge h ?_⟩
    rw [hsize]
    exact (hcard false).le

omit [Finite F] in
/-- An automorphism preserving a marked unitriangular subgroup permutes its
 two elementary abelian planes, with the second image complementary to the first. -/
theorem marked_plane_permutation {G : Type*} [Group G] [Finite G]
    (S : Subgroup G) (e : U F ≃* S) (α : MulAut G)
    (hS : S.map α.toMonoidHom = S) :
    ∃ b : Bool,
      ((V₁ F).map (markedHom F S e)).map α.toMonoidHom =
        (if b then V₁ F else V₂ F).map (markedHom F S e) ∧
      ((V₂ F).map (markedHom F S e)).map α.toMonoidHom =
        (if !b then V₁ F else V₂ F).map (markedHom F S e) := by
  obtain ⟨b,hb⟩ := marked_plane_image F S e α hS true
  obtain ⟨c,hc⟩ := marked_plane_image F S e α hS false
  have hne : b ≠ c := by
    intro he
    rw [← he] at hc
    have hplanes : (V₁ F).map (markedHom F S e) = (V₂ F).map (markedHom F S e) :=
      Subgroup.map_injective α.injective (hb.trans hc.symm)
    have hv : V₁ F = V₂ F := Subgroup.map_injective (markedHom_injective F S e) hplanes
    exact plane₁_not_le_plane₂ F hv.le
  have he : c = !b := by cases b <;> cases c <;> simp_all
  exact ⟨b,hb,he ▸ hc⟩

omit [Finite F] [CharP F 2] in
private theorem marked_upper : markedHom F (unipotent F) (unipotentEquiv F) = projective F := rfl

/-- The upper pair of elementary abelian planes is invariant as a pair. -/
theorem upper_plane_permutation (α : MulAut PSL(3,F))
    (hα : (upperUnipotent F).map α.toMonoidHom = upperUnipotent F) :
    ∃ b : Bool, (rootPlane F true).map α.toMonoidHom = rootPlane F b ∧
      (rootPlane F false).map α.toMonoidHom = rootPlane F (!b) := by
  have h := marked_plane_permutation F (unipotent F) (unipotentEquiv F) α hα
  simpa only [rootPlane_eq_map, marked_upper, Bool.false_eq_true, ↓reduceIte] using h

/-- The lower pair is the actual inverse-transpose image of the upper pair. -/
theorem lower_plane_permutation (α : MulAut PSL(3,F))
    (hα : (lowerUnipotent F).map α.toMonoidHom = lowerUnipotent F) :
    ∃ b : Bool, (lowerPlane F true).map α.toMonoidHom = lowerPlane F b ∧
      (lowerPlane F false).map α.toMonoidHom = lowerPlane F (!b) := by
  let e : U F ≃* lowerUnipotent F :=
    (unipotentEquiv F).trans ((graph F).subgroupMap (unipotent F))
  have he : markedHom F (lowerUnipotent F) e =
      (graph F).toMonoidHom.comp (projective F) := rfl
  have h := marked_plane_permutation F (lowerUnipotent F) e α hα
  simpa only [lowerPlane, rootPlane_eq_map, he, Subgroup.map_map,
    Bool.false_eq_true, ↓reduceIte] using h
end Matrix.PSL3Even.AutomorphismCoverage.RootOrientation
