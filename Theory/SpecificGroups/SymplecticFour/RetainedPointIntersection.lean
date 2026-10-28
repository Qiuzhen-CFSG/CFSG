module
public import Theory.SpecificGroups.SymplecticFour.PointIndividualGeneration
public import Theory.SpecificGroups.SymplecticFour.PointSupplement

/-!
# The marked plane intersection for a retained pair of actors

Fix the endpoint, mover and conjugator. If their join is proper but its
point-local intersection projects onto the full rank-one quotient, that
intersection meets the point radical centrally. Every two-subgroup in it
therefore has order at most q squared. This applies to the same marked plane
core and, after conjugating back, bounds the original mover's plane intersection.

No selector is replaced and no bound on the whole individual mover is asserted.
This isolates the local numerical implication used in MS93 (5.5)(c), printed
pp.915--917, and its N1 application on p.925.
-/

public noncomputable section
open Subgroup
namespace Theory.SpecificGroups.SymplecticFour.RetainedPointIntersection
open CentralRootGeometry.SmallMovers
variable {F : Type*} [Field F] [Finite F] [CharP F 2]

/-- A proper join with full point-local projection has a square-order bound
on its intersection with the same marked plane core. -/
theorem marked_core_card_bound {n : ℕ} (hcard : Nat.card F = 2^n) (hn : 1<n)
    (A : Subgroup (Sp F)) (E : Subgroup (unipotent (F := F)))
    (hfixed : fixed E = point F) (w : Sp F) (hw : w ∉ pointParabolic)
    (hproper : A ⊔ (E.map unipotent.subtype).map (MulAut.conj w).toMonoidHom ≠ ⊤)
    (hproj : ((A ⊔ (E.map unipotent.subtype).map (MulAut.conj w).toMonoidHom).subgroupOf
      pointLocal).map pointQuotient = ⊤)
    (hcore : (planeParabolic.map (MulAut.conj w).toMonoidHom).pCoreIn 2 ≤ pointLocal) :
    Nat.card ((A ⊔ (E.map unipotent.subtype).map (MulAut.conj w).toMonoidHom) ⊓
      (planeParabolic.map (MulAut.conj w).toMonoidHom).pCoreIn 2 : Subgroup (Sp F)) ≤
        Nat.card F^2 := by
  let N := A ⊔ (E.map unipotent.subtype).map (MulAut.conj w).toMonoidHom
  let D := N.subgroupOf pointLocal
  let C := (planeParabolic.map (MulAut.conj w).toMonoidHom).pCoreIn 2
  have hD : D ≠ ⊤ := by
    intro htop
    apply hproper
    apply PointIndividualGeneration.generate_of_pointLocal_le hcard hn A E hfixed w hw
    intro x hx
    exact (show (⟨x,hx⟩ : pointLocal) ∈ D from htop.symm ▸ mem_top _)
  have hsupp : D ⊔ pointRadical = ⊤ := by
    rw [←pointQuotient_ker,←comap_map_eq]
    rw [hproj,comap_top]
  have hc : D ⊓ pointRadical ≤ center (pointLocal (F := F)) :=
    (PointSupplement.supplement_dichotomy hcard hn D hsupp).resolve_left hD
  let T := (N ⊓ C).subgroupOf pointLocal
  have hTL : N ⊓ C ≤ pointLocal := inf_le_right.trans hcore
  have hTtwo : IsPGroup 2 T :=
    ((isPGroup_pCoreIn 2 _).to_le (show N ⊓ C ≤ C from inf_le_right)).comap_subtype
  have hbound := PointSupplement.central_kernel_pgroup_card_bound hcard hn D T hc
    (comap_mono inf_le_left) hTtwo
  have hmap : T.map pointLocal.subtype = N ⊓ C := map_subgroupOf_eq_of_le hTL
  rw [←hmap,card_map_of_injective pointLocal.subtype_injective]
  exact hbound

/-- Pull the same marked intersection back by the retained conjugator. Its
square-order witness contains the original mover's full plane intersection. -/
theorem original_plane_intersection_witness {n : ℕ}
    (hcard : Nat.card F = 2^n) (hn : 1<n)
    (A : Subgroup (Sp F)) (E : Subgroup (unipotent (F := F)))
    (hfixed : fixed E = point F) (w : Sp F) (hw : w ∉ pointParabolic)
    (hproper : A ⊔ (E.map unipotent.subtype).map (MulAut.conj w).toMonoidHom ≠ ⊤)
    (hproj : ((A ⊔ (E.map unipotent.subtype).map (MulAut.conj w).toMonoidHom).subgroupOf
      pointLocal).map pointQuotient = ⊤)
    (hcore : (planeParabolic.map (MulAut.conj w).toMonoidHom).pCoreIn 2 ≤ pointLocal) :
    let W := ((A ⊔ (E.map unipotent.subtype).map (MulAut.conj w).toMonoidHom) ⊓
      (planeParabolic.map (MulAut.conj w).toMonoidHom).pCoreIn 2).map
        (MulAut.conj w⁻¹).toMonoidHom
    Nat.card W ≤ Nat.card F^2 ∧
      E.map unipotent.subtype ⊓ (CentralRootGeometry.wing true).map unipotent.subtype ≤ W := by
  let : Algebra (ZMod 2) F := ZMod.algebra F 2
  let N := A ⊔ (E.map unipotent.subtype).map (MulAut.conj w).toMonoidHom
  let C := (planeParabolic.map (MulAut.conj w).toMonoidHom).pCoreIn 2
  let P := (CentralRootGeometry.wing (F := F) true).map unipotent.subtype
  have hC : C = P.map (MulAut.conj w).toMonoidHom := by
    dsimp only [C,P]
    rw [←map_pCoreIn_of_injective 2 _ _ (MulAut.conj w).injective,pCoreIn,
      planeParabolic_core_map_eq_radical hcard hn]
    exact congrArg (Subgroup.map (MulAut.conj w).toMonoidHom)
      SymplecticConjugatePair.planeRadical_eq_wing
  have back (B : Subgroup (Sp F)) :
      (B.map (MulAut.conj w).toMonoidHom).map (MulAut.conj w⁻¹).toMonoidHom = B := by
    rw [Subgroup.map_map]
    have he : (MulAut.conj w⁻¹).toMonoidHom.comp (MulAut.conj w).toMonoidHom =
        MonoidHom.id _ := by
      ext x
      simp [MulAut.conj_apply,mul_assoc]
    rw [he,Subgroup.map_id]
  dsimp only
  constructor
  · rw [card_map_of_injective (MulAut.conj w⁻¹).injective]
    exact marked_core_card_bound hcard hn A E hfixed w hw hproper hproj hcore
  · have hle : ((E.map unipotent.subtype) ⊓ P).map (MulAut.conj w).toMonoidHom ≤ N ⊓ C := by
      rw [map_inf _ _ _ (MulAut.conj w).injective,hC]
      exact le_inf (inf_le_left.trans (show
        (E.map unipotent.subtype).map (MulAut.conj w).toMonoidHom ≤ N from le_sup_right))
        inf_le_right
    have hh := map_mono hle (f := (MulAut.conj w⁻¹).toMonoidHom)
    rw [back] at hh
    exact hh

end Theory.SpecificGroups.SymplecticFour.RetainedPointIntersection
