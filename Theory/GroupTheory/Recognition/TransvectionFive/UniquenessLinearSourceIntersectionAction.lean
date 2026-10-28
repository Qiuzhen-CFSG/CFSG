module
public import Theory.GroupTheory.Recognition.TransvectionFive.UniquenessLinearSourceIntersection
import all Theory.GroupTheory.Recognition.TransvectionFive.UniquenessLinearSourcePlaneImage

/-!
# The marked automorphism action on the characteristic rectangle

An automorphism of the actual point–plane intersection fixing z acts on
its characteristic rectangle by an additive permutation. Transport the
rank-one locus through that permutation. The five marked centralizer
shears still preserve it, and its 21 elements have constant additive pair
counts. The existing census forces it to be the original rank-one locus.
The full point-centralizer action therefore realizes this restriction by
an element of the same intersection centralizing z.

The final theorem applies this directly to the original three-space
rectangle via the opposite marking. This is the rectangle-action step in
the marked alignment alternative to Aschbacher, *Sporadic Groups* (1994),
41.3–41.4, printed p.222. It uses no ambient simplicity assumption.
-/

public noncomputable section
namespace Theory.GroupTheory.TransvectionFive.UniquenessLinear.PlaneCensus

theorem rankOne_of_conjugates_shears (f : Equiv.Perm Code)
    (hadd : ∀ x y, f (x ^^^ y) = f x ^^^ f y) (h4 : f 4 = 4)
    (hconj : ∀ k, f⁻¹ * shearPerm k * f ∈ rankOneGroup) : f ∈ rankOneGroup := by
  classical
  let P : Finset Code := Finset.univ.filter (fun x => pure x = true)
  have hP (x : Code) : x ∈ P ↔ pure x = true := by simp [P]
  let S := P.map f.toEmbedding
  have hS (x : Code) : f x ∈ S ↔ x ∈ P := by
    simp only [S, Finset.mem_map_equiv, Equiv.symm_apply_apply]
  have hzero : f 0 = 0 := by
    have hh := hadd 0 0
    rw [show (0 : Code) ^^^ 0 = 0 by decide,
      (by decide : ∀ x : Code, x ^^^ x = 0) (f 0)] at hh
    exact hh
  have h0 : (0 : Code) ∉ S := by
    rw [← hzero, hS, hP]
    decide
  have hpoint : (4 : Code) ∈ S := by
    rw [← h4, hS, hP]
    decide
  have hcard : S.card = 21 := by
    rw [Finset.card_map]
    decide
  have hshear (k : Fin 5) (x : Code) : shear k x ∈ S ↔ x ∈ S := by
    obtain ⟨y, rfl⟩ := f.surjective x
    have he : shear k (f y) = f ((f⁻¹ * shearPerm k * f) y) := by
      simp [shearPerm_apply]
    rw [he, hS, hS, hP, hP]
    rw [((mem_rankOneGroup _).mp (hconj k)).2 y]
  have hpairs (a : Code) (ha : a ∈ S) : pairCount S a = pairCount S 4 := by
    have hcount (x : Code) : pairCount S (f x) = pairCount P x := by
      unfold pairCount
      symm
      apply Finset.card_bijective f f.bijective
      intro b
      simp only [Finset.mem_filter]
      rw [← hadd, hS, hS]
    obtain ⟨x, rfl⟩ := f.surjective a
    have hx := (hP x).mp ((hS x).mp ha)
    rw [← h4, hcount, hcount]
    exact (by decide : ∀ x : Code, pure x = true → pairCount P x = pairCount P 4) x hx
  have he := eq_pure_of_twenty_one S h0 hpoint hcard hshear hpairs
  apply (mem_rankOneGroup f).mpr
  refine ⟨hadd, fun x => ?_⟩
  have hiff := (he (f x)).symm.trans ((hS x).trans (hP x))
  cases h₁ : pure (f x) <;> cases h₂ : pure x <;> simp_all

end Theory.GroupTheory.TransvectionFive.UniquenessLinear.PlaneCensus

public noncomputable section
open Subgroup BinaryLinear.TransvectionFiveLocal
namespace Theory.GroupTheory.TransvectionFive.UniquenessLinear
open PlaneCensus PlaneTensor
variable {G : Type*} [Group G] [Finite G] {z : G}
  (F : MarkedCentralizer z) (hlinear : F.LinearFusion)

include hlinear
theorem characteristic_plane_point_action
    (K : Subgroup G) (hAK : F.plane ≤ K) (hKN : K ≤ sourcePlaneNormalizer F)
    (hCK : Subgroup.centralizer ({z} : Set G) ⊓ sourcePlaneNormalizer F ≤ K)
    [(F.plane.subgroupOf K).Characteristic]
    (a : MulAut K) (ha : a ⟨z, hAK (point_mem_plane F)⟩ = ⟨z, hAK (point_mem_plane F)⟩) :
    ∃ c : K, (c : G) ∈ Subgroup.centralizer ({z} : Set G) ∧
      ∀ b : F.plane.subgroupOf K, a b = c * b * c⁻¹ := by
  let A := F.plane.subgroupOf K
  let e : A ≃* F.plane := subgroupOfEquivOfLe hAK
  let b := MulAut.congr e (MulAut.characteristic A a)
  let f := coordinatePermutation F b
  have hf (x : Code) : element F (f x) =
      (a ⟨element F x, hAK (element_mem F x)⟩ : G) := by
    rw [coordinatePermutation_element]
    rfl
  have hadd (x y : Code) : f (x ^^^ y) = f x ^^^ f y := by
    apply element_injective F
    rw [element_xor, hf, hf, hf]
    have he : (⟨element F (x ^^^ y), hAK (element_mem F _)⟩ : K) =
        ⟨element F x, hAK (element_mem F _)⟩ * ⟨element F y, hAK (element_mem F _)⟩ :=
      Subtype.ext (element_xor F x y)
    rw [he, map_mul]
    rfl
  have h4 : f 4 = 4 := by
    apply element_injective F
    rw [element_point, hf]
    have he : (⟨element F 4, hAK (element_mem F _)⟩ : K) =
        ⟨z, hAK (point_mem_plane F)⟩ := Subtype.ext (element_point F)
    rw [he, ha]
  have hconj (j : Fin 5) : f⁻¹ * shearPerm j * f ∈ rankOneGroup := by
    obtain ⟨n, hn⟩ := exists_shear_normalizer F j
    let nK : K := ⟨n, hCK n.property⟩
    let k := a.symm nK
    let m : sourcePlaneNormalizer F := ⟨k, hKN k.property⟩
    have he : f⁻¹ * shearPerm j * f = normalizerAction F m := by
      apply Equiv.ext
      intro x
      apply f.injective
      change f (f.symm ((shearPerm j) (f x))) = f (normalizerAction F m x)
      rw [f.apply_symm_apply, ← hn, pointCodeAction_apply]
      apply element_injective F
      rw [normalizerAction_element, hf, hf]
      have hm : (⟨element F (normalizerAction F m x), hAK (element_mem F _)⟩ : K) =
          k * ⟨element F x, hAK (element_mem F x)⟩ * k⁻¹ :=
        Subtype.ext (normalizerAction_element F m x)
      rw [hm, map_mul, map_mul, map_inv]
      change (n : G) * (a ⟨element F x, hAK (element_mem F x)⟩ : G) * (n : G)⁻¹ =
        (a (a.symm nK) : G) * (a ⟨element F x, hAK (element_mem F x)⟩ : G) *
          (a (a.symm nK) : G)⁻¹
      rw [a.apply_symm_apply]
    rw [he]
    exact normalizer_rankOne F hlinear m
  have hmem := rankOne_of_conjugates_shears f hadd h4 hconj
  obtain ⟨c, hc⟩ := exists_point_code_action F f hmem h4
  refine ⟨⟨c, hCK c.property⟩, c.property.1, fun x => ?_⟩
  obtain ⟨v, hv⟩ := (sourceEquiv F).surjective (e x)
  have hx : element F v = ((x : K) : G) := congrArg Subtype.val hv
  have he := hf v
  rw [← hc, pointCodeAction_apply, normalizerAction_element] at he
  apply Subtype.ext
  have hxK : (⟨element F v, hAK (element_mem F v)⟩ : K) = x := Subtype.ext hx
  rw [hxK, hx] at he
  exact he.symm

theorem intersection_point_action
    (a : MulAut (rowThreeIntersection F))
    (ha : a ⟨z, threeSpace_le_rowThreeIntersection F (point_mem_threeSpace F)⟩ =
      ⟨z, threeSpace_le_rowThreeIntersection F (point_mem_threeSpace F)⟩) :
    ∃ c : rowThreeIntersection F,
      (c : G) ∈ Subgroup.centralizer ({z} : Set G) ∧
        ∀ b : F.threeSpace.subgroupOf (rowThreeIntersection F), a b = c * b * c⁻¹ := by
  let E := oppositeMarking F
  have hAK : E.plane ≤ rowThreeIntersection F := by
    rw [oppositeMarking_plane]
    exact threeSpace_le_rowThreeIntersection F
  have hKN : rowThreeIntersection F ≤ sourcePlaneNormalizer E := by
    change rowThreeIntersection F ≤ normalizer (E.plane : Set G)
    rw [oppositeMarking_plane]
    exact inf_le_right
  have hCK : Subgroup.centralizer ({z} : Set G) ⊓ sourcePlaneNormalizer E ≤
      rowThreeIntersection F := by
    intro x hx
    refine ⟨point_centralizer_le_row_normalizer F hx.1, ?_⟩
    simpa only [sourcePlaneNormalizer, E, oppositeMarking_plane] using hx.2
  let : (E.plane.subgroupOf (rowThreeIntersection F)).Characteristic := by
    rw [oppositeMarking_plane]
    exact intersection_threeSpace_characteristic F hlinear
  have h := characteristic_plane_point_action E (oppositeMarking_linearFusion F hlinear)
    (rowThreeIntersection F) hAK hKN hCK a ha
  change ∃ c : rowThreeIntersection F,
    (c : G) ∈ Subgroup.centralizer ({z} : Set G) ∧
      ∀ b : (oppositeMarking F).plane.subgroupOf (rowThreeIntersection F),
        a b = c * b * c⁻¹ at h
  rw [oppositeMarking_plane F] at h
  exact h

end Theory.GroupTheory.TransvectionFive.UniquenessLinear
