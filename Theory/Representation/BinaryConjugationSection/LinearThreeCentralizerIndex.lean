module
public import Theory.Representation.BinaryConjugationSection.LinearThreePoint
public import Theory.GroupTheory.SylowSmallIndex

/-!
# Centralizers of lifted natural-three points

The natural point stabilizer has index seven. For a binary conjugation
section with central kernel Z of order two, the lift stabilizer maps to Z
by its commutator with the chosen point. Its kernel is the actual point
centralizer, whose index therefore divides fourteen. An index-two support
stabilizer contributes at most one further factor two.

The resulting point centralizer contains a two-subgroup of order at least
one quarter of the original Sylow order. All quotient actions and original
points are retained. This supplies the upper bound in Aschbacher--Smith
14.6.24(3), printed p.1041, for the Chapter14 paired-component consumer.
-/

public noncomputable section
open Subgroup Representation
open scoped MatrixGroups commutatorElement
namespace Representation.BinaryConjugationSection
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
/-- A nonzero natural point has centralizer index dividing fourteen when
the coordinate kernel is a central subgroup of order two. -/
theorem linearThree_lift_centralizer_index_dvd
    {A W Z : Subgroup G} (f : A →* SL(3,ZMod 2)) (hf : Function.Surjective f)
    (c : BinaryConjugationSection A W Z ((specialLinearNatural 3).comp f))
    (hcent : A ≤ centralizer (Z : Set G)) (hz : Nat.card Z = 2)
    (w : W) (hw : (w : G) ∉ Z) :
    (centralizer ({(w : G)} : Set G)).relIndex A ∣ 14 := by
  let P : Subgroup A := (MulAction.stabilizer SL(3,ZMod 2) (c.coordinates w).toAdd).comap f
  have hw0 : (c.coordinates w).toAdd ≠ 0 := by
    intro he
    exact hw ((c.coordinates_eq_one_iff w).mp he)
  have hPi : P.index = 7 := (index_comap_of_surjective _ hf).trans
    (BinaryLinear.NaturalThreePoint.stabilizer_index _ hw0)
  have hcomm (x : P) : ⁅(w : G),(x.val : G)⁆ ∈ Z := by
    have he : specialLinearNatural 3 (f x.val) (c.coordinates w).toAdd =
        (c.coordinates w).toAdd := x.property
    have hcoord := c.equivariant x.val w
    change (c.coordinates ⟨(x.val : G) * w * (x.val : G)⁻¹,_⟩).toAdd =
      specialLinearNatural 3 (f x.val) (c.coordinates w).toAdd at hcoord
    rw [he] at hcoord
    let v : W := ⟨(x.val : G) * w * (x.val : G)⁻¹,
      (mem_normalizer_iff.mp (c.normalized x.val.property) w).mp w.property⟩
    have hv : (v : G) * (w : G)⁻¹ ∈ Z := by
      apply (c.coordinates_eq_one_iff (v * w⁻¹)).mp
      rw [map_mul,map_inv,show c.coordinates v = c.coordinates w from hcoord,mul_inv_cancel]
    have hh : ⁅(x.val : G),(w : G)⁆ ∈ Z := hv
    rw [←commutatorElement_inv]
    exact Z.inv_mem hh
  let χ : P →* Z := {
    toFun x := ⟨⁅(w : G),(x.val : G)⁆,hcomm x⟩
    map_one' := Subtype.ext (by simp)
    map_mul' x y := by
      apply Subtype.ext
      change ⁅(w : G),(x.val : G) * (y.val : G)⁆ =
        ⁅(w : G),(x.val : G)⁆ * ⁅(w : G),(y.val : G)⁆
      rw [commutatorElement_mul_right_eq_mul_conj]
      have hh := hcent x.val.property _ (hcomm y)
      calc
        _ = ⁅(w : G),(x.val : G)⁆ * ((x.val : G) * ⁅(w : G),(y.val : G)⁆) *
          (x.val : G)⁻¹ := by group
        _ = _ := by rw [←hh]; group }
  let C : Subgroup A := (centralizer ({(w : G)} : Set G)).subgroupOf A
  have hCP : C ≤ P := by
    intro x hx
    have he : (⟨(x : G) * w * (x : G)⁻¹,
        (mem_normalizer_iff.mp (c.normalized x.property) w).mp w.property⟩ : W) = w := by
      apply Subtype.ext
      change (x : G) * (w : G) * (x : G)⁻¹ = (w : G)
      calc
        _ = (w : G) * (x : G) * (x : G)⁻¹ :=
          congrArg (fun y : G => y * (x : G)⁻¹) (mem_centralizer_singleton_iff.mp hx)
        _ = _ := mul_inv_cancel_right _ _
    have hh := c.equivariant x w
    rw [he] at hh
    exact hh.symm
  have hker : χ.ker = C.subgroupOf P := by
    ext x
    change (⟨⁅(w : G),(x.val : G)⁆,_⟩ : Z) = 1 ↔
      (x.val : G) ∈ centralizer ({(w : G)} : Set G)
    rw [Subtype.ext_iff]
    change ⁅(w : G),(x.val : G)⁆ = 1 ↔ _
    rw [commutatorElement_eq_one_iff_mul_comm,mem_centralizer_singleton_iff,eq_comm]
  have hCi : C.relIndex P ∣ 2 := by
    change (C.subgroupOf P).index ∣ 2
    rw [←hker,index_ker,←hz]
    exact χ.range.card_subgroup_dvd_card
  have hm := relIndex_mul_index hCP
  rw [hPi] at hm
  change C.index ∣ 14
  rw [←hm]
  exact Nat.mul_dvd_mul hCi (dvd_refl 7)

end Representation.BinaryConjugationSection


namespace Representation.BinaryConjugationSection
variable {G : Type*} [Group G] [Finite G]
/-- The natural-point centralizer in an index-two support stabilizer
contains a two-subgroup with at least one quarter of the original Sylow order. -/
theorem linearThree_point_large_two_subgroup
    (T : Sylow 2 G) (H A W Z : Subgroup G)
    (hTH : (T : Subgroup G) ≤ H) (hAH : A ≤ H) (hi : A.relIndex H ∣ 2)
    (f : A →* SL(3,ZMod 2)) (hf : Function.Surjective f)
    (c : BinaryConjugationSection A W Z ((specialLinearNatural 3).comp f))
    (hcent : A ≤ centralizer (Z : Set G)) (hz : Nat.card Z = 2)
    (w : W) (hw : (w : G) ∉ Z) :
    ∃ S : Subgroup G, S ≤ H ⊓ centralizer ({(w : G)} : Set G) ∧
      IsPGroup 2 S ∧ Nat.card T ≤ 4 * Nat.card S := by
  let C := A ⊓ centralizer ({(w : G)} : Set G)
  have hC : C ≤ H := inf_le_left.trans hAH
  have hCA : C.relIndex A ∣ 14 := by
    rw [show C.relIndex A = (centralizer ({(w : G)} : Set G)).relIndex A from
      inf_relIndex_left _ _]
    exact linearThree_lift_centralizer_index_dvd f hf c hcent hz w hw
  have hCH : C.relIndex H ∣ 28 := by
    rw [←relIndex_mul_relIndex C A H inf_le_left hAH]
    exact Nat.mul_dvd_mul hCA hi
  obtain ⟨S,hSC,hS,hsize⟩ :=
    exists_two_subgroup_large_of_index_dvd_twentyEight T H C hTH hC hCH
  exact ⟨S,hSC.trans (inf_le_inf_right _ hAH),hS,hsize⟩
end Representation.BinaryConjugationSection
