module
public import Theory.AtlasPort.LinearGroups.G2.BinaryParabolicPair.CoreIdentification
public import Theory.Representation.G2BinaryPointFlag
public import Theory.GroupTheory.CubicKernelIntersection
public import Theory.GroupTheory.CoprimeQuotientSubgroups

/-!
# Cubic fixed bounds in the binary G₂ point stabilizer

The explicit point-parabolic cubic fixes only the outer C-root among
positive-root elements. It fixes a plane on the natural six-space. Both
statements follow from small coordinate calculations in the existing
split-octonion model. Consequently its two-core centralizer has order at
most two and its natural fixed space has order at most four.

A lift through an elementary kernel of order 64 remains an actual cubic.
An injective equivariant marking gives the fixed-kernel bound; coprime
decomposition then bounds its intersection with a second normal two-kernel
by four. This is applied to the literal Rudvalis point stabilizer in
OriginalOddNormalizer.RudvalisCubicIntersection, retaining both quotient maps.
Source: Aschbacher--Smith 4.2.13, printed p.612. The imported root coordinates
retain their ATLAS attribution and license in LICENSES/ATLAS.txt.
-/

public section
open Subgroup Atlas.G2 Atlas.G2.BinaryCore Atlas.G2.BinaryParabolicPair Atlas.SplitOctonion
namespace Atlas.G2.BinaryParabolicPair
set_option maxRecDepth 100000 in
private theorem cubic_coordinates : ∀ t : Fin 6 → ZMod 2,
    (∀ i j : Fin 8,
      (unipotentProduct t * movingActor).val (basisVector i) j =
      (movingActor * unipotentProduct t).val (basisVector i) j) →
    t = (Pi.single (2 : Fin 6) (t 2) : Fin 6 → ZMod 2) := by
  decide +kernel

/-- Only one binary root coordinate survives centralization by the marked cubic. -/
theorem unipotent_centralizer_moving_card_le_two :
    Nat.card (unipotent ⊓ centralizer ({movingActor} : Set (Model (ZMod 2))) : Subgroup _) ≤ 2 := by
  classical
  let C := unipotent ⊓ centralizer ({movingActor} : Set (Model (ZMod 2)))
  have hex (x : C) : ∃ t, unipotentProduct t = (x : Model (ZMod 2)) := by
    have hx := x.property.1
    rwa [unipotent_eq_range] at hx
  let t (x : C) := Classical.choose (hex x)
  have ht (x : C) : unipotentProduct (t x) = (x : Model (ZMod 2)) := Classical.choose_spec (hex x)
  have hsingle (x : C) : t x = Pi.single (2 : Fin 6) (t x 2) := by
    apply cubic_coordinates
    intro i j
    rw [ht]
    exact congrArg (fun y : Model (ZMod 2) => y.val (basisVector i) j)
      (mem_centralizer_singleton_iff.mp x.property.2)
  have hi : Function.Injective (fun x : C => t x 2) := by
    intro x y h
    apply Subtype.ext
    change t x 2 = t y 2 at h
    rw [←ht x,←ht y,hsingle x,hsingle y,h]
  exact (Nat.card_le_card_of_injective _ hi).trans_eq (by simp)

/-- The same bound holds in the literal point-parabolic two-core. -/
theorem point_core_centralizer_moving_card_le_two :
    Nat.card (pCore 2 secondParabolic ⊓
      centralizer ({(⟨movingActor,movingActor_mem⟩ : secondParabolic)} : Set secondParabolic) :
        Subgroup secondParabolic) ≤ 2 := by
  let C := pCore 2 secondParabolic ⊓
    centralizer ({(⟨movingActor,movingActor_mem⟩ : secondParabolic)} : Set secondParabolic)
  let N := unipotent ⊓ centralizer ({movingActor} : Set (Model (ZMod 2)))
  have hcore : pCore 2 secondParabolic ≤
      (commonSylow.subtype (show (commonSylow : Subgroup (Model (ZMod 2))) ≤
        secondParabolic from unipotent_le_parabolic) : Subgroup secondParabolic) :=
    pCore_isPGroup.le_sylow_of_normal _
  let f : C → N := fun x => ⟨x.val.val,hcore x.property.1,
    mem_centralizer_singleton_iff.mpr (congrArg Subtype.val
      (mem_centralizer_singleton_iff.mp x.property.2))⟩
  have hf : Function.Injective f := by
    intro x y h
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun v : N => (v : Model (ZMod 2))) h
  exact (Nat.card_le_card_of_injective f hf).trans unipotent_centralizer_moving_card_le_two
end Atlas.G2.BinaryParabolicPair

namespace Atlas.G2.Natural.BinaryPointFlag
set_option maxRecDepth 100000 in
private theorem fixed_coordinates : ∀ v : Fin 6 → F,
    Restricted.NaturalCoordinates.action F movingActor v = v →
      v = ![v 0,0,0,0,0,v 5] := by
  decide +kernel

/-- The marked cubic fixes at most four vectors of the natural six-space. -/
theorem moving_fixed_card_le_four :
    Nat.card {v : Natural.Space F // Natural.action F movingActor v = v} ≤ 4 := by
  let E := Restricted.NaturalCoordinates.equiv F
  let f : {v : Natural.Space F // Natural.action F movingActor v = v} → (Fin 2 → F) :=
    fun v => ![E v.val 0,E v.val 5]
  have hc (v : {v : Natural.Space F // Natural.action F movingActor v = v}) :
      E v.val = ![E v.val 0,0,0,0,0,E v.val 5] := by
    apply fixed_coordinates
    have he := LinearMap.congr_fun ((Restricted.NaturalCoordinates.repEquiv F).isIntertwining' movingActor) v.val
    change E (Natural.action F movingActor v.val) =
      Restricted.NaturalCoordinates.action F movingActor (E v.val) at he
    rw [v.property] at he
    exact he.symm
  have hi : Function.Injective f := by
    intro v w h
    apply Subtype.ext
    apply E.injective
    have h0 : E v.val 0 = E w.val 0 := congrFun h 0
    have h5 : E v.val 5 = E w.val 5 := congrFun h 1
    rw [hc v,hc w,h0,h5]
  exact (Nat.card_le_card_of_injective f hi).trans_eq (by simp [F])
end Atlas.G2.Natural.BinaryPointFlag

namespace Atlas.G2.Natural.BinaryPointFlag
open Subgroup Theory.GroupTheory
open Atlas.G2.BinaryParabolicPair
variable {P : Type*} [Group P] [Finite P]

/-- Lift the actual cubic and bound its fixed subgroup in the second kernel. -/
theorem exists_cubic_kernel_intersection_fixed_card_le_four
    (b : P →* BinaryCore.secondParabolic) (hb : Function.Surjective b)
    [IsElementaryAbelian 2 b.ker] (hbk : Nat.card b.ker = 64)
    (coordinates : b.ker → Natural.Space F) (hi : Function.Injective coordinates)
    (hfix : ∀ (x : P) (v : b.ker), x * (v : P) = (v : P) * x →
      Natural.action F (b x : Model F) (coordinates v) = coordinates v)
    (R : Subgroup P) [R.Normal] (hR : IsPGroup 2 R)
    (hnot : ¬ b.ker ≤ R) (hcomm : ⁅pCore 2 P,⊤⁆ ≤ R) :
    ∃ x : P, orderOf x = 3 ∧
      b x = (⟨movingActor,movingActor_mem⟩ : BinaryCore.secondParabolic) ∧
      Nat.card (R ⊓ centralizer ({x} : Set P) : Subgroup P) ≤ 4 := by
  let : Finite (Natural.Space F) := Finite.of_equiv (Fin 6 → F)
    (Restricted.NaturalCoordinates.equiv F).symm.toEquiv
  let y : BinaryCore.secondParabolic := ⟨movingActor,movingActor_mem⟩
  have hy3 : y ^ 3 = 1 := Subtype.ext movingActor_cube
  have hyn : y ≠ 1 := by
    intro hh
    have hh' : movingActor = 1 := congrArg Subtype.val hh
    exact movingActor_moves (by rw [hh']; simp)
  let : IsElementaryAbelian 3 (zpowers y) := IsElementaryAbelian.zpowers_of_pow_eq_one hy3
  obtain ⟨A,hA,hmap,_⟩ := exists_elementaryAbelian_map_eq_of_surjective_coprime
    (p := 3) b hb (by rw [hbk]; decide) (zpowers y)
  let := hA
  have hym : y ∈ A.map b := hmap.symm ▸ mem_zpowers y
  obtain ⟨x,hx,hxy⟩ := hym
  have hx3 : orderOf x = 3 := orderOf_eq_prime_iff.mpr
    ⟨elemPow_eq_one_of_isElementaryAbelian x hx,by intro he; apply hyn; rw [←hxy,he,map_one]⟩
  refine ⟨x,hx3,hxy,?_⟩
  apply cubic_kernel_intersection_fixed_card_le_four b hb hbk R hR hnot hcomm x hx3
  · let C := b.ker ⊓ centralizer ({x} : Set P)
    let f : C → {v : Natural.Space F // Natural.action F movingActor v = v} := fun v =>
      ⟨coordinates ⟨v.val,v.property.1⟩,by
        have hh := hfix x ⟨v.val,v.property.1⟩
          (mem_centralizer_singleton_iff.mp v.property.2).symm
        rw [hxy] at hh
        exact hh⟩
    have hf : Function.Injective f := by
      intro u v h
      have hh := hi (congrArg (fun v : {v : Natural.Space F // Natural.action F movingActor v = v} => v.val) h)
      exact Subtype.ext (congrArg (fun v : b.ker => (v : P)) hh)
    exact (Nat.card_le_card_of_injective f hf).trans moving_fixed_card_le_four
  · rw [hxy]
    exact point_core_centralizer_moving_card_le_two
end Atlas.G2.Natural.BinaryPointFlag
