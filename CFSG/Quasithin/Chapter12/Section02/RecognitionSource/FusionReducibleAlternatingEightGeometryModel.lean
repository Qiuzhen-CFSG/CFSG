module
public import CFSG.Quasithin.Chapter12.Section02.RecognitionSource.FusionReducibleAdjustment
public import Theory.Representation.BinaryPermutation.EightCoreOrbits
public import Theory.GroupTheory.ConjugationOrbitSize

/-!
# The actual eight-core coordinates in the reducible alternating row

This packages only the supplied L/O₂(L) conjugation marking. Transport of
weight classes through its vector equivalence identifies the actual L-orbits
in V and their sizes. The all-one word gives the unique nonidentity element
of C_V(L), allowing the existing fixed-line fusion theorems to apply.
No fusion or Sylow condition is included in these coordinates.

Source: Aschbacher--Smith, 12.2.16, printed pp.799--800.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section02.RecognitionSource
variable {G : Type*} [Group G] {L V : Subgroup G}

structure AlternatingEightCoreCoordinates (L V : Subgroup G) where
  groupEquiv : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 8)
  vectorEquiv : V ≃* Multiplicative (BinaryPermutation.core (Fin 8))
  intertwines : ∀ (l : L) (w : V),
    ((vectorEquiv.symm (Multiplicative.ofAdd
      (BinaryPermutation.alternatingCoreRepresentation (Fin 8)
        (groupEquiv (QuotientGroup.mk' (pCore 2 L) l))
        (vectorEquiv w).toAdd))) : G) = (l : G) * (w : G) * (l : G)⁻¹

namespace AlternatingEightCoreCoordinates
open BinaryPermutation
variable (C : AlternatingEightCoreCoordinates L V)

abbrev word (v : V) : core (Fin 8) := (C.vectorEquiv v).toAdd
abbrev weight (v : V) : ℕ := wordWeight (C.word v).val

def realize (w : core (Fin 8)) : G := C.vectorEquiv.symm (Multiplicative.ofAdd w)

theorem realize_injective : Function.Injective C.realize :=
  Subtype.val_injective.comp (C.vectorEquiv.symm.injective.comp Multiplicative.ofAdd.injective)

@[simp] theorem realize_word (v : V) : C.realize (C.word v) = v := by
  simp [realize]

@[simp] theorem realize_zero : C.realize 0 = 1 := by
  change (C.vectorEquiv.symm 1 : G) = 1
  simp

def fiber (n : ℕ) : Set G := C.realize '' {w | wordWeight w.val = n}

theorem fiber_card (n : ℕ) : (C.fiber n).ncard = EightCore.orbitSize n := by
  rw [fiber,Set.ncard_image_of_injective _ C.realize_injective,EightCore.weight_fiber_card]

theorem mem_fiber (v : V) (n : ℕ) : (v : G) ∈ C.fiber n ↔ C.weight v = n := by
  constructor
  · rintro ⟨w,hw,he⟩
    have hh : w = C.word v := C.realize_injective (he.trans (C.realize_word v).symm)
    simpa [hh] using hw
  · intro h
    exact ⟨C.word v,h,C.realize_word v⟩

theorem orbit_eq_fiber (v : V) : conjugacyOrbit L (v : G) = C.fiber (C.weight v) := by
  ext x
  constructor
  · rintro ⟨l,rfl⟩
    refine ⟨alternatingCoreRepresentation (Fin 8)
      (C.groupEquiv (QuotientGroup.mk' (pCore 2 L) l)) (C.word v),?_,C.intertwines l v⟩
    exact wordWeight_permute _ _
  · rintro ⟨w,hw,rfl⟩
    obtain ⟨a,ha⟩ := exists_even_permutation_of_weight
      (by decide : 3 ≤ Fintype.card (Fin 8)) (C.word v).val w.val hw.symm
    obtain ⟨l,hl⟩ := QuotientGroup.mk'_surjective (pCore 2 L) (C.groupEquiv.symm a)
    have he : C.groupEquiv (QuotientGroup.mk' (pCore 2 L) l) = a := by
      rw [hl,C.groupEquiv.apply_symm_apply]
    refine ⟨l,?_⟩
    change (l : G) * (v : G) * (l : G)⁻¹ = C.realize w
    rw [← C.intertwines l v,he]
    exact congrArg C.realize (Subtype.ext ha)

theorem orbit_card (v : V) :
    (conjugacyOrbit L (v : G)).ncard = EightCore.orbitSize (C.weight v) := by
  rw [C.orbit_eq_fiber,C.fiber_card]

theorem conjugator_of_weight (v w : V) (hw : C.weight v = C.weight w) :
    ∃ l ∈ L, l * (v : G) * l⁻¹ = w := by
  have hh : (w : G) ∈ conjugacyOrbit L (v : G) := by
    rw [C.orbit_eq_fiber,C.mem_fiber]
    exact hw.symm
  obtain ⟨l,hl⟩ := hh
  exact ⟨l,l.property,hl⟩

theorem normalizer_preserves_size (v w : V) {m : G}
    (hm : m ∈ normalizer (L : Set G)) (he : m * (v : G) * m⁻¹ = w) :
    EightCore.orbitSize (C.weight v) = EightCore.orbitSize (C.weight w) := by
  rw [← C.orbit_card v,← C.orbit_card w,← he,conjugacyOrbit_normalizer L (v : G) m hm]

def z : V := C.vectorEquiv.symm (Multiplicative.ofAdd EightCore.oneWord)

@[simp] theorem word_z : C.word C.z = EightCore.oneWord := C.vectorEquiv.apply_symm_apply _

theorem constant (i : Fin 8) : (C.word C.z).val i = 1 := by rw [C.word_z]; rfl

theorem z_ne : (C.z : G) ≠ 1 := by
  intro he
  have hh := C.constant 0
  change (C.vectorEquiv C.z).toAdd.val 0 = 1 at hh
  rw [show C.z = 1 from Subtype.ext he,map_one] at hh
  exact zero_ne_one hh

@[simp] theorem weight_zero_iff (v : V) : C.weight v = 0 ↔ v = 1 := by
  rw [weight,EightCore.weight_zero_iff]
  exact C.vectorEquiv.map_eq_one_iff

@[simp] theorem weight_eight_iff (v : V) : C.weight v = 8 ↔ v = C.z := by
  rw [weight,EightCore.weight_eight_iff,← C.word_z]
  exact ⟨fun h => C.vectorEquiv.injective h,fun h => congrArg C.word h⟩

theorem weight_mul_z (v : V) : C.weight (v * C.z) = 8 - C.weight v := by
  change wordWeight (C.vectorEquiv (v * C.z)).toAdd.val = _
  rw [map_mul]
  exact (congrArg (fun w : core (Fin 8) => wordWeight (C.word v + w).val) C.word_z).trans
    (EightCore.weight_complement (C.word v))

@[simp] theorem z_mul_z : C.z * C.z = 1 := by
  apply C.vectorEquiv.injective
  rw [map_mul,map_one]
  change Multiplicative.ofAdd (C.word C.z + C.word C.z) = 1
  rw [C.word_z,EightCore.oneWord_add_oneWord]
  rfl

theorem z_fixed : (C.z : G) ∈ centralizer (L : Set G) := by
  intro l hl
  have he := C.intertwines ⟨l,hl⟩ C.z
  have hf : alternatingCoreRepresentation (Fin 8)
      (C.groupEquiv (QuotientGroup.mk' (pCore 2 L) ⟨l,hl⟩))
      (C.word C.z) = C.word C.z := by
    apply Subtype.ext
    funext i
    exact (C.constant _).trans (C.constant i).symm
  rw [hf,ofAdd_toAdd,C.vectorEquiv.symm_apply_apply] at he
  exact mul_inv_eq_iff_eq_mul.mp he.symm

theorem fixed_line : ∀ w ∈ V, w ∈ centralizer (L : Set G) → w = 1 ∨ w = (C.z : G) := by
  intro w hw hL
  let w' : V := ⟨w,hw⟩
  have hfixed : ∀ a : alternatingGroup (Fin 8),
      coreRepresentation (Fin 8) a.val (C.word w') = C.word w' := by
    intro a
    obtain ⟨l,hl⟩ := QuotientGroup.mk'_surjective (pCore 2 L) (C.groupEquiv.symm a)
    have ha : C.groupEquiv (QuotientGroup.mk' (pCore 2 L) l) = a := by
      rw [hl,C.groupEquiv.apply_symm_apply]
    have he := C.intertwines l w'
    rw [ha] at he
    have hc : (l : G) * (w' : G) * (l : G)⁻¹ = w' :=
      mul_inv_eq_iff_eq_mul.mpr (hL l l.property)
    rw [hc] at he
    have hh := congrArg (fun x : V => (C.vectorEquiv x).toAdd) (Subtype.ext he)
    simpa only [C.vectorEquiv.apply_symm_apply,toAdd_ofAdd,
      alternatingCoreRepresentation,MonoidHom.comp_apply,Subgroup.coe_subtype] using hh
  obtain ⟨c,hc⟩ := (mem_constants_iff _).mp
    ((core_fixed_iff_constant (by norm_num) _).mp hfixed)
  rcases (by decide : ∀ c : ZMod 2, c = 0 ∨ c = 1) c with rfl | rfl
  · left
    have he : C.vectorEquiv w' = 1 := by
      apply Multiplicative.toAdd.injective
      apply Subtype.ext
      funext i
      exact hc i
    exact congrArg Subtype.val (C.vectorEquiv.map_eq_one_iff.mp he)
  · right
    apply congrArg (fun x : V => (x : G)) (show w' = C.z from ?_)
    apply C.vectorEquiv.injective
    apply Multiplicative.toAdd.injective
    apply Subtype.ext
    funext i
    exact (hc i).trans (C.constant i).symm

end AlternatingEightCoreCoordinates
end CFSG.Quasithin.Chapter12.Section02.RecognitionSource
