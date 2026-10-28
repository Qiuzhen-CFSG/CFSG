module
public import Theory.Representation.BinaryPermutation.SixCoreExtension
public import Theory.Representation.BinaryPermutation.Faithful
public import Theory.Representation.BinaryPermutationNaturalStructure
public import Theory.Representation.BinaryOffender.SectionLinear
public import Theory.Representation.BinaryOffender.EquivariantOffender

/-!
# A concrete four-group offender in the six-letter augmentation core

The even flips of three disjoint coordinate pairs form an elementary four.
The pair-constant vectors give a three-dimensional fixed subspace in the
five-dimensional augmentation core, so the four is an offender. The same
literal subgroup remains an offender in every equivariant extension of the
core by fixed vectors: the map on fixed-space quotients is surjective.

Source: Aschbacher--Smith B.1.1–3 and B.3.1–2; this module supplies the
actual offender used with the binary M₂₂ hexad of I.2.2(6).
-/

public section
namespace BinaryPermutation.SixCoreExtension
open Subgroup Representation Representation.BinaryOffender

private def a : A := ⟨Equiv.swap 0 1 * Equiv.swap 2 3, by simp [Equiv.Perm.mem_alternatingGroup]⟩
private def b : A := ⟨Equiv.swap 0 1 * Equiv.swap 4 5, by simp [Equiv.Perm.mem_alternatingGroup]⟩

def pairedFour : Subgroup A where
  carrier := {g | g = 1 ∨ g = a ∨ g = b ∨ g = a * b}
  one_mem' := .inl rfl
  mul_mem' := by rintro x y (rfl|rfl|rfl|rfl) (rfl|rfl|rfl|rfl) <;> decide
  inv_mem' := by rintro x (rfl|rfl|rfl|rfl) <;> decide
private instance (x : A) : Decidable (x ∈ pairedFour) := inferInstanceAs
  (Decidable (x = 1 ∨ x = a ∨ x = b ∨ x = a * b))
private instance : Fintype pairedFour := Fintype.ofFinset {1,a,b,a*b}
  (by intro x; simp [pairedFour])

theorem pairedFour_card : Nat.card pairedFour = 4 := by
  rw [Nat.card_eq_fintype_card]
  decide

theorem pairedFour_elementary : IsElementaryAbelian 2 pairedFour where
  toIsMulCommutative := ⟨⟨by decide⟩⟩
  exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr (by decide)

private def pairedVectors : (Fin 3 → ZMod 2) →ₗ[ZMod 2] V where
  toFun x := ⟨![x 0,x 0,x 1,x 1,x 2,x 2],by
    rw [mem_core]
    simp [Fin.sum_univ_succ,CharTwo.add_self_eq_zero]⟩
  map_add' x y := by apply Subtype.ext; funext i; fin_cases i <;> rfl
  map_smul' c x := by apply Subtype.ext; funext i; fin_cases i <;> rfl

private theorem pairedVectors_injective : Function.Injective pairedVectors := by
  intro x y h
  funext i
  fin_cases i
  · exact congrArg (fun v : V => v.val 0) h
  · exact congrArg (fun v : V => v.val 2) h
  · exact congrArg (fun v : V => v.val 4) h

private theorem pairedVectors_fixed : ∀ (g : pairedFour) (x : Fin 3 → ZMod 2),
    coreRepresentation (Fin 6) (g : A).val (pairedVectors x) = pairedVectors x := by decide

abbrev coreAltRepresentation : Representation (ZMod 2) A V :=
  (coreRepresentation (Fin 6)).comp (alternatingGroup (Fin 6)).subtype

/-- The actual six-letter augmentation action is faithful. -/
theorem coreAltRepresentation_injective : Function.Injective coreAltRepresentation := by
  intro a b hab
  apply Subtype.ext
  apply naturalRepresentation_injective (Fin 6) (by decide)
  ext v
  obtain ⟨u,rfl⟩ := coreToNatural_surjective v
  rw [← coreToNatural_equivariant,← coreToNatural_equivariant]
  exact congrArg (fun w : V => (coreToNatural (Fin 6) w).val) (LinearMap.congr_fun hab u)

theorem pairedFour_core_fixedCodim : fixedCodim coreAltRepresentation pairedFour ≤ 2 := by
  let f : (Fin 3 → ZMod 2) →ₗ[ZMod 2] fixedSpace coreAltRepresentation pairedFour :=
    pairedVectors.codRestrict _ (fun x g => pairedVectors_fixed g x)
  have hi : Function.Injective f := fun _ _ h =>
    pairedVectors_injective (congrArg Subtype.val h)
  have hdim := LinearMap.finrank_le_finrank_of_injective hi
  have he := fixedCodim_add_finrank coreAltRepresentation pairedFour
  have hv : Module.finrank (ZMod 2) V = 5 := by simpa using BinaryPermutation.finrank_core (Fin 6)
  have hf : Module.finrank (ZMod 2) (Fin 3 → ZMod 2) = 3 := by simp
  rw [hf] at hdim
  omega

/-- The actual paired four remains an offender when the augmentation core
is supplemented by vectors fixed by the whole alternating group. -/
theorem pairedFour_extension_offender {W : Type*} [AddCommGroup W]
    [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W]
    (ρ : Representation (ZMod 2) A W) (j : V →ₗ[ZMod 2] W)
    (he : ∀ g v, j (coreAltRepresentation g v) = ρ g (j v))
    (hgen : j.range ⊔ ρ.invariants = ⊤) : IsOffender ρ pairedFour := by
  let D := fixedSpace coreAltRepresentation pairedFour
  let C := fixedSpace ρ pairedFour
  have hmap : D ≤ C.comap j := by
    intro v hv g
    change ρ g (j v) = j v
    rw [← he]
    exact congrArg j (hv g)
  let f := D.mapQ C j hmap
  have hf : Function.Surjective f := by
    intro x
    obtain ⟨w,rfl⟩ := C.mkQ_surjective x
    have hw : w ∈ j.range ⊔ ρ.invariants := hgen ▸ Submodule.mem_top
    obtain ⟨v,⟨v₀,rfl⟩,c,hc,rfl⟩ := Submodule.mem_sup.mp hw
    refine ⟨D.mkQ v₀,?_⟩
    change C.mkQ (j v₀) = C.mkQ (j v₀ + c)
    have hc0 : C.mkQ c = 0 := (Submodule.Quotient.mk_eq_zero C).mpr (fun g => hc g)
    rw [map_add,hc0,add_zero]
  have hdim := LinearMap.finrank_le_finrank_of_surjective hf
  refine ⟨⟨?_,pairedFour_elementary⟩,?_⟩
  · intro hb
    have hc := pairedFour_card
    rw [hb,card_bot] at hc
    omega
  · have hr : rank pairedFour = 2 := by rw [rank,pairedFour_card]; decide
    rw [hr]
    exact hdim.trans pairedFour_core_fixedCodim

end BinaryPermutation.SixCoreExtension
