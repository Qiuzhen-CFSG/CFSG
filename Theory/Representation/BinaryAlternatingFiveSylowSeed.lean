module
public import Theory.SpecificGroups.Alternating.FiveSylowMaximal
public import Theory.Representation.BinaryPermutationAlternatingActions
public import Theory.Representation.BinaryConjugationSection
public import Theory.GroupTheory.SylowCentralizerComplement
/-!
# Sylow-fixed seeds in the binary A₅ module

A nonzero even coloring of five letters has stabilizer of order six or
twelve. A Sylow four-group forces the latter, a maximal subgroup of A₅.
The unique proper Sylow overgroup therefore fixes every Sylow-fixed word.
For a literal conjugation section, averaging over the odd Sylow index
splits each seed element into a module vector and an H-central element.
This transfers the same fixation to the original ambient seed.

Source: Aschbacher--Smith, completion of 12.3.1, printed p.811,
using the splitting argument of B.2.14.
-/

public section
open Subgroup
open Theory.SpecificGroups.Alternating.FiveSylowMaximal
namespace BinaryPermutation
local notation "A" => alternatingGroup (Fin 5)
private def fixer (w : Full (Fin 5)) : Subgroup A where
  carrier := {g | representation (Fin 5) g.val w = w}
  one_mem' := by change representation (Fin 5) 1 w = w; rw [map_one]; rfl
  mul_mem' := by
    intro a b ha hb
    change representation (Fin 5) (a.val * b.val) w = w
    rw [map_mul,Module.End.mul_apply,hb,ha]
  inv_mem' := by
    intro a ha
    have h := congrArg (representation (Fin 5) a.val⁻¹) ha
    rw [←Module.End.mul_apply,←map_mul,inv_mul_cancel,map_one,Module.End.one_apply] at h
    exact h.symm
private instance (w : Full (Fin 5)) : DecidablePred (· ∈ fixer w) := fun g =>
  inferInstanceAs (Decidable (representation (Fin 5) g.val w = w))
private theorem fixer_card (w : Full (Fin 5)) (hw : ∑ i, w i = 0) (hw0 : w ≠ 0) :
    Nat.card (fixer w) = 6 ∨ Nat.card (fixer w) = 12 := by
  rw [Nat.card_eq_fintype_card]
  have h : ∀ w : Full (Fin 5), (∑ i, w i = 0) → w ≠ 0 →
      Fintype.card (fixer w) = 6 ∨ Fintype.card (fixer w) = 12 := by decide +kernel
  exact h w hw hw0

theorem core_fixed_of_proper_sylow_overgroup
    (P : Sylow 2 A) (B : Subgroup A) (hPB : (P : Subgroup A) ≤ B)
    (hB : B ≠ ⊤) (w : core (Fin 5))
    (hw : ∀ g ∈ P, alternatingCoreRepresentation (Fin 5) g w = w)
    (g : A) (hg : g ∈ B) : alternatingCoreRepresentation (Fin 5) g w = w := by
  by_cases hw0 : w = 0
  · rw [hw0,map_zero]
  have hwv : w.val ≠ 0 := fun h => hw0 (Subtype.ext h)
  have hPF : (P : Subgroup A) ≤ fixer w.val := by
    intro a ha
    exact congrArg Subtype.val (hw a ha)
  have hp4 : Nat.card P = 4 := by
    rw [P.card_eq_multiplicity,nat_card_alternatingGroup, Nat.card_eq_fintype_card]
    decide +kernel
  have hf12 : Nat.card (fixer w.val) = 12 := by
    rcases fixer_card w.val w.property hwv with h | h
    · have hd := card_dvd_of_le hPF
      rw [hp4,h] at hd
      norm_num at hd
    · exact h
  have hindex : (fixer w.val).index = 5 := by
    have h := (fixer w.val).card_mul_index
    rw [hf12,nat_card_alternatingGroup] at h
    norm_num [Nat.factorial] at h
    omega
  have hco : IsCoatom (fixer w.val) := by
    refine ⟨?_,?_⟩
    · intro he
      simp [he] at hindex
    · intro J hJ
      have hd := index_dvd_of_le hJ.le
      rw [hindex] at hd
      rcases (Nat.dvd_prime Nat.prime_five).mp hd with he | he
      · exact index_eq_one.mp he
      · have := index_strictAnti hJ
        omega
  have hBF := (sylow_unique P).le_maximal ⟨hPF,hco.covBy_top⟩ hPB
    (lt_top_iff_ne_top.mpr hB)
  exact Subtype.ext (hBF hg)
end BinaryPermutation

namespace Representation.BinaryConjugationSection
open scoped IsMulCommutative commutatorElement
variable {G : Type*} [Group G] [Finite G] {H W : Subgroup G}

/-- A proper Sylow overgroup fixes every Sylow-central seed whose H-displacement
lies in the actual binary A₅ module. -/
theorem centralizes_seed_of_five_sylow_overgroup
    (q : H →* alternatingGroup (Fin 5)) (hq : Function.Surjective q)
    (c : BinaryConjugationSection H W ⊥
      ((BinaryPermutation.alternatingCoreRepresentation (Fin 5)).comp q))
    (R : Sylow 2 H) (X Z : Subgroup G) (hXH : X ≤ H)
    (hRX : (R : Subgroup H).map H.subtype ≤ X)
    (hproper : (X.subgroupOf H).map q ≠ ⊤)
    (hZ : Z ≤ centralizer ((R : Subgroup H).map H.subtype : Set G))
    (hm : ⁅Z,H⁆ ≤ W) : X ≤ centralizer (Z : Set G) := by
  have hci : Function.Injective c.coordinates := by
    apply (MonoidHom.ker_eq_bot_iff _).mp
    rw [c.kernel_eq,bot_subgroupOf]
  let : CommGroup W := MonoidHom.commGroupOfInjective c.coordinates hci
  intro x hx
  apply mem_centralizer_iff.mpr
  intro z hz
  obtain ⟨w,hw,hwz⟩ := fixed_coset_of_sylow H W c.normalized
    (fun w hw => congrArg Subtype.val (c.square_eq_one_of_trivial_kernel rfl ⟨w,hw⟩))
    R z (fun a ha => by
      apply hm
      rw [commutator_comm]
      exact commutator_mem_commutator ha hz)
    (fun a ha => hZ hz (a : G) (mem_map_of_mem H.subtype ha))
  have hwR : w ∈ centralizer ((R : Subgroup H).map H.subtype : Set G) := by
    have hh := (centralizer ((R : Subgroup H).map H.subtype : Set G)).mul_mem
      (centralizer_le (map_subtype_le _) hwz) (inv_mem (hZ hz))
    simpa only [mul_inv_cancel_right] using hh
  have hfix (a : H) (ha : a ∈ R) :
      BinaryPermutation.alternatingCoreRepresentation (Fin 5) (q a)
        (c.coordinates ⟨w,hw⟩).toAdd = (c.coordinates ⟨w,hw⟩).toAdd := by
    have he : (a : G) * w * (a : G)⁻¹ = w := mul_inv_eq_iff_eq_mul.mpr
      ((mem_centralizer_iff.mp hwR) _ (mem_map_of_mem H.subtype ha))
    have hh := c.equivariant a ⟨w,hw⟩
    have he' : (⟨(a : G) * w * (a : G)⁻¹,
        (mem_normalizer_iff.mp (c.normalized a.property) w).mp hw⟩ : W) = ⟨w,hw⟩ :=
      Subtype.ext he
    rw [he'] at hh
    exact hh.symm
  have hfix' : ∀ a ∈ R.mapSurjective hq,
      BinaryPermutation.alternatingCoreRepresentation (Fin 5) a
        (c.coordinates ⟨w,hw⟩).toAdd = (c.coordinates ⟨w,hw⟩).toAdd := by
    rintro a ⟨b,hb,rfl⟩
    exact hfix b hb
  have himage : (R.mapSurjective hq : Subgroup (alternatingGroup (Fin 5))) ≤
      (X.subgroupOf H).map q := map_mono (by
    intro a ha
    exact hRX (mem_map_of_mem H.subtype ha))
  have hxfix := BinaryPermutation.core_fixed_of_proper_sylow_overgroup
    (R.mapSurjective hq) ((X.subgroupOf H).map q) himage hproper
    (c.coordinates ⟨w,hw⟩).toAdd hfix' (q ⟨x,hXH hx⟩)
    (mem_map_of_mem q hx)
  have hh := c.equivariant ⟨x,hXH hx⟩ ⟨w,hw⟩
  have he : x*w*x⁻¹=w := congrArg Subtype.val
    (hci (Multiplicative.toAdd.injective (hh.trans hxfix)))
  have hxw : w*x=x*w := (mul_inv_eq_iff_eq_mul.mp he).symm
  have hxwz := mem_centralizer_iff.mp hwz x (hXH hx)
  calc
    z*x = w⁻¹ * ((w*z)*x) := by group
    _ = w⁻¹ * (x*(w*z)) := by rw [←hxwz]
    _ = x*z := by rw [←mul_assoc x w z,←hxw]; group
end Representation.BinaryConjugationSection
