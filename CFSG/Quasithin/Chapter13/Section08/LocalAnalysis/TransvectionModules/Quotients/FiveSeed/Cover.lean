module

public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.TransvectionModules.Quotients.Sections
public import Theory.Representation.BinaryPermutationAlternatingActions
public import Theory.GroupTheory.PPerfectHom
/-!
# The centralizer line in the five-dimensional cover

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, combined
manuscript of 1 March 2004, printed p.948, the last paragraph of 13.8.6.

The A₆-fixed vectors in the actual augmentation core on six letters are zero
and the constant vector. Two-perfectness lifts these fixed vectors through a
central elementary two-kernel: the displacement homomorphism into that kernel
vanishes. A weight-four flag misses the constant vector, giving the source
relative index two. Normalization of the kernel and centralizer then gives the
local commutator bound. No abelianness of the L-conjugate span is used.

The coordinate projection in this module has its kernel and action specified.
The sibling source adapter constructs it from the literal Utilde quotient.
-/

@[expose] public section

open Subgroup
open scoped commutatorElement IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section08.TransvectionQuotients.FiveSeed
open BinaryPermutation

def oneVector : core (Fin 6) := ⟨allOne (Fin 6), by change augmentation (Fin 6) _ = 0; rw [augmentation_allOne]; rfl⟩

private def moveZero (i : Fin 6) : Equiv.Perm (Fin 6) :=
  if i = 0 then 1 else if i = 1 then Equiv.swap 0 2 * Equiv.swap 0 1
  else Equiv.swap 0 1 * Equiv.swap 0 i

private theorem moveZero_spec (i : Fin 6) :
    moveZero i ∈ alternatingGroup (Fin 6) ∧ moveZero i 0 = i := by
  change Equiv.Perm.sign (moveZero i) = 1 ∧ moveZero i 0 = i
  fin_cases i <;> decide

theorem core_fixed_iff (v : core (Fin 6)) :
    (∀ g : alternatingGroup (Fin 6), alternatingCoreRepresentation (Fin 6) g v = v) ↔
      v = 0 ∨ v = oneVector := by
  constructor
  · intro h
    have hc (i : Fin 6) : v.val i = v.val 0 := by
      let g : alternatingGroup (Fin 6) := ⟨moveZero i, (moveZero_spec i).1⟩
      have he := congrArg (fun w : core (Fin 6) => w.val (g.val 0)) (h g)
      change v.val (g.val.symm (g.val 0)) = v.val (g.val 0) at he
      rw [Equiv.symm_apply_apply] at he
      change v.val 0 = v.val (moveZero i 0) at he
      rw [(moveZero_spec i).2] at he
      exact he.symm
    have hv : v.val 0 = 0 ∨ v.val 0 = 1 := by
      have h : ∀ c : ZMod 2, c = 0 ∨ c = 1 := by decide
      exact h _
    rcases hv with hz | ho
    · left; apply Subtype.ext; funext i; exact (hc i).trans hz
    · right; apply Subtype.ext; funext i; exact (hc i).trans ho
  · rintro (rfl | rfl) g
    · exact map_zero _
    · apply Subtype.ext; exact permute_allOne (Fin 6) g.val

theorem oneVector_ne_zero : oneVector ≠ 0 := by
  intro h
  have := congrArg (fun v : core (Fin 6) => v.val 0) h
  exact one_ne_zero this

variable {G : Type*} [Group G]

/-- Central displacement in a two-group vanishes for a two-perfect actor. -/
private theorem centralizes_of_displacement (K Z : Subgroup G)
    [IsMulCommutative Z] (hK : IsPPerfect 2 K) (hZ : IsPGroup 2 Z)
    (hcentral : Z ≤ centralizer (K : Set G)) (u : G)
    (hu : ∀ k : K, ⁅(k : G), u⁆ ∈ Z) : u ∈ centralizer (K : Set G) := by
  let d : K →* Z := {
    toFun k := ⟨⁅(k : G), u⁆, hu k⟩
    map_one' := by apply Subtype.ext; simp
    map_mul' := by
      intro k l
      apply Subtype.ext
      change ⁅(k : G) * l, u⁆ = ⁅(k : G), u⁆ * ⁅(l : G), u⁆
      have hc := mem_centralizer_iff.mp (hcentral (hu l)) k k.property
      rw [commutatorElement_mul_left_eq_conj_mul, hc, mul_inv_cancel_right]
      exact congrArg Subtype.val (mul_comm (⟨⁅(l : G), u⁆, hu l⟩ : Z)
        (⟨⁅(k : G), u⁆, hu k⟩ : Z)) }
  have hd := hK.hom_eq_one_of_isPGroup hZ d
  rw [mem_centralizer_iff]
  intro k hk
  have he := congrArg (fun f : K →* Z => (f ⟨k, hk⟩ : G)) hd
  change ⁅k, u⁆ = 1 at he
  exact commutatorElement_eq_one_iff_mul_comm.mp he

/-- The weight-four flag misses the constant vector of weight six. -/
theorem constant_not_weight_four (v : core (Fin 6))
    (hv : v = 0 ∨ Fintype.card {i : Fin 6 // v.val i ≠ 0} = 4) : v ≠ oneVector := by
  rintro rfl
  rcases hv with h | h
  · exact oneVector_ne_zero h
  · have : Fintype.card {i : Fin 6 // oneVector.val i ≠ 0} = 6 := by decide
    omega

variable (U Z K : Subgroup G) [IsElementaryAbelian 2 Z]
  (hK : IsPPerfect 2 K) (hcentral : Z ≤ centralizer (K : Set G))
  (hKU : K ≤ normalizer (U : Set G))
  (q : U →* Multiplicative (core (Fin 6)))
  (hker : ∀ u : U, q u = 1 ↔ (u : G) ∈ Z)
  (α : K →* alternatingGroup (Fin 6)) (hα : Function.Surjective α)
  (heq : ∀ (k : K) (u : U),
    (q ⟨(k : G) * u * (k : G)⁻¹,
      (mem_normalizer_iff.mp (hKU k.property) u).mp u.property⟩).toAdd =
        alternatingCoreRepresentation (Fin 6) (α k) (q u).toAdd)

include hK hcentral hKU hker hα heq

theorem centralizer_iff_coordinates (u : U) :
    (u : G) ∈ centralizer (K : Set G) ↔
      (q u).toAdd = 0 ∨ (q u).toAdd = oneVector := by
  rw [← core_fixed_iff]
  constructor
  · intro hu g
    obtain ⟨k, rfl⟩ := hα g
    rw [← heq k u]
    congr 3
    exact mul_inv_eq_iff_eq_mul.mpr (mem_centralizer_iff.mp hu k k.property)
  · intro hu
    apply centralizes_of_displacement K Z hK (IsElementaryAbelian.isPGroup 2 Z) hcentral u
    intro k
    let c : U := ⟨(k : G) * u * (k : G)⁻¹,
      (mem_normalizer_iff.mp (hKU k.property) u).mp u.property⟩
    have hc : q c = q u := by
      apply Multiplicative.toAdd.injective
      exact (heq k u).trans (hu (α k))
    have hq : q (c * u⁻¹) = 1 := by rw [map_mul, map_inv, hc, mul_inv_cancel]
    exact (hker (c * u⁻¹)).mp hq

/-- In the marked five-dimensional cover, the genuine centralizer has a
nonzero image and that image consists of precisely the constant line. -/
theorem centralizer_has_nonzero_image (hq : Function.Surjective q) :
    ∃ u : U, (u : G) ∈ centralizer (K : Set G) ∧ (q u).toAdd = oneVector := by
  obtain ⟨u, hu⟩ := hq (Multiplicative.ofAdd oneVector)
  refine ⟨u, (centralizer_iff_coordinates U Z K hK hcentral hKU q hker α hα heq u).mpr
    (Or.inr (congrArg Multiplicative.toAdd hu)), congrArg Multiplicative.toAdd hu⟩

/-- The local commutator bound follows from the fixed line and preservation
of the kernel, without assuming that the ambient conjugate span is abelian. -/
theorem centralizer_commutator_le (R : Subgroup G)
    (hRU : R ≤ normalizer (U : Set G)) (hRZ : R ≤ normalizer (Z : Set G))
    (hRC : R ≤ normalizer (centralizer (K : Set G) : Set G)) :
    ⁅R, U ⊓ centralizer (K : Set G)⁆ ≤ Z := by
  apply commutator_le.mpr
  intro r hr u hu
  let uU : U := ⟨u, hu.1⟩
  let c : U := ⟨r * u * r⁻¹, (mem_normalizer_iff.mp (hRU hr) u).mp hu.1⟩
  have hcC : (c : G) ∈ centralizer (K : Set G) :=
    (mem_normalizer_iff.mp (hRC hr) u).mp hu.2
  have hcu : q c = q uU := by
    by_cases huZ : u ∈ Z
    · have hcZ := (mem_normalizer_iff.mp (hRZ hr) u).mp huZ
      rw [(hker c).mpr hcZ, (hker uU).mpr huZ]
    · have hcZ : (c : G) ∉ Z := fun h => huZ ((mem_normalizer_iff.mp (hRZ hr) u).mpr h)
      have hu0 : (q uU).toAdd ≠ 0 := fun h => huZ ((hker uU).mp h)
      have hc0 : (q c).toAdd ≠ 0 := fun h => hcZ ((hker c).mp h)
      have hu1 := (centralizer_iff_coordinates U Z K hK hcentral hKU q hker α hα heq uU).mp hu.2
      have hc1 := (centralizer_iff_coordinates U Z K hK hcentral hKU q hker α hα heq c).mp hcC
      exact Multiplicative.toAdd.injective ((hc1.resolve_left hc0).trans (hu1.resolve_left hu0).symm)
  apply (hker (c * uU⁻¹)).mp
  rw [map_mul, map_inv, hcu, mul_inv_cancel]

/-- The source relative index is obtained from the cover, its genuine fixed
points, and the earlier weight-four flag. No index assumption is used. -/
theorem centralizer_seed_index (V F : Subgroup G)
    (hq : Function.Surjective q) (hVU : V ⊓ U = F) (hZV : Z ≤ V)
    (hweight : ∀ u : U, (u : G) ∈ F → (q u).toAdd = 0 ∨
      Fintype.card {i : Fin 6 // (q u).toAdd.val i ≠ 0} = 4) :
    V.relIndex (U ⊓ centralizer (K : Set G)) = 2 := by
  obtain ⟨a, haC, haq⟩ := centralizer_has_nonzero_image U Z K hK hcentral hKU q hker α hα heq hq
  have hqa_ne : q a ≠ 1 := by
    intro h
    exact oneVector_ne_zero (haq.symm.trans (congrArg Multiplicative.toAdd h))
  have haV : (a : G) ∉ V := by
    intro ha
    have haF : (a : G) ∈ F := hVU ▸ ⟨ha, a.property⟩
    exact constant_not_weight_four _ (hweight a haF) haq
  apply relIndex_eq_two_iff_exists_notMem_and.mpr
  refine ⟨a, ⟨a.property, haC⟩, haV, ?_⟩
  intro b hb
  let bU : U := ⟨b, hb.1⟩
  rcases (centralizer_iff_coordinates U Z K hK hcentral hKU q hker α hα heq bU).mp hb.2 with hz | ho
  · exact Or.inr (hZV ((hker bU).mp hz))
  · left
    apply hZV
    apply (hker (bU * a)).mp
    apply Multiplicative.toAdd.injective
    change (q (bU * a)).toAdd = 0
    rw [map_mul]
    change (q bU).toAdd + (q a).toAdd = 0
    rw [ho, haq]
    simpa only [add_smul, one_smul, zero_smul] using
      congrArg (fun c : ZMod 2 => c • oneVector) (show (1 : ZMod 2) + 1 = 0 from rfl)

end CFSG.Quasithin.Chapter13.Section08.TransvectionQuotients.FiveSeed

end
