module
public import Theory.Representation.MathieuCodeRestriction.CodeLocal.CentralizerGeometry.SectionAction
public import Theory.Representation.MathieuCodeRestriction.M22.SourceModules.Displacement.Involutions
public import Theory.Mathieu.M22.Properties.NoOrder15
public import Theory.Mathieu.M22.Properties.HexadExtension
public import Theory.Mathieu.M22.Properties.SolvableSylowOvergroups.Coverage.Intransitive
public import Theory.Representation.MathieuCodeRestriction.NormalizedShadowRows.CartanField

/-!
# Split tori fixing the original M22-code Sylow vector

A nonzero Sylow-fixed vector in the ten-dimensional code is the marked
hexad vector: the Sylow contains that hexad's pointwise kernel, whose fixed
space is the known binary line. Its stabilizer is the hexad stabilizer.
An embedded binary split torus fixing this vector has order dividing 5760.
The only possible fields of size at least four are four and sixteen; the
proved absence of order-fifteen elements in M22 excludes sixteen. Odd
actors in the full pair stabilizer are transported through the actual
inner M22 embedding, so no outer actor is silently discarded.

This discharges the field reduction in the original M22-code application
of Aschbacher--Smith 3.1.9(6) and 8.2.2(1), printed pp.578 and715,
refs/quasithin.pdf, using the literal H.13/H.16 hexad fixed line. The source
application retains the original overlap, whole-span cover and automizer.
-/

public noncomputable section
open Subgroup Representation.BinaryOffender Sporadic.Mathieu
open Sporadic.Mathieu.M24LocalGeometry
open scoped Pointwise
namespace MathieuCode.NormalizedShadowRows

/-- Odd elements in the full outer pair action belong to the inner M22. -/
theorem odd_pair_mem_inner (g : m22PairStabilizer) (hg : Odd (orderOf g)) :
    g ∈ m22ToPairStabilizer.range := by
  have hs : g ^ 2 ∈ m22ToPairStabilizer.range := by
    rw [m22ToPairStabilizer_mem_range_iff_fixed_zero]
    by_cases h : g ∈ m22ToPairStabilizer.range
    · have h0 := (m22ToPairStabilizer_mem_range_iff_fixed_zero g).mp h
      change g.val • (g.val • (0 : Fin 24)) = 0
      rw [h0,h0]
    · have h0 := m22PairStabilizer_swaps_of_not_mem_range g h
      have h9 : g.val • (9 : Fin 24) = 0 := by
        have hm := MulAction.mem_stabilizer_finset'.mp g.property
          (by simp [m22Pair] : (9 : Fin 24) ∈ m22Pair)
        have he : g.val • (9 : Fin 24) = 0 ∨ g.val • (9 : Fin 24) = 9 := by
          simpa [m22Pair] using hm
        exact he.resolve_right (fun hh => (by decide : (0 : Fin 24) ≠ 9)
          ((MulAction.injective g.val) (h0.trans hh.symm)))
      change g.val • (g.val • (0 : Fin 24)) = 0
      rw [h0,h9]
  obtain ⟨k,hk⟩ := exists_pow_eq_self_of_coprime (x := g) hg.coprime_two_left
  exact hk ▸ m22ToPairStabilizer.range.pow_mem hs k

/-- Fixing the actual marked code vector preserves the original hexad. -/
theorem hexad_vector_stabilizer {B : Finset (Fin 22)} (hB : B ∈ m22Blocks)
    (g : M22) (hg : m22CodeRepresentation g (m22HexadVector hB) = m22HexadVector hB) :
    g ∈ MulAction.stabilizer M22 B := by
  have hh := (SectionAction.octadVector_fixed_iff (m22Octad hB) (m22Embedding g)).mp
    (congrArg Subtype.val hg)
  apply MulAction.mem_stabilizer_finset'.mpr
  intro i hi
  have hm := MulAction.mem_stabilizer_finset'.mp hh
    ((mem_m22AugmentedOctad B (m22Coordinates i)).mpr (Or.inr (Or.inr ⟨i,hi,rfl⟩)))
  change (m22Embedding g).val (m22Coordinates i) ∈ m22AugmentedOctad B at hm
  rw [m22Embedding_apply,mem_m22AugmentedOctad] at hm
  rcases hm with hm | hm | ⟨j,hj,hji⟩
  · exact False.elim ((by decide +kernel : ∀ j : Fin 22, m22Coordinates j ≠ 0) _ hm)
  · exact False.elim ((by decide +kernel : ∀ j : Fin 22, m22Coordinates j ≠ 9) _ hm)
  · exact (m22Coordinates.injective hji) ▸ hj

/-- Every nonzero Sylow-fixed code vector is the vector of an actual hexad. -/
theorem sylow_fixed_code_vector (S : Sylow 2 M22) (v : M22Code) (hv : v ≠ 0)
    (hfix : v ∈ fixedSpace m22CodeRepresentation S) :
    ∃ B : Finset (Fin 22), ∃ hB : B ∈ m22Blocks, v = m22HexadVector hB := by
  obtain ⟨B,hB,hSB⟩ := M22SolvableSylow.sylow_preserves_hexad S
  have hKS := M22SolvableSylow.kernel_le_of_sylow hB S hSB
  have hm : v ∈ fixedSpace m22CodeRepresentation (m22HexadPointwiseKernel B) :=
    fun g => hfix ⟨g,hKS g.property⟩
  rw [m22Hexad_fixedSpace_eq_span_native hB] at hm
  obtain ⟨r,hr⟩ := Submodule.mem_span_singleton.mp hm
  have hr1 : r = 1 := by
    have hz : r ≠ 0 := by intro hz; rw [hz,zero_smul] at hr; exact hv hr.symm
    exact (by decide : ∀ r : ZMod 2, r ≠ 0 → r = 1) r hz
  refine ⟨B,hB,?_⟩
  simpa only [hr1,one_smul] using hr.symm

/-- A split binary torus fixing a nonzero Sylow-fixed M22-code vector has
field order four. Both the outer pair action and original inner Sylow remain literal. -/
theorem code_fixed_split_torus_field_four
    (F : Type*) [Field F] [Finite F] [CharP F 2]
    (hlarge : 4 ≤ Nat.card F)
    (t : Fˣ →* m22PairStabilizer) (ht : Function.Injective t)
    (S : Sylow 2 M22) (v : M22Code) (hv : v ≠ 0)
    (hS : v ∈ fixedSpace m22CodeRepresentation S)
    (hfix : ∀ a, m22OuterCodeRepresentation (t a) v = v) : Nat.card F = 4 := by
  let : Fintype F := Fintype.ofFinite F
  obtain ⟨⟨n,hn⟩,_,hcard⟩ := FiniteField.card F 2
  change Fintype.card F = 2 ^ n at hcard
  have hc : Nat.card F = 2 ^ n := by simpa only [Nat.card_eq_fintype_card] using hcard
  have ho : Odd (Nat.card Fˣ) := by
    rw [Nat.card_units,hc]
    obtain ⟨k,hk⟩ := (by decide : Even 2).pow_of_ne_zero (Nat.ne_of_gt hn)
    have hp : 0 < 2 ^ n := pow_pos (by decide) _
    exact ⟨k-1,by omega⟩
  have hi (a : Fˣ) : t a ∈ m22ToPairStabilizer.range :=
    odd_pair_mem_inner (t a) ((ho.of_dvd_nat (orderOf_dvd_natCard a)).of_dvd_nat (orderOf_map_dvd t a))
  have hj : Function.Injective m22ToPairStabilizer := by
    intro x y he
    exact m22Embedding_injective (congrArg Subtype.val he)
  let e := MonoidHom.ofInjective hj
  let u : Fˣ →* M22 := e.symm.toMonoidHom.comp (t.codRestrict _ hi)
  have hu (a : Fˣ) : m22ToPairStabilizer (u a) = t a :=
    congrArg Subtype.val (e.apply_symm_apply ⟨t a,hi a⟩)
  have hui : Function.Injective u := by
    intro a b hab
    exact ht ((hu a).symm.trans ((congrArg m22ToPairStabilizer hab).trans (hu b)))
  obtain ⟨B,hB,rfl⟩ := sylow_fixed_code_vector S v hv hS
  have huB (a : Fˣ) : u a ∈ MulAction.stabilizer M22 B := by
    apply hexad_vector_stabilizer hB
    rw [←m22OuterCodeRepresentation_restrict,hu]
    exact hfix a
  let f := u.codRestrict (MulAction.stabilizer M22 B) huB
  have hd : 2 ^ n - 1 ∣ 5760 := by
    have hh := card_dvd_of_injective f (fun _ _ he => hui (congrArg Subtype.val he))
    rwa [Nat.card_units,hc,m22Hexad_stabilizer_card hB] at hh
  have hn13 : n < 13 := by
    by_contra hh
    have hp := Nat.pow_le_pow_right (by decide : 0 < 2) (show 13 ≤ n by omega)
    have hl := Nat.le_of_dvd (by decide : 0 < 5760) hd
    norm_num at hp
    omega
  have hn24 : n = 2 ∨ n = 4 := by
    have hge : 4 ≤ 2 ^ n := hc ▸ hlarge
    interval_cases n <;> omega
  rcases hn24 with rfl | rfl
  · exact hc
  · obtain ⟨a,ha⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := Fˣ)
    have hu15 : orderOf (u a) = 15 := by
      rw [orderOf_injective u hui,ha,Nat.card_units,hc]
      decide
    exact (m22_orderOf_ne_fifteen (u a) hu15).elim
end MathieuCode.NormalizedShadowRows
