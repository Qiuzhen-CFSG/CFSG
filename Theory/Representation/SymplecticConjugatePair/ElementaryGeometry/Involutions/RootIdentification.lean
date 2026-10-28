module

public import Theory.Representation.SymplecticConjugatePair.ElementaryGeometry.Involutions.CentralTypes
public import Theory.Representation.SymplecticConjugatePair.ElementaryGeometry.Placement
public import Theory.SpecificGroups.SymplecticFour.RootNormalizerResidual.Weyl

/-!
# Root identification for native symplectic involutions

Every involution generates an elementary subgroup. The proved shear placement
puts it into a conjugate of the Sylow center or gives paired codimension at
least 5n. The latter is impossible: in characteristic two the displacement
image of an involution lies in its fixed space, so its codimension on the
8n-dimensional pair is at most 4n.

The central coordinate calculation then identifies b₁ with conjugates of
root 0 and a₂ with conjugates of root 4. Explicit Weyl conjugations cover
all eight original matrix roots. Consequently the geometric Suzuki root
types are exactly the actual root elements, and c₂ is the non-root type.
No conjugacy classification is assumed.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*,
Definition E.2.6, printed p.218, and H.7, printed pp.388–389.
-/

public section

open scoped Matrix
open Matrix Representation Representation.BinaryOffender
open Theory.SpecificGroups.SymplecticFour
open Representation.OneCohomology.SymplecticFour
open Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms.ExceptionalGraph
open Theory.SpecificGroups.SymplecticFour.InvolutionTypes

namespace SymplecticConjugatePair.Involutions
set_option linter.unusedSimpArgs false
variable {F : Type*} [Field F] [CharP F 2] [Finite F] [Algebra (ZMod 2) F]

/-- In characteristic two an involution fixes every vector in its displacement image. -/
lemma involution_displacement_le_fixed (g : Sp F) (hg : g^2 = 1) :
    LinearMap.range (graphPair g - LinearMap.id) ≤ fixedSpace graphPair (Subgroup.zpowers g) := by
  rintro _ ⟨v,rfl⟩
  rw [mem_fixedSpace_zpowers_iff]
  change graphPair g (graphPair g v-v) = graphPair g v-v
  rw [map_sub]
  have hs : graphPair g (graphPair g v) = v := by
    change (graphPair g * graphPair g) v = v
    rw [← map_mul,← pow_two,hg,map_one]
    rfl
  rw [hs]
  ext i <;> simp [sub_eq_add_neg,CharTwo.neg_eq,add_comm]

private lemma involution_fixedCodim_upper {n : ℕ} (hF : Nat.card F = 2^n)
    (g : Sp F) (hg : g^2 = 1) : fixedCodim graphPair (Subgroup.zpowers g) ≤ 4*n := by
  have hi := Submodule.finrank_mono (involution_displacement_le_fixed g hg)
  have hc := fixedCodim_add_finrank (graphPair (F := F)) (Subgroup.zpowers g)
  rw [finrank_space hF] at hc
  rw [fixedCodim_zpowers_eq_displacement_rank] at hc ⊢
  omega

/-- Every native involution is conjugate to the actual two-root Sylow center. -/
lemma involution_conjugate_central {n : ℕ} (hF : Nat.card F = 2^n)
    (g : Sp F) (hg : orderOf g = 2) :
    ∃ h : Sp F, ∃ s t : F, h*g*h⁻¹ = rootElement 0 s * rootElement 4 t := by
  have hn : 0 < n := by
    by_contra hn
    have hn0 : n = 0 := by omega
    have hc : Nat.card F = 1 := by simpa [hn0] using hF
    let : Subsingleton F := (Nat.card_eq_one_iff_unique.mp hc).1
    exact zero_ne_one (Subsingleton.elim (0:F) 1)
  have hsq : g^2 = 1 := (orderOf_eq_prime_iff.mp hg).1
  let := IsElementaryAbelian.zpowers_of_pow_eq_one hsq
  rcases elementary_subgroup_placement hF hn (Subgroup.zpowers g) with ⟨h,hh⟩ | hb
  · have hm := hh (Subgroup.mem_map_of_mem (MulAut.conj h).toMonoidHom (Subgroup.mem_zpowers g))
    obtain ⟨s,t,he⟩ := (mem_sylowCenter_iff _).mp hm
    exact ⟨h,s,t,he.symm⟩
  · have hu := involution_fixedCodim_upper hF g hsq
    omega

lemma isB1_iff_conjugate_root_zero {n : ℕ} (hF : Nat.card F = 2^n) (g : Sp F) :
    IsB1 g ↔ ∃ h : Sp F, ∃ t : F, t ≠ 0 ∧ g = h * rootElement 0 t * h⁻¹ := by
  constructor
  · intro hg
    obtain ⟨h,s,t,he⟩ := involution_conjugate_central hF g hg.1
    have hz := (isB1_conj_iff h g).mpr hg
    rw [he,central_isB1_iff] at hz
    obtain ⟨hs,rfl⟩ := hz
    simp only [RootSubgroup.element_zero,mul_one] at he
    refine ⟨h⁻¹,s,hs,?_⟩
    rw [← he]
    group
  · rintro ⟨h,t,ht,rfl⟩
    apply (isB1_conj_iff h _).mpr
    simpa only [RootSubgroup.element_zero,mul_one] using central_isB1 ht

lemma isA2_iff_conjugate_root_four {n : ℕ} (hF : Nat.card F = 2^n) (g : Sp F) :
    IsA2 g ↔ ∃ h : Sp F, ∃ t : F, t ≠ 0 ∧ g = h * rootElement 4 t * h⁻¹ := by
  constructor
  · intro hg
    obtain ⟨h,s,t,he⟩ := involution_conjugate_central hF g hg.1
    have hz := (isA2_conj_iff h g).mpr hg
    rw [he,central_isA2_iff] at hz
    obtain ⟨rfl,ht⟩ := hz
    simp only [RootSubgroup.element_zero,one_mul] at he
    refine ⟨h⁻¹,t,ht,?_⟩
    rw [← he]
    group
  · rintro ⟨h,t,ht,rfl⟩
    apply (isA2_conj_iff h _).mpr
    simpa only [RootSubgroup.element_zero,one_mul] using central_isA2 ht

lemma rootElement_type (r : Fin 8) {t : F} (ht : t ≠ 0) :
    IsB1 (rootElement r t) ∨ IsA2 (rootElement r t) := by
  obtain ⟨w,hw⟩ := RootNormalizerResidual.exists_root_conjugation (F := F) r
  have hm : rootElement r t ∈ (RootSubgroup.group (if r.val < 4 then 0 else 4)).map
      (MulAut.conj w).toMonoidHom := by
    rw [hw]
    exact (RootSubgroup.mem_group_iff _ _).mpr ⟨t,rfl⟩
  obtain ⟨_,hy,he⟩ := hm
  obtain ⟨u,rfl⟩ := (RootSubgroup.mem_group_iff _ _).mp hy
  have hu : u ≠ 0 := by
    intro hu
    have ho := InvolutionCentralizers.rootElement_orderOf r ht
    simp only [hu,RootSubgroup.element_zero,map_one] at he
    rw [← he,orderOf_one] at ho
    omega
  by_cases hr : r.val < 4
  · left
    rw [if_pos hr] at he
    rw [← he]
    apply (isB1_conj_iff w _).mpr
    simpa only [RootSubgroup.element_zero,mul_one] using central_isB1 hu
  · right
    rw [if_neg hr] at he
    rw [← he]
    apply (isA2_conj_iff w _).mpr
    simpa only [RootSubgroup.element_zero,one_mul] using central_isA2 hu

/-- The geometric Suzuki root types are precisely conjugates of the eight matrix root groups. -/
lemma isRootElement_iff {n : ℕ} (hF : Nat.card F = 2^n) (g : Sp F) :
    IsRootElement g ↔ IsB1 g ∨ IsA2 g := by
  constructor
  · rintro ⟨h,r,t,ht,rfl⟩
    exact (rootElement_type r ht).elim
      (fun hb => Or.inl ((isB1_conj_iff h _).mpr hb))
      (fun ha => Or.inr ((isA2_conj_iff h _).mpr ha))
  · rintro (hb | ha)
    · obtain ⟨h,t,ht,he⟩ := (isB1_iff_conjugate_root_zero hF g).mp hb
      exact ⟨h,0,t,ht,he⟩
    · obtain ⟨h,t,ht,he⟩ := (isA2_iff_conjugate_root_four hF g).mp ha
      exact ⟨h,4,t,ht,he⟩

lemma isC2_iff_not_root {n : ℕ} (hF : Nat.card F = 2^n) (g : Sp F)
    (hg : orderOf g = 2) : IsC2 g ↔ ¬ IsRootElement g := by
  rw [isRootElement_iff hF]
  constructor
  · rintro ⟨_,hc,v,hv⟩ (hb | ha)
    · have hb := hb.2
      omega
    · exact hv (ha.2.2 v)
  · intro h
    exact (InvolutionCentralizers.involution_types g hg).resolve_left
      (fun hb => h (Or.inl hb)) |>.resolve_left (fun ha => h (Or.inr ha))
end SymplecticConjugatePair.Involutions
