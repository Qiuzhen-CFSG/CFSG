module

public import Theory.SpecificGroups.Tits.ExceptionalParabolics.FullRee.LongRootPaths.AbelianNormalizer
public import Theory.SpecificGroups.Tits.ExceptionalParabolics.FullRee.LongRootPaths.NormalizerCertificate
public import Mathlib.GroupTheory.Complement

/-!
# The actual five-normalizer in the full first Ree parabolic

One-point separation leaves exactly the eight derived Sylow words generated
by s₁ and s₅. The specified outer root q normalizes the same rotation, so
correcting its coset gives exactly I as the full Sylow intersection. The
five-coset cover of the derived first parabolic and the same outer correction
then prove N_first(B₅)=B₅ I, of order80, with the literal subgroup marks.
Source: Aschbacher--Smith, proof of J.4.7, printed p.442.
-/

public section
noncomputable section
namespace Tits.ExceptionalParabolics.FullRee.LongRootPaths.FiveNormalizer
open Subgroup ReeF4
open RootRelations
open Tits.InvolutionRootGeometry.BinaryDerivedFusion
open Tits.OuterOddSubgroups.OverlapCentralizers
open scoped Pointwise

private theorem normalForm_mem_I (n : Fin 2048)
    (hn : atlasEmbedding (atlas1600SylowTwoNormalForm n) ∈ fiveNormalizer) :
    atlasEmbedding (atlas1600SylowTwoNormalForm n) ∈ I := by
  classical
  have hh := (mem_normalizer_iff.mp hn rotation).mp (mem_zpowers rotation)
  obtain ⟨k, hk, he⟩ := Finset.mem_image.mp
    (mem_zpowers_iff_mem_range_orderOf.mp hh)
  have hk5 : k < 5 := by simpa only [rotation_order, Finset.mem_range] using hk
  have hmul := mul_inv_eq_iff_eq_mul.mp he.symm
  have ha : atlas1600SylowTwoNormalForm n * firstRotation =
      firstRotation^k * atlas1600SylowTwoNormalForm n := by
    apply atlasEmbedding_injective
    simpa only [map_mul, map_pow, rotation] using hmul
  have hp := congrArg Subtype.val ha
  change (atlas1600SylowTwoNormalForm n).val * firstRotation.val =
    firstRotation.val^k * (atlas1600SylowTwoNormalForm n).val at hp
  have hr : firstRotation.val = Atlas1600ParrottData.s1Perm * Atlas1600ParrottData.r1Perm := by
    change (atlas1600ParrottAssignment .s1).val * (atlas1600ParrottAssignment .r1).val = _
    rw [atlas1600ParrottAssignment_val, atlas1600ParrottAssignment_val]
    rfl
  rw [hr] at hp
  have hn' := NormalizerCertificate.normalForm_coordinates n ⟨k,hk5⟩ (by
    simpa only [atlas1600SylowTwoNormalForm_val,
      Atlas1600SylowTwoCertificate.normalForm] using hp)
  have h2 : n.val / 2 % 2 = 0 := by omega
  have h3 : n.val / 4 % 4 = 0 := by omega
  have h4 : n.val / 16 % 2 = 0 := by omega
  have h6 : n.val / 128 % 2 = 0 := by omega
  have h7 : n.val / 256 % 4 = 0 := by omega
  have h8 : n.val / 1024 % 2 = 0 := by omega
  have heq : atlasEmbedding (atlas1600SylowTwoNormalForm n) =
      u^(n.val%2) * s^(n.val/32%4) := by
    rw [atlas1600SylowTwoNormalForm_eq, h2, h3, h4, h6, h7, h8]
    simp only [pow_zero, mul_one, map_mul, map_pow, u, Atlas.a, s]
  rw [heq, ← q_square]
  exact I.mul_mem (I.pow_mem (I.pow_mem (mem_sup_right (mem_zpowers q)) 2) _)
    (I.pow_mem (mem_sup_left (mem_zpowers s)) _)

private theorem derived_sylow_bound {x : Model 0} (hx : x ∈ S)
    (hd : x ∈ commutator (Model 0)) (hn : x ∈ fiveNormalizer) : x ∈ I := by
  have hm : x ∈ ExceptionalParabolics.S.map atlasEmbedding := by
    rw [atlas_sylow_map]
    exact ⟨hx,hd⟩
  obtain ⟨a,ha,rfl⟩ := hm
  obtain ⟨n,rfl⟩ := atlas1600SylowTwoNormalForm_surjective ha
  exact normalForm_mem_I n hn

/-- Exactly the marked sixteen-element abelian subgroup lies in the Borel
and normalizes the selected five-subgroup. -/
theorem sylow_inf_normalizer : S ⊓ fiveNormalizer = I := by
  apply le_antisymm
  · rintro x ⟨hx,hn⟩
    by_cases hd : x ∈ commutator (Model 0)
    · exact derived_sylow_bound hx hd hn
    · obtain ⟨n,he⟩ := outer_unipotent_normalForm x hx hd
      change x = q * atlasEmbedding (atlas1600SylowTwoNormalForm n) at he
      rw [he] at hn ⊢
      have hq : q ∈ fiveNormalizer := I_le_normalizer (mem_sup_right (mem_zpowers q))
      exact I.mul_mem (mem_sup_right (mem_zpowers q))
        (normalForm_mem_I n ((mul_mem_cancel_left hq).mp hn))
  · exact le_inf I_le_sylow I_le_normalizer

private theorem derived_first_bound {x : Model 0} (hx : x ∈ first)
    (hd : x ∈ commutator (Model 0)) (hn : x ∈ fiveNormalizer) : x ∈ five ⊔ I := by
  have hm : x ∈ ExceptionalParabolics.first.map atlasEmbedding := by
    rw [atlas_first_map]
    exact ⟨hx,hd⟩
  obtain ⟨a,ha,rfl⟩ := hm
  obtain ⟨⟨n,k⟩,he⟩ := firstNormalForm_surjective ⟨a,ha⟩
  have ha' := congrArg Subtype.val he
  change atlas1600SylowTwoNormalForm n * firstRotation ^ k.val = a at ha'
  rw [← ha', map_mul, map_pow] at hn ⊢
  change atlasEmbedding (atlas1600SylowTwoNormalForm n) * rotation^k.val ∈ fiveNormalizer at hn
  have hr : rotation^k.val ∈ five := pow_mem (mem_zpowers _) _
  have hh : atlasEmbedding (atlas1600SylowTwoNormalForm n) ∈ fiveNormalizer :=
    (mul_mem_cancel_right (five.le_normalizer hr)).mp hn
  exact (five ⊔ I).mul_mem (mem_sup_right (normalForm_mem_I n hh)) (mem_sup_left hr)

/-- The literal normalizer is the product of the chosen five-group and I. -/
theorem first_inf_normalizer : first ⊓ fiveNormalizer = five ⊔ I := by
  apply le_antisymm
  · rintro x ⟨hx,hn⟩
    by_cases hd : x ∈ commutator (Model 0)
    · exact derived_first_bound hx hd hn
    · have hqF : q ∈ first := sylow_le_first q_mem_sylow
      have hqN : q ∈ fiveNormalizer := I_le_normalizer (mem_sup_right (mem_zpowers q))
      have hout : q⁻¹ ∉ commutator (Model 0) := by
        simpa only [q, inv_mem_iff] using fixedU_zero_not_mem
      have hD : q⁻¹*x ∈ commutator (Model 0) :=
        ((commutator (Model 0)).mul_mem_iff_of_index_two derived_index).mpr
          (iff_of_false hout hd)
      have hbound := derived_first_bound (first.mul_mem (first.inv_mem hqF) hx) hD
        (fiveNormalizer.mul_mem (fiveNormalizer.inv_mem hqN) hn)
      have hprod := (five ⊔ I).mul_mem (mem_sup_right (mem_sup_right (mem_zpowers q))) hbound
      simpa only [mul_inv_cancel_left] using hprod
  · exact sup_le (le_inf (zpowers_le.mpr rotation_mem_first) five.le_normalizer)
      (le_inf (I_le_sylow.trans sylow_le_first) I_le_normalizer)

theorem first_normalizer_product :
    ((first ⊓ fiveNormalizer : Subgroup (Model 0)) : Set (Model 0)) =
      (five : Set (Model 0)) * (I : Set (Model 0)) := by
  rw [first_inf_normalizer]
  exact coe_mul_of_right_le_normalizer_left five I I_le_normalizer

theorem first_normalizer_card : Nat.card (first ⊓ fiveNormalizer : Subgroup (Model 0)) = 80 := by
  have hd : Disjoint five I := disjoint_of_coprime_natCard (by
    rw [five, Nat.card_zpowers, rotation_order, I_card]
    decide)
  let f : five × I → (first ⊓ fiveNormalizer : Subgroup (Model 0)) :=
    fun a => ⟨a.1*a.2, first_inf_normalizer.symm ▸ mul_mem_sup a.1.property a.2.property⟩
  have hf : Function.Bijective f := by
    constructor
    · intro a b h
      exact mul_injective_of_disjoint hd (congrArg Subtype.val h)
    · intro g
      have hg := g.property
      change (g : Model 0) ∈ ((first ⊓ fiveNormalizer : Subgroup (Model 0)) : Set (Model 0)) at hg
      rw [first_normalizer_product] at hg
      obtain ⟨a,ha,b,hb,he⟩ := hg
      exact ⟨(⟨a,ha⟩,⟨b,hb⟩),Subtype.ext he⟩
  have hc := Nat.card_congr (Equiv.ofBijective f hf)
  rw [Nat.card_prod, five, Nat.card_zpowers, rotation_order, I_card] at hc
  exact hc.symm

end Tits.ExceptionalParabolics.FullRee.LongRootPaths.FiveNormalizer
