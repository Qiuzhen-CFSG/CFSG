module

public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.M22Identification.OrderRecognition.LocalAnalysis.InvolutionNormalizers.FAction.Coordinates

/-!
# Transitivity of the F-automizer

The local group has eight images of d. Its exact order-eight stabilizer of z,
together with the lower bound eight for the stabilizer of d, forces their
orbits to meet: disjoint orbits would contain at least sixteen nonidentity
points in an elementary sixteen.

Once z and d are fused, all eight points outside the coordinate hyperplane
lie in that orbit. Any omitted nonidentity point belongs to a local orbit
containing a pair with product z. An automorphism taking z to d preserves
the omitted set, so the two images still lie in the hyperplane, whereas
their product is d. This contradiction gives transitivity, and orbit–stabilizer
gives order 120. No classification of linear subgroups is used here, and
this result does not identify the order-120 group with S5.

Source: Z. Janko, *A characterization of the Mathieu simple groups, I*,
J. Algebra 9 (1968), Section 2, proof of Lemma 2, pp.4–5.
-/

open Subgroup
namespace Theory.GroupTheory.HeldM22A10.M22Identification.CaseII.FAction
local instance : Finite modelF := Nat.finite_of_card_ne_zero (modelF_card ▸ (by decide))
local instance : Finite (MulAut modelF) := Finite.of_injective
  (fun a : MulAut modelF => (a : modelF → modelF)) DFunLike.coe_injective

variable (H : Subgroup (MulAut modelF))

public theorem pointZ_ne_one : pointZ ≠ 1 := by
  rw [← word_one, ← word_zero]
  exact fun h => (by decide : (1 : Fin 16) ≠ 0) (word_injective h)

public theorem pointD_ne_one : pointD ≠ 1 := by
  rw [← word_eight, ← word_zero]
  exact fun h => (by decide : (8 : Fin 16) ≠ 0) (word_injective h)

private theorem orbit_nonidentity (x : modelF) (hx : x ≠ 1) :
    MulAction.orbit H x ⊆ ({1} : Set modelF)ᶜ := by
  intro y hy h1
  obtain ⟨g, rfl⟩ := MulAction.mem_orbit_iff.mp hy
  apply hx
  exact (g : MulAut modelF).injective (h1.trans (map_one _).symm)

private theorem nonidentity_card : (({1} : Set modelF)ᶜ).ncard = 15 := by
  rw [Set.ncard_compl, Set.ncard_singleton, modelF_card]

public theorem orbit_card (h : FiniteSetup H) : Nat.card H =
    8 * (MulAction.orbit H pointZ).ncard := by
  have hs : MulAction.stabilizer H pointZ = localAutomizer.subgroupOf H := by
    ext g
    exact h.stabilizer_z g g.property
  have hc : Nat.card (MulAction.stabilizer H pointZ) = 8 := by
    rw [hs, Nat.card_congr (subgroupOfEquivOfLe h.local_le).toEquiv, localAutomizer_card]
  have hh := (MulAction.stabilizer H pointZ).card_mul_index
  rw [hc, MulAction.index_stabilizer] at hh
  exact hh.symm

private theorem orbit_card_le : (MulAction.orbit H pointZ).ncard ≤ 15 := by
  simpa only [nonidentity_card] using Set.ncard_le_ncard (orbit_nonidentity H pointZ pointZ_ne_one)

private theorem local_orbit_mem (hle : localAutomizer ≤ H) (i : Fin 16) :
    word i ∈ MulAction.orbit H (word (representative i)) := by
  obtain ⟨t, ht⟩ := local_orbit_witness i
  exact ⟨⟨localAction t, hle (localAction_mem t)⟩, ht⟩

private theorem orbit_d_card_ge (hle : localAutomizer ≤ H) :
    8 ≤ (MulAction.orbit H pointD).ncard := by
  let f : Fin 8 → MulAction.orbit H pointD := fun i =>
    ⟨word ⟨8 + i.val, by omega⟩, by
      have h := local_orbit_mem H hle ⟨8 + i.val, by omega⟩
      have hrall : ∀ j : Fin 8, representative ⟨8 + j.val, by omega⟩ = 8 := by
        decide +kernel
      have hr := hrall i
      rwa [hr, word_eight] at h⟩
  have hf : Function.Injective f := by
    intro i j hij
    have he := word_injective (congrArg Subtype.val hij)
    have := congrArg Fin.val he
    exact Fin.ext (by simpa using this)
  simpa only [Nat.card_fin, Nat.card_coe_set_eq] using Nat.card_le_card_of_injective f hf

private theorem stabilizer_d_card_ge (h : FiniteSetup H) :
    8 ≤ Nat.card (MulAction.stabilizer H pointD) := by
  have he : MulAction.stabilizer H pointD =
      (H ⊓ MulAction.stabilizer (MulAut modelF) pointD).subgroupOf H := by
    ext g
    change (g : MulAut modelF) pointD = pointD ↔
      (g : MulAut modelF) ∈ H ∧ (g : MulAut modelF) pointD = pointD
    simp only [g.property, true_and]
  rw [he, Nat.card_congr (subgroupOfEquivOfLe inf_le_left).toEquiv]
  exact h.stabilizer_d

public theorem pointD_mem_orbit (h : FiniteSetup H) : pointD ∈ MulAction.orbit H pointZ := by
  have hd := orbit_d_card_ge H h.local_le
  have hs := stabilizer_d_card_ge H h
  have hc := (MulAction.stabilizer H pointD).card_mul_index
  rw [MulAction.index_stabilizer, orbit_card H h] at hc
  have hz : 8 ≤ (MulAction.orbit H pointZ).ncard := by nlinarith
  by_contra hnot
  have hdis : Disjoint (MulAction.orbit H pointZ) (MulAction.orbit H pointD) := by
    apply Set.disjoint_left.mpr
    intro x hxZ hxD
    have he := (MulAction.orbit_eq_iff.mpr hxZ).symm.trans (MulAction.orbit_eq_iff.mpr hxD)
    exact hnot (he.symm ▸ MulAction.mem_orbit_self pointD)
  have hb : (MulAction.orbit H pointZ ∪ MulAction.orbit H pointD).ncard ≤ 15 := by
    apply (Set.ncard_le_ncard (Set.union_subset
      (orbit_nonidentity H pointZ pointZ_ne_one)
      (orbit_nonidentity H pointD pointD_ne_one))).trans_eq nonidentity_card
  rw [Set.ncard_union_eq hdis] at hb
  omega


private theorem orbit_word_iff (hle : localAutomizer ≤ H) (i : Fin 16) :
    word i ∈ MulAction.orbit H pointZ ↔
      word (representative i) ∈ MulAction.orbit H pointZ := by
  calc
    _ ↔ pointZ ∈ MulAction.orbit H (word i) := MulAction.mem_orbit_symm
    _ ↔ pointZ ∈ MulAction.orbit H (word (representative i)) := by
      rw [MulAction.orbit_eq_iff.mpr (local_orbit_mem H hle i)]
    _ ↔ _ := MulAction.mem_orbit_symm

private theorem outside_orbit_low (hle : localAutomizer ≤ H)
    (hd : pointD ∈ MulAction.orbit H pointZ) (i : Fin 16)
    (hi : word i ∉ MulAction.orbit H pointZ) : i.val < 8 := by
  by_contra hnot
  have hr : representative i = 8 := by
    simp only [representative]
    split_ifs <;> omega
  apply hi
  apply (orbit_word_iff H hle i).mpr
  rwa [hr, word_eight]

private theorem representative_pair : ∀ i : Fin 16, 2 ≤ i.val → i.val < 8 →
    representative (i ^^^ 1) = representative i := by decide +kernel

private theorem xor_pair : ∀ i : Fin 16, i ^^^ (i ^^^ 1) = 1 := by decide +kernel

private theorem xor_low : ∀ i j : Fin 16, i.val < 8 → j.val < 8 →
    i ^^^ j ≠ 8 := by decide +kernel

/-- Moving z to d forces transitivity: any missing local orbit contains a
pair with product z, whereas all missing points lie in the hyperplane below d. -/
public theorem transitive_of_pointD_mem (hle : localAutomizer ≤ H)
    (hd : pointD ∈ MulAction.orbit H pointZ) :
    ∀ x : modelF, x ≠ 1 → x ∈ MulAction.orbit H pointZ := by
  intro x hx
  obtain ⟨i, rfl⟩ := word_surjective x
  by_contra hi
  have hilo : i.val < 8 := outside_orbit_low H hle hd i hi
  have hizi : 2 ≤ i.val := by
    have hi0 : i ≠ 0 := fun he => hx (he ▸ word_zero)
    have hi1 : i ≠ 1 := by
      intro he
      apply hi
      rw [he, word_one]
      exact MulAction.mem_orbit_self _
    omega
  have hpair : word (i ^^^ 1) ∉ MulAction.orbit H pointZ := by
    rw [orbit_word_iff H hle (i ^^^ 1), representative_pair i hizi hilo,
      ← orbit_word_iff H hle i]
    exact hi
  obtain ⟨f, hf⟩ := MulAction.mem_orbit_iff.mp hd
  have hout (y : modelF) (hy : y ∉ MulAction.orbit H pointZ) :
      f • y ∉ MulAction.orbit H pointZ := by
    intro hh
    apply hy
    simpa only [inv_smul_smul] using MulAction.mem_orbit_of_mem_orbit f⁻¹ hh
  obtain ⟨j, hj⟩ := word_surjective (f • word i)
  obtain ⟨l, hl⟩ := word_surjective (f • word (i ^^^ 1))
  have hjlo : j.val < 8 := outside_orbit_low H hle hd j (hj.symm ▸ hout _ hi)
  have hllo : l.val < 8 := outside_orbit_low H hle hd l (hl.symm ▸ hout _ hpair)
  have hprod : word j * word l = pointD := by
    rw [hj, hl]
    change (f : MulAut modelF) (word i) * (f : MulAut modelF) (word (i ^^^ 1)) = _
    rw [← map_mul, ← word_xor, xor_pair, word_one]
    exact hf
  rw [← word_xor, ← word_eight] at hprod
  exact xor_low j l hjlo hllo (word_injective hprod)

/-- The finite stabilizer constraints give one orbit of length fifteen
and an automizer of order 120. -/
public theorem finite_orbits (h : FiniteSetup H) : Nat.card H = 120 ∧
    ∀ x y : modelF, x ≠ 1 → y ≠ 1 → ∃ a : H, (a : MulAut modelF) x = y := by
  have htrans := transitive_of_pointD_mem H h.local_le (pointD_mem_orbit H h)
  have horbit : MulAction.orbit H pointZ = ({1} : Set modelF)ᶜ :=
    Set.Subset.antisymm (orbit_nonidentity H pointZ pointZ_ne_one) (fun _ hx => htrans _ hx)
  refine ⟨?_, ?_⟩
  · rw [orbit_card H h, horbit, nonidentity_card]
  · intro x y hx hy
    obtain ⟨a, ha⟩ := MulAction.mem_orbit_iff.mp (htrans x hx)
    obtain ⟨b, hb⟩ := MulAction.mem_orbit_iff.mp (htrans y hy)
    refine ⟨b * a⁻¹, ?_⟩
    change (b * a⁻¹) • x = y
    rw [← ha, mul_smul, inv_smul_smul, hb]

end Theory.GroupTheory.HeldM22A10.M22Identification.CaseII.FAction
