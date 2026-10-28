module

public import Theory.SpecificGroups.SymmetricSeven.LocalResidualRecognition.Coordinates
public import Theory.SpecificGroups.SymmetricSix.ResidualPairRecognition.Reduction
/-!
# Placement of index-three Sylow overgroups on seven letters

The orbit of the fixed letter has at most three points. The standard
Sylow subgroup acts transitively on `{2,3,4,5}`, so that orbit is contained
in `{0,1,6}`. If it is a singleton, the six-point parabolic theorem applies.
Otherwise its point stabilizer is the original Sylow subgroup. The kernel
on the triple is the dihedral group on the other four letters. Its unique
nonidentity central element is `(23)(45)`, so the overgroup preserves the
matching `{23,45}` and lies in the cubic overgroup.

Only calculations within the sixteen-element Sylow subgroup are enumerated;
no enumeration of seven-letter overgroups is used.
Source: Aschbacher–Smith, I.5 and the final proof of 15.3.1, printed p.1155.
-/

@[expose] public section

open Equiv Subgroup
open Theory.SpecificGroups.SymmetricSix
open Theory.SpecificGroups.SymmetricSeven.LocalResidualModels
namespace Theory.SpecificGroups.SymmetricSeven.LocalResidualRecognition
private theorem orbit_small (H : Subgroup S7) (_hB : standardTwo ≤ H)
    (hi : standardTwo.relIndex H = 3) : (MulAction.orbit H (6 : Fin 7)).ncard ≤ 3 := by
  have hle : standardTwo.subgroupOf H ≤ MulAction.stabilizer H (6 : Fin 7) := by
    intro x hx
    exact hx.1.1
  have hd := Subgroup.index_dvd_of_le hle
  change (MulAction.stabilizer H (6 : Fin 7)).index ∣ standardTwo.relIndex H at hd
  rw [hi, MulAction.index_stabilizer] at hd
  exact Nat.le_of_dvd (by decide) hd

private theorem four_transitive : ∀ i j : Fin 7,
    i ∈ ({2,3,4,5} : Finset (Fin 7)) → j ∈ ({2,3,4,5} : Finset (Fin 7)) →
    ∃ t : Fin 16, sylowWord t i = j := by decide +kernel

theorem orbit_subset_triple (H : Subgroup S7) (hB : standardTwo ≤ H)
    (hi : standardTwo.relIndex H = 3) (i : Fin 7) (hiO : i ∈ MulAction.orbit H (6 : Fin 7)) :
    i = 0 ∨ i = 1 ∨ i = 6 := by
  by_contra hn
  have hi4 : i ∈ ({2,3,4,5} : Finset (Fin 7)) := by
    fin_cases i <;> simp_all
  have hs : (↑({2,3,4,5} : Finset (Fin 7)) : Set (Fin 7)) ⊆ MulAction.orbit H (6 : Fin 7) := by
    intro j hj
    obtain ⟨t, ht⟩ := four_transitive i j hi4 hj
    obtain ⟨g, hg⟩ := hiO
    refine ⟨(⟨sylowWord t, hB (sylowWord_mem t)⟩ : H) * g, ?_⟩
    change sylowWord t (g.val 6) = j
    change g.val 6 = i at hg
    rw [hg, ht]
  have hcard := Set.ncard_le_ncard hs
  have hfour : (↑({2,3,4,5} : Finset (Fin 7)) : Set (Fin 7)).ncard = 4 := by simp
  rw [hfour] at hcard
  have hsmall := orbit_small H hB hi
  omega


theorem point_stabilizer_eq (H : Subgroup S7) (hB : standardTwo ≤ H)
    (hi : standardTwo.relIndex H = 3) (hn : ¬ H ≤ MulAction.stabilizer S7 (6 : Fin 7)) :
    H ⊓ MulAction.stabilizer S7 (6 : Fin 7) = standardTwo := by
  let K := H ⊓ MulAction.stabilizer S7 (6 : Fin 7)
  have hb : standardTwo ≤ K := fun x hx => ⟨hB hx, hx.1.1⟩
  have he := relIndex_mul_relIndex standardTwo K H hb (show K ≤ H from inf_le_left)
  rw [hi] at he
  have hd : standardTwo.relIndex K ∣ 3 := ⟨K.relIndex H, he.symm⟩
  rcases (Nat.dvd_prime (by decide : Nat.Prime 3)).mp hd with h1 | h3
  · exact le_antisymm (relIndex_eq_one.mp h1) hb
  · have hk : K.relIndex H = 1 := by rw [h3] at he; omega
    exact (hn ((relIndex_eq_one.mp hk).trans inf_le_right)).elim

theorem triple_mem_orbit (H : Subgroup S7) (hB : standardTwo ≤ H)
    (hi : standardTwo.relIndex H = 3) (hn : ¬ H ≤ MulAction.stabilizer S7 (6 : Fin 7)) :
    (0 : Fin 7) ∈ MulAction.orbit H (6 : Fin 7) ∧
    (1 : Fin 7) ∈ MulAction.orbit H (6 : Fin 7) := by
  classical
  obtain ⟨g, hgH, hg⟩ : ∃ g ∈ H, g 6 ≠ 6 := by
    by_contra h
    apply hn
    intro g hgH
    change g 6 = 6
    by_contra hg
    exact h ⟨g, hgH, hg⟩
  have ho : g 6 ∈ MulAction.orbit H (6 : Fin 7) := ⟨⟨g, hgH⟩, rfl⟩
  have ht : swap (0 : Fin 7) 1 ∈ H := hB (by decide)
  have htrans (i : Fin 7) (hi : i ∈ MulAction.orbit H (6 : Fin 7)) :
      swap (0 : Fin 7) 1 i ∈ MulAction.orbit H (6 : Fin 7) :=
    MulAction.mem_orbit_of_mem_orbit (⟨swap 0 1, ht⟩ : H) hi
  rcases orbit_subset_triple H hB hi (g 6) ho with he | he | he
  · rw [he] at ho
    exact ⟨ho, by simpa using htrans 0 ho⟩
  · rw [he] at ho
    exact ⟨by simpa using htrans 1 ho, ho⟩
  · exact (hg he).elim


private def fourKernel : Subgroup S7 := standardTwo ⊓
  (MulAction.stabilizer S7 (0 : Fin 7) ⊓ MulAction.stabilizer S7 (1 : Fin 7))
private def centralDouble : S7 := swap 2 3 * swap 4 5

private theorem centralDouble_mem : centralDouble ∈ fourKernel := by
  change centralDouble ∈ standardTwo ∧ centralDouble 0 = 0 ∧ centralDouble 1 = 1
  decide

private theorem centralDouble_comm (k : S7) (hk : k ∈ standardTwo) :
    centralDouble * k = k * centralDouble := by
  obtain ⟨i, hi⟩ := sylowEquiv.surjective ⟨k, hk⟩
  have he : sylowWord i = k := congrArg Subtype.val hi
  rw [← he]
  exact (show ∀ i, centralDouble * sylowWord i = sylowWord i * centralDouble by decide +kernel) i

private theorem kernel_center (k : S7) (hk : k ∈ fourKernel)
    (hc : ∀ l ∈ fourKernel, k * l = l * k) : k = 1 ∨ k = centralDouble := by
  obtain ⟨i, hi⟩ := sylowEquiv.surjective ⟨k, hk.1⟩
  have he : sylowWord i = k := congrArg Subtype.val hi
  have htable : ∀ i : Fin 16, sylowWord i 0 = 0 → sylowWord i 1 = 1 →
      (∀ j : Fin 16, sylowWord j 0 = 0 → sylowWord j 1 = 1 →
        sylowWord i * sylowWord j = sylowWord j * sylowWord i) →
      sylowWord i = 1 ∨ sylowWord i = centralDouble := by decide +kernel
  rw [← he] at hk hc ⊢
  exact htable i hk.2.1 hk.2.2 (fun j hj0 hj1 => hc _ ⟨sylowWord_mem j, hj0, hj1⟩)

private theorem nonfixed_conjugates_centralDouble (H : Subgroup S7) (hB : standardTwo ≤ H)
    (hi : standardTwo.relIndex H = 3) (hn : ¬ H ≤ MulAction.stabilizer S7 (6 : Fin 7)) :
    ∀ g ∈ H, g * centralDouble * g⁻¹ = centralDouble := by
  have hpoint := point_stabilizer_eq H hB hi hn
  have htriple := triple_mem_orbit H hB hi hn
  have hpres (g : S7) (hg : g ∈ H) (i : Fin 7) (hi : i = 0 ∨ i = 1 ∨ i = 6) :
      g i = 0 ∨ g i = 1 ∨ g i = 6 := by
    have ho : i ∈ MulAction.orbit H (6 : Fin 7) := by
      rcases hi with rfl | rfl | rfl
      · exact htriple.1
      · exact htriple.2
      · exact MulAction.mem_orbit_self _
    exact orbit_subset_triple H hB ‹standardTwo.relIndex H = 3› _
      (MulAction.mem_orbit_of_mem_orbit (⟨g, hg⟩ : H) ho)
  have hconj (g : S7) (hg : g ∈ H) (k : S7) (hk : k ∈ fourKernel) :
      g * k * g⁻¹ ∈ fourKernel := by
    have hfix (i : Fin 7) (hi : i = 0 ∨ i = 1 ∨ i = 6) :
        (g * k * g⁻¹) i = i := by
      change g (k (g⁻¹ i)) = i
      have hkfix : k (g⁻¹ i) = g⁻¹ i := by
        rcases hpres g⁻¹ (H.inv_mem hg) i hi with he | he | he
        · rw [he]; exact hk.2.1
        · rw [he]; exact hk.2.2
        · rw [he]; exact hk.1.1.1
      rw [hkfix]
      exact g.apply_symm_apply i
    refine ⟨?_, hfix 0 (Or.inl rfl), hfix 1 (Or.inr (Or.inl rfl))⟩
    rw [← hpoint]
    exact ⟨H.mul_mem (H.mul_mem hg (hB hk.1)) (H.inv_mem hg),
      hfix 6 (Or.inr (Or.inr rfl))⟩
  intro g hg
  have hcz := hconj g hg centralDouble centralDouble_mem
  have hcc : ∀ k ∈ fourKernel,
      (g * centralDouble * g⁻¹) * k = k * (g * centralDouble * g⁻¹) := by
    intro k hk
    have hh := centralDouble_comm (g⁻¹ * k * g)
      (by simpa using (hconj g⁻¹ (H.inv_mem hg) k hk).1)
    have hh' := congrArg (fun x : S7 => g * x * g⁻¹) hh
    simpa only [mul_assoc, inv_mul_cancel_left, mul_inv_cancel_left,
      mul_inv_cancel, inv_mul_cancel, mul_one, one_mul] using hh'
  rcases kernel_center _ hcz hcc with he | he
  · have hh : centralDouble = 1 := (MulAut.conj g).injective (by simpa using he)
    exact (by decide : centralDouble ≠ 1) hh |>.elim
  · exact he

private theorem centralDouble_stabilizer (g : S7)
    (hg : g * centralDouble * g⁻¹ = centralDouble) : g ∈ cubicOvergroup := by
  have hmul : g * centralDouble = centralDouble * g := by
    have hh := congrArg (fun x : S7 => x * g) hg
    simpa only [mul_assoc, inv_mul_cancel, mul_one] using hh
  have h23 : g 3 = centralDouble (g 2) := congrArg (fun x : S7 => x 2) hmul
  have h45 : g 5 = centralDouble (g 4) := congrArg (fun x : S7 => x 4) hmul
  have hne23 : g 2 ≠ g 3 := g.injective.ne (by decide)
  have hne45 : g 4 ≠ g 5 := g.injective.ne (by decide)
  have hne24 : g 2 ≠ g 4 := g.injective.ne (by decide)
  have hne25 : g 2 ≠ g 5 := g.injective.ne (by decide)
  change ({{2,3},{4,5}} : Finset (Finset (Fin 7))).image (fun t => t.image g) = _
  simp only [Finset.image_insert, Finset.image_singleton]
  simp only [h23, h45] at hne23 hne45 hne25 ⊢
  generalize h2 : g 2 = a at *
  generalize h4 : g 4 = b at *
  fin_cases a <;> fin_cases b <;>
    simp_all [centralDouble, Perm.mul_apply, swap_apply_def, Finset.pair_comm]


theorem index_three_card (H : Subgroup S7) (hB : standardTwo ≤ H)
    (hi : standardTwo.relIndex H = 3) : Nat.card H = 48 := by
  have hc := (standardTwo.subgroupOf H).card_mul_index
  rw [Nat.card_congr (subgroupOfEquivOfLe hB).toEquiv, standardTwo_card] at hc
  change 16 * standardTwo.relIndex H = Nat.card H at hc
  rw [hi] at hc
  exact hc.symm

private theorem fixed_point_classification (H : Subgroup S7) (hB : standardTwo ≤ H)
    (hi : standardTwo.relIndex H = 3) (hf : H ≤ MulAction.stabilizer S7 (6 : Fin 7)) :
    H = duadOvergroup ∨ H = synthemeOvergroup := by
  have hrange : H ≤ liftSix.range := fun g hg => (mem_liftSix_range g).mpr (hf hg)
  have hmap : (H.comap liftSix).map liftSix = H := map_comap_eq_self hrange
  have hb : borel ≤ H.comap liftSix := by
    intro g hg
    exact hB (by rw [standardTwo_eq_map]; exact mem_map_of_mem liftSix hg)
  have hi6 : borel.relIndex (H.comap liftSix) = 3 := by
    have hh := relIndex_map_map_of_injective borel (H.comap liftSix) liftSix_injective
    rw [← standardTwo_eq_map, hmap, hi] at hh
    exact hh.symm
  rcases ResidualPairRecognition.index_three_over_borel (H.comap liftSix) hb hi6 with hd | hs
  · left
    rw [← hmap, hd, duadOvergroup_eq_map]
  · right
    rw [← hmap, hs, synthemeOvergroup_eq_map]

theorem index_three_placement (H : Subgroup S7) (hB : standardTwo ≤ H)
    (hi : standardTwo.relIndex H = 3) :
    H = duadOvergroup ∨ H = synthemeOvergroup ∨ H ≤ cubicOvergroup := by
  by_cases hf : H ≤ MulAction.stabilizer S7 (6 : Fin 7)
  · rcases fixed_point_classification H hB hi hf with hd | hs
    · exact Or.inl hd
    · exact Or.inr (Or.inl hs)
  · exact Or.inr (Or.inr (fun g hg => centralDouble_stabilizer g
      (nonfixed_conjugates_centralDouble H hB hi hf g hg)))

end Theory.SpecificGroups.SymmetricSeven.LocalResidualRecognition
