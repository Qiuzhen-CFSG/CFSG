module
public import Theory.SpecificGroups.SymmetricEight.A6ShadowTwoLocals.TreeWreathModel
public import Theory.GroupTheory.SylowNormalIntersection
public import Theory.GroupTheory.CentralizerSmallKernelTransport
public import Mathlib.GroupTheory.SpecificGroups.Alternating
public import Mathlib.GroupTheory.Perm.Centralizer
public import Mathlib.Tactic

/-!
# The even pair stabilizer from a Sylow-central actor in A₈

The standard binary-tree Sylow has just one nonidentity central element:
the product of its four pair interchanges. A bounded certificate uses only
its 128 established normal forms and six even generators. Sylow conjugacy
therefore places every nontrivial Sylow-central actor at this element.
Its centralizer is the even pair stabilizer, of order 192. A subgroup of
that centralizer which properly contains a Sylow subgroup of order 64 is
consequently the whole centralizer.

The actual application is the image of L₁*T* in K*V* in the A₈ branch of
Aschbacher–Smith 13.5.21, printed p.924. It retains the original actor of
order two, rather than replacing the module by an unmarked abstract plane.
-/

@[expose] public section
open Subgroup Equiv.Perm
namespace Theory.SpecificGroups.SymmetricEight.CentralPair
open A6ShadowTwoLocals
abbrev A8 := alternatingGroup (Fin 8)

def mate : S8 :=
  Equiv.swap 0 1 * Equiv.swap 2 3 * Equiv.swap 4 5 * Equiv.swap 6 7

theorem mate_even : mate ∈ A8 := by
  change sign mate = 1
  decide +kernel

def z : A8 := ⟨mate, mate_even⟩

private theorem mate_ne : ∀ i : Fin 8, mate i ≠ i := by decide +kernel
private theorem same_pair : ∀ i j : Fin 8,
    j.val / 2 = i.val / 2 ↔ j = i ∨ j = mate i := by decide +kernel

theorem centralizer_mate : centralizer ({mate} : Set S8) = pairStabilizer := by
  ext g
  rw [mem_centralizer_singleton_iff, mem_pairStabilizer]
  constructor
  · intro h i j
    have hc (i : Fin 8) : g (mate i) = mate (g i) := congrArg (fun p : S8 => p i) h
    rw [same_pair (g j) (g i), same_pair j i, ← hc j]
    simp only [g.injective.eq_iff]
  · intro h
    apply Equiv.ext
    intro i
    change g (mate i) = mate (g i)
    have hh := (h (mate i) i).mpr ((same_pair i (mate i)).mpr (Or.inr rfl))
    exact ((same_pair (g i) (g (mate i))).mp hh).resolve_left
      (fun he => mate_ne i (g.injective he))

theorem centralizer_z : centralizer ({z} : Set A8) = pairStabilizer.subgroupOf A8 := by
  ext g
  change g ∈ centralizer ({z} : Set A8) ↔ g.val ∈ pairStabilizer
  rw [← centralizer_mate, mem_centralizer_singleton_iff, mem_centralizer_singleton_iff]
  exact Subtype.ext_iff

noncomputable def evenTreeSylow : Sylow 2 A8 :=
  (treeSylow.exists_subgroupOf_eq_of_normal A8).choose

theorem evenTreeSylow_coe :
    (evenTreeSylow : Subgroup A8) = treeGroup.subgroupOf A8 :=
  (treeSylow.exists_subgroupOf_eq_of_normal A8).choose_spec

private def evenGenerator : Fin 6 → S8 :=
  ![treeGenerator 0 * treeGenerator 1,
    treeGenerator 0 * treeGenerator 2,
    treeGenerator 0 * treeGenerator 3,
    treeGenerator 4, treeGenerator 5, treeGenerator 6]

private theorem evenGenerator_even : ∀ j, sign (evenGenerator j) = 1 := by
  decide +kernel

private theorem evenGenerator_mem (j : Fin 6) : evenGenerator j ∈ treeGroup := by
  fin_cases j
  · exact treeGroup.mul_mem (treeGenerator_mem 0) (treeGenerator_mem 1)
  · exact treeGroup.mul_mem (treeGenerator_mem 0) (treeGenerator_mem 2)
  · exact treeGroup.mul_mem (treeGenerator_mem 0) (treeGenerator_mem 3)
  · exact treeGenerator_mem 4
  · exact treeGenerator_mem 5
  · exact treeGenerator_mem 6

private theorem center_certificate : ∀ i : Fin 128,
    (∀ j : Fin 6, treeWord i * evenGenerator j = evenGenerator j * treeWord i) →
    treeWord i = 1 ∨ treeWord i = mate := by
  decide +kernel

/-- The nontrivial center of the literal even binary-tree Sylow. -/
theorem evenTree_center (v : A8) (hv : v ∈ (evenTreeSylow : Subgroup A8))
    (hc : ∀ t ∈ (evenTreeSylow : Subgroup A8), v * t = t * v) : v = 1 ∨ v = z := by
  have ht : v.val ∈ treeGroup := by
    rw [evenTreeSylow_coe] at hv
    exact hv
  obtain ⟨i, hi⟩ := (mem_treeGroup v.val).mp ht
  have hh (j : Fin 6) : treeWord i * evenGenerator j = evenGenerator j * treeWord i := by
    let t : A8 := ⟨evenGenerator j, mem_alternatingGroup.mpr (evenGenerator_even j)⟩
    have hm : t ∈ (evenTreeSylow : Subgroup A8) := by
      rw [evenTreeSylow_coe]
      exact evenGenerator_mem j
    simpa only [hi, Subgroup.coe_mul, t] using congrArg Subtype.val (hc t hm)
  rcases center_certificate i hh with he | he
  · exact Or.inl (Subtype.ext (hi.symm.trans he))
  · exact Or.inr (Subtype.ext (hi.symm.trans he))

theorem sylow_card (S : Sylow 2 A8) : Nat.card S = 64 := by
  rw [Sylow.card_eq_multiplicity, nat_card_alternatingGroup, Nat.card_fin]
  norm_num [Nat.factorial]
  rw [show 20160 = 2 ^ 6 * 315 by norm_num,
    Nat.factorization_mul (by norm_num) (by norm_num), Nat.factorization_pow]
  norm_num [Nat.prime_two.factorization,
    Nat.factorization_eq_zero_of_not_dvd (by decide : ¬ 2 ∣ 315)]

private def evenCentralizerEquiv : centralizer ({z} : Set A8) ≃*
    (sign.comp (centralizer ({mate} : Set S8)).subtype).ker where
  toFun y := ⟨⟨y.1.1, mem_centralizer_singleton_iff.mpr
    (congrArg Subtype.val (mem_centralizer_singleton_iff.mp y.2))⟩,
    mem_alternatingGroup.mp y.1.2⟩
  invFun y := ⟨⟨y.1.1, mem_alternatingGroup.mpr y.2⟩,
    mem_centralizer_singleton_iff.mpr (Subtype.ext (mem_centralizer_singleton_iff.mp y.1.2))⟩
  left_inv _ := by apply Subtype.ext; rfl
  right_inv _ := by apply Subtype.ext; apply Subtype.ext; rfl
  map_mul' _ _ := by apply Subtype.ext; apply Subtype.ext; rfl

theorem centralizer_z_card : Nat.card (centralizer ({z} : Set A8)) = 192 := by
  let C := centralizer ({mate} : Set S8)
  let f : C →* ℤˣ := sign.comp C.subtype
  let t : C := ⟨Equiv.swap (0 : Fin 8) 1,
    mem_centralizer_singleton_iff.mpr (by decide +kernel)⟩
  have hft : f t = -1 := sign_swap (show (0 : Fin 8) ≠ 1 by decide)
  have hrange : f.range = ⊤ := by
    ext a
    simp only [Subgroup.mem_top, iff_true]
    rcases Int.units_eq_one_or a with rfl | rfl
    · exact ⟨1, map_one f⟩
    · exact ⟨t, hft⟩
  have hc := f.ker.card_mul_index
  have hint : Nat.card ℤˣ = 2 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_units_int]
  rw [Subgroup.index_ker, hrange, Subgroup.card_top, hint] at hc
  have he : Nat.card (centralizer ({z} : Set A8)) = Nat.card f.ker :=
    Nat.card_congr evenCentralizerEquiv.toEquiv
  have hmate : mate.cycleType = {2,2,2,2} := by decide +kernel
  have hC : Nat.card C = 384 := by
    rw [show C = centralizer ({mate} : Set S8) from rfl, nat_card_centralizer, hmate]
    norm_num [Nat.factorial]
  rw [← he, hC] at hc
  omega

/-- Sylow conjugacy marks every nontrivial central actor with the pair flip. -/
theorem central_in_sylow_conjugate (S : Sylow 2 A8) (v : A8)
    (hv : v ∈ (S : Subgroup A8)) (hv1 : v ≠ 1)
    (hc : (S : Subgroup A8) ≤ centralizer ({v} : Set A8)) :
    ∃ g : A8, (MulAut.conj g) z = v := by
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq A8 evenTreeSylow S
  have he : (evenTreeSylow : Subgroup A8).map (MulAut.conj g).toMonoidHom = S := by
    change ((g • evenTreeSylow : Sylow 2 A8) : Subgroup A8) = _
    rw [hg]
  let w := (MulAut.conj g).symm v
  have hw : w ∈ (evenTreeSylow : Subgroup A8) := by
    have hh : v ∈ (evenTreeSylow : Subgroup A8).map
        (MulAut.conj g).toMonoidHom := he.symm ▸ hv
    exact (mem_map_equiv).mp hh
  have hwc : ∀ t ∈ (evenTreeSylow : Subgroup A8), w * t = t * w := by
    intro t ht
    apply (MulAut.conj g).injective
    simp only [map_mul, w, MulEquiv.apply_symm_apply]
    exact (mem_centralizer_singleton_iff.mp (hc (he ▸ mem_map_of_mem _ ht))).symm
  rcases evenTree_center w hw hwc with hw1 | hwz
  · apply (hv1 ?_).elim
    have hh := congrArg (MulAut.conj g) hw1
    simpa only [w, MulEquiv.apply_symm_apply, map_one] using hh
  · exact ⟨g, by rw [← hwz]; exact (MulAut.conj g).apply_symm_apply v⟩

/-- A nontrivial odd extension of the Sylow inside the actor centralizer
is precisely a conjugate of the even pair stabilizer. -/
theorem pair_marking (S : Sylow 2 A8) (J : Subgroup A8)
    (hSJ : (S : Subgroup A8) ≤ J) (hne : J ≠ (S : Subgroup A8))
    (v : A8) (hv : v ∈ (S : Subgroup A8)) (hv1 : v ≠ 1)
    (hJ : J ≤ centralizer ({v} : Set A8)) :
    ∃ g : A8, J = (pairStabilizer.subgroupOf A8).map (MulAut.conj g).toMonoidHom := by
  obtain ⟨g, hg⟩ := central_in_sylow_conjugate S v hv hv1 (hSJ.trans hJ)
  have he : (centralizer ({z} : Set A8)).map (MulAut.conj g).toMonoidHom =
      centralizer ({v} : Set A8) := by
    rw [Theory.GroupTheory.CentralizerSmallKernelTransport.map_centralizer, hg]
  have hc : Nat.card (centralizer ({v} : Set A8)) = 192 := by
    rw [← he, card_map_of_injective (MulAut.conj g).injective, centralizer_z_card]
  have hi : (S : Subgroup A8).relIndex (centralizer ({v} : Set A8)) = 3 := by
    have hh := relIndex_mul_relIndex (⊥ : Subgroup A8) (S : Subgroup A8)
      (centralizer ({v} : Set A8)) bot_le (hSJ.trans hJ)
    simp only [relIndex_bot_left] at hh
    rw [sylow_card, hc] at hh
    omega
  have hh := relIndex_mul_relIndex (S : Subgroup A8) J
    (centralizer ({v} : Set A8)) hSJ hJ
  rw [hi] at hh
  have hd : J.relIndex (centralizer ({v} : Set A8)) ∣ 3 :=
    ⟨(S : Subgroup A8).relIndex J, by simpa only [mul_comm] using hh.symm⟩
  have hjc : J = centralizer ({v} : Set A8) := by
    rcases Nat.prime_three.eq_one_or_self_of_dvd _ hd with h1 | h3
    · exact le_antisymm hJ (relIndex_eq_one.mp h1)
    · rw [h3] at hh
      have hs1 : (S : Subgroup A8).relIndex J = 1 := by omega
      exact (hne (le_antisymm (relIndex_eq_one.mp hs1) hSJ)).elim
  exact ⟨g, hjc.trans (by rw [← he, centralizer_z])⟩

end Theory.SpecificGroups.SymmetricEight.CentralPair
