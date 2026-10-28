module

public import Mathlib.Algebra.Group.ConjFinite
public import Mathlib.GroupTheory.Perm.Cycle.Type
public import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple
public import Theory.GroupTheory.PCoreSurjective

/-!
# The iterated two-three core of a transposition centralizer in S₇

The action on the five fixed letters and the two moved letters identifies the
centralizer with S₅ × S₂. Projection onto S₅ has two-group kernel. Since every
nontrivial normal subgroup of S₅ contains A₅, its two-core and three-core vanish.
Thus the centralizer's two-core is the transposition factor, and the three-core
of the quotient by that two-core vanishes as well.

The final calculation uses the preimage convention for O₂,₃, not a join of
prime cores. It transports both intrinsic cores through a supplied permutation
marking and returns their images in the original ambient group.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), the A₇ exclusion
in 13.5.21, printed p.924 (PDF p.941).
-/

@[expose] public section
open Equiv Equiv.Perm Subgroup
namespace AlternatingSeven.TranspositionCore
private abbrev S7 := Perm (Fin 7)
private abbrev S5 := Perm (Fin 5)
private abbrev S2 := Perm (Fin 2)

private theorem five_core (p : ℕ) [Fact p.Prime] (hp : p = 2 ∨ p = 3) : pCore p S5 = ⊥ := by
  by_contra h
  have hn : Nontrivial (pCore p S5) := (Subgroup.nontrivial_iff_ne_bot _).mpr h
  have hle := alternatingGroup_le_of_normal (α := Fin 5) (by simp) hn
  obtain ⟨n,hn⟩ := ((pCore_isPGroup (p := p) (G := S5)).to_le hle).exists_card_dvd_pow
  have hc : Nat.card (alternatingGroup (Fin 5)) = 60 := by
    rw [nat_card_alternatingGroup]
    norm_num [Nat.factorial]
  rw [hc] at hn
  have hd : 5 ∣ p := Nat.prime_five.dvd_of_dvd_pow ((by decide : 5 ∣ 60).trans hn)
  rcases hp with rfl | rfl <;> norm_num at hd

private def blocks : S5 × S2 →* S7 :=
  (permCongrHom (finSumFinEquiv : Fin 5 ⊕ Fin 2 ≃ Fin 7)).toMonoidHom.comp
    (sumCongrHom (Fin 5) (Fin 2))
private theorem blocks_injective : Function.Injective blocks :=
  (permCongrHom finSumFinEquiv).injective.comp sumCongrHom_injective

private theorem blocks_fixed : ∀ g : S5 × S2,
    swap (5 : Fin 7) 6 * blocks g = blocks g * swap 5 6 := by
  decide +kernel

private abbrev C := centralizer ({swap (5 : Fin 7) 6} : Set S7)
private def blocksToCentralizer : S5 × S2 →* C :=
  blocks.codRestrict C (fun g => mem_centralizer_singleton_iff.mpr (blocks_fixed g).symm)
private theorem centralizer_card : Nat.card C = 240 := by
  rw [nat_card_centralizer]
  have hs : (swap (5 : Fin 7) 6).cycleType = {2} :=
    isSwap_iff_cycleType.mp (swap_isSwap_iff.mpr (by decide))
  rw [hs]
  norm_num [Nat.factorial]

private noncomputable def standardEquiv : C ≃* S5 × S2 :=
  (MulEquiv.ofBijective blocksToCentralizer
    ((Nat.bijective_iff_injective_and_card _).mpr ⟨
      fun _ _ h => blocks_injective (congrArg Subtype.val h), by
        rw [centralizer_card]
        norm_num [Nat.card_prod, Nat.card_eq_fintype_card, Fintype.card_perm, Nat.factorial]⟩)).symm

private noncomputable def projection : C →* S5 := (MonoidHom.fst S5 S2).comp standardEquiv.toMonoidHom
private theorem projection_surjective : Function.Surjective projection := by
  intro x
  exact ⟨standardEquiv.symm (x,1), congrArg Prod.fst (standardEquiv.apply_symm_apply (x,1))⟩
private theorem projection_kernel_two : IsPGroup 2 projection.ker := by
  have hp : IsPGroup 2 S2 := IsPGroup.of_card (n := 1) (by
    norm_num [Nat.card_eq_fintype_card, Fintype.card_perm, Nat.factorial])
  let f : projection.ker →* S2 :=
    ((MonoidHom.snd S5 S2).comp standardEquiv.toMonoidHom).comp projection.ker.subtype
  apply hp.of_injective f
  intro x y hh
  apply Subtype.ext
  apply standardEquiv.injective
  apply Prod.ext
  · exact (MonoidHom.mem_ker.mp x.property).trans (MonoidHom.mem_ker.mp y.property).symm
  · exact hh
private theorem standard_core : pCore 2 C = projection.ker := by
  have hh := projection.comap_pCore_of_ker_isPGroup projection_surjective projection_kernel_two
  rw [five_core 2 (Or.inl rfl)] at hh
  exact hh.symm

private theorem standard_quotient_three : pCore 3 (C ⧸ pCore 2 C) = ⊥ := by
  let e : (C ⧸ pCore 2 C) ≃* S5 :=
    (QuotientGroup.quotientMulEquivOfEq standard_core).trans
      (QuotientGroup.quotientKerEquivOfSurjective projection projection_surjective)
  have hh := pCore_map_iso 3 e.symm
  rw [five_core 3 (Or.inr rfl), Subgroup.map_bot] at hh
  exact hh.symm


private theorem standard_core_card : Nat.card (pCore 2 C) = 2 := by
  have hi : projection.ker.index = 120 := by
    rw [index_ker, MonoidHom.range_eq_top.mpr projection_surjective,
      Nat.card_congr topEquiv.toEquiv]
    norm_num [Nat.card_eq_fintype_card, Fintype.card_perm, Nat.factorial]
  have hc := projection.ker.card_mul_index
  rw [hi, centralizer_card] at hc
  rw [standard_core]
  omega

private theorem standard_core_image : (pCore 2 C).map C.subtype = zpowers (swap (5 : Fin 7) 6) := by
  have ht : blocksToCentralizer (1, swap 0 1) ∈ pCore 2 C := by
    rw [standard_core, MonoidHom.mem_ker]
    change (standardEquiv (standardEquiv.symm (1, swap 0 1))).1 = 1
    rw [standardEquiv.apply_symm_apply]
  have he : (blocksToCentralizer (1, swap 0 1) : S7) = swap 5 6 := by decide +kernel
  have hle : zpowers (swap (5 : Fin 7) 6) ≤ (pCore 2 C).map C.subtype := by
    apply zpowers_le.mpr
    rw [← he]
    exact mem_map_of_mem _ ht
  apply (eq_of_le_of_card_ge hle ?_).symm
  rw [card_map_of_injective C.subtype_injective, standard_core_card, Nat.card_zpowers]
  have ho : orderOf (swap (5 : Fin 7) 6) = 2 := orderOf_eq_prime (by decide +kernel) (by decide +kernel)
  rw [ho]

private theorem centralizer_map {A B : Type*} [Group A] [Group B] (e : A ≃* B) (a : A) :
    (centralizer ({a} : Set A)).map e.toMonoidHom = centralizer ({e a} : Set B) := by
  apply le_antisymm
  · simpa only [Set.image_singleton, MulEquiv.coe_toMonoidHom] using map_centralizer_le_centralizer_image ({a} : Set A) e.toMonoidHom
  · intro b hb
    refine ⟨e.symm b, ?_, e.apply_symm_apply b⟩
    apply mem_centralizer_singleton_iff.mpr
    apply e.injective
    simpa only [map_mul, e.apply_symm_apply] using mem_centralizer_singleton_iff.mp hb

private noncomputable def centralizerEquiv {A B : Type*} [Group A] [Group B]
    (e : A ≃* B) (a : A) : centralizer ({a} : Set A) ≃* centralizer ({e a} : Set B) :=
  (e.subgroupMap _).trans (MulEquiv.subgroupCongr (centralizer_map e a))

/-- The centralizer of a transposition is the product of its two-letter and five-letter actions. -/
theorem transposition_centralizer_equiv {E : Type*} [Group E] (e : E ≃* Perm (Fin 7))
    (v : E) (hv : (e v).IsSwap) :
    Nonempty (centralizer ({v} : Set E) ≃* (Perm (Fin 5) × Perm (Fin 2))) := by
  have hc : IsConj (e v) (swap (5 : Fin 7) 6) := isConj_of_cycleType_eq
    ((isSwap_iff_cycleType.mp hv).trans
      (isSwap_iff_cycleType.mp (swap_isSwap_iff.mpr (by decide))).symm)
  obtain ⟨p,hp⟩ := isConj_iff.mp hc
  let f := e.trans (MulAut.conj p)
  have hf : f v = swap 5 6 := hp
  exact ⟨((centralizerEquiv f v).trans
    (MulEquiv.subgroupCongr (congrArg (fun x => centralizer ({x} : Set S7)) hf))).trans standardEquiv⟩

/-- Both stages of the transposition-centralizer calculation retain the original ambient maps. -/
theorem transposition_cores {E : Type*} [Group E] [Finite E] (e : E ≃* Perm (Fin 7))
    (v : E) (hv : (e v).IsSwap) :
    let C := centralizer ({v} : Set E)
    (pCore 2 C).map C.subtype = zpowers v ∧ pCore 3 (C ⧸ pCore 2 C) = ⊥ := by
  have hc : IsConj (e v) (swap (5 : Fin 7) 6) := isConj_of_cycleType_eq
    ((isSwap_iff_cycleType.mp hv).trans
      (isSwap_iff_cycleType.mp (swap_isSwap_iff.mpr (by decide))).symm)
  obtain ⟨p,hp⟩ := isConj_iff.mp hc
  let f := e.trans (MulAut.conj p)
  have hf : f v = swap 5 6 := hp
  let D := centralizer ({v} : Set E)
  let c : D ≃* C := (centralizerEquiv f v).trans
    (MulEquiv.subgroupCongr (congrArg (fun x => centralizer ({x} : Set S7)) hf))
  constructor
  · apply (map_injective (f := f.toMonoidHom) f.injective)
    rw [MonoidHom.map_zpowers, MulEquiv.coe_toMonoidHom, hf, ← standard_core_image, map_map, ← pCore_map_iso 2 c, map_map]
    rfl
  · let q : (D ⧸ pCore 2 D) ≃* (C ⧸ pCore 2 C) :=
      QuotientGroup.congr _ _ c (pCore_map_iso 2 c)
    have hq := pCore_map_iso 3 q.symm
    rw [standard_quotient_three, Subgroup.map_bot] at hq
    exact hq.symm

/-- O₂,₃ uses the preimage of O₃(C/O₂(C)); for this centralizer it is exactly the actor. -/
theorem transposition_twoThreeCore {E : Type*} [Group E] [Finite E] (e : E ≃* Perm (Fin 7))
    (v : E) (hv : (e v).IsSwap) :
    let C := centralizer ({v} : Set E)
    ((pCore 3 (C ⧸ pCore 2 C)).comap (QuotientGroup.mk' (pCore 2 C))).map C.subtype = zpowers v := by
  obtain ⟨h2,h3⟩ := transposition_cores e v hv
  dsimp only
  rw [h3]
  change (QuotientGroup.mk' (pCore 2 (centralizer ({v} : Set E)))).ker.map
    (centralizer ({v} : Set E)).subtype = zpowers v
  rw [QuotientGroup.ker_mk']
  exact h2
end AlternatingSeven.TranspositionCore
