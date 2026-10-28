module

public import Theory.SpecificGroups.AlternatingSix.ProperSylowOvergroups
public import Theory.SpecificGroups.AlternatingSix.SmallIndex
public import Theory.SpecificGroups.SymmetricFive.PentagonNormalizer
public import Theory.GroupTheory.Hall.Existence
public import Theory.GroupTheory.NormalizedSupConsequences
import Mathlib.GroupTheory.Perm.Centralizer
import Mathlib.GroupTheory.IsPerfect

/-!
# Five-divisibility in small alternating Sylow overgroups

A solvable subgroup of A₅, A₆, A₇ or A₈ containing a full Sylow two-subgroup
has order prime to five. The first two cases use simplicity and the
already proved A₆ Sylow-overgroup bound. In A₇ a Hall {2,5}-subgroup would
have order forty and a unique Sylow five-subgroup. Its normalizer in A₇
has order twenty: the permutation centralizer formula bounds it by forty,
and Sylow's normalizer congruence fixes its exact order. The eight-letter
case reduces to A₇ through a point stabilizer of index eight.

The final theorem applies this obstruction to a solvable subgroup normalized
by the literal chosen Sylow subgroup, by adjoining that Sylow subgroup.
This is the alternating-model comparison used in Aschbacher–Smith,
*The Classification of Quasithin Groups*, 15.2.4, printed pp.1106–1107.
-/

public section

open Subgroup Equiv.Perm
namespace Theory.SpecificGroups.Alternating.SmallSolvableFive
local instance : Fact (Nat.Prime 5) := ⟨by decide⟩
local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

private theorem seven_five_normalizer_card (P : Subgroup (alternatingGroup (Fin 7)))
    (hP : Nat.card P = 5) : Nat.card (normalizer (P : Set (alternatingGroup (Fin 7)))) = 20 := by
  let f := (alternatingGroup (Fin 7)).subtype
  let Q := P.map f
  have hQ : Nat.card Q = 5 := (card_map_of_injective (alternatingGroup (Fin 7)).subtype_injective).trans hP
  obtain ⟨x,hx⟩ := exists_prime_orderOf_dvd_card' (G := Q) 5 (by rw [hQ])
  have ho : orderOf (x : Equiv.Perm (Fin 7)) = 5 := (orderOf_coe x).trans hx
  have hcycle : (x : Equiv.Perm (Fin 7)).IsCycle :=
    isCycle_of_prime_order' (by rw [ho]; decide) (by rw [ho]; decide)
  have htype : (x : Equiv.Perm (Fin 7)).cycleType = {5} := by
    rw [hcycle.cycleType, ← hcycle.orderOf, ho]
  have hg : zpowers (x : Equiv.Perm (Fin 7)) = Q :=
    eq_of_le_of_card_ge (zpowers_le.mpr x.property) (by rw [Nat.card_zpowers,ho,hQ])
  have hC : Nat.card (centralizer (Q : Set (Equiv.Perm (Fin 7)))) = 10 := by
    rw [← hg,zpowers_eq_closure,centralizer_closure,nat_card_centralizer,htype]
    norm_num
  let : IsCyclic Q := isCyclic_of_prime_card hQ
  have hA : Nat.card (MulAut Q) = 4 := by rw [IsCyclic.card_mulAut,hQ]; decide
  have hd := Q.card_normalizer_dvd_card_centralizer_mul_card_mulAut
  rw [hC,hA] at hd
  have hb : Nat.card (normalizer (P : Set (alternatingGroup (Fin 7)))) ≤ 40 := by
    calc
      _ = Nat.card ((normalizer (P : Set (alternatingGroup (Fin 7)))).map f) :=
        (card_map_of_injective (alternatingGroup (Fin 7)).subtype_injective).symm
      _ ≤ Nat.card (normalizer (Q : Set (Equiv.Perm (Fin 7)))) :=
        Nat.le_of_dvd Nat.card_pos (card_dvd_of_le (P.le_normalizer_map f))
      _ ≤ 40 := Nat.le_of_dvd (by decide) hd
  have hm := Sylow.card_normalizer_modEq_card (p := 5) (n := 1) (H := P) hP
  have hcard : Nat.card (alternatingGroup (Fin 7)) = 2520 := by
    rw [nat_card_alternatingGroup]; norm_num [Nat.factorial]
  rw [hcard] at hm
  change _ % 25 = 2520 % 25 at hm
  omega

private theorem normal_five_of_card_forty {G : Type*} [Group G] [Finite G]
    (hG : Nat.card G = 40) : ∃ P : Subgroup G, P.Normal ∧ Nat.card P = 5 := by
  let P : Sylow 5 G := Classical.choice inferInstance
  have hP : Nat.card P = 5 := by
    rw [Sylow.card_eq_multiplicity,hG]; decide +kernel
  have hi : (P : Subgroup G).index = 8 := by
    have h := (P : Subgroup G).card_mul_index
    rw [hP,hG] at h
    omega
  have hn : Nat.card (Sylow 5 G) = 1 := by
    have hd := P.card_dvd_index
    rw [hi] at hd
    have hm := card_sylow_modEq_one 5 G
    have hb := Nat.le_of_dvd (by decide : 0 < 8) hd
    change Nat.card (Sylow 5 G) % 5 = 1 % 5 at hm
    interval_cases hn : Nat.card (Sylow 5 G) <;> omega
  let : Subsingleton (Sylow 5 G) := (Nat.card_eq_one_iff_unique.mp hn).1
  exact ⟨P, P.normal_of_subsingleton, hP⟩

private theorem exists_forty_of_solvable {G : Type*} [Group G] [Finite G]
    (hsolv : Group.IsSolvable G) (hG : Nat.card G ∣ 2520)
    (h8 : 8 ∣ Nat.card G) (h5 : 5 ∣ Nat.card G) :
    ∃ H : Subgroup G, Nat.card H = 40 := by
  let _ : MulDistribMulAction Unit G := {
    smul _ x := x
    one_smul _ := rfl
    mul_smul _ _ _ := rfl
    smul_one _ := rfl
    smul_mul _ _ _ := rfl }
  let π : Set Nat.Primes := {p | p.val = 2 ∨ p.val = 5}
  obtain ⟨H,hHall,_⟩ := exists_isHallSubgroup_isInvariant (A := Unit) hsolv (by simp) π
  have h3 : ¬ 3 ∣ Nat.card H := by
    intro h
    have hh := hHall.p_in_pi_of_p_dvd_card ⟨3,by decide⟩ h
    change 3 = 2 ∨ 3 = 5 at hh
    omega
  have h7 : ¬ 7 ∣ Nat.card H := by
    intro h
    have hh := hHall.p_in_pi_of_p_dvd_card ⟨7,by decide⟩ h
    change 7 = 2 ∨ 7 = 5 at hh
    omega
  have hcop : Nat.Coprime (Nat.card H) 63 := by
    have h3c := (Nat.prime_three.coprime_iff_not_dvd.mpr h3).symm
    have h7c := ((show Nat.Prime 7 by decide).coprime_iff_not_dvd.mpr h7).symm
    simpa using (h3c.pow_right 2).mul_right h7c
  have hd : Nat.card H ∣ 40 := hcop.dvd_of_dvd_mul_right (H.card_subgroup_dvd_card.trans hG)
  have hi2 : ¬ 2 ∣ H.index := fun h =>
    hHall.p_in_pi_of_p_dvd_index ⟨2,Nat.prime_two⟩ h (Or.inl rfl)
  have hi5 : ¬ 5 ∣ H.index := fun h =>
    hHall.p_in_pi_of_p_dvd_index ⟨5,by decide⟩ h (Or.inr rfl)
  have hd8 : 8 ∣ Nat.card H := by
    have hc := (Nat.prime_two.coprime_iff_not_dvd.mpr hi2).pow_left 3
    exact hc.dvd_of_dvd_mul_right (H.card_mul_index.symm ▸ h8)
  have hd5 : 5 ∣ Nat.card H :=
    (Nat.Prime.dvd_mul (by decide : Nat.Prime 5)).mp (H.card_mul_index.symm ▸ h5) |>.resolve_right hi5
  exact ⟨H,Nat.dvd_antisymm hd ((show Nat.Coprime 8 5 by decide).mul_dvd_of_dvd_of_dvd hd8 hd5)⟩

/-- Solvable overgroups of a full Sylow two-subgroup of A₇ have order prime to five. -/
theorem seven_not_five_dvd (D : Subgroup (alternatingGroup (Fin 7)))
    (hsolv : Group.IsSolvable D) (S : Sylow 2 (alternatingGroup (Fin 7)))
    (hSD : (S : Subgroup _) ≤ D) : ¬ 5 ∣ Nat.card D := by
  intro h5
  have hA : Nat.card (alternatingGroup (Fin 7)) = 2520 := by
    rw [nat_card_alternatingGroup]; norm_num [Nat.factorial]
  have hS : Nat.card S = 8 := by
    rw [Sylow.card_eq_multiplicity,hA]; decide +kernel
  obtain ⟨H,hH⟩ := exists_forty_of_solvable hsolv (hA ▸ D.card_subgroup_dvd_card)
    (hS ▸ card_dvd_of_le hSD) h5
  obtain ⟨P,hPn,hP⟩ := normal_five_of_card_forty hH
  let : P.Normal := hPn
  let f := D.subtype.comp H.subtype
  have hf : Function.Injective f := D.subtype_injective.comp H.subtype_injective
  let Q := P.map f
  have hQ : Nat.card Q = 5 := (card_map_of_injective hf).trans hP
  have hN : H.map D.subtype ≤ normalizer (Q : Set (alternatingGroup (Fin 7))) := by
    have hh := P.le_normalizer_map f
    rw [normalizer_eq_top, ← MonoidHom.range_eq_map] at hh
    simpa only [f, MonoidHom.range_comp, range_subtype] using hh
  have hd : 40 ∣ 20 := by
    have hh := card_dvd_of_le hN
    rw [card_map_of_injective D.subtype_injective,hH,seven_five_normalizer_card Q hQ] at hh
    exact hh
  norm_num at hd

/-- Solvable overgroups of a full Sylow two-subgroup of A₅ have order prime to five. -/
theorem five_not_five_dvd (D : Subgroup (alternatingGroup (Fin 5)))
    (hsolv : Group.IsSolvable D) (S : Sylow 2 (alternatingGroup (Fin 5)))
    (hSD : (S : Subgroup _) ≤ D) : ¬ 5 ∣ Nat.card D := by
  have hA : Nat.card (alternatingGroup (Fin 5)) = 60 := by
    rw [nat_card_alternatingGroup]; norm_num [Nat.factorial]
  have hp : D ≠ ⊤ := by
    intro h
    let : Group.IsSolvable D := hsolv
    let : Group.IsSolvable (alternatingGroup (Fin 5)) :=
      Group.isSolvable_of_surjective (f := D.subtype) (by
        intro x
        exact ⟨⟨x,h ▸ mem_top x⟩,rfl⟩)
    let : Group.IsPerfect (alternatingGroup (Fin 5)) :=
      ⟨commutator_alternatingGroup_eq_top (by simp)⟩
    exact Group.IsPerfect.not_isSolvable (alternatingGroup (Fin 5)) inferInstance
  have hi : 5 ≤ D.index := by
    by_contra hn
    apply hp
    apply Atlas.GroupTheory.subgroup_eq_top_of_index_factorial_lt
    have hb := Nat.factorial_le (show D.index ≤ 4 by omega)
    rw [hA]
    norm_num [Nat.factorial] at hb ⊢
    omega
  have hm := D.card_mul_index
  rw [hA] at hm
  have hb : Nat.card D ≤ 12 := by nlinarith
  have hS : Nat.card S = 4 := by
    rw [Sylow.card_eq_multiplicity,hA]; decide +kernel
  intro h5
  have h4 : 4 ∣ Nat.card D := hS ▸ card_dvd_of_le hSD
  have h20 : 20 ∣ Nat.card D := (show Nat.Coprime 4 5 by decide).mul_dvd_of_dvd_of_dvd h4 h5
  have hh := Nat.le_of_dvd (Nat.card_pos (α := D)) h20
  omega

/-- Solvable overgroups of a full Sylow two-subgroup of A₆ have order prime to five. -/
theorem six_not_five_dvd (D : Subgroup (alternatingGroup (Fin 6)))
    (hsolv : Group.IsSolvable D) (S : Sylow 2 (alternatingGroup (Fin 6)))
    (hSD : (S : Subgroup _) ≤ D) : ¬ 5 ∣ Nat.card D := by
  have hp : D ≠ ⊤ := by
    intro h
    let : Group.IsSolvable D := hsolv
    let : Group.IsSolvable (alternatingGroup (Fin 6)) :=
      Group.isSolvable_of_surjective (f := D.subtype) (by
        intro x
        exact ⟨⟨x,h ▸ mem_top x⟩,rfl⟩)
    let : Group.IsPerfect (alternatingGroup (Fin 6)) :=
      ⟨commutator_alternatingGroup_eq_top (by simp)⟩
    exact Group.IsPerfect.not_isSolvable (alternatingGroup (Fin 6)) inferInstance
  rcases AlternatingSix.ProperSylowOvergroups.card_eight_or_twentyFour S D hSD hp with h | h
  · rw [h]; decide
  · rw [h]; decide

/-- The point stabilizer reduces the A₈ obstruction to the A₇ theorem. -/
theorem eight_not_five_dvd (D : Subgroup (alternatingGroup (Fin 8)))
    (hsolv : Group.IsSolvable D) (S : Sylow 2 (alternatingGroup (Fin 8)))
    (hSD : (S : Subgroup _) ≤ D) : ¬ 5 ∣ Nat.card D := by
  let : Group.IsSolvable D := hsolv
  let H := MulAction.stabilizer D (0 : Fin 8)
  let K := MulAction.stabilizer (alternatingGroup (Fin 8)) (0 : Fin 8)
  let f₀ : H →* K := {
    toFun x := ⟨x.val.val,x.property⟩
    map_one' := rfl
    map_mul' _ _ := rfl }
  let f : H →* alternatingGroup (Fin 7) :=
    (AlternatingSix.SmallIndex.pointEquiv (0 : Fin 8)).toMonoidHom.comp f₀
  have hf₀ : Function.Injective f₀ := by
    intro a b h
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun z : K => z.val) h
  have hf : Function.Injective f :=
    (AlternatingSix.SmallIndex.pointEquiv (0 : Fin 8)).injective.comp hf₀
  have hHcard : Nat.card f.range = Nat.card H := (Nat.card_congr (MonoidHom.ofInjective hf).toEquiv).symm
  have h7 : Nat.card (alternatingGroup (Fin 7)) = 2520 := by
    rw [nat_card_alternatingGroup]; norm_num [Nat.factorial]
  have hHdiv : Nat.card H ∣ 2520 := by
    rw [←hHcard, ←h7]
    exact f.range.card_subgroup_dvd_card
  have hi : H.index ≤ 8 := by
    rw [MulAction.index_stabilizer]
    simpa using Set.ncard_le_ncard (Set.subset_univ (MulAction.orbit D (0 : Fin 8)))
  have h8 : Nat.card (alternatingGroup (Fin 8)) = 20160 := by
    rw [nat_card_alternatingGroup]; norm_num [Nat.factorial]
  have hS : Nat.card S = 64 := by
    rw [Sylow.card_eq_multiplicity,h8]; decide +kernel
  have h64 : 64 ∣ Nat.card D := hS ▸ card_dvd_of_le hSD
  have hi8 : H.index = 8 := by
    have hd : 64 ∣ 2520 * H.index :=
      (H.card_mul_index.symm ▸ h64).trans (Nat.mul_dvd_mul_right hHdiv H.index)
    have hp : 0 < H.index := Nat.card_pos
    omega
  have h8H : 8 ∣ Nat.card H := by
    have hh : 8 * 8 ∣ Nat.card H * 8 := by
      have hh := H.card_mul_index
      rw [hi8] at hh
      simpa only [hh] using h64
    exact (Nat.mul_dvd_mul_iff_right (by decide : 0 < 8)).mp hh
  obtain ⟨P,hP⟩ := Sylow.exists_subgroup_card_pow_prime (G := H) 2 (n := 3) h8H
  let Q := P.map f
  have hQ : Nat.card Q = 8 := (card_map_of_injective hf).trans hP
  let T : Sylow 2 (alternatingGroup (Fin 7)) := Sylow.ofCard Q (by rw [hQ,h7]; decide +kernel)
  have hsolvf : Group.IsSolvable f.range := Group.isSolvable_of_surjective f.rangeRestrict_surjective
  have hn : ¬5 ∣ Nat.card H := by
    rw [← hHcard]
    exact seven_not_five_dvd f.range hsolvf T (map_le_range f P)
  intro h5
  have hh : 5 ∣ Nat.card H * 8 := by
    have hh := H.card_mul_index
    rw [hi8] at hh
    simpa only [hh] using h5
  exact hn (((show Nat.Prime 5 by decide).dvd_mul.mp hh).resolve_right (by decide))

/-- The actual normalized solvable subgroup form used in the marked-five source argument. -/
theorem not_five_dvd_of_sylow_normalizes {n : ℕ} (hn : n = 5 ∨ n = 6 ∨ n = 7 ∨ n = 8)
    (Y : Subgroup (alternatingGroup (Fin n))) (hsolv : Group.IsSolvable Y)
    (S : Sylow 2 (alternatingGroup (Fin n)))
    (hSY : (S : Subgroup (alternatingGroup (Fin n))) ≤ normalizer (Y : Set (alternatingGroup (Fin n)))) : ¬ 5 ∣ Nat.card Y := by
  let : Group.IsSolvable Y := hsolv
  let : Group.IsNilpotent S := S.isPGroup'.isNilpotent
  let : Group.IsSolvable (Y ⊔ (S : Subgroup (alternatingGroup (Fin n))) : Subgroup (alternatingGroup (Fin n))) :=
    Group.isSolvable_sup_of_normalizes Y (S : Subgroup (alternatingGroup (Fin n))) hSY
  intro h5
  have hd : 5 ∣ Nat.card (Y ⊔ (S : Subgroup (alternatingGroup (Fin n))) : Subgroup (alternatingGroup (Fin n))) :=
    h5.trans (card_dvd_of_le le_sup_left)
  rcases hn with rfl | rfl | rfl | rfl
  · exact (five_not_five_dvd _ inferInstance S le_sup_right) hd
  · exact (six_not_five_dvd _ inferInstance S le_sup_right) hd
  · exact (seven_not_five_dvd _ inferInstance S le_sup_right) hd
  · exact (eight_not_five_dvd _ inferInstance S le_sup_right) hd

end Theory.SpecificGroups.Alternating.SmallSolvableFive
