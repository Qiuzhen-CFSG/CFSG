module
public import CFSG.Quasithin.Chapter14.Section06.SourceParabolicRankThreeComplete.Seven.OrdinaryGeometry.Pair.Cubic.Certificates
public import Mathlib.GroupTheory.Complement
public import Theory.Representation.BinaryPermutation.SevenParabolic.Ordinary
public import Mathlib.GroupTheory.Perm.Centralizer
/-!
# Recognizing the fixed-Sylow cubic pair on seven letters

Cauchy's theorem and coprime complement counting place each local subgroup
in one of the checked cubic families. Every pair except the paired and
complementary families preserves a proper point, block or Fano-plane
stabilizer. A common relabelling identifies the surviving two groups with
the literal lambda and theta partition stabilizers; their orders prove
that both containments are equalities. Both A₇ and S₇ are included.

Source: Aschbacher--Smith, original14.6.10(5), printed p.1029.
-/

@[expose] public section
open Equiv Subgroup AlternatingSeven.DihedralLocals
namespace CFSG.Quasithin.Chapter14.Section06.Seven.OrdinaryGeometry.Pair.Cubic
private theorem words_mul (full : Bool) (i j : Fin (if full then 16 else 8)) :
    ∃ k, word full i * word full j = word full k := by
  cases full <;> decide +revert +kernel
private theorem words_inv (full : Bool) (i : Fin (if full then 16 else 8)) :
    ∃ j, (word full i)⁻¹ = word full j := by
  cases full <;> decide +revert +kernel

def sylowGroup (full : Bool) : Subgroup Perm7 where
  carrier := Set.range (word full)
  one_mem' := ⟨⟨0,by cases full <;> decide⟩,by cases full <;> decide⟩
  mul_mem' := by
    rintro _ _ ⟨i,rfl⟩ ⟨j,rfl⟩
    obtain ⟨k,hk⟩ := words_mul full i j
    exact ⟨k,hk.symm⟩
  inv_mem' := by
    rintro _ ⟨i,rfl⟩
    obtain ⟨j,hj⟩ := words_inv full i
    exact ⟨j,hj.symm⟩

theorem sylowGroup_card (full : Bool) : Nat.card (sylowGroup full) = if full then 16 else 8 := by
  let f : Fin (if full then 16 else 8) → sylowGroup full := fun i => ⟨word full i,i,rfl⟩
  have hi : Function.Injective (word full) := by cases full <;> decide +kernel
  have hb : Function.Bijective f := ⟨fun i j h => hi (congrArg Subtype.val h),by
    rintro ⟨_,i,rfl⟩
    exact ⟨i,rfl⟩⟩
  rw [←Nat.card_congr (Equiv.ofBijective f hb)]
  exact Nat.card_fin _

theorem tWord_mem (full : Bool) (i : Fin 8) : tWord i ∈ sylowGroup full := by
  cases full
  · exact ⟨i,by decide +revert +kernel⟩
  · exact ⟨⟨i.val,by simpa using (i.isLt.trans (by decide : 8 < 16))⟩,by decide +revert +kernel⟩

/-- Every local subgroup retains a cubic from the checked catalogue. -/
theorem local_containment (full : Bool) (H : Subgroup Perm7)
    (hT : sylowGroup full ≤ H) (hc : Nat.card H = 3 * (if full then 16 else 8)) :
    ∃ j : Fin 5, (full = true → j.val = 0 ∨ j.val = 3 ∨ j.val = 4) ∧
      ∀ Q : Subgroup Perm7, sylowGroup full ≤ Q → cube j ∈ Q → H ≤ Q := by
  obtain ⟨a,ha⟩ := exists_prime_orderOf_dvd_card' (G := H) 3 (by rw [hc]; exact dvd_mul_right _ _)
  have ht : Nat.card ((sylowGroup full).subgroupOf H) = if full then 16 else 8 :=
    (Nat.card_congr (subgroupOfEquivOfLe hT).toEquiv).trans (sylowGroup_card full)
  have haC : Nat.card (zpowers a) = 3 := by rw [Nat.card_zpowers,ha]
  have hprod : ((sylowGroup full).subgroupOf H).IsComplement' (zpowers a) :=
    isComplement'_of_coprime (by rw [ht,haC,hc]; omega)
      (by rw [ht,haC]; cases full <;> decide)
  have hcrit : Criterion full a.val := by
    refine ⟨?_,?_,?_⟩
    · exact congrArg Subtype.val (ha ▸ pow_orderOf_eq_one a)
    · intro he
      have ha1 : a = 1 := Subtype.ext he
      simp [ha1] at ha
    · intro i
      let x : H := a * ⟨word full i,hT ⟨i,rfl⟩⟩
      obtain ⟨⟨t,z⟩,htz⟩ := hprod.2 x
      obtain ⟨j,hj⟩ := t.property
      obtain ⟨k,hklt,hk⟩ := Finset.mem_image.mp (mem_zpowers_iff_mem_range_orderOf.mp z.property)
      have hk3 : k < 3 := by simpa [ha] using Finset.mem_range.mp hklt
      refine ⟨j,⟨k,hk3⟩,?_⟩
      have hval := congrArg (fun y : H => y.val) htz
      change t.val.val * z.val.val = a.val * word full i at hval
      change word full j = t.val.val at hj
      have hk' : a.val ^ k = z.val.val := congrArg Subtype.val hk
      rw [←hj,←hk'] at hval
      exact hval.symm
  obtain ⟨j,hj,i,hi⟩ := catalogue full a.val hcrit
  refine ⟨j,hj,fun Q hQ hjQ => ?_⟩
  have haQ : a.val ∈ Q := by
    rw [hi]
    exact Q.mul_mem (Q.mul_mem (hQ (tWord_mem full i)) hjQ) (Q.inv_mem (hQ (tWord_mem full i)))
  have hC : zpowers a ≤ Q.subgroupOf H := zpowers_le.mpr haQ
  intro x hx
  obtain ⟨⟨t,z⟩,htz⟩ := hprod.2 (⟨x,hx⟩ : H)
  have he : t.val.val * z.val.val = x := congrArg Subtype.val htz
  rw [←he]
  exact Q.mul_mem (hQ t.property) (hC z.property)
end CFSG.Quasithin.Chapter14.Section06.Seven.OrdinaryGeometry.Pair.Cubic

open scoped Pointwise
namespace CFSG.Quasithin.Chapter14.Section06.Seven.OrdinaryGeometry.Pair.Cubic
private def badGroup (j k : Fin 5) : Subgroup Perm7 :=
  if j = 4 ∨ k = 4 ∨ (j ≠ 3 ∧ k ≠ 3) then MulAction.stabilizer Perm7 block else
  if j = 1 ∨ k = 1 then MulAction.stabilizer Perm7 planePlus else
  if j = 2 ∨ k = 2 then MulAction.stabilizer Perm7 planeMinus else
  MulAction.stabilizer Perm7 (6 : Fin 7)
private instance (j k : Fin 5) (g : Perm7) : Decidable (g ∈ badGroup j k) := by
  unfold badGroup
  split
  · change Decidable (g • block = block); infer_instance
  · split
    · change Decidable (g • planePlus = planePlus); infer_instance
    · split
      · change Decidable (g • planeMinus = planeMinus); infer_instance
      · change Decidable (g (6 : Fin 7) = 6); infer_instance
private def allowed (full : Bool) (j : Fin 5) : Prop :=
  full = true → j.val = 0 ∨ j.val = 3 ∨ j.val = 4
private def goodPair (j k : Fin 5) : Prop := (j = 3 ∧ k = 4) ∨ (j = 4 ∧ k = 3)
private instance (full : Bool) (j : Fin 5) : Decidable (allowed full j) :=
  inferInstanceAs (Decidable (_ → _ ∨ _ ∨ _))
private instance (j k : Fin 5) : Decidable (goodPair j k) :=
  inferInstanceAs (Decidable ((_ ∧ _) ∨ (_ ∧ _)))
set_option maxRecDepth 4096 in
private theorem bad_generators_0 (full : Bool) (k : Fin 5)
    (hj : allowed full 0) (hk : allowed full k) (hn : ¬ goodPair 0 k) :
    (∀ i, word full i ∈ badGroup 0 k) ∧ cube 0 ∈ badGroup 0 k ∧ cube k ∈ badGroup 0 k := by
  revert hn hk hj k
  cases full <;> decide +kernel

set_option maxRecDepth 4096 in
private theorem bad_generators_1 (full : Bool) (k : Fin 5)
    (hj : allowed full 1) (hk : allowed full k) (hn : ¬ goodPair 1 k) :
    (∀ i, word full i ∈ badGroup 1 k) ∧ cube 1 ∈ badGroup 1 k ∧ cube k ∈ badGroup 1 k := by
  revert hn hk hj k
  cases full <;> decide +kernel

set_option maxRecDepth 4096 in
private theorem bad_generators_2 (full : Bool) (k : Fin 5)
    (hj : allowed full 2) (hk : allowed full k) (hn : ¬ goodPair 2 k) :
    (∀ i, word full i ∈ badGroup 2 k) ∧ cube 2 ∈ badGroup 2 k ∧ cube k ∈ badGroup 2 k := by
  revert hn hk hj k
  cases full <;> decide +kernel

set_option maxRecDepth 4096 in
private theorem bad_generators_3 (full : Bool) (k : Fin 5)
    (hj : allowed full 3) (hk : allowed full k) (hn : ¬ goodPair 3 k) :
    (∀ i, word full i ∈ badGroup 3 k) ∧ cube 3 ∈ badGroup 3 k ∧ cube k ∈ badGroup 3 k := by
  revert hn hk hj k
  cases full <;> decide +kernel

set_option maxRecDepth 4096 in
private theorem bad_generators_4 (full : Bool) (k : Fin 5)
    (hj : allowed full 4) (hk : allowed full k) (hn : ¬ goodPair 4 k) :
    (∀ i, word full i ∈ badGroup 4 k) ∧ cube 4 ∈ badGroup 4 k ∧ cube k ∈ badGroup 4 k := by
  revert hn hk hj k
  cases full <;> decide +kernel

private theorem bad_generators (full : Bool) (j k : Fin 5)
    (hj : allowed full j) (hk : allowed full k) (hn : ¬ goodPair j k) :
    (∀ i, word full i ∈ badGroup j k) ∧ cube j ∈ badGroup j k ∧ cube k ∈ badGroup j k := by
  fin_cases j
  · exact bad_generators_0 full k hj hk hn
  · exact bad_generators_1 full k hj hk hn
  · exact bad_generators_2 full k hj hk hn
  · exact bad_generators_3 full k hj hk hn
  · exact bad_generators_4 full k hj hk hn
private def escaping : Perm7 := swap 0 1 * swap 1 6
private theorem escaping_even : escaping ∈ alternatingGroup (Fin 7) := by
  change Perm.sign escaping = 1
  decide
private theorem escaping_bad (j k : Fin 5) : escaping ∉ badGroup j k := by
  decide +revert +kernel

/-- Only the paired and complementary cubic families generate the ambient alternating group. -/
theorem generating_pair_types (full : Bool) (A B : Subgroup Perm7)
    (hTA : sylowGroup full ≤ A) (hTB : sylowGroup full ≤ B)
    (hcA : Nat.card A = 3 * (if full then 16 else 8))
    (hcB : Nat.card B = 3 * (if full then 16 else 8))
    (hgen : alternatingGroup (Fin 7) ≤ A ⊔ B) :
    ∃ j k : Fin 5, ((j = 3 ∧ k = 4) ∨ (j = 4 ∧ k = 3)) ∧
      (∀ Q : Subgroup Perm7, sylowGroup full ≤ Q → cube j ∈ Q → A ≤ Q) ∧
      (∀ Q : Subgroup Perm7, sylowGroup full ≤ Q → cube k ∈ Q → B ≤ Q) := by
  obtain ⟨j,hj,ha⟩ := local_containment full A hTA hcA
  obtain ⟨k,hk,hb⟩ := local_containment full B hTB hcB
  refine ⟨j,k,?_,ha,hb⟩
  by_contra hn
  have hbad := bad_generators full j k hj hk hn
  have ht : sylowGroup full ≤ badGroup j k := by
    rintro _ ⟨i,rfl⟩
    exact hbad.1 i
  exact escaping_bad j k ((hgen.trans (sup_le (ha _ ht hbad.2.1) (hb _ ht hbad.2.2))) escaping_even)
end CFSG.Quasithin.Chapter14.Section06.Seven.OrdinaryGeometry.Pair.Cubic

namespace CFSG.Quasithin.Chapter14.Section06.Seven.OrdinaryGeometry.Pair.Cubic

def ambient (full : Bool) : Subgroup Perm7 := if full then ⊤ else alternatingGroup (Fin 7)

theorem ambient_card (full : Bool) : Nat.card (ambient full) = if full then 5040 else 2520 := by
  cases full
  · change Nat.card (alternatingGroup (Fin 7)) = 2520
    rw [nat_card_alternatingGroup]
    norm_num [Nat.factorial]
  · change Nat.card (⊤ : Subgroup Perm7) = 5040
    rw [Nat.card_congr Subgroup.topEquiv.toEquiv, Nat.card_eq_fintype_card, Fintype.card_perm]
    decide

theorem sylowGroup_le_ambient (full : Bool) : sylowGroup full ≤ ambient full := by
  cases full
  · rintro _ ⟨i,rfl⟩
    exact (by decide +kernel : ∀ i, Perm.sign (word false i) = 1) i
  · exact le_top

def sylow (full : Bool) : Sylow 2 (ambient full) :=
  Sylow.ofCard ((sylowGroup full).subgroupOf (ambient full)) (by
    rw [Nat.card_congr (subgroupOfEquivOfLe (sylowGroup_le_ambient full)).toEquiv,
      sylowGroup_card,ambient_card]
    cases full <;> decide +kernel)

theorem sylow_map (full : Bool) :
    (sylow full : Subgroup (ambient full)).map (ambient full).subtype = sylowGroup full :=
  map_subgroupOf_eq_of_le (sylowGroup_le_ambient full)

theorem ambient_cases (J : Subgroup Perm7) (hJ : alternatingGroup (Fin 7) ≤ J) :
    ∃ full : Bool, J = ambient full := by
  have hd : J.index ∣ 2 := by
    rw [←alternatingGroup.index_eq_two (α := Fin 7)]
    exact index_dvd_of_le hJ
  rcases (Nat.dvd_prime Nat.prime_two).mp hd with he | he
  · exact ⟨true,index_eq_one.mp he⟩
  · exact ⟨false,Perm.eq_alternatingGroup_of_index_eq_two he⟩

end CFSG.Quasithin.Chapter14.Section06.Seven.OrdinaryGeometry.Pair.Cubic

namespace CFSG.Quasithin.Chapter14.Section06.Seven.OrdinaryGeometry.Pair.Cubic
open BinaryPermutation.SevenParabolic.Ordinary
private theorem even_intersection_card (H : Subgroup Perm7) (hc : Nat.card H = 48)
    (ho : oddSwap ∈ H) : Nat.card (alternatingGroup (Fin 7) ⊓ H : Subgroup Perm7) = 24 := by
  have hi : (alternatingGroup (Fin 7)).relIndex H = 2 := by
    have hd : (alternatingGroup (Fin 7)).relIndex H ∣ 2 := by
      rw [←alternatingGroup.index_eq_two (α := Fin 7)]
      exact relIndex_dvd_index_of_normal _ _
    rcases (Nat.dvd_prime Nat.prime_two).mp hd with hh | hh
    · have he := relIndex_eq_one.mp hh ho
      have hn : oddSwap ∉ alternatingGroup (Fin 7) := by
        change ¬ Perm.sign oddSwap = 1
        decide
      exact (hn he).elim
    · exact hh
  have hcard := ((alternatingGroup (Fin 7) ⊓ H).subgroupOf H).card_mul_index
  rw [Nat.card_congr (subgroupOfEquivOfLe (show alternatingGroup (Fin 7) ⊓ H ≤ H from inf_le_right)).toEquiv,hc] at hcard
  change Nat.card (alternatingGroup (Fin 7) ⊓ H : Subgroup Perm7) *
    (alternatingGroup (Fin 7) ⊓ H).relIndex H = 48 at hcard
  rw [inf_relIndex_right,hi] at hcard
  omega
private theorem parabolic_card (full : Bool) :
    Nat.card (ambient full ⊓ lambda : Subgroup Perm7) = 3 * (if full then 16 else 8) ∧
    Nat.card (ambient full ⊓ theta : Subgroup Perm7) = 3 * (if full then 16 else 8) := by
  have hl : Nat.card lambda = 48 := by
    rw [lambda,Perm.nat_card_centralizer,show tripleSwap.cycleType = {2,2,2} by decide]
    norm_num [Nat.factorial]
  have ht : Nat.card theta = 48 := by
    rw [theta,Perm.nat_card_centralizer,show doubleSwap.cycleType = {2,2} by decide]
    norm_num [Nat.factorial]
  have hol : oddSwap ∈ lambda := by rw [lambda,mem_centralizer_singleton_iff]; decide
  have hot : oddSwap ∈ theta := by rw [theta,mem_centralizer_singleton_iff]; decide
  cases full
  · exact ⟨even_intersection_card lambda hl hol,even_intersection_card theta ht hot⟩
  · simpa [ambient] using And.intro hl ht
end CFSG.Quasithin.Chapter14.Section06.Seven.OrdinaryGeometry.Pair.Cubic

namespace CFSG.Quasithin.Chapter14.Section06.Seven.OrdinaryGeometry.Pair.Cubic
open BinaryPermutation.SevenParabolic.Ordinary
def relabelling : Perm7 := swap 1 2
private theorem target_generators (full : Bool) :
    (∀ i, (MulAut.conj relabelling) (word full i) ∈ lambda ∧
      (MulAut.conj relabelling) (word full i) ∈ theta) ∧
    (MulAut.conj relabelling) (cube 3) ∈ lambda ∧
    (MulAut.conj relabelling) (cube 4) ∈ theta := by
  simp only [lambda,theta,mem_centralizer_singleton_iff]
  cases full <;> decide +kernel
theorem map_ambient (full : Bool) (g : Perm7) :
    (ambient full).map (MulAut.conj g).toMonoidHom = ambient full := by
  cases full
  · change (alternatingGroup (Fin 7)).map (MulAut.conj g).toMonoidHom = alternatingGroup (Fin 7)
    apply le_antisymm
    · rintro _ ⟨x,hx,rfl⟩
      exact (inferInstance : (alternatingGroup (Fin 7)).Normal).conj_mem x hx g
    · intro x hx
      refine ⟨g⁻¹*x*g,?_,?_⟩
      · have hh := (inferInstance : (alternatingGroup (Fin 7)).Normal).conj_mem x hx g⁻¹
        rw [inv_inv] at hh
        exact hh
      · change g*(g⁻¹*x*g)*g⁻¹=x
        group
  · exact map_top_of_surjective _ (MulAut.conj g).surjective

private theorem target_equality (full : Bool) (H : Subgroup Perm7)
    (hH : H ≤ ambient full) (hc : Nat.card H = 3 * (if full then 16 else 8))
    (j : Fin 5) (hj : j = 3 ∨ j = 4)
    (hlocal : ∀ Q : Subgroup Perm7, sylowGroup full ≤ Q → cube j ∈ Q → H ≤ Q) :
    H.map (MulAut.conj relabelling).toMonoidHom =
      ambient full ⊓ (if j = 3 then lambda else theta) := by
  let target : Subgroup Perm7 := if j = 3 then lambda else theta
  have ht : H.map (MulAut.conj relabelling).toMonoidHom ≤ target := by
    apply map_le_iff_le_comap.mpr
    apply hlocal
    · rintro _ ⟨i,rfl⟩
      rcases hj with rfl | rfl
      · exact (target_generators full).1 i |>.1
      · exact (target_generators full).1 i |>.2
    · rcases hj with rfl | rfl
      · exact (target_generators full).2.1
      · exact (target_generators full).2.2
  have hle : H.map (MulAut.conj relabelling).toMonoidHom ≤ ambient full ⊓ target :=
    le_inf ((map_mono hH).trans (map_ambient full relabelling).le) ht
  apply eq_of_le_of_card_ge hle
  rw [card_map_of_injective (MulAut.conj relabelling).injective,hc]
  rcases hj with rfl | rfl
  · exact (parabolic_card full).1.le
  · exact (parabolic_card full).2.le

/-- The actual fixed-Sylow cubic pair has precisely the two marked partition images. -/
theorem fixed_pair (full : Bool) (A B : Subgroup Perm7)
    (hA : A ≤ ambient full) (hB : B ≤ ambient full)
    (hTA : sylowGroup full ≤ A) (hTB : sylowGroup full ≤ B)
    (hcA : Nat.card A = 3 * (if full then 16 else 8))
    (hcB : Nat.card B = 3 * (if full then 16 else 8))
    (hgen : alternatingGroup (Fin 7) ≤ A ⊔ B) :
    (A.map (MulAut.conj relabelling).toMonoidHom = ambient full ⊓ lambda ∧
      B.map (MulAut.conj relabelling).toMonoidHom = ambient full ⊓ theta) ∨
    (A.map (MulAut.conj relabelling).toMonoidHom = ambient full ⊓ theta ∧
      B.map (MulAut.conj relabelling).toMonoidHom = ambient full ⊓ lambda) := by
  obtain ⟨j,k,hjk,ha,hb⟩ := generating_pair_types full A B hTA hTB hcA hcB hgen
  rcases hjk with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
  · exact Or.inl ⟨target_equality full A hA hcA 3 (Or.inl rfl) ha,
      target_equality full B hB hcB 4 (Or.inr rfl) hb⟩
  · exact Or.inr ⟨target_equality full A hA hcA 4 (Or.inr rfl) ha,
      target_equality full B hB hcB 3 (Or.inl rfl) hb⟩
end CFSG.Quasithin.Chapter14.Section06.Seven.OrdinaryGeometry.Pair.Cubic
