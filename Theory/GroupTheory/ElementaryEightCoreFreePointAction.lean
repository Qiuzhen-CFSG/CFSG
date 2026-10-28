module
public import Theory.GroupTheory.ElementaryEightSylowFour
public import Theory.GroupTheory.SmallIndexSolvable
public import Theory.GroupTheory.SpecificGroups.KleinFourAut
public import Mathlib.GroupTheory.SpecificGroups.Cyclic
public import Theory.SpecificGroups.PSL3Two.Parabolics.Subgroups
/-!
# Small reduced elementary-two automizers

A two-core-free subgroup of GL(3,2) with four-divisible order is the full
automorphism group. Its point stabilizers cannot be two-groups. The proof
uses the actual projective-plane parabolics and the Sylow-four solvability
criterion. This is the small-action step in Aschbacher–Smith 13.9.8.
-/
public section
open Subgroup MulAction

private theorem isSolvable_of_proper_elementary_eight_sylow_eight
    (E : Type*) [Group E] [Finite E] [IsElementaryAbelian 2 E]
    (hE : Nat.card E = 8) (A : Subgroup (MulAut E)) (hne : A ≠ ⊤)
    (P : Sylow 2 A) (hP : Nat.card P = 8) : Group.IsSolvable A := by
  let e : MulAut E ≃* Matrix.PSL3Two.PSL :=
    (elementaryEight_mulAut_equiv_GL E hE).some.trans
      (Matrix.PSL3Two.equivGL.symm.trans Matrix.PSL3Two.equiv)
  let H := A.map e.toMonoidHom
  let f := e.toMonoidHom.comp A.subtype
  have hf : Function.Injective f := e.injective.comp A.subtype_injective
  let R := (P : Subgroup A).map f
  have hR : Nat.card R = 8 := (card_map_of_injective hf).trans hP
  let S : Sylow 2 Matrix.PSL3Two.PSL := Sylow.ofCard R (by
    rw [hR,Matrix.PSL3Two.card_PSL]
    decide +kernel)
  have hSH : (S : Subgroup Matrix.PSL3Two.PSL) ≤ H := by
    rintro x ⟨a,_,rfl⟩
    exact ⟨a,a.property,rfl⟩
  have hHne : H ≠ ⊤ := by
    intro hh
    apply hne
    apply Subgroup.map_injective (f := e.toMonoidHom) e.injective
    rw [← MonoidHom.range_eq_map]
    exact hh.trans (MonoidHom.range_eq_top.mpr e.surjective).symm
  obtain ⟨K,hK,hHK⟩ := (eq_top_or_exists_le_coatom H).resolve_left hHne
  obtain ⟨K1,K2,_,_,_,_,hK1,hK2,hclass⟩ := Matrix.PSL3Two.sylow_parabolics S
  have hcardK : Nat.card K = 24 := by
    rcases (hclass K hK).mp (hSH.trans hHK) with rfl | rfl
    · exact hK1
    · exact hK2
  have hd : Nat.card A ∣ 24 := by
    have hh := card_dvd_of_le hHK
    rw [hcardK,show Nat.card H = Nat.card A from card_map_of_injective e.injective] at hh
    exact hh
  have hi := P.toSubgroup.card_mul_index
  rw [hP] at hi
  have hbound := Nat.le_of_dvd (by decide : 0 < 24) hd
  let : Group.IsNilpotent P := P.isPGroup'.isNilpotent
  exact P.toSubgroup.isSolvable_of_index_le_four (by omega)

private theorem two_subgroup_card_dvd_eight
    {H : Type*} [Group H] [Finite H] (hH : Nat.card H = 168)
    (P : Subgroup H) (hP : IsPGroup 2 P) : Nat.card P ∣ 8 := by
  have hd : Nat.card P ∣ 8 * 21 := by simpa only [hH] using P.card_subgroup_dvd_card
  have hc : Nat.Coprime (Nat.card P) 21 := by
    obtain ⟨n,hn⟩ := hP.exists_card_eq
    rw [hn]
    exact (by decide : Nat.Coprime 2 21).pow_left n
  exact hc.dvd_mul_right.mp hd

/-- A two-core-free elementary-eight automizer with four-divisible order
is the full automorphism group. The proof uses the actual binary plane
parabolics and the small Sylow-order-four theorem. -/
theorem elementaryEight_automizer_eq_top_of_pCore_eq_bot
    (E : Type*) [Group E] [Finite E] [IsElementaryAbelian 2 E]
    (hE : Nat.card E = 8) (A : Subgroup (MulAut E))
    (hcore : pCore 2 A = ⊥) (hfour : 4 ∣ Nat.card A) : A = ⊤ := by
  by_contra hne
  let P : Sylow 2 A := Classical.choice inferInstance
  have hd : Nat.card P ∣ 8 := by
    let R := (P : Subgroup A).map A.subtype
    have hR : Nat.card R = Nat.card P := card_map_of_injective A.subtype_injective
    rw [← hR]
    exact two_subgroup_card_dvd_eight (card_mulAut_of_elementary_eight E hE)
      R (P.isPGroup'.map A.subtype)
  have hf : 4 ∣ Nat.card P := P.pow_dvd_card_of_pow_dvd_card (n := 2) hfour
  have hc : Nat.card P = 4 ∨ Nat.card P = 8 := by
    have hm := Nat.mem_divisors.mpr ⟨hd,by decide⟩
    have hd8 : (8 : ℕ).divisors = {1,2,4,8} := by decide
    rw [hd8] at hm
    simp only [Finset.mem_insert,Finset.mem_singleton] at hm
    have hge := Nat.le_of_dvd Nat.card_pos hf
    omega
  have hs : Group.IsSolvable A := by
    rcases hc with h4 | h8
    · exact isSolvable_of_elementary_eight_automorphisms_sylow_four E hE A P h4
    · exact isSolvable_of_proper_elementary_eight_sylow_eight E hE A hne P h8
  let := hs
  have hh := four_le_card_pCore_of_solvable_elementary_eight_automorphisms E hE A hfour
  rw [hcore,Nat.card_unique] at hh
  omega

/-- A two-core-free elementary-eight automizer with a two-group point
stabilizer has two-part at most two. This is the precise rank-three action
obstruction in Aschbacher--Smith 13.9.8. -/
theorem not_four_dvd_card_elementaryEight_automizer_of_pgroup_stabilizer
    (E : Type*) [Group E] [Finite E] [IsElementaryAbelian 2 E]
    (hE : Nat.card E = 8) (A : Subgroup (MulAut E))
    (hcore : pCore 2 A = ⊥) (v : E)
    (hstab : IsPGroup 2 (stabilizer A v)) : ¬ 4 ∣ Nat.card A := by
  intro hfour
  have htop := elementaryEight_automizer_eq_top_of_pCore_eq_bot E hE A hcore hfour
  have hA : Nat.card A = 168 := by
    rw [htop,card_top]
    exact card_mulAut_of_elementary_eight E hE
  have hs : Nat.card (stabilizer A v) ≤ 8 :=
    Nat.le_of_dvd (by decide) (two_subgroup_card_dvd_eight hA _ hstab)
  have ho : Nat.card (orbit A v) ≤ 8 := by
    rw [← hE]
    exact Nat.card_le_card_of_injective Subtype.val Subtype.val_injective
  have hm := Nat.card_congr (orbitProdStabilizerEquivGroup A v)
  rw [Nat.card_prod,hA] at hm
  have hprod := Nat.mul_le_mul ho hs
  omega

/-- The same action obstruction covers all elementary groups of order at
most eight; orders one, two, and four have automorphism two-part at most two. -/
theorem not_four_dvd_card_small_elementary_automizer_of_pgroup_stabilizer
    (E : Type*) [Group E] [Finite E] [IsElementaryAbelian 2 E]
    (hE : Nat.card E ≤ 8) (A : Subgroup (MulAut E))
    (hcore : pCore 2 A = ⊥) (v : E)
    (hstab : IsPGroup 2 (stabilizer A v)) : ¬ 4 ∣ Nat.card A := by
  obtain ⟨n,hn⟩ := (IsElementaryAbelian.isPGroup 2 E).exists_card_eq
  have hnle : n ≤ 3 := by
    by_contra! hh
    have hp := Nat.pow_le_pow_right (by decide : 0 < 2) (show 4 ≤ n by omega)
    rw [← hn] at hp
    norm_num at hp
    omega
  interval_cases n
  · have hc : Nat.card E = 1 := by simpa using hn
    let : Subsingleton E := (Nat.card_eq_one_iff_unique.mp hc).1
    let : Subsingleton (MulAut E) := ⟨fun a b => MulEquiv.ext (fun x => Subsingleton.elim _ _)⟩
    have hAut : Nat.card (MulAut E) = 1 := Nat.card_unique
    intro hf
    have hd := hf.trans A.card_subgroup_dvd_card
    norm_num [hAut] at hd
  · have hc : Nat.card E = 2 := by simpa using hn
    let : IsCyclic E := isCyclic_of_prime_card hc
    have hAut : Nat.card (MulAut E) = 1 := by rw [IsCyclic.card_mulAut,hc]; norm_num
    intro hf
    have hd := hf.trans A.card_subgroup_dvd_card
    norm_num [hAut] at hd
  · have hc : Nat.card E = 4 := by simpa using hn
    let : Nontrivial E := Finite.one_lt_card_iff_nontrivial.mp (by omega)
    let : IsKleinFour E := ⟨hc,IsElementaryAbelian.exponent_eq_prime⟩
    intro hf
    have hd := hf.trans A.card_subgroup_dvd_card
    norm_num [IsKleinFour.card_mulAut E] at hd
  · exact not_four_dvd_card_elementaryEight_automizer_of_pgroup_stabilizer
      E (by simpa using hn) A hcore v hstab
