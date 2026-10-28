module

public import Glauberman.DicksonClassification
public import GorensteinWalter.PSL2DihedralSylow
public import GorensteinWalter.PGL2Cardinality
public import Mathlib.LinearAlgebra.Projectivization.PSL.PSL2
public import Mathlib.GroupTheory.IsPerfect

/-!
# Odd-prime subgroups in solvable Sylow overgroups of PSL₂

Over an odd finite field, a solvable subgroup containing a full Sylow
two-subgroup has cyclic p-subgroups for every prime p > 3. Dickson's
classification reduces this to dihedral and small groups. The elementary
and elementary-by-cyclic rows cannot contain the noncyclic ambient Sylow
two-subgroup. Solvability reduces projective subfield rows to field order
three. The remaining groups have cyclic odd-prime subgroups by direct
rotation or order arguments.

Source: Huppert II.8.27 (Dickson), applied in Aschbacher–Smith A.3.15(1),
printed pp.50–51. The accompanying original-source consumer retains the
literal Sylow intersection and permuting p-subgroup.
-/

public noncomputable section
open Subgroup BenderSuzuki.MatrixGroups
open scoped Pointwise
namespace Theory.PSL2.OddSylowProducts

private theorem cyclic_of_small_card {G : Type*} [Group G] [Finite G]
    {p : ℕ} [Fact p.Prime] (hp : 3 < p) (hG : IsPGroup p G)
    (hc : Nat.card G ∣ 120) : IsCyclic G := by
  obtain ⟨a,ha⟩ := hG.exists_card_eq
  have ha1 : a ≤ 1 := by
    by_contra h
    have hs : p ^ 2 ∣ 120 := (pow_dvd_pow p (by omega : 2 ≤ a)).trans (ha ▸ hc)
    have hl := Nat.le_of_dvd (by decide : 0 < 120) hs
    have hbound : p ≤ 10 := by nlinarith
    interval_cases p
    all_goals norm_num at hs
  apply isCyclic_of_card_dvd_prime (p := p)
  rw [ha]
  interval_cases a <;> simp

private theorem cyclic_of_odd_dihedral_embedding
    {G : Type*} [Group G] [Finite G] {n : ℕ} (hn : n ≠ 0)
    (e : G →* DihedralGroup n) (he : Function.Injective e)
    (ho : Odd (Nat.card G)) : IsCyclic G := by
  let : NeZero n := ⟨hn⟩
  let C := zpowers (DihedralGroup.r 1 : DihedralGroup n)
  have hmem (x : G) : e x ∈ C := by
    cases hx : e x with
    | r i =>
      have h := C.pow_mem (mem_zpowers (DihedralGroup.r 1)) i.val
      simpa only [DihedralGroup.r_one_pow, ZMod.natCast_zmod_val] using h
    | sr i =>
      have hd : 2 ∣ Nat.card G := by
        rw [← DihedralGroup.orderOf_sr i, ← hx, orderOf_injective e he]
        exact orderOf_dvd_natCard x
      exact (ho.not_two_dvd_nat hd).elim
  exact isCyclic_of_injective (e.codRestrict C hmem)
    (fun _ _ h => he (congrArg Subtype.val h))

private theorem field_card_le_three_of_solvable
    (F : Type*) [Field F] [Finite F] [Group.IsSolvable (PSL2MatrixGroup F)] :
    Nat.card F ≤ 3 := by
  by_contra h
  have hfour : 4 ≤ Nat.card F := by omega
  obtain ⟨x,hx⟩ : IsCyclic Fˣ := inferInstance
  have hsq : (x : F)^2 ≠ 1 := by
    intro he
    grw [Nat.card_eq_card_units_add_one F, ← orderOf_eq_card_of_forall_mem_zpowers hx,
      orderOf_le_of_pow_eq_one zero_lt_two (Units.ext (by simpa using he))] at hfour
    omega
  let : Group.IsPerfect (PSL2MatrixGroup F) :=
    ⟨SL2Simple.PSL_commutator_eq_top ⟨x,Units.ne_zero x,hsq⟩⟩
  exact Group.IsPerfect.not_isSolvable (PSL2MatrixGroup F) inferInstance

private theorem quotient_cyclic_of_complement
    {G : Type*} [Group G] (N C : Subgroup G) [N.Normal]
    (hC : IsCyclic C) (hd : Disjoint N C) (hjoin : N ⊔ C = ⊤) :
    IsCyclic (G ⧸ N) := by
  have hcomp : N.IsComplement' C := by
    refine ⟨mul_injective_of_disjoint hd, ?_⟩
    intro g
    have hg : g ∈ (N:Set G) * (C:Set G) := by
      rw [← normal_mul N C,hjoin]
      trivial
    obtain ⟨n,hn,c,hc,he⟩ := hg
    exact ⟨⟨⟨n,hn⟩,⟨c,hc⟩⟩,he⟩
  exact hcomp.symm.QuotientMulEquiv.isCyclic.mpr hC

private theorem cyclic_two_subgroup_of_odd_by_cyclic
    {G : Type*} [Group G] [Finite G] (N P : Subgroup G) [N.Normal]
    (ho : Odd (Nat.card N)) (hP : IsPGroup 2 P) [IsCyclic (G ⧸ N)] : IsCyclic P := by
  let q := QuotientGroup.mk' N
  have hi : Disjoint P N := disjoint_of_coprime_natCard
    (by
      obtain ⟨a,ha⟩ := hP.exists_card_eq
      rw [ha]
      exact ho.coprime_two_left.pow_left a)
  apply isCyclic_of_injective (q.comp P.subtype)
  rw [← MonoidHom.ker_eq_bot_iff]
  apply bot_unique
  intro x hx
  have hxN : x.val ∈ N := (QuotientGroup.eq_one_iff _).mp hx
  have hx1 : x.val = 1 := mem_bot.mp (hi.le_bot ⟨x.property,hxN⟩)
  exact Subtype.ext hx1


/-- Every large odd-prime subgroup of a solvable Sylow-two overgroup in
odd PSL₂ is cyclic. -/
theorem isCyclic_of_solvable_sylow_overgroup
    {F : Type*} [Field F] [Finite F] {q f p : ℕ} [Fact q.Prime] [Fact p.Prime]
    (hF : Nat.card F = q ^ f) (ho : Odd q) (hp : 3 < p)
    (S : Sylow 2 (PSL2MatrixGroup F)) (H : Subgroup (PSL2MatrixGroup F))
    (hSH : (S : Subgroup _) ≤ H) [Group.IsSolvable H]
    (B : Subgroup H) (hB : IsPGroup p B) : IsCyclic B := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hf : f ≠ 0 := by
    intro hz
    have hc : Nat.card F = 1 := by simpa only [hz,pow_zero] using hF
    exact (Finite.one_lt_card (α := F)).ne' hc
  have hoddF : GorensteinWalter.IsOddPrimePower (Nat.card F) :=
    ⟨q,f,Fact.out,ho,Nat.one_le_iff_ne_zero.mpr hf,hF⟩
  have hSnot : ¬ IsCyclic S := by
    obtain ⟨m,hm,⟨e⟩⟩ := GorensteinWalter.psl2_odd_hasDihedralSylowTwo_model F hoddF S
    intro hc
    exact DihedralGroup.not_isCyclic
      (ne_of_gt (Nat.one_lt_pow (Nat.ne_of_gt hm) (by decide))) (e.isCyclic.mp hc)
  let SN := (S : Subgroup (PSL2MatrixGroup F)).subgroupOf H
  have hSN : IsPGroup 2 SN := S.isPGroup'.of_equiv (subgroupOfEquivOfLe hSH).symm
  have hSNnot : ¬ IsCyclic SN := fun hc => hSnot ((subgroupOfEquivOfLe hSH).isCyclic.mp hc)
  have hbo : Odd (Nat.card B) := by
    obtain ⟨a,ha⟩ := hB.exists_card_eq
    rw [ha]
    exact ((Fact.out : p.Prime).odd_of_ne_two (by omega)).pow
  have hsmall (hc : Nat.card H ∣ 120) : IsCyclic B :=
    cyclic_of_small_card hp hB (card_subgroup_dvd_card B |>.trans hc)
  rcases Glauberman.Dickson.huppert_II_8_27_dickson_psl2_subgroup_classification hF H with
    hEl | hCy | hDi | hA4 | hS4 | hA5 | hSD | hPSL | hPGL
  · let : IsElementaryAbelian q H := hEl
    obtain ⟨a,ha⟩ := (IsElementaryAbelian.isPGroup q H).exists_card_eq
    have htopodd : Odd (Nat.card (⊤ : Subgroup H)) := by simpa only [card_top,ha] using ho.pow (n := a)
    let : Subsingleton (H ⧸ (⊤ : Subgroup H)) := QuotientGroup.subsingleton_quotient_top
    let : IsCyclic (H ⧸ (⊤ : Subgroup H)) := inferInstance
    exact (hSNnot (cyclic_two_subgroup_of_odd_by_cyclic (⊤ : Subgroup H) SN htopodd hSN)).elim
  · let : IsCyclic H := hCy.choose_spec.2.2
    infer_instance
  · obtain ⟨n,_,hcard,⟨e⟩⟩ := hDi
    have hn : n ≠ 0 := by intro hn; have hpH := Nat.card_pos (α := H); simp [hn] at hcard; omega
    exact cyclic_of_odd_dihedral_embedding hn (e.toMonoidHom.comp B.subtype)
      (e.injective.comp B.subtype_injective) hbo
  · obtain ⟨e⟩ := hA4.2
    apply hsmall
    rw [Nat.card_congr e.toEquiv, alternatingGroup.card_of_card_eq_four (by simp)]
    decide
  · obtain ⟨e⟩ := hS4.2
    apply hsmall
    rw [Nat.card_congr e.toEquiv, Nat.card_perm]
    norm_num [Nat.card_eq_fintype_card, Nat.factorial]
  · obtain ⟨e⟩ := hA5.2
    apply hsmall
    rw [Nat.card_congr e.toEquiv,nat_card_alternatingGroup]
    norm_num [Nat.card_eq_fintype_card, Nat.factorial]
  · obtain ⟨a,c,_,_,N,C,hN,hNE,hNc,hCc,_,hd,hjoin⟩ := hSD
    let := hN
    let : IsCyclic (H ⧸ N) := quotient_cyclic_of_complement N C hCc hd hjoin
    have hNo : Odd (Nat.card N) := by rw [hNc]; exact ho.pow
    exact (hSNnot (cyclic_two_subgroup_of_odd_by_cyclic N SN hNo hSN)).elim
  · obtain ⟨m,hm,_,⟨e⟩⟩ := hPSL
    let K := GaloisField q m
    let : Group.IsSolvable (PSL2MatrixGroup K) := Group.isSolvable_of_surjective (f := e.toMonoidHom) e.surjective
    have hKcard : Nat.card K = q ^ m := GaloisField.card q m hm
    have hle := field_card_le_three_of_solvable K
    have hq3 : 3 ≤ q := by have hq2 := (Fact.out : q.Prime).two_le; have := ho.not_two_dvd_nat; omega
    have hge : 3 ≤ Nat.card K := by
      rw [hKcard]
      exact hq3.trans (by simpa only [pow_one] using Nat.pow_le_pow_right (by omega : 1 ≤ q) (Nat.one_le_iff_ne_zero.mpr hm))
    have hK3 : Nat.card K = 3 := by omega
    apply hsmall
    rw [Nat.card_congr e.toEquiv, GorensteinWalter.psl2_card_formula K
      ⟨q,m,Fact.out,ho,Nat.one_le_iff_ne_zero.mpr hm,hKcard⟩,hK3]
    decide
  · obtain ⟨m,hm,_,⟨e⟩⟩ := hPGL
    let K := GaloisField q m
    let : Group.IsSolvable (Matrix.ProjGenLinGroup (Fin 2) K) := Group.isSolvable_of_surjective (f := e.toMonoidHom) e.surjective
    let : Group.IsSolvable (PSL2MatrixGroup K) := Group.isSolvable_of_isSolvable_injective
      (Matrix.ProjectiveSpecialLinearGroup.toPGL_injective (n := Fin 2) (R := K))
    have hKcard : Nat.card K = q ^ m := GaloisField.card q m hm
    have hle := field_card_le_three_of_solvable K
    have hq3 : 3 ≤ q := by have hq2 := (Fact.out : q.Prime).two_le; have := ho.not_two_dvd_nat; omega
    have hge : 3 ≤ Nat.card K := by
      rw [hKcard]
      exact hq3.trans (by simpa only [pow_one] using Nat.pow_le_pow_right (by omega : 1 ≤ q) (Nat.one_le_iff_ne_zero.mpr hm))
    have hK3 : Nat.card K = 3 := by omega
    apply hsmall
    rw [Nat.card_congr e.toEquiv, GorensteinWalter.pgl2_card_formula K,hK3]
    decide

end Theory.PSL2.OddSylowProducts
