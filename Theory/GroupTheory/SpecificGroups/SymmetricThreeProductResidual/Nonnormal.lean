module
public import Theory.GroupTheory.SpecificGroups.SymmetricThreeProductResidual
public import Theory.GroupTheory.PResidual.FiniteImage
/-!
# Faithful projections of subgroups with nonnormal two-residual

In S₃ × S₃, a nonnormal embedded two-residual has order three: order one
and order nine would make it normal. Both coordinate projections of its
nonidentity elements are nontrivial, since the two coordinate axes are
normal. Its normalizer therefore has no two-element in the kernel of a
coordinate projection. A kernel element is cubic and lies in the residual,
whose projection is faithful. Thus the projection of the entire subgroup
is faithful. If the subgroup contains an involution, its image is all S₃.

The finite identities concern individual permutations of three letters;
no subgroup enumeration or unproved model classification is used.
Application: the literal Omega intersection action in Aschbacher--Smith
15.2.18(3ii), printed p.1113.
-/

public section
open Subgroup
namespace SymmetricThreeProductResidual
local notation "S3" => Equiv.Perm (Fin 3)
local notation "Pair" => S3 × S3

private theorem cubic_powers_cases {D : Type*} [Group D] [Finite D]
    (a x : D) (ha : orderOf a = 3) (hx : x ∈ zpowers a) :
    x = 1 ∨ x = a ∨ x = a^2 := by
  classical
  rw [mem_zpowers_iff_mem_range_orderOf,ha] at hx
  obtain ⟨i,hi,hix⟩ := Finset.mem_image.mp hx
  have hi3 := Finset.mem_range.mp hi
  interval_cases i <;> simp_all

private theorem cube_conjugate_table : ∀ a b c : S3,
    a^3=1 → a≠1 → b^3=1 → b≠1 →
    ((a,c*b*c⁻¹) = (1,1) ∨ (a,c*b*c⁻¹) = (a,b) ∨
      (a,c*b*c⁻¹) = (a^2,b^2)) → c^3=1 := by
  decide +kernel

private theorem cubic_square_ne_one : ∀ a : S3, a^3=1 → a≠1 → a^2≠1 := by
  decide +kernel

private theorem nonnormal_residual_card (N : Subgroup Pair)
    (hn : ¬ ((pResidual 2 N).map N.subtype).Normal) :
    Nat.card ((pResidual 2 N).map N.subtype) = 3 := by
  let R := (pResidual 2 N).map N.subtype
  have hle : R ≤ pResidual 2 Pair := map_pResidual_le 2 N.subtype
  have hd : Nat.card R ∣ 9 := residual_card ▸ card_dvd_of_le hle
  have hcases : Nat.card R = 1 ∨ Nat.card R = 3 ∨ Nat.card R = 9 := by
    have hh := Nat.mem_divisors.mpr ⟨hd,by decide⟩
    have he : (9:ℕ).divisors = {1,3,9} := by decide
    rwa [he,Finset.mem_insert,Finset.mem_insert,Finset.mem_singleton] at hh
  rcases hcases with h1 | h3 | h9
  · have he := card_eq_one.mp h1
    exact (hn (show R.Normal by rw [he]; infer_instance)).elim
  · exact h3
  · have he : R = pResidual 2 Pair := eq_of_le_of_card_ge hle (by rw [h9,residual_card])
    exact (hn (show R.Normal by rw [he]; infer_instance)).elim

/-- A nonnormal residual makes the first projection faithful on the entire subgroup. -/
theorem fst_injective_of_nonnormal_residual (N : Subgroup Pair)
    (hn : ¬ ((pResidual 2 N).map N.subtype).Normal) :
    Function.Injective ((MonoidHom.fst S3 S3).comp N.subtype) := by
  classical
  let R := (pResidual 2 N).map N.subtype
  have hRc : Nat.card R = 3 := nonnormal_residual_card N hn
  have hRne : R ≠ ⊥ := by intro he; rw [he,card_bot] at hRc; contradiction
  obtain ⟨a,ha,hane⟩ := R.bot_or_exists_ne_one.resolve_left hRne
  have ha3 : a^3=1 := by
    have h := pow_card_eq_one' (x := (⟨a,ha⟩ : R))
    rw [hRc] at h
    exact congrArg Subtype.val h
  have hao : orderOf a = 3 := orderOf_eq_prime ha3 hane
  have hpow : zpowers a = R := eq_of_le_of_card_ge (zpowers_le.mpr ha)
    (by rw [Nat.card_zpowers,hao,hRc])
  have hRa : R ≤ (alternatingGroup (Fin 3)).prod (alternatingGroup (Fin 3)) := by
    rw [←residual_eq]
    exact map_pResidual_le 2 N.subtype
  have ha1 : a.1 ≠ 1 := by
    intro hz
    let A := (⊥ : Subgroup S3).prod (alternatingGroup (Fin 3))
    have hRA : R ≤ A := by
      rw [←hpow]
      exact zpowers_le.mpr ⟨hz,(hRa ha).2⟩
    have hc : Nat.card A = 3 := by
      rw [Nat.card_congr (prodEquiv _ _).toEquiv,Nat.card_prod,card_bot,one_mul,
        nat_card_alternatingGroup,Nat.card_fin]
      rfl
    have he : R = A := eq_of_le_of_card_ge hRA (by rw [hRc,hc])
    exact hn (show R.Normal by rw [he]; infer_instance)
  have ha2 : a.2 ≠ 1 := by
    intro hz
    let A := (alternatingGroup (Fin 3)).prod (⊥ : Subgroup S3)
    have hRA : R ≤ A := by
      rw [←hpow]
      exact zpowers_le.mpr ⟨(hRa ha).1,hz⟩
    have hc : Nat.card A = 3 := by
      rw [Nat.card_congr (prodEquiv _ _).toEquiv,Nat.card_prod,card_bot,mul_one,
        nat_card_alternatingGroup,Nat.card_fin]
      rfl
    have he : R = A := eq_of_le_of_card_ge hRA (by rw [hRc,hc])
    exact hn (show R.Normal by rw [he]; infer_instance)
  have hnorm : N ≤ normalizer (R : Set Pair) := by
    have hh := (pResidual 2 N).le_normalizer_map N.subtype
    simpa only [normalizer_eq_top,←MonoidHom.range_eq_map,range_subtype] using hh
  apply (MonoidHom.ker_eq_bot_iff _).mp
  apply bot_unique
  intro x hx
  have hx1 : x.val.1 = 1 := hx
  have hconj : x.val*a*x.val⁻¹ ∈ R :=
    (mem_normalizer_iff.mp (hnorm x.property) a).mp ha
  have hcases := cubic_powers_cases a (x.val*a*x.val⁻¹) hao (hpow.symm ▸ hconj)
  have ht : (a.1,x.val.2*a.2*x.val.2⁻¹) = (1,1) ∨
      (a.1,x.val.2*a.2*x.val.2⁻¹) = (a.1,a.2) ∨
      (a.1,x.val.2*a.2*x.val.2⁻¹) = (a.1^2,a.2^2) := by
    simpa only [Prod.ext_iff,Prod.fst_mul,Prod.snd_mul,Prod.fst_inv,Prod.snd_inv,
      Prod.pow_fst,Prod.pow_snd,Prod.fst_one,Prod.snd_one,hx1,one_mul,inv_one,mul_one]
      using hcases
  have hx3 : x^3=1 := by
    apply Subtype.ext
    exact Prod.ext (by simp [hx1]) (cube_conjugate_table a.1 a.2 x.val.2
      (congrArg Prod.fst ha3) ha1 (congrArg Prod.snd ha3) ha2 ht)
  have hxR : x.val ∈ R := mem_map_of_mem N.subtype
    (mem_pResidual_of_orderOf_coprime ((by decide : Nat.Coprime 2 3).of_dvd_right
      (orderOf_dvd_of_pow_eq_one hx3)))
  rcases cubic_powers_cases a x.val hao (hpow.symm ▸ hxR) with he | he | he
  · exact Subtype.ext he
  · exact (ha1 ((congrArg Prod.fst he).symm.trans hx1)).elim
  · exact (cubic_square_ne_one a.1 (congrArg Prod.fst ha3) ha1
      ((congrArg Prod.fst he).symm.trans hx1)).elim

/-- An even subgroup with nonnormal two-residual is an actual symmetric group. -/
theorem equiv_symmetricThree_of_nonnormal_residual (N : Subgroup Pair)
    (hn : ¬ ((pResidual 2 N).map N.subtype).Normal)
    (b : N) (hb : orderOf b = 2) : Nonempty (N ≃* S3) := by
  let f := (MonoidHom.fst S3 S3).comp N.subtype
  have hf : Function.Injective f := fst_injective_of_nonnormal_residual N hn
  have h3 : 3 ∣ Nat.card N := by
    have hc := nonnormal_residual_card N hn
    rw [card_map_of_injective N.subtype_injective] at hc
    simpa only [hc] using card_subgroup_dvd_card (pResidual 2 N)
  have h2 : 2 ∣ Nat.card N := hb ▸ orderOf_dvd_natCard b
  have hS : Nat.card S3 = 6 := by rw [Nat.card_perm,Nat.card_fin]; rfl
  have hd : Nat.card N ∣ 6 := hS ▸ card_dvd_of_injective f hf
  have hc : Nat.card N = 6 := by
    have hp := Nat.card_pos (α := N)
    have hu := Nat.le_of_dvd (by decide : 0 < 6) hd
    omega
  exact ⟨MulEquiv.ofBijective f ((Nat.bijective_iff_injective_and_card f).mpr
    ⟨hf,hc.trans hS.symm⟩)⟩
end SymmetricThreeProductResidual
