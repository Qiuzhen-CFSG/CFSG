module
public import CFSG.Quasithin.ChapterC.Section01.BlockTypes.Basic
public import Theory.SpecificGroups.SL2.OddSylowCentralizer
public import Theory.SpecificGroups.SL2.NaturalStabilizer
public import Theory.GroupTheory.CoprimeSylowGeneration
/-!
# Odd fixed points with a central two-core supplement

The two-block source initially places each block's two-core in its natural
commutator module times its center. An element of a Sylow two subgroup fixed
by a nontrivial odd torus first lies in the two-core, by the SL₂ quotient.
Remove its central factor, then the natural-plane fixed-point calculation
makes the remaining module element central as well.

The ambient consumer retains the literal Sylow image and torus inclusion.
Source: Aschbacher–Smith, the two-block shadow argument, printed p.540;
compare the single-block fixed-point argument of 2.4.8(5), printed p.530.
-/
public section
open Subgroup Matrix
namespace CFSG.Quasithin.ChapterC
open Subgroup
open scoped MatrixGroups
variable {L : Type*} [Group L] [Finite L]

theorem IsL2EvenBlock.sylow_odd_fixed_le_core_center_of_core_le {n : ℕ} (hL : IsL2EvenBlock L n)
    (hcore : pCore 2 L ≤ blockU L ⊔ center L) (P : Sylow 2 L) (D : Subgroup L)
    (hodd : Odd (Nat.card D)) (hD : D ≠ ⊥) :
    (P : Subgroup L) ⊓ centralizer (D : Set L) ≤ center L ⊓ pCore 2 L := by
  obtain ⟨_,_,F,_,_,hF,_,ρ,⟨m⟩,hρ⟩ := hL
  let := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow
    (by simpa only [Nat.card_eq_fintype_card] using hF)
  let q : L →* SL(2,F) := m.quotientIso.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))
  have hq : Function.Surjective q := m.quotientIso.surjective.comp (QuotientGroup.mk'_surjective _)
  have hk : q.ker = pCore 2 L := by
    ext x
    exact m.quotientIso.map_eq_one_iff.trans (QuotientGroup.eq_one_iff _)
  have hdis : Disjoint (pCore 2 L) D := by
    obtain ⟨k,hk⟩ := (pCore_isPGroup (p := 2) (G := L)).exists_card_eq
    apply disjoint_of_coprime_natCard
    rw [hk]
    exact (Nat.coprime_two_left.mpr hodd).pow_left k
  obtain ⟨d,hd,hd1⟩ := D.bot_or_exists_ne_one.resolve_left hD
  have hqd : q d ≠ 1 := by
    intro he
    have hc : d ∈ pCore 2 L := hk ▸ he
    exact hd1 (disjoint_def.mp hdis hc hd)
  have hpow : (q d)^(Nat.card D) = 1 := by
    rw [←map_pow]
    have he := congrArg Subtype.val (pow_card_eq_one' (x := (⟨d,hd⟩ : D)))
    exact (congrArg q he).trans q.map_one
  rintro x ⟨hxP,hxD⟩
  have hcomm : Commute (q x) (q d) := by
    have he := (mem_centralizer_iff.mp hxD) d hd
    simpa only [Commute,SemiconjBy,map_mul] using (congrArg q he).symm
  have hqx : q x = 1 := Matrix.SpecialLinearGroup.eq_one_of_sylow_commutes_nontrivial_odd
    (P.mapSurjective hq) (q x) (q d) (mem_map_of_mem q hxP) hqd hodd hpow hcomm
  have hxcore : x ∈ pCore 2 L := hk ▸ hqx
  obtain ⟨y,hy,z,hz,hyz⟩ := mem_sup_of_normal_right.mp (hcore hxcore)
  have hyD : y ∈ centralizer (D : Set L) := by
    have hh := (centralizer (D : Set L)).mul_mem hxD
      ((centralizer (D : Set L)).inv_mem (center_le_centralizer _ hz))
    rw [← hyz, mul_inv_cancel_right] at hh
    exact hh
  let u : blockU L := ⟨y,hy⟩
  let v := m.moduleIso (QuotientGroup.mk' (blockFixed L) u)
  have hv : (q d).val *ᵥ v.toAdd = v.toAdd := by
    have hconj : blockConjugate L d u = u := by
      apply Subtype.ext
      change d*y*d⁻¹=y
      rw [(mem_centralizer_iff.mp hyD) d hd,mul_inv_cancel_right]
    have he := m.intertwining d u
    rw [hconj] at he
    have hh := congrArg Multiplicative.toAdd he
    rw [hρ] at hh
    exact hh.symm
  have hv0 : v.toAdd = 0 := by
    by_contra hvne
    have htwo := Matrix.SL2.pow_two_eq_one_of_nonzero_fixed (q d) v.toAdd hvne hv
    exact hqd (orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes
      (Nat.coprime_two_left.mpr hodd) (orderOf_dvd_of_pow_eq_one htwo)
      (orderOf_dvd_of_pow_eq_one hpow)))
  have hv1 : v = 1 := Multiplicative.toAdd.injective hv0
  have hu1 : QuotientGroup.mk' (blockFixed L) u = 1 := m.moduleIso.map_eq_one_iff.mp hv1
  have hu : u ∈ blockFixed L := (QuotientGroup.eq_one_iff u).mp hu1
  exact ⟨hyz ▸ (center L).mul_mem hu hz,hxcore⟩

/-- The centralizer form allows a central supplement to the natural module. -/
theorem IsL2EvenBlock.sylow_odd_fixed_le_center_of_core_le {n : ℕ} (hL : IsL2EvenBlock L n)
    (hcore : pCore 2 L ≤ blockU L ⊔ center L) (P : Sylow 2 L) (D : Subgroup L)
    (hodd : Odd (Nat.card D)) (hD : D ≠ ⊥) :
    (P : Subgroup L) ⊓ centralizer (D : Set L) ≤ center L :=
  (hL.sylow_odd_fixed_le_core_center_of_core_le hcore P D hodd hD).trans inf_le_left

end CFSG.Quasithin.ChapterC

namespace CFSG.Quasithin.ChapterC
variable {G : Type*} [Group G] [Finite G]

/-- Ambient form for the literal Sylow image and odd torus in an even block. -/
theorem IsL2EvenBlock.ambient_sylow_odd_fixed_le_center_of_core_le
    (L D : Subgroup G) {n : ℕ} (hL : IsL2EvenBlock L n)
    (hcore : pCore 2 L ≤ blockU L ⊔ center L) (P : Sylow 2 L)
    (hDL : D ≤ L) (hodd : Odd (Nat.card D)) (hD : D ≠ ⊥) :
    (P : Subgroup L).map L.subtype ⊓ centralizer (D : Set G) ≤
      (center L).map L.subtype := by
  have ho : Odd (Nat.card (D.subgroupOf L)) := by
    rwa [Nat.card_congr (subgroupOfEquivOfLe hDL).toEquiv]
  have hne : D.subgroupOf L ≠ ⊥ := by
    intro he
    have hh := congrArg (Subgroup.map L.subtype) he
    rw [map_subgroupOf_eq_of_le hDL,Subgroup.map_bot] at hh
    exact hD hh
  rintro x ⟨⟨y,hy,rfl⟩,hx⟩
  have hyc : y ∈ centralizer (D.subgroupOf L : Set L) := by
    apply mem_centralizer_iff.mpr
    intro z hz
    exact Subtype.ext ((mem_centralizer_iff.mp hx) z hz)
  exact mem_map_of_mem L.subtype
    (hL.sylow_odd_fixed_le_center_of_core_le hcore P (D.subgroupOf L) ho hne ⟨hy,hyc⟩)

end CFSG.Quasithin.ChapterC
