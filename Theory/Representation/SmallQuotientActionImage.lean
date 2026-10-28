module
public import Theory.Representation.BinaryOffender.ActionImage
public import Theory.GroupTheory.PCoreKernelRange

/-!
# Exact section kernels over quotients of order dividing twenty

For a binary representation killing the kernel of a core-free quotient of
order dividing twenty, a nontrivial core-free action image forces equality
of the two kernels. The action image has order divisible by five. Hence the
remaining normal kernel has order dividing four and is trivial. The first
isomorphism theorem retains every original quotient representative.

This is the small solvable replacement-section step in DGS, Groups and
Graphs (1985), 6.4--6.5, pp.120--122. It allows the opposite-core closure to
have a proper image in the enlarged quotient, as can occur for Sz(2).
-/

public noncomputable section
open Subgroup Representation.BinaryOffender
namespace Representation
variable {H D W : Type*} [Group H] [Finite H] [Group D] [Finite D]
  [AddCommGroup W] [Module (ZMod 2) W] [Nontrivial W]

private theorem five_dvd_of_core_free_card_dvd_twenty {K : Type*} [Group K] [Finite K]
    (hc : Nat.card K ∣ 20) (hcore : pCore 2 K = ⊥) (hne : 1 < Nat.card K) :
    5 ∣ Nat.card K := by
  by_contra hn
  have hcop : Nat.Coprime (Nat.card K) 5 :=
    ((Nat.Prime.coprime_iff_not_dvd (by decide : Nat.Prime 5)).mpr hn).symm
  have hdiv : Nat.card K ∣ 4 := hcop.dvd_mul_right.mp hc
  have hp : IsPGroup 2 K := isPGroup_iff_card_dvd_pow.mpr ⟨2,hdiv⟩
  have ht : (⊤ : Subgroup K) ≤ pCore 2 K :=
    le_sSup ⟨inferInstance,hp.of_equiv (topEquiv (G := K)).symm⟩
  have he : (⊤ : Subgroup K) = ⊥ := le_bot_iff.mp (hcore ▸ ht)
  have hh := congrArg (fun C : Subgroup K => Nat.card C) he
  rw [card_top,card_bot] at hh
  omega

/-- A nonzero fixed-point-free section over a core-free quotient of order dividing twenty
has exactly the given quotient kernel. -/
theorem ker_eq_of_quotient_card_dvd_twenty (ρ : Representation (ZMod 2) H W)
    (q : H →* D) (hq : Function.Surjective q) (hle : q.ker ≤ ρ.ker)
    (hD : Nat.card D ∣ 20) (hcore : pCore 2 D = ⊥)
    (himage : pCore 2 (actionImage ρ) = ⊥) (hf : fixedSpace ρ ⊤ = ⊥) :
    ρ.ker = q.ker := by
  have hnt : ρ.ker ≠ ⊤ := by
    intro ht
    have hall (w : W) : w = 0 := by
      have hw : w ∈ fixedSpace ρ ⊤ := by
        intro g
        have he : ρ g = 1 := by
          change g.val ∈ ρ.ker
          rw [ht]
          exact mem_top _
        change ρ g w = w
        rw [he]
        rfl
      simpa only [hf,Submodule.mem_bot] using hw
    obtain ⟨w,hw⟩ := exists_ne (0 : W)
    exact hw (hall w)
  have hi : ρ.ker.index = Nat.card (actionImage ρ) := by
    have he : ρ.asGroupHom.ker = ρ.ker := by
      ext x
      exact ⟨fun hh => congrArg Units.val hh,fun hh => Units.ext hh⟩
    rw [←he]
    exact index_ker ρ.asGroupHom
  let N := ρ.ker.map q
  let : N.Normal := (inferInstance : ρ.ker.Normal).map q hq
  have hN : N.index = Nat.card (actionImage ρ) :=
    ((ρ.ker).index_map_eq hq hle).trans hi
  have hcard : Nat.card (actionImage ρ) ∣ 20 :=
    hN ▸ (index_dvd_card N).trans hD
  have hne : 1 < Nat.card (actionImage ρ) := by
    have hp : 0 < Nat.card (actionImage ρ) := Nat.card_pos
    have hn1 : Nat.card (actionImage ρ) ≠ 1 := fun hh => hnt (index_eq_one.mp (hi.trans hh))
    omega
  have h5 : 5 ∣ N.index := hN.symm ▸ five_dvd_of_core_free_card_dvd_twenty hcard himage hne
  have hsmall : Nat.card N ∣ 4 := by
    have hh : Nat.card N * 5 ∣ 20 :=
      (Nat.mul_dvd_mul_left (Nat.card N) h5).trans (N.card_mul_index ▸ hD)
    exact (Nat.mul_dvd_mul_iff_right (by decide : 0 < 5)).mp hh
  have hp : IsPGroup 2 N := isPGroup_iff_card_dvd_pow.mpr ⟨2,hsmall⟩
  have hb : N = ⊥ := bot_unique (hcore ▸ (le_sSup ⟨inferInstance,hp⟩ : N ≤ pCore 2 D))
  exact le_antisymm ((map_eq_bot_iff ρ.ker).mp hb) hle

/-- The literal faithful image is the specified quotient of order dividing twenty, with its original map retained. -/
theorem actionImage_equiv_of_quotient_card_dvd_twenty (ρ : Representation (ZMod 2) H W)
    (q : H →* D) (hq : Function.Surjective q) (hle : q.ker ≤ ρ.ker)
    (hD : Nat.card D ∣ 20) (hcore : pCore 2 D = ⊥)
    (himage : pCore 2 (actionImage ρ) = ⊥) (hf : fixedSpace ρ ⊤ = ⊥) :
    ρ.ker = q.ker ∧ ∃ e : actionImage ρ ≃* D, ∀ h, e (actionHom ρ h) = q h := by
  have hk := ker_eq_of_quotient_card_dvd_twenty ρ q hq hle hD hcore himage hf
  have ha : (actionHom ρ).ker = q.ker := by
    change ρ.asGroupHom.rangeRestrict.ker = q.ker
    rw [MonoidHom.ker_rangeRestrict]
    have he : ρ.asGroupHom.ker = ρ.ker := by
      ext h
      exact ⟨fun hh => congrArg Units.val hh, fun hh => Units.ext hh⟩
    exact he.trans hk
  let e := (QuotientGroup.quotientKerEquivOfSurjective
    (actionHom ρ) ρ.asGroupHom.rangeRestrict_surjective).symm |>.trans
      ((QuotientGroup.quotientMulEquivOfEq ha).trans
        (QuotientGroup.quotientKerEquivOfSurjective q hq))
  refine ⟨hk,e,?_⟩
  intro h
  have hh := (QuotientGroup.quotientKerEquivOfSurjective
    (actionHom ρ) ρ.asGroupHom.rangeRestrict_surjective).symm_apply_apply
      (QuotientGroup.mk' (actionHom ρ).ker h)
  change e (actionHom ρ h) = q h
  dsimp only [e,MulEquiv.trans_apply]
  rw [show (QuotientGroup.quotientKerEquivOfSurjective (actionHom ρ)
    ρ.asGroupHom.rangeRestrict_surjective).symm (actionHom ρ h) =
    QuotientGroup.mk' (actionHom ρ).ker h from hh]
  rfl
end Representation
