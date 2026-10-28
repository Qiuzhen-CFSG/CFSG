module
public import CFSG.Quasithin.ChapterE.Section02.Witnesses.BenderPlacement.OriginalModels
public import CFSG.Quasithin.ChapterE.Section02.Witnesses.QuotientLift.Source
public import Theory.SpecificGroups.SL2.UpperUnipotent
public import Theory.SpecificGroups.Suzuki.StandardSubgroups

/-!
# Source geometry for the strict Bender actor bounds

The original two-conjugate pair has nontrivial star image. In the odd
dihedral model that image has order two. In the binary linear model the
same stored Borel contains the image Sylow, forcing that Sylow to be the
upper-root group. TI restricts along the actual pair inclusion.

These are the geometric inputs to E.2.13–15, printed pp.224–228; no new
placement or classification premise is imposed on the marked witness.
-/

public section
open Matrix (SpecialLinearGroup)
open Subgroup Theory.GroupTheory
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.ChapterE.Witnesses.BenderPlacement
open TwoConjugate
variable {I : Type*} [Group I] [Finite I]
  {T : Sylow 2 I} {V M : Subgroup I} {g : I}

theorem dihedral_star_card (h : Hypotheses T V M g) (hproper : V ≠ ⊤)
    {p a : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (e : (I ⧸ J M) ≃* DihedralGroup (p^a)) :
    Nat.card (V.map (QuotientGroup.mk' (J M))) = 2 := by
  let := h.elementary
  let q := QuotientGroup.mk' (J M)
  let E := V.map q
  have hEp : IsPGroup 2 E := (IsElementaryAbelian.isPGroup 2 V).map q
  have hne : E ≠ ⊥ := by
    intro hh
    have hv : V ≤ J M := by simpa [q] using (map_eq_bot_iff V).mp hh
    exact h.V_not_le_twoCore hproper (h.le_twoCore_of_le_J V
      (IsElementaryAbelian.isPGroup 2 V) hv)
  have hd : Nat.card E ∣ 2 * p^a := by
    have hh := E.card_subgroup_dvd_card
    rwa [Nat.card_congr e.toEquiv, DihedralGroup.nat_card] at hh
  obtain ⟨k,hk⟩ := hEp.exists_card_eq
  have hc : Nat.Coprime (Nat.card E) (p^a) := by
    rw [hk]
    exact (Nat.coprime_two_left.mpr (hp.odd_of_ne_two hp2)).pow k a
  have hd2 := hc.dvd_of_dvd_mul_right hd
  exact ((Nat.dvd_prime Nat.prime_two).mp hd2).resolve_left
    (fun he => hne (Subgroup.card_eq_one.mp he))

theorem linear_sylow_borel {F : Type*} [Field F] [Finite F] [CharP F 2]
    (h : Hypotheses T V M g) (e : (I ⧸ J M) ≃* SL(2,F))
    (hb : (M.map (QuotientGroup.mk' (J M))).map e.toMonoidHom =
      SpecialLinearGroup.rankOneBorel F) :
    ∃ S : Sylow 2 SL(2,F),
      (T : Subgroup I).map (e.toMonoidHom.comp (QuotientGroup.mk' (J M))) = (S : Subgroup SL(2,F)) ∧
      M.map (e.toMonoidHom.comp (QuotientGroup.mk' (J M))) = normalizer (S : Set SL(2,F)) := by
  let q := e.toMonoidHom.comp (QuotientGroup.mk' (J M))
  let S := T.mapSurjective (f := q) (e.surjective.comp (QuotientGroup.mk'_surjective _))
  have hM : M.map q = SpecialLinearGroup.rankOneBorel F := by
    simpa only [q, ← Subgroup.map_map] using hb
  have hSN : (S : Subgroup SL(2,F)) ≤ normalizer (SpecialLinearGroup.upperUnipotent F : Set _) := by
    exact (map_mono (h.sylow_le_normalizer.trans h.normalizer_le)).trans hM.le
  have hSU : (S : Subgroup SL(2,F)) ≤ SpecialLinearGroup.upperUnipotent F := by
    calc
      _ = (S : Subgroup SL(2,F)) ⊓ normalizer (SpecialLinearGroup.upperUnipotent F : Set _) :=
        (inf_eq_left.mpr hSN).symm
      _ = (S : Subgroup SL(2,F)) ⊓ (SpecialLinearGroup.upperUnipotentSylow F 2 : Subgroup _) :=
        S.isPGroup'.inf_normalizer_sylow (SpecialLinearGroup.upperUnipotentSylow F 2)
      _ ≤ _ := inf_le_right
  have heq : S = SpecialLinearGroup.upperUnipotentSylow F 2 :=
    Sylow.ext (S.is_maximal' (SpecialLinearGroup.upperUnipotentSylow F 2).isPGroup' hSU).symm
  refine ⟨S,rfl,?_⟩
  rw [hM,heq]
  rfl

omit [Finite I] in
theorem QuotientModel.card_ne_one {d : ℕ} (model : QuotientModel M d) :
    Nat.card (I ⧸ M.normalCore) ≠ 1 := by
  cases model with
  | dihedral hd p a hp hp2 ha e =>
    rw [Nat.card_congr e.toEquiv,DihedralGroup.nat_card]
    omega
  | linear hd e hb =>
    have hc := Nat.card_le_card_of_injective
      (SpecialLinearGroup.upperUnipotent (GaloisField 2 d)).subtype
      (SpecialLinearGroup.upperUnipotent (GaloisField 2 d)).subtype_injective
    rw [SpecialLinearGroup.card_upperUnipotent,
      GaloisField.card 2 d (by omega)] at hc
    rw [Nat.card_congr e.toEquiv]
    have hh : 1 < 2^d := one_lt_pow₀ (by decide) (by omega)
    omega
  | suzuki m hm hd e hb =>
    have hc := Nat.card_le_card_of_injective
      (BenderSuzuki.MatrixGroups.SuzukiRootSubgroup m).subtype
      (BenderSuzuki.MatrixGroups.SuzukiRootSubgroup m).subtype_injective
    rw [BenderSuzuki.MatrixGroups.suzukiRootSubgroup_card m hm] at hc
    rw [Nat.card_congr e.toEquiv]
    have hh : 1 < (2^(2*m+1))^2 := one_lt_pow₀
      (one_lt_pow₀ (by decide) (by omega)) (by decide)
    omega

variable {H : Type*} [Group H] {A B W : Subgroup H}
omit [Finite I] in
theorem restrict_TI (hW : W ≤ A)
    (hTI : ∀ x ∈ B, W ⊓ W.map (MulAut.conj x).toMonoidHom = ⊥ ∨
      W.map (MulAut.conj x).toMonoidHom = W) :
    ∀ x ∈ B.subgroupOf A, W.subgroupOf A ⊓
      (W.subgroupOf A).map (MulAut.conj x).toMonoidHom = ⊥ ∨
      (W.subgroupOf A).map (MulAut.conj x).toMonoidHom = W.subgroupOf A := by
  intro x hx
  have hmap : ((W.subgroupOf A).map (MulAut.conj x).toMonoidHom).map A.subtype =
      W.map (MulAut.conj (x:H)).toMonoidHom := by
    rw [map_map]
    have hc : A.subtype.comp (MulAut.conj x).toMonoidHom =
        (MulAut.conj (x:H)).toMonoidHom.comp A.subtype := by ext y; rfl
    rw [hc, ← map_map,map_subgroupOf_eq_of_le hW]
  rcases hTI x hx with he | he
  · left
    apply map_injective A.subtype_injective
    rw [Subgroup.map_inf _ _ _ A.subtype_injective,map_subgroupOf_eq_of_le hW,hmap,he,Subgroup.map_bot]
  · right
    apply map_injective A.subtype_injective
    rw [hmap,map_subgroupOf_eq_of_le hW,he]
end CFSG.Quasithin.ChapterE.Witnesses.BenderPlacement
