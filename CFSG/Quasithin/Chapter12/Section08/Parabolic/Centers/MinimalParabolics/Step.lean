module

public import CFSG.Quasithin.Chapter12.Section08.Parabolic.Centers.Intersections
public import Theory.GroupTheory.PResidual.PerfectCover
public import Theory.GroupAction.FixedIndexTwoResidual

/-!
# The corrected minimal-parabolic induction step

Write D = Z(I₂) and assume the already derived splitting Z(U) = D × V₁.
If J centralizes D, then J and its right conjugate by k centralize
B = D ∩ Dᵏ. The new two-residual R lies in H, so it also fixes V₁ and
normalizes Z(U). Counting two hyperplanes gives [Z(U):BV₁] ≤ 2. The
actual action of R has two-group image, and R's two-perfectness kills it.
Generation by J and R then gives centralization of D at the next stage.

The conclusion is deliberately centralization of D. The printed argument's
claim that the accumulated group centralizes Z(U) would incorrectly make
the first minimal-parabolic residual fix V₁. The two-group action theorem
here needs no elementary-abelian assumption on Z(U).

Source: Aschbacher–Smith, Lemma 12.8.10(5), printed p.854 (PDF p.871).
-/

open Subgroup
open scoped Pointwise commutatorElement
namespace CFSG.Quasithin.Chapter12.Section08
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
private theorem center_le_self (Z : Subgroup G) : centerIn Z ≤ Z := map_subtype_le _

omit [Finite G] in
private theorem center_centralizes (Z : Subgroup G) :
    centerIn Z ≤ centralizer (Z : Set G) := by
  rintro x ⟨a, ha, rfl⟩ b hb
  exact congrArg Subtype.val (mem_center_iff.mp ha ⟨b, hb⟩)

omit [Finite G] in
private theorem normalizer_normalizes_center (Z : Subgroup G) :
    normalizer (Z : Set G) ≤ normalizer (centerIn Z : Set G) := by
  intro g hg
  apply (conjugate_eq_iff _ g).mp
  rw [← centerIn_conjugate, (conjugate_eq_iff Z g).mpr hg]

omit [Finite G] in
private theorem card_mul_index (A B : Subgroup G) (h : A ≤ B) :
    Nat.card A * A.relIndex B = Nat.card B := by
  simpa only [relIndex_bot_left] using
    relIndex_mul_relIndex (⊥ : Subgroup G) A B bot_le h

private theorem complement_intersection_index (Z D A : Subgroup G)
    (hZ : Z = D ⊔ A) (hd : Disjoint D A) (hA : Nat.card A = 2)
    (hc : D ≤ centralizer (A : Set G)) (k : G)
    (hk : k ∈ normalizer (Z : Set G)) :
    ((D ⊓ conjugate D k) ⊔ A).relIndex Z ≤ 2 := by
  have hDZ : D ≤ Z := hZ ▸ le_sup_left
  have hAZ : A ≤ Z := hZ ▸ le_sup_right
  have hDkZ : conjugate D k ≤ Z := conjugate_le_of_normalizes hDZ k hk
  have hFZ : D ⊓ conjugate D k ≤ Z := inf_le_left.trans hDZ
  obtain ⟨e, _⟩ := exists_mulEquiv_prod_sup_of_disjoint_of_commuting D A hd hc
  have hcZ : Nat.card Z = Nat.card D * 2 := by
    rw [hZ, ← Nat.card_congr e.toEquiv, Nat.card_prod, hA]
  have hiD : D.relIndex Z = 2 := by
    have hh := card_mul_index D Z hDZ
    rw [hcZ] at hh
    exact Nat.eq_of_mul_eq_mul_left Nat.card_pos hh
  have hcDk : Nat.card (conjugate D k) = Nat.card D :=
    card_map_of_injective (MulAut.conj k⁻¹).injective
  have hiDk : (conjugate D k).relIndex Z = 2 := by
    have hh := card_mul_index (conjugate D k) Z hDkZ
    rw [hcDk, hcZ] at hh
    exact Nat.eq_of_mul_eq_mul_left Nat.card_pos hh
  have hiF : (D ⊓ conjugate D k).relIndex Z ≤ 4 := by
    have hh := relIndex_inf_le (H := D) (K := conjugate D k) (L := Z)
    simpa only [hiD, hiDk] using hh
  obtain ⟨f, _⟩ := exists_mulEquiv_prod_sup_of_disjoint_of_commuting
    (D ⊓ conjugate D k) A (hd.mono_left inf_le_left) (inf_le_left.trans hc)
  have hcE : Nat.card ((D ⊓ conjugate D k) ⊔ A : Subgroup G) =
      Nat.card (D ⊓ conjugate D k : Subgroup G) * 2 := by
    rw [← Nat.card_congr f.toEquiv, Nat.card_prod, hA]
  have hiFE : (D ⊓ conjugate D k).relIndex ((D ⊓ conjugate D k) ⊔ A) = 2 := by
    have hh := card_mul_index (D ⊓ conjugate D k) ((D ⊓ conjugate D k) ⊔ A) le_sup_left
    rw [hcE] at hh
    exact Nat.eq_of_mul_eq_mul_left Nat.card_pos hh
  have hh := relIndex_mul_relIndex (D ⊓ conjugate D k) ((D ⊓ conjugate D k) ⊔ A) Z
    le_sup_left (sup_le hFZ hAZ)
  rw [hiFE] at hh
  omega

private theorem centralizes_of_fixed_index (R Z D : Subgroup G)
    (hR : IsPPerfect 2 R) (hZ : IsPGroup 2 Z)
    (hn : R ≤ normalizer (Z : Set G)) (hc : R ≤ centralizer (D : Set G))
    (hi : D.relIndex Z ≤ 2) : R ≤ centralizer (Z : Set G) := by
  let ρ : R →* MulAut Z := Z.normalizerMonoidHom.comp (inclusion hn)
  have hf (r : R) (z : Z) (hz : z ∈ D.subgroupOf Z) : ρ r z = z := by
    apply Subtype.ext
    change (r : G) * z * (r : G)⁻¹ = z
    exact mul_inv_eq_iff_eq_mul.mpr (hc r.property z hz).symm
  intro r hr z hz
  have he := MulAut.eq_one_of_pPerfect_of_fixed_index_le_two ρ hR hZ
    (D.subgroupOf Z) hi hf ⟨r, hr⟩
  have hh := congrArg (fun a : MulAut Z => (a ⟨z, hz⟩ : G)) he
  change r * z * r⁻¹ = z at hh
  exact (mul_inv_eq_iff_eq_mul.mp hh).symm

namespace InvariantFlag
variable {T : Sylow 2 G} {V : Subgroup G} {n : ℕ}

/-- The corrected induction step acts on Z(U) only with the new residual R.
The accumulated group J may move the marked point. -/
public theorem center_induction_step (F : InvariantFlag T V n) (hn : 1 ≤ n)
    (L J R : Subgroup G) (hUT : F.U ≤ T)
    (hsplit : F.ZU = centerIn (F.I₂ L) ⊔ F.Vi 1)
    (hdisjoint : Disjoint (centerIn (F.I₂ L)) (F.Vi 1))
    (hJ : J ≤ centralizer (centerIn (F.I₂ L) : Set G))
    (hR : IsPPerfect 2 R) (hRH : R ≤ F.H)
    (k : G) (hk : k ∈ F.H)
    (hgen : J ⊔ R = J ⊔ conjugate J k) :
    J ⊔ R ≤ centralizer (centerIn (F.I₂ L) : Set G) := by
  let D := centerIn (F.I₂ L)
  let B := D ⊓ conjugate D k
  have hDZ : D ≤ F.ZU := hsplit ▸ le_sup_left
  have hpoint : Nat.card (F.Vi 1) = 2 := by simpa using F.card 1 hn
  have hHZ : F.H ≤ normalizer (F.ZU : Set G) :=
    (le_normalizer_conjugateSpanBy V F.H).trans (normalizer_normalizes_center F.U)
  have hHP : F.H ≤ centralizer (F.Vi 1 : Set G) :=
    normalizer_le_centralizer_of_card_two _ hpoint
  have hJk : conjugate J k ≤ centralizer (conjugate D k : Set G) :=
    (map_mono hJ).trans (map_centralizer_le_centralizer_image _ _)
  have hB : J ⊔ R ≤ centralizer (B : Set G) := by
    rw [hgen]
    exact sup_le (hJ.trans (centralizer_le inf_le_left))
      (hJk.trans (centralizer_le inf_le_right))
  have hRE : R ≤ centralizer ((B ⊔ F.Vi 1 : Subgroup G) : Set G) := by
    apply le_centralizer_iff.mpr
    apply sup_le
    · exact le_centralizer_iff.mp ((show R ≤ J ⊔ R from le_sup_right).trans hB)
    · exact le_centralizer_iff.mp (hRH.trans hHP)
  have hcomm : D ≤ centralizer (F.Vi 1 : Set G) :=
    hDZ.trans ((center_centralizes F.U).trans (centralizer_le
      ((F.le_seed 1).trans (le_conjugateSpanBy V F.H))))
  have hi := complement_intersection_index F.ZU D (F.Vi 1)
    hsplit hdisjoint hpoint hcomm k (hHZ hk)
  have hZtwo : IsPGroup 2 F.ZU :=
    T.isPGroup'.to_le ((center_le_self F.U).trans hUT)
  have hRZ := centralizes_of_fixed_index R F.ZU (B ⊔ F.Vi 1)
    hR hZtwo (hRH.trans hHZ) hRE hi
  exact sup_le hJ (hRZ.trans (centralizer_le hDZ))
end InvariantFlag
end CFSG.Quasithin.Chapter12.Section08
