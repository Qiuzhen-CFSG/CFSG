module

public import Theory.SpecificGroups.LieType.F4RootCentralizer.OddTorus
public import Theory.GroupTheory.OddCentralInvertedPlane
public import CFSG.Quasithin.ChapterA.Section02.OddLie.ExceptionalStructure.F4Centralizer.DefiningRank

/-!
# Excluding every odd central cover of odd-characteristic F₄

If the defining prime divides the kernel, partial inversion makes the
preimage of the actual root plane abelian. Total inversion splits that plane
through the central kernel. A central element of order p then gives rank
three in the centralizer of the lifted fundamental involution.

For a defining-prime-coprime kernel, the proved root-cover transfer bounds
the complementary residual rank by one, contradicting the actual rank-two
plane. The two cases handle every finite odd central cover; neither
perfectness nor equality of the kernel with the full center is required.
The final application retains the original G/Z(G) identification.

Source: Aschbacher–Smith, A.2.17, printed p.39. Only the preceding odd-center
reduction remains with the source assembly; the F₄ defining-center and
post-reduction contradictions are both proved here.
-/

public noncomputable section
namespace CFSG.Quasithin.ChapterA.Section02.F4OddCover
open Subgroup Theory.GroupTheory
open ExceptionalSplit ExceptionalSplit.F4RootCentralizer
open scoped MatrixGroups
variable {G F : Type*} [Group G] [Finite G] [Field F] [Finite F]

omit [Finite F] in
private lemma two_ne_zero {p : ℕ} [Fact p.Prime] [CharP F p]
    (hp : p ≠ 2) : (2 : F) ≠ 0 := by
  intro h
  have hlt : 2 < p := lt_of_le_of_ne (Fact.out : p.Prime).two_le (Ne.symm hp)
  exact Nat.not_dvd_of_pos_of_lt (by decide : 0 < 2) hlt
    ((CharP.cast_eq_zero_iff F p 2).mp (by simpa using h))

private theorem not_quasithin_of_kernel_prime_dvd {p : ℕ} [Fact p.Prime] [CharP F p]
    (hp : p ≠ 2) (f : G →* F4 F) (hf : Function.Surjective f)
    (hk : f.ker ≤ center G) (ho : Odd (Nat.card f.ker))
    (hd : p ∣ Nat.card f.ker) : ¬ IsQuasithin G := by
  intro hqt
  have hpo : Odd p := (Fact.out : p.Prime).odd_of_ne_two hp
  have hz := Matrix.SpecialLinearGroup.map_neg_one_isInvolution hp
    (F4RootSL2.hom (F := F)) (F4RootSL2.hom_injective (two_ne_zero hp))
  let x := OddTorus.planeHom (F := F) p (Multiplicative.ofAdd 1,1)
  let y := OddTorus.planeHom (F := F) p (1,Multiplicative.ofAdd 1)
  have hxy : Commute x y := by
    change (OddTorus.planeHom p _) * (OddTorus.planeHom p _) =
      (OddTorus.planeHom p _) * (OddTorus.planeHom p _)
    rw [← map_mul,← map_mul,mul_comm]
  obtain ⟨z',hz',hz'2,hrank⟩ := OddCentralInvertedPlane.rank_three_of_kernel_divisible
    f hf hk ho hpo
    (OddTorus.plane (F := F) p) (OddTorus.plane_pow p) (OddTorus.plane_card p)
    x y (OddTorus.coroot 3) OddTorus.inverter (F4RootSL2.hom (-1 : SL(2,F)))
    (OddTorus.plane_generated p) hxy (OddTorus.plane_partial_inversion p).1
    (OddTorus.plane_partial_inversion p).2 OddTorus.inverter_square
    (OddTorus.plane_total_inversion p) hz.1 hz.2 (OddTorus.plane_centralizes p) hd
  have hloc := isTwoLocal_involution_centralizer (orderOf_eq_prime hz'2 hz')
  have hupper := (isQuasithin_iff_twoLocal.mp hqt) _ hloc p Fact.out hpo
  omega

private theorem not_quasithin_of_coprime_kernel {p d : ℕ} [Fact p.Prime] [CharP F p]
    (hp : p ≠ 2) (hcard : Nat.card F = p ^ d)
    (f : G →* F4 F) (hf : Function.Surjective f)
    (hk : f.ker ≤ center G) (ho : Odd (Nat.card f.ker))
    (hcop : Nat.Coprime p (Nat.card f.ker)) : ¬ IsQuasithin G := by
  intro hqt
  have hpo : Odd p := (Fact.out : p.Prime).odd_of_ne_two hp
  have hFo : Odd (Nat.card F) := by rw [hcard]; exact hpo.pow
  let j : SL(2,F) →* F4 F := F4RootSL2.hom
  have hj : Function.Injective j := F4RootSL2.hom_injective (two_ne_zero hp)
  obtain ⟨k,hki,hfk,hK⟩ := RootCoverTransfer.exists_root_lift (F := F) hFo f hf hk ho hcop j hj
  have hres := (RootCoverTransfer.complementaryResidual_image (F := F) hFo f hf hk ho hcop j hj).2
  let K := RootCoverTransfer.rootResidual p f j
  let J := RootCoverTransfer.complementaryResidual p K
  have hJK : J ≤ centralizer (k.range : Set G) := by
    rw [hK]
    exact map_subtype_le _
  have hpd : p ∣ Nat.card SL(2,F) := by
    rw [GorensteinWalter.sl2_card_formula F,hcard]
    have hd : d ≠ 0 := by
      intro hd
      have hFcard : 1 < Nat.card F := Finite.one_lt_card
      simp [hd] at hcard
      omega
    exact dvd_mul_of_dvd_left (dvd_pow_self p hd) _
  have hlocal (z : G) (hz : z ≠ 1) (hz2 : z ^ 2 = 1) :
      primeRank p (centralizer ({z} : Set G)) ≤ 2 :=
    (isQuasithin_iff_twoLocal.mp hqt) _
      (isTwoLocal_involution_centralizer (orderOf_eq_prime hz2 hz)) p Fact.out hpo
  have hb := (RootCoverTransfer.sl2_complementary_primeRank_le_one hp hpo hFo
    k hki J hJK hpd hlocal (f.subgroupMap J) (f.subgroupMap_surjective J)).2
  change J.map f = RootCoverTransfer.complementaryResidual p j.range at hres
  rw [hres] at hb
  apply F4DefiningRank.source_bound_contradiction (MulEquiv.refl (F4 F))
  change primeRank p (RootCoverTransfer.complementaryResidual p
    ((MonoidHom.id (F4 F)).comp j).range) ≤ 1
  rw [MonoidHom.id_comp]
  exact hb

/-- Every finite odd central cover of the actual odd-characteristic F₄
carrier violates quasithinness. The kernel need not be the entire center,
and no perfectness or defining-prime-free kernel is assumed. -/
theorem not_quasithin_of_central_cover {p d : ℕ} [Fact p.Prime] [CharP F p]
    (hp : p ≠ 2) (hcard : Nat.card F = p ^ d)
    (f : G →* F4 F) (hf : Function.Surjective f)
    (hk : f.ker ≤ center G) (ho : Odd (Nat.card f.ker)) : ¬ IsQuasithin G := by
  by_cases hd : p ∣ Nat.card f.ker
  · exact not_quasithin_of_kernel_prime_dvd hp f hf hk ho hd
  · exact not_quasithin_of_coprime_kernel hp hcard f hf hk ho
      ((Fact.out : p.Prime).coprime_iff_not_dvd.mpr hd)

/-- The complete odd-center F₄ source exclusion on the original group.
Only the preceding A.2.13 odd-center reduction remains explicit; the
initial defining-center exclusion and all root/torus/rank inputs are
proved internally for this F₄ branch, including characteristic three. -/
theorem not_quasithin_of_odd_center {p d : ℕ} [Fact p.Prime] [CharP F p]
    (hp : p ≠ 2) (hcard : Nat.card F = p ^ d)
    (e : G ⧸ center G ≃* F4 F) (ho : Odd (Nat.card (center G))) : ¬ IsQuasithin G := by
  let f : G →* F4 F := e.toMonoidHom.comp (QuotientGroup.mk' (center G))
  have hf : Function.Surjective f := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hfker : f.ker = center G := by
    dsimp only [f]
    rw [MonoidHom.ker_comp_of_injective _ _ e.injective,QuotientGroup.ker_mk']
  exact not_quasithin_of_central_cover hp hcard f hf (by rw [hfker])
    (by simpa only [hfker] using ho)

end CFSG.Quasithin.ChapterA.Section02.F4OddCover
