module
public import CFSG.Quasithin.ChapterC.Section01.BlockTypes.SL2BorelResidual
public import Theory.GroupTheory.PResidual.ThreeFree
public import CFSG.Quasithin.Chapter7.NormalizedSource.DoubledBinaryFiveStar
public import CFSG.Quasithin.ChapterC.Section01.BlockTypes.SL2SylowFixed
public import Theory.GroupTheory.PResidual.PrimeToAction
public import Theory.SpecificGroups.SymmetricThree.CubicSelection

/-!
# Excluding natural blocks on the original doubled orbit

A natural-block Borel is two-perfect. Its image in the paired-plane S₃
actor is nontrivial: otherwise Borel rigidity would make the entire block
centralize the orbit. Its image is therefore the unique cubic subgroup,
which also contains the original residual image.

The residual commutator consequently lies in the Borel commutator.
Coprime splitting for the actual action image makes the latter disjoint
from the block center. At field order four, the original Sylow fixes it,
so the natural-module bound gives order at most four. At larger fields,
the Borel's {2,3}-residual acts trivially through S₃ and fixes only central
vectors in the natural cover, so the commutator is trivial. The residual
supplement would then give the full orbit order at most sixteen, contrary
to its order sixty-four. No central splitting or odd Borel order is used.

NonFFSourceDoubledBinaryNaturalFour discharges the hypotheses on the
actual chosen module. Source: Aschbacher–Smith, 7.7.9(1), printed p.708,
refs/quasithin.pdf, with the natural Borel residual calculation used in
15.3.18. Remaining constrained rows, ambient containment and final non-FF
assembly remain with qt-d-1222-nonff-doubled.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
open scoped IsMulCommutative commutatorElement Pointwise
namespace CFSG.Quasithin.Chapter7.NormalizedSource.DoubledBinaryNaturalFour
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
private theorem twoPerfect_image_le (N A : Subgroup G) (hAN : A ≤ N)
    (π : N →* Equiv.Perm (Fin 3)) (hp : IsPPerfect 2 A) :
    (A.subgroupOf N).map π ≤ alternatingGroup (Fin 3) := by
  rw [← Theory.SpecificGroups.SymmetricThree.CubicSelection.residual_eq]
  exact le_pResidual_of_isPPerfect _ ((hp.of_surjective
    (subgroupOfEquivOfLe hAN).symm.toMonoidHom (subgroupOfEquivOfLe hAN).symm.surjective).of_surjective
      (π.subgroupMap _) (π.subgroupMap_surjective _))

private theorem cubic_image_eq (I : Subgroup (Equiv.Perm (Fin 3)))
    (hle : I ≤ alternatingGroup (Fin 3)) (hne : I ≠ ⊥) :
    I = alternatingGroup (Fin 3) := by
  have hc : Nat.card (alternatingGroup (Fin 3)) = 3 := by
    rw [nat_card_alternatingGroup,Nat.card_fin]; rfl
  have hd : Nat.card I ∣ 3 := by simpa only [hc] using card_dvd_of_le hle
  rcases (Nat.dvd_prime Nat.prime_three).mp hd with hi | hi
  · exact (hne (card_eq_one.mp hi)).elim
  · exact eq_of_le_of_card_ge hle (by rw [hi,hc])

omit [Finite G] in
private theorem image_action_ker (W N B : Subgroup G)
    (hNW : N ≤ normalizer (W : Set G)) (hBN : B ≤ N)
    (π : N →* Equiv.Perm (Fin 3))
    (hk : π.ker = (centralizer (W : Set G)).subgroupOf N) :
    (W.normalizerMonoidHom.comp (inclusion (hBN.trans hNW))).ker =
      (π.comp (inclusion hBN)).ker := by
  ext b
  change inclusion (hBN.trans hNW) b ∈ W.normalizerMonoidHom.ker ↔ inclusion hBN b ∈ π.ker
  rw [normalizerMonoidHom_ker]
  change (b : G) ∈ centralizer (W : Set G) ↔ inclusion hBN b ∈ π.ker
  rw [hk]
  rfl

omit [Finite G] in
private theorem image_action_card (W N B : Subgroup G)
    (hNW : N ≤ normalizer (W : Set G)) (hBN : B ≤ N)
    (π : N →* Equiv.Perm (Fin 3))
    (hk : π.ker = (centralizer (W : Set G)).subgroupOf N) :
    Nat.card (W.normalizerMonoidHom.comp (inclusion (hBN.trans hNW))).range =
      Nat.card ((B.subgroupOf N).map π) := by
  let a := W.normalizerMonoidHom.comp (inclusion (hBN.trans hNW))
  let b := π.comp (inclusion hBN)
  have he : a.ker = b.ker := image_action_ker W N B hNW hBN π hk
  have hr : b.range = (B.subgroupOf N).map π := by
    ext x
    constructor
    · rintro ⟨y,rfl⟩
      exact ⟨inclusion hBN y,y.property,rfl⟩
    · rintro ⟨y,hy,rfl⟩
      exact ⟨⟨y,hy⟩,rfl⟩
  rw [←hr]
  exact Nat.card_congr (((QuotientGroup.quotientKerEquivRange a).symm.trans
    (QuotientGroup.quotientMulEquivOfEq he)).trans
      (QuotientGroup.quotientKerEquivRange b)).toEquiv

omit [Finite G] in
private theorem commutator_le_of_image_le (W N A B : Subgroup G)
    (hNW : N ≤ normalizer (W : Set G)) (hAN : A ≤ N) (_hBN : B ≤ N)
    (π : N →* Equiv.Perm (Fin 3))
    (hk : π.ker = (centralizer (W : Set G)).subgroupOf N)
    (hab : (A.subgroupOf N).map π ≤ (B.subgroupOf N).map π) : ⁅W,A⁆ ≤ ⁅W,B⁆ := by
  apply commutator_le.mpr
  intro w hw a ha
  obtain ⟨b,hb,he⟩ := hab (mem_map_of_mem π (show (⟨a,hAN ha⟩ : N) ∈ A.subgroupOf N from ha))
  have hker : b⁻¹ * ⟨a,hAN ha⟩ ∈ π.ker := by
    rw [MonoidHom.mem_ker,map_mul,map_inv,he,inv_mul_cancel]
  have hc : (b : G)⁻¹*a ∈ centralizer (W : Set G) := by
    rw [hk] at hker
    exact hker
  have hf : W.normalizerMonoidHom (inclusion hNW b) =
      W.normalizerMonoidHom (inclusion hNW ⟨a,hAN ha⟩) := by
    apply inv_mul_eq_one.mp
    rw [←map_inv,←map_mul]
    change inclusion hNW (b⁻¹ * ⟨a,hAN ha⟩) ∈ W.normalizerMonoidHom.ker
    rw [normalizerMonoidHom_ker]
    exact hc
  have hv := congrArg (fun f : MulAut W => ((f (⟨w,hw⟩ : W)⁻¹ : W) : G)) hf
  change (b : G)*w⁻¹*(b : G)⁻¹ = a*w⁻¹*a⁻¹ at hv
  have hm : ⁅w,a⁆ = ⁅w,(b : G)⁆ := by
    simp only [commutatorElement_def,mul_assoc]
    simpa only [mul_assoc] using congrArg (fun x => w*x) hv.symm
  rw [hm]
  exact commutator_mem_commutator hw hb


/-- A natural L₂(2ⁿ) block cannot escape while its Borel and the original
residual act through the paired-plane S₃ image on the full orbit. -/
theorem natural_block_no_escape
    (W C N A U : Subgroup G) [IsElementaryAbelian 2 W]
    (hC : C.IsCComponent) {n : ℕ} (hb : ChapterC.IsL2EvenBlock C n)
    (hWcore : W ≤ pCore 2 G) (hout : ¬ C ≤ centralizer (W : Set G))
    (P : Sylow 2 C)
    (hWP : W ≤ centralizer ((P : Subgroup C).map C.subtype : Set G))
    (hNW : N ≤ normalizer (W : Set G)) (hAN : A ≤ N)
    (hBN : (normalizer (P : Set C)).map C.subtype ≤ N)
    (hA : IsPPerfect 2 A)
    (π : N →* Equiv.Perm (Fin 3))
    (hk : π.ker = (centralizer (W : Set G)).subgroupOf N)
    (hsup : U ⊔ ⁅W,A⁆ = W) (hU : Nat.card U = 4) (hW : Nat.card W = 64) : False := by
  let B := (normalizer (P : Set C)).map C.subtype
  have hBW : B ≤ normalizer (W : Set G) := hBN.trans hNW
  have hB : IsPPerfect 2 B := (hb.borel_twoPerfect P).of_surjective
    (C.subtype.subgroupMap _) (C.subtype.subgroupMap_surjective _)
  have hBI : (B.subgroupOf N).map π = alternatingGroup (Fin 3) := by
    apply cubic_image_eq _ (twoPerfect_image_le N B hBN π hB)
    intro hbot
    have hBC : B ≤ centralizer (W : Set G) := by
      intro b hbB
      have hh : (⟨b,hBN hbB⟩ : N) ∈ π.ker :=
        (Subgroup.map_eq_bot_iff _).mp hbot hbB
      rw [hk] at hh
      exact hh
    have hWC : W ≤ normalizer (C : Set G) := hWcore.trans (hC.pCore_le_normalizer 2)
    apply hout
    apply le_centralizer_iff.mp
    intro w hw c hc
    let α : MulAut C := C.normalizerMonoidHom ⟨w,hWC hw⟩
    have hα : α = 1 := hb.borel_fixer P α (by
      intro x hx
      apply Subtype.ext
      change w*(x:G)*w⁻¹=(x:G)
      have hh := hBC (mem_map_of_mem C.subtype hx) w hw
      change w*(x:G)=(x:G)*w at hh
      rw [hh,mul_inv_cancel_right])
    have he := congrArg (fun f : MulAut C => ((f ⟨c,hc⟩ : C) : G)) hα
    change w*c*w⁻¹=c at he
    exact (mul_inv_eq_iff_eq_mul.mp he).symm
  have hAB : ⁅W,A⁆ ≤ ⁅W,B⁆ := commutator_le_of_image_le W N A B hNW hAN hBN π hk
    (by rw [hBI]; exact twoPerfect_image_le N A hAN π hA)
  have hcard : Nat.card (W.normalizerMonoidHom.comp (inclusion hBW)).range = 3 := by
    rw [image_action_card W N B hNW hBN π hk,hBI,nat_card_alternatingGroup,Nat.card_fin]
    rfl
  have hsplit := commutator_centralizer_decomposition_of_coprime_image W B hBW
    (show Nat.Coprime
      (Nat.card (W.normalizerMonoidHom.comp (inclusion hBW)).range) (Nat.card W) by
        rw [hcard,hW]; decide)
  let D := ⁅W,B⁆
  have hDW : D ≤ W := le_normalizer_iff_commutator_le_left.mp hBW
  have hDU : D ≤ (ChapterC.blockU C).map C.subtype :=
    (commutator_mono hWcore (map_subtype_le _)).trans
      (commutator_le_core_commutator_of_isSubnormal C (pCore 2 G)
        hC.subnormal hb.2.1.twoPerfect pCore_isPGroup le_normalizer_of_normal)
  have hDC : D ≤ C := hDU.trans (map_subtype_le _)
  have hDCU : D.subgroupOf C ≤ ChapterC.blockU C := by
    intro x hx
    obtain ⟨y,hy,he⟩ := hDU hx
    exact (Subtype.ext he : y=x) ▸ hy
  have hDP : D.subgroupOf C ≤ centralizer (P : Set C) := by
    intro x hx p hp
    exact Subtype.ext (hWP (hDW hx) p (mem_map_of_mem C.subtype hp))
  have hDZ : Disjoint (D.subgroupOf C) (center C) := by
    apply disjoint_iff.mpr
    apply le_bot_iff.mp
    intro x hx
    have hz : (x : G) ∈ centralizer (B : Set G) := by
      rintro b ⟨y,hy,rfl⟩
      exact congrArg Subtype.val (mem_center_iff.mp hx.2 y)
    have hh : (x : G) ∈ D ⊓ (W ⊓ centralizer (B : Set G)) :=
      ⟨hx.1,hDW hx.1,hz⟩
    rw [hsplit.2] at hh
    exact Subtype.ext (mem_bot.mp hh)
  have hD4 : Nat.card D ≤ 4 := by
    by_cases hn : n = 2
    · subst n
      have hh := hb.card_le_of_sylow_fixed_disjoint_center P (D.subgroupOf C) hDCU hDP hDZ
      rwa [Nat.card_congr (subgroupOfEquivOfLe hDC).toEquiv] at hh
    have hn' : 2 < n := by have := hb.1; omega
    obtain ⟨_,_,F,_,_,hF,_,r,⟨m⟩,hr⟩ := hb
    let : Fintype F := Fintype.ofFinite F
    let : CharP F 2 := charP_of_card_eq_prime_pow (p := 2) (f := n)
      (by simpa only [Nat.card_eq_fintype_card] using hF)
    let q := m.quotientIso.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 C))
    have hq : Function.Surjective q := m.quotientIso.surjective.comp (QuotientGroup.mk'_surjective _)
    let B₀ := normalizer (P : Set C)
    let a₀ := (π.comp (inclusion hBN)).comp (C.subtype.subgroupMap B₀)
    have hpi : IsPiGroup twoThreePrimes (Equiv.Perm (Fin 3)) := by
      rw [IsPiGroup_iff]
      intro p hp
      have hd : (p : ℕ) ∣ 6 := by
        simpa [Nat.card_eq_fintype_card,Fintype.card_perm,Nat.factorial] using hp
      rcases p.property.dvd_mul.mp (show (p : ℕ) ∣ 2*3 from hd) with h2 | h3
      · exact Or.inl ((Nat.prime_dvd_prime_iff_eq p.property Nat.prime_two).mp h2)
      · exact Or.inr ((Nat.prime_dvd_prime_iff_eq p.property Nat.prime_three).mp h3)
    have hres : piResidual twoThreePrimes B₀ ≤ a₀.ker :=
      piResidual_le_ker_of_range twoThreePrimes a₀
        (hpi.of_injective a₀.range.subtype a₀.range.subtype_injective)
    have hfix : D.subgroupOf C ≤ centralizer
        (((piResidual twoThreePrimes B₀).map B₀.subtype : Subgroup C) : Set C) := by
      intro x hx
      rintro b ⟨y,hy,rfl⟩
      have he : inclusion hBN (C.subtype.subgroupMap B₀ y) ∈ π.ker := hres hy
      rw [hk] at he
      exact Subtype.ext (he x (hDW hx)).symm
    have hz : D.subgroupOf C ≤ center C := (le_inf hDCU hfix).trans
      (ChapterC.natural_block_residual_fixed_le_center hn' hF r m hr B₀
        (P.mapSurjective hq) (P.normalizer_map_surjective q hq))
    have hbot := hDZ.eq_bot
    rw [inf_eq_left.mpr hz] at hbot
    have hh : Nat.card (D.subgroupOf C) = 1 := card_eq_one.mpr hbot
    rw [Nat.card_congr (subgroupOfEquivOfLe hDC).toEquiv] at hh
    omega
  have hUW : U ≤ W := by rw [←hsup]; exact le_sup_left
  have hUD : U ⊔ D = W := le_antisymm (sup_le hUW hDW)
    (hsup.symm.le.trans (sup_le_sup_left hAB U))
  have hn : D ≤ normalizer (U : Set G) := by
    apply (show D ≤ centralizer (U : Set G) from ?_).trans (Subgroup.centralizer_le_normalizer _)
    intro d hd u hu
    exact congrArg Subtype.val (mul_comm (⟨u,hUW hu⟩ : W) ⟨d,hDW hd⟩)
  let m : U × D → W := fun x => ⟨(x.1:G)*(x.2:G),W.mul_mem (hUW x.1.property) (hDW x.2.property)⟩
  have hm : Function.Surjective m := by
    intro w
    have hw : (w:G) ∈ (U : Set G) * (D : Set G) := by
      rw [←coe_mul_of_right_le_normalizer_left U D hn,hUD]
      exact w.property
    obtain ⟨u,hu,d,hd,he⟩ := hw
    exact ⟨(⟨u,hu⟩,⟨d,hd⟩),Subtype.ext he⟩
  have hh := Nat.card_le_card_of_surjective m hm
  rw [Nat.card_prod,hU,hW] at hh
  omega

/-- A natural L₂(4) block cannot escape while its Borel and the original
residual act through the paired-plane S₃ image on the full orbit. -/
theorem natural_four_no_escape
    (W C N A U : Subgroup G) [IsElementaryAbelian 2 W]
    (hC : C.IsCComponent) (hb : ChapterC.IsL2EvenBlock C 2)
    (hWcore : W ≤ pCore 2 G) (hout : ¬ C ≤ centralizer (W : Set G))
    (P : Sylow 2 C)
    (hWP : W ≤ centralizer ((P : Subgroup C).map C.subtype : Set G))
    (hNW : N ≤ normalizer (W : Set G)) (hAN : A ≤ N)
    (hBN : (normalizer (P : Set C)).map C.subtype ≤ N)
    (hA : IsPPerfect 2 A)
    (π : N →* Equiv.Perm (Fin 3))
    (hk : π.ker = (centralizer (W : Set G)).subgroupOf N)
    (hsup : U ⊔ ⁅W,A⁆ = W) (hU : Nat.card U = 4) (hW : Nat.card W = 64) : False := by
  exact natural_block_no_escape W C N A U hC hb hWcore hout P hWP hNW hAN hBN
    hA π hk hsup hU hW

end CFSG.Quasithin.Chapter7.NormalizedSource.DoubledBinaryNaturalFour
