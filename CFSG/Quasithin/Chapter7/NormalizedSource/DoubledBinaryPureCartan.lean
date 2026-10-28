module
public import CFSG.Quasithin.Chapter7.NormalizedSource.DoubledBinaryCartan
public import CFSG.Quasithin.Chapter7.NormalizedSource.DoubledBinaryPointCentralizers

/-!
# Pure-line Cartan obstruction for the original H1 component

The pure-line stabilizer induces a subgroup of S₄ on the whole orbit W.
The original component Sylow centralizes W, so its normalizer has odd
image, of order dividing three. The literal central-quotient map carries
this normalizer onto the quotient Sylow normalizer. The marked inner
action carries orbit centralizers into centralizers of the faithful
sixteen. Its already proved large Cartan index forces the normalizer
outside N_G(W).

The chosen-module application supplies the pure-line bound on both marked
axes and combines this obstruction with actual model normalizer placement.
Source: Aschbacher–Smith 7.7.3, H1 argument, printed p.706, and 7.7.4,
printed p.704, refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter7.NormalizedSource.DoubledBinaryPureCartan

private theorem inner_conj {K : Type*} [Group K] (k : K) :
    innerEquivCentralQuotient ((MulAut.conj : K →* MulAut K).rangeRestrict k) =
      (QuotientGroup.mk' (center K)) k := by
  change QuotientGroup.quotientMulEquivOfEq DoubleCoverCentralizer.conj_kernel
    ((QuotientGroup.quotientKerEquivRange (MulAut.conj : K →* MulAut K)).symm
      (MulAut.conj.rangeRestrict k)) = _
  have he : (QuotientGroup.quotientKerEquivRange (MulAut.conj : K →* MulAut K)).symm
      (MulAut.conj.rangeRestrict k) = QuotientGroup.mk k := by
    apply (QuotientGroup.quotientKerEquivRange (MulAut.conj : K →* MulAut K)).injective
    rw [MulEquiv.apply_symm_apply]
    rfl
  rw [he]
  rfl

/-- The original component Sylow kills the orbit action, so the S₄ point
image of its normalizer has odd order, necessarily dividing three. -/
theorem normalizer_index_dvd_three
    {G : Type*} [Group G] [Finite G] (W Z K : Subgroup G)
    (hKC : K ≤ centralizer (Z : Set G))
    (hpoint : Nat.card (ChapterE.inducedAutomizer W (centralizer (Z : Set G))) ∣ 24)
    (P : Sylow 2 K) (hPW : (P : Subgroup K).map K.subtype ≤ centralizer (W : Set G))
    (hN : (normalizer (P : Set K)).map K.subtype ≤ normalizer (W : Set G)) :
    (centralizer (W : Set G)).relIndex ((normalizer (P : Set K)).map K.subtype) ∣ 3 := by
  let N := normalizer (P : Set K)
  let f := K.subtype.comp N.subtype
  let D := (centralizer (W : Set G)).comap f
  have hD : D.index = (centralizer (W : Set G)).relIndex (N.map K.subtype) := by
    rw [index_comap,MonoidHom.range_comp,N.range_subtype]
  have hP : (P.subtype (show (P : Subgroup K) ≤ N from le_normalizer) : Subgroup N) ≤ D := by
    intro p hp
    exact hPW (mem_map_of_mem K.subtype hp)
  have ho : Odd D.index := Nat.not_even_iff_odd.mp (by
    rw [even_iff_two_dvd]
    exact fun he => (P.subtype le_normalizer).not_dvd_index
      (he.trans (index_dvd_of_le hP)))
  have hd : D.index ∣ 24 := by
    rw [hD,← doubledBinary_induced_card W (N.map K.subtype) hN]
    exact (card_dvd_of_le (map_mono (comap_mono
      ((map_subtype_le N).trans hKC)))).trans hpoint
  have hc : D.index.Coprime 8 := by simpa using ho.coprime_two_right.pow_right 3
  rw [←hD]
  exact hc.dvd_of_dvd_mul_left hd

/-- The large Cartan action in the literal central quotient forces the same
component Sylow normalizer to escape M, using the pure-line S₄ bound. -/
theorem normalizer_escape
    {G : Type*} [Group G] [Finite G] (W Z K A : Subgroup G)
    (hAW : A ≤ W) (hKC : K ≤ centralizer (Z : Set G))
    (hAN : A ≤ normalizer (K : Set G))
    (hpoint : Nat.card (ChapterE.inducedAutomizer W (centralizer (Z : Set G))) ∣ 24)
    (j : A →* K ⧸ center K)
    (hact : ∀ a : A, (innerEquivCentralQuotient.symm (j a) : MulAut K) =
      K.normalizerMonoidHom (inclusion hAN a))
    (P : Sylow 2 K) (hPW : (P : Subgroup K).map K.subtype ≤ centralizer (W : Set G))
    (hlarge : let Q := P.mapSurjective (QuotientGroup.mk'_surjective (center K))
      3 < ((centralizer (j.range : Set (K ⧸ center K))).subgroupOf
        (normalizer (Q : Set (K ⧸ center K)))).index) :
    ¬ (normalizer (P : Set K)).map K.subtype ≤ normalizer (W : Set G) := by
  intro hN
  let X := K ⧸ center K
  let q := QuotientGroup.mk' (center K)
  let Q := P.mapSurjective (QuotientGroup.mk'_surjective (center K))
  let N := normalizer (P : Set K)
  let NQ := normalizer (Q : Set X)
  let C := (centralizer (j.range : Set X)).subgroupOf NQ
  let D := (centralizer (W : Set G)).comap (K.subtype.comp N.subtype)
  have hD : D.index = (centralizer (W : Set G)).relIndex (N.map K.subtype) := by
    rw [index_comap,MonoidHom.range_comp,N.range_subtype]
  have hmap : N.map q = NQ := P.normalizer_map_surjective q (QuotientGroup.mk'_surjective _)
  let g : N →* NQ := (MulEquiv.subgroupCongr hmap).toMonoidHom.comp (q.subgroupMap N)
  have hg : Function.Surjective g :=
    (MulEquiv.subgroupCongr hmap).surjective.comp (q.subgroupMap_surjective N)
  have hk : D ≤ C.comap g := by
    intro n hnW
    change q n.val ∈ centralizer (j.range : Set X)
    rintro _ ⟨a,rfl⟩
    let e := innerEquivCentralQuotient (H := K)
    have hf : (e.symm (j a) : MulAut K) n.val = n.val := by
      rw [hact a]
      apply Subtype.ext
      change (a : G) * (n.val : G) * (a : G)⁻¹ = (n.val : G)
      exact mul_inv_eq_iff_eq_mul.mpr (hnW a (hAW a.property))
    have hq : e.symm (q n.val) = (MulAut.conj : K →* MulAut K).rangeRestrict n.val := by
      apply e.injective
      rw [e.apply_symm_apply,inner_conj]
    apply e.symm.injective
    rw [map_mul,map_mul,hq]
    apply Subtype.ext
    apply MulEquiv.ext
    intro x
    change (e.symm (j a) : MulAut K) (n.val * x * n.val⁻¹) =
      n.val * (e.symm (j a) : MulAut K) x * n.val⁻¹
    rw [map_mul,map_mul,map_inv,hf]
  have hd : D.index ∣ 3 := by
    rw [hD]
    exact normalizer_index_dvd_three W Z K hKC hpoint P hPW hN
  have hc : C.index ≤ 3 := by
    rw [←C.index_comap_of_surjective hg]
    exact Nat.le_of_dvd (by decide) ((index_dvd_of_le hk).trans hd)
  exact (not_lt_of_ge hc) hlarge

end CFSG.Quasithin.Chapter7.NormalizedSource.DoubledBinaryPureCartan
