module
public import Theory.GroupTheory.ReducedNormal.QuasisimpleKernel
public import Theory.Representation.NormalElementaryQuotient
public import Theory.Representation.BinaryFourQuinticFixed
public import Theory.Representation.BinaryAlternatingSevenControl.Normalizer

/-!
# Reduced binary four-space geometry

A subgroup of order divisible by five inside a detected component has no
nonzero fixed vector on a reduced binary four-space. The two-core kernel
cannot remove its quintic element, and a faithful quintic operator moves
all four dimensions. A normal A₇ component is the full action image by
self-normalization in GL₄(2); with a two-group supplement this identifies
the whole literal two-core quotient.

Source application: Aschbacher–Smith 5.1.13, printed pp.637–638.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace Theory.GroupTheory
variable {G : Type*} [Group G] [Finite G]

private theorem four_finrank (U : Subgroup G) [IsElementaryAbelian 2 U]
    (hc : Nat.card U = 16) : Module.finrank (ZMod 2) (Additive U) = 4 := by
  apply Nat.pow_right_injective (by decide : 2 ≤ 2)
  have hh := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive U)
  change Nat.card U = Nat.card (ZMod 2) ^ Module.finrank (ZMod 2) (Additive U) at hh
  simpa only [Nat.card_zmod, hc] using hh.symm

private theorem five_image {Q : Type*} [Group Q]
    (q : G →* Q) (R : Subgroup G)
    (hk : IsPGroup 2 (q.subgroupMap R).ker) (h5 : 5 ∣ Nat.card R) :
    5 ∣ Nat.card (R.map q) := by
  have hnot : ¬ 5 ∣ Nat.card (q.subgroupMap R).ker := by
    intro hh
    obtain ⟨n,hn⟩ := hk.exists_card_dvd_pow
    have := Nat.prime_five.dvd_of_dvd_pow (hh.trans hn)
    norm_num at this
  have hc := (q.subgroupMap R).ker.card_mul_index
  rw [Subgroup.index_ker, MonoidHom.range_eq_top_of_surjective _
    (q.subgroupMap_surjective R), card_top] at hc
  exact (Nat.prime_five.dvd_mul.mp (hc.symm ▸ h5)).resolve_left hnot

/-- A four-dimensional reduced module has no fixed vector for a subgroup
whose order is divisible by five inside its detected simple component. -/
theorem four_reduced_fixed_eq_bot (U K R : Subgroup G)
    [U.Normal] [K.Normal] [IsElementaryAbelian 2 U]
    [IsQuasisimple (K ⧸ pCore 2 K)]
    (hr : IsPReduced 2 U) (hz : center (K ⧸ pCore 2 K) = ⊥)
    (hm : ⁅U,K⁆ ≠ ⊥) (hc : Nat.card U = 16)
    (hRK : R ≤ K) (h5 : 5 ∣ Nat.card R) :
    U ⊓ centralizer (R : Set G) = ⊥ := by
  let q := QuotientGroup.mk' (centralizer (U : Set G))
  let i := inclusion hRK
  have hk : IsPGroup 2 (q.subgroupMap R).ker := by
    apply ((pCore_isPGroup (p := 2) (G := K)).comap_of_injective i
      (inclusion_injective hRK)).to_le
    intro r hr'
    change i r ∈ pCore 2 K
    rw [←reduced_quasisimple_subgroupMap_ker U K hr hz hm]
    apply Subtype.ext
    exact congrArg (fun x : R.map q => (x : G ⧸ centralizer (U : Set G))) hr'
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  obtain ⟨x,hx⟩ := exists_prime_orderOf_dvd_card' (G := R.map q) 5 (five_image q R hk h5)
  let ρ := NormalElementaryQuotient.representation U q (QuotientGroup.mk'_surjective _)
    (QuotientGroup.ker_mk' _)
  apply bot_unique
  intro u hu
  have hv := (NormalElementaryQuotient.mem_fixedSpace_image U q
    (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _) R
    (Additive.ofMul (⟨u,hu.1⟩ : U))).mpr hu.2
  have he := four_fixed_eq_zero_of_order_five ρ
    (NormalElementaryQuotient.representation_injective U q _ _) (four_finrank U hc)
    x.val ((Subgroup.orderOf_coe x).trans hx) _ (hv x)
  exact congrArg (fun v : Additive U => (v.toMul : G)) he

/-- A normal A₇ component accounts for the entire action on a reduced
binary four-space, with the original centralizer quotient map. -/
theorem four_reduced_alternatingSeven_image_top (U K : Subgroup G)
    [U.Normal] [K.Normal] [IsElementaryAbelian 2 U]
    [IsQuasisimple (K ⧸ pCore 2 K)]
    (hr : IsPReduced 2 U) (hz : center (K ⧸ pCore 2 K) = ⊥)
    (hm : ⁅U,K⁆ ≠ ⊥) (hc : Nat.card U = 16)
    (e : (K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 7)) :
    K.map (QuotientGroup.mk' (centralizer (U : Set G))) = ⊤ := by
  let q := QuotientGroup.mk' (centralizer (U : Set G))
  let ρ := NormalElementaryQuotient.representation U q (QuotientGroup.mk'_surjective _)
    (QuotientGroup.ker_mk' _)
  let : (K.map q).Normal := Subgroup.Normal.map inferInstance q (QuotientGroup.mk'_surjective _)
  exact BinaryAlternatingSevenControl.normal_alternatingSeven_eq_top ρ
    (NormalElementaryQuotient.representation_injective U q _ _) (four_finrank U hc)
    (K.map q) ((reducedQuasisimpleImageEquiv U K hr hz hm).symm.trans e)
/-- With a two-group supplement, the whole two-core quotient is the same A₇. -/
theorem four_reduced_alternatingSeven_quotient (U K : Subgroup G)
    [U.Normal] [K.Normal] [IsElementaryAbelian 2 U]
    [IsQuasisimple (K ⧸ pCore 2 K)]
    (hr : IsPReduced 2 U) (hz : center (K ⧸ pCore 2 K) = ⊥)
    (hm : ⁅U,K⁆ ≠ ⊥) (hc : Nat.card U = 16)
    (e : (K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 7))
    (hquot : IsPGroup 2 (G ⧸ K)) :
    Nonempty ((G ⧸ pCore 2 G) ≃* alternatingGroup (Fin 7)) := by
  let q := QuotientGroup.mk' (centralizer (U : Set G))
  have htop := four_reduced_alternatingSeven_image_top U K hr hz hm hc e
  have hker := reduced_quasisimple_centralizer_eq_pCore U K hr hz hm hquot
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hker.symm).trans
    ((MulEquiv.subgroupCongr htop).trans Subgroup.topEquiv).symm |>.trans
    ((reducedQuasisimpleImageEquiv U K hr hz hm).symm.trans e)⟩
/-- The Sylow-fixed subgroup of the same four-space has order two. -/
theorem four_reduced_alternatingSeven_sylow_fixed_card (U K : Subgroup G)
    [U.Normal] [K.Normal] [IsElementaryAbelian 2 U]
    [IsQuasisimple (K ⧸ pCore 2 K)]
    (hr : IsPReduced 2 U) (hz : center (K ⧸ pCore 2 K) = ⊥)
    (hm : ⁅U,K⁆ ≠ ⊥) (hc : Nat.card U = 16)
    (e : (K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 7)) (S : Sylow 2 G) :
    Nat.card (U ⊓ centralizer ((S : Subgroup G) : Set G) : Subgroup G) = 2 := by
  let q := QuotientGroup.mk' (centralizer (U : Set G))
  have htop := four_reduced_alternatingSeven_image_top U K hr hz hm hc e
  let a : (G ⧸ centralizer (U : Set G)) ≃* alternatingGroup (Fin 7) :=
    ((MulEquiv.subgroupCongr htop).trans Subgroup.topEquiv).symm.trans
      ((reducedQuasisimpleImageEquiv U K hr hz hm).symm.trans e)
  let r := a.toMonoidHom.comp q
  have hs : Function.Surjective r := a.surjective.comp (QuotientGroup.mk'_surjective _)
  have hk : r.ker = centralizer (U : Set G) :=
    (MonoidHom.ker_comp_of_injective q a.toMonoidHom a.injective).trans (QuotientGroup.ker_mk' _)
  let ρ := NormalElementaryQuotient.representation U r hs hk
  have hf := BinaryAlternatingSevenControl.sylow_fixed_finrank ρ
    (NormalElementaryQuotient.representation_injective U r hs hk) (four_finrank U hc)
    (S.mapSurjective hs)
  have hh := Module.natCard_eq_pow_finrank (K := ZMod 2)
    (V := fixedSpace ρ (S.mapSurjective hs))
  rw [hf,Nat.card_zmod,pow_one] at hh
  exact (Nat.card_congr (NormalElementaryQuotient.fixedSpaceEquiv U r hs hk
    (S : Subgroup G))).symm.trans hh

end Theory.GroupTheory
