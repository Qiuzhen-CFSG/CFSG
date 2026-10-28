module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalM23.CubicCentralizer
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalM23.CubicLocal
public import Theory.GroupTheory.Recognition.QuasithinM23.ScalarCentralizer
public import GorensteinWalter.BrauerSuzukiWallCardTwoA5
/-!
# The original scalar cubic's full ambient normalizer

The actual marked ΓL₂(4) complement supplies a subgroup of order 180 in
the ambient cubic centralizer. The literal quotient by that cubic has one
involution class and elementary involution centralizers of order four.
The order-two branch of Brauer–Suzuki–Wall recognizes the quotient as A₅:
a factor of five excludes the alternative with a normal Sylow subgroup.
Thus the ambient cubic centralizer has order 180. Its normalizer has order
at most 360, forcing equality with the original marked local normalizer.

The chosen cubic is still Sylow in the exact preimage of the centralizer
of L/O₂(L), and the ΓL₂(4) marking is the original quotient map. This proves
the cubic-normalizer step of Aschbacher–Smith 5.2.15, printed pp.654–655
(`refs/quasithin.pdf`), from the prepared nonmaximal linear branch in either
orientation. The compatible linear completion and ambient M₂₃ recognition
are further obligations.
-/
public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
private theorem mem_cyclic_two {X : Type*} [Group X] [Finite X]
    {t x : X} (ht : orderOf t = 2) (hx : x ∈ zpowers t) : x = 1 ∨ x = t := by
  classical
  rw [mem_zpowers_iff_mem_range_orderOf,ht] at hx
  obtain ⟨n,hn,rfl⟩ := Finset.mem_image.mp hx
  have hn2 : n < 2 := Finset.mem_range.mp hn
  interval_cases n <;> simp

private theorem alternating_five_of_four_centralizer
    {X : Type*} [Group X] [Finite X]
    (t : X) (ht : orderOf t = 2)
    (hcard : Nat.card (centralizer ({t} : Set X)) = 4)
    (hel : IsElementaryAbelian 2 (centralizer ({t} : Set X)))
    (hfus : ∀ a b : X, orderOf a = 2 → orderOf b = 2 → IsConj a b)
    (hfive : 5 ∣ Nat.card X) : Nonempty (X ≃* alternatingGroup (Fin 5)) := by
  classical
  let H := centralizer ({t} : Set X)
  let K := zpowers t
  let := hel
  have ht2 : t^2=1 := ht ▸ pow_orderOf_eq_one t
  have ht1 : t ≠ 1 := by intro hh; simp [hh] at ht
  have hK : Nat.card K = 2 := (Nat.card_zpowers t).trans ht
  have hKH : K ≤ H := zpowers_le.mpr (mem_centralizer_singleton_iff.mpr rfl)
  have hHK : ¬ H ≤ K := by
    intro hh
    have hle := Nat.card_le_card_of_injective (inclusion hh) (inclusion_injective hh)
    rw [hcard,hK] at hle
    omega
  obtain ⟨s,hsH,hsK⟩ := SetLike.not_le_iff_exists.mp hHK
  have hs2 : s^2=1 := elemPow_eq_one_of_isElementaryAbelian (p := 2) s hsH
  have hs1 : s ≠ 1 := fun hh => hsK (hh ▸ K.one_mem)
  have hs : orderOf s = 2 := orderOf_eq_prime hs2 hs1
  have hc (x : X) (hx : x ∈ K) : s*x=x*s :=
    congrArg Subtype.val (mul_comm' (⟨s,hsH⟩ : H) ⟨x,hKH hx⟩)
  have hSc : zpowers s ≤ centralizer (K : Set X) :=
    zpowers_le.mpr (fun x hx => (hc x hx).symm)
  have hdis : Disjoint K (zpowers s) := by
    apply disjoint_def.mpr
    intro x hx hy
    rcases mem_cyclic_two hs hy with he | he
    · exact he
    · exact (hsK (he ▸ hx)).elim
  have hjoin : H = K ⊔ zpowers s := by
    symm
    apply eq_of_le_of_card_ge (sup_le hKH (zpowers_le.mpr hsH))
    rw [card_sup_eq_mul_of_normalizes_of_disjoint K (zpowers s)
      (hSc.trans (Subgroup.centralizer_le_normalizer _)) hdis,hK,Nat.card_zpowers,hs,hcard]
  let b : GorensteinWalter.BrauerSuzukiWallHypotheses X :=
    { t := t
      K := K
      H := H
      s := s
      t_involution := ⟨ht1,ht2⟩
      t_mem_K := mem_zpowers t
      H_eq_centralizer := rfl
      K_commutative := inferInstance
      s_involution := ⟨hs1,hs2⟩
      s_not_mem_K := hsK
      H_eq_join := hjoin
      fixed_subgroup_eq := inf_eq_left.mpr (fun x hx => mem_centralizer_singleton_iff.mpr (hc x hx).symm)
      s_inverts_K := fun x hx => by
        have hx2 : x*x=1 := by
          simpa only [pow_two] using elemPow_eq_one_of_isElementaryAbelian (p := 2) x (hKH hx)
        rw [hc x hx,mul_inv_cancel_right,inv_eq_of_mul_eq_one_right hx2]
      conjugate_disjoint := by
        intro g hg
        apply disjoint_def.mpr
        intro x hx hy
        rcases mem_cyclic_two ht hx with hh | hh
        · exact hh
        · subst x
          obtain ⟨y,hy,he⟩ := hy
          change g*y*g⁻¹=t at he
          rcases mem_cyclic_two ht hy with rfl | rfl
          · exact (ht1 (by simpa using he.symm)).elim
          · exact (hg (mem_centralizer_singleton_iff.mpr (mul_inv_eq_iff_eq_mul.mp he))).elim
      involutions_conjugate := fun u hu =>
        isConj_iff.mp (hfus u t (orderOf_eq_prime hu.2 hu.1) ht) }
  have hbK : Nat.card b.K = 2 := hK
  have hN : normalizer (b.H : Set X) ≠ ⊤ := by
    intro htop
    have hh := Nat.card_congr
      (b.normalizer_mulEquiv_alternatingGroup_four_of_card_K_eq_two hbK).some.toEquiv
    rw [htop,card_top,alternatingGroup.card_of_card_eq_four (by simp)] at hh
    rw [hh] at hfive
    norm_num at hfive
  exact b.mulEquiv_alternatingGroup_five_of_card_K_eq_two_of_normalizer_ne_top hbK hN

open Representation.SL2FourNatural Representation.SL2FourNatural.SemilinearNormalizer
private theorem normalizer_card_le_twice_centralizer
    {G : Type*} [Group G] [Finite G]
    (C : Subgroup G) (hC : Nat.card C = 3) :
    Nat.card (normalizer (C : Set G)) ≤ 2 * Nat.card (centralizer (C : Set G)) := by
  let : IsCyclic C := isCyclic_of_prime_card hC
  have hAut : Nat.card (MulAut C) = 2 := by rw [IsCyclic.card_mulAut,hC]; decide
  let f := C.normalizerMonoidHom
  have hb : Nat.card f.range ≤ 2 := hAut ▸ Nat.card_le_card_of_injective f.range.subtype f.range.subtype_injective
  have hk : Nat.card f.ker = Nat.card (centralizer (C : Set G)) := by
    rw [normalizerMonoidHom_ker,
      Nat.card_congr (subgroupOfEquivOfLe (Subgroup.centralizer_le_normalizer (C : Set G))).toEquiv]
  have hh := f.ker.card_mul_index
  rw [index_ker,hk] at hh
  rw [←hh]
  nlinarith

theorem Preparation.linear_nonmaximal_scalar_cubic_ambient_normalizer
    {G : Type*} [Group G] [Finite G]
    {T : Sylow 2 G} {L W H A B : Subgroup G} {n : ℕ}
    (d : Preparation T L H A B (residual H))
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hp : Group.IsPerfect (residual H))
    (E : Type) [Field E] [Finite E] [CharP E 2]
    {m : ℕ} (hm : 0 < m) (hE : Nat.card E = 2^m)
    (he : Nonempty (RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H))
      (ChapterF.GreenBook.LieModels.LinearThree.amalgam E)) ∨
      Nonempty (RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H))
      (ChapterF.GreenBook.LieModels.LinearThree.amalgam E).reverse))
    (hnonmax : residual H ∉ Chapter1.LStar G (T : Subgroup G)) :
    let M := normalizer (L : Set G)
    let π := QuotientGroup.mk' (pCore 2 M)
    let Lbar := (L.subgroupOf M).map π
    ∃ e : (M ⧸ pCore 2 M) ≃* Gamma,
      (L.subgroupOf M).map (e.toMonoidHom.comp π) = special.range ∧
      ∃ C : Subgroup M, C.map (e.toMonoidHom.comp π) = scalar.range ∧ Nat.card C = 3 ∧
        (∃ P : Sylow 3 ((centralizer (Lbar : Set (M ⧸ pCore 2 M))).comap π),
          (P : Subgroup ((centralizer (Lbar : Set (M ⧸ pCore 2 M))).comap π)).map
            ((centralizer (Lbar : Set (M ⧸ pCore 2 M))).comap π).subtype = C) ∧
        (pCore 2 M).IsComplement' (Subgroup.normalizer (C : Set M)) ∧
        (∃ eN : Subgroup.normalizer (C : Set M) ≃* Gamma,
          ∀ x : Subgroup.normalizer (C : Set M), eN x = e (π x)) ∧
        Subgroup.normalizer (C.map M.subtype : Set G) =
          (Subgroup.normalizer (C : Set M)).map M.subtype ∧
        Nonempty (Subgroup.normalizer (C.map M.subtype : Set G) ≃* Gamma) := by
  classical
  let M := normalizer (L : Set G)
  let π := QuotientGroup.mk' (pCore 2 M)
  obtain ⟨e,heL,C,heC,hC,hP,hcomp,eN,heN⟩ :=
    d.linear_nonmaximal_scalar_cubic_local_normalizer h hH hp E hm hE he hnonmax
  let N := Subgroup.normalizer (C : Set M)
  obtain ⟨c,hc⟩ := exists_prime_orderOf_dvd_card' (G := C) 3 (by rw [hC])
  let cN : N := ⟨c,C.le_normalizer c.property⟩
  let f : N →* G := M.subtype.comp N.subtype
  have hf : Function.Injective f := M.subtype_injective.comp N.subtype_injective
  have hec : eN cN ∈ scalar.range := by
    rw [heN,←heC]
    exact mem_map_of_mem (e.toMonoidHom.comp π) c.property
  have hd : 180 ∣ Nat.card (centralizer ({f cN} : Set G)) :=
    Theory.GroupTheory.QuasithinM23.marked_scalar_centralizer_card_multiple f hf eN cN hec
  have hcG : orderOf (f cN) = 3 := (orderOf_injective f hf cN).trans
    ((Subgroup.orderOf_coe cN).symm.trans ((Subgroup.orderOf_coe c).trans hc))
  let X := centralizer ({f cN} : Set G)
  let Z := Theory.GroupTheory.QuasithinM23.centralizerCyclic (f cN)
  let Q := Theory.GroupTheory.QuasithinM23.cubicCentralizerQuotient (f cN)
  let q := QuotientGroup.mk' Z
  have hZ : Nat.card Z = 3 := by rw [Nat.card_zpowers,←Subgroup.orderOf_coe]; exact hcG
  have hprod : Nat.card X = 3 * Nat.card Q := by
    have hh := Z.card_mul_index
    rw [hZ,index_eq_card] at hh
    exact hh.symm
  have h5X : 5 ∣ Nat.card X := dvd_trans (by decide : 5 ∣ 180) hd
  have h5Q : 5 ∣ Nat.card Q := by
    rw [hprod] at h5X
    exact (Nat.Prime.dvd_mul (by decide : Nat.Prime 5)).mp h5X |>.resolve_left (by decide)
  obtain ⟨t,ht⟩ := exists_prime_orderOf_dvd_card' (G := X) 2 (dvd_trans (by decide : 2 ∣ 180) hd)
  have hqt : orderOf (q t) = 2 := by
    apply orderOf_eq_prime
    · simpa only [map_pow,map_one,ht] using congrArg q (pow_orderOf_eq_one t)
    · intro hh
      have hh1 := OddCentralLifting.kernel_involution_eq_one q
        (by rw [QuotientGroup.ker_mk',hZ]; decide) hh (ht ▸ pow_orderOf_eq_one t)
      simp [hh1] at ht
  obtain ⟨hfus,hfour⟩ := d.linear_nonmaximal_cubic_quotient_centralizers h hH hp E hm hE he hnonmax (f cN) hcG
  obtain ⟨hcard,hel⟩ := hfour (q t) hqt
  have hA5 : Nonempty (Q ≃* alternatingGroup (Fin 5)) :=
    alternating_five_of_four_centralizer (q t) hqt hcard hel hfus h5Q
  have hQcard : Nat.card Q = 60 := by
    rw [Nat.card_congr hA5.some.toEquiv,nat_card_alternatingGroup]
    norm_num [Nat.factorial]
  have hXcard : Nat.card X = 180 := by rw [hprod,hQcard]
  have hcyc : C = zpowers (c : M) := by
    symm
    apply eq_of_le_of_card_ge (zpowers_le.mpr c.property)
    rw [Nat.card_zpowers,Subgroup.orderOf_coe,hc,hC]
  have hCG : C.map M.subtype = zpowers (f cN) := by
    rw [hcyc,MonoidHom.map_zpowers]
    rfl
  have hcent : Nat.card (centralizer (C.map M.subtype : Set G)) = 180 := by
    rw [hCG,zpowers_eq_closure,centralizer_closure]
    exact hXcard
  have hbound := normalizer_card_le_twice_centralizer (C.map M.subtype)
    (by rw [card_map_of_injective M.subtype_injective,hC])
  rw [hcent] at hbound
  have hNle : N.map M.subtype ≤ Subgroup.normalizer (C.map M.subtype : Set G) :=
    le_normalizer_map M.subtype
  have hNeq : N.map M.subtype = Subgroup.normalizer (C.map M.subtype : Set G) := by
    apply eq_of_le_of_card_ge hNle
    rw [card_map_of_injective M.subtype_injective,Nat.card_congr eN.toEquiv,gamma_card]
    exact hbound
  let eNG := (N.equivMapOfInjective M.subtype M.subtype_injective).trans (MulEquiv.subgroupCongr hNeq)
  exact ⟨e,heL,C,heC,hC,hP,hcomp,⟨eN,heN⟩,hNeq.symm,⟨eNG.symm.trans eN⟩⟩


end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
