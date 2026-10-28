module

public import Theory.SpecificGroups.SymmetricEight.FourBlockResidual
public import Theory.GroupTheory.PrimeRankProduct
public import Theory.GroupTheory.PrimeRankCubeFree
public import Theory.SpecificGroups.SymmetricTwoResidual
public import Mathlib.GroupTheory.SpecificGroups.Alternating.KleinFour

/-!
# The four-block prime-to-three residual

The literal block-diagonal embedding identifies R with A₄ × A₄. Three-cycles
in the two blocks generate R; conjugating them by an unordered block
stabilizer again gives internal three-cycles. Thus R is normal in both the
S₈ block stabilizer H and its even subgroup P. Its index in S₈ is 280, so
its relative indices are prime to three. These facts identify the embedded
O^{3′} residual in every subgroup between R and H.

The displayed quotient map has kernel the existing block Klein group
V₄ × V₄. Its quotient is the product of the two literal A₄/V₄ quotients,
an elementary group of order nine. A product embedding gives rank at least
two, while the absence of a factor 3³ in 8! gives the upper bound. The
independent paired-Borel application also uses O²(A₄ × A₄) = A₄ × A₄.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, the
point-centralizer calculation in 12.8.13(5), printed pp.855–856, under the
orthogonal alternative G.11.2(5), printed p.364. This extends the literal
embedding in `Theory.SpecificGroups.SymmetricEight.FourBlockResidual` and
discharges its residual criterion, rather than assuming that criterion's
normality, index, or generation premises.
-/

@[expose] public section
noncomputable section
open Subgroup
open scoped IsMulCommutative
namespace BinaryPermutation.TerminalOrthogonal.FourBlockResidual
abbrev A4 := alternatingGroup (Fin 4)
abbrev Product := A4 × A4

theorem alternating_cubic_generation (N : Subgroup A4)
    (hN : ∀ x : A4, x ^ 3 = 1 → x ∈ N) : N = ⊤ := by
  apply top_unique
  rw [← alternatingGroup.closure_isThreeCycles_eq_top, closure_le]
  intro x hx
  apply hN
  apply Subtype.ext
  change (x : Equiv.Perm (Fin 4)) ^ 3 = 1
  rw [← hx.orderOf]
  exact pow_orderOf_eq_one _

theorem product_cubic_generation (N : Subgroup Product)
    (hN : ∀ x : Product, x ^ 3 = 1 → x ∈ N) : N = ⊤ := by
  have hl : N.comap (MonoidHom.inl A4 A4) = ⊤ :=
    alternating_cubic_generation _ (fun x hx => hN (x, 1) (by ext <;> simp [hx]))
  have hr : N.comap (MonoidHom.inr A4 A4) = ⊤ :=
    alternating_cubic_generation _ (fun x hx => hN (1, x) (by ext <;> simp [hx]))
  apply top_unique
  intro x _
  have ha : (x.1, 1) ∈ N := show x.1 ∈ N.comap (MonoidHom.inl A4 A4) from hl ▸ mem_top _
  have hb : (1, x.2) ∈ N := show x.2 ∈ N.comap (MonoidHom.inr A4 A4) from hr ▸ mem_top _
  simpa using N.mul_mem ha hb

theorem product_primeToResidual : primeToResidual 3 Product = ⊤ := by
  apply product_cubic_generation
  intro x hx
  exact mem_primeToResidual_of_pow (n := 1) (by simpa using hx)

theorem product_pResidual : pResidual 2 Product = ⊤ := by
  apply product_cubic_generation
  intro x hx
  apply mem_pResidual_of_orderOf_coprime
  exact (by decide : Nat.Coprime 2 3).coprime_dvd_right (orderOf_dvd_of_pow_eq_one hx)

theorem a4_card : Nat.card A4 = 12 :=
  alternatingGroup.card_of_card_eq_four (by simp)

theorem product_card : Nat.card Product = 144 := by
  rw [Nat.card_prod, a4_card]

theorem a4_primeRank : primeRank 3 A4 = 1 := by
  apply le_antisymm
  · apply (primeRank_le_iff_elementary_card_le A4).mpr
    intro E hE
    let := hE
    obtain ⟨k, hk⟩ := (IsElementaryAbelian.isPGroup 3 E).exists_card_eq
    have hd := E.card_subgroup_dvd_card
    rw [a4_card, hk] at hd
    have hkle : k ≤ 1 := by
      by_contra! h
      have : 9 ∣ 12 := (show 3 ^ 2 ∣ 3 ^ k from pow_dvd_pow 3 h).trans hd
      norm_num at this
    rw [hk]
    exact Nat.pow_le_pow_right (by decide) hkle
  · obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := A4) 3
      (by rw [a4_card]; decide)
    let C := Subgroup.zpowers z
    let : CommGroup C := IsCyclic.commGroup
    have hc : Nat.card C = 3 := (Nat.card_zpowers z).trans hz
    exact primeRank_ge_of_elementary_embedding (A := C) (p := 3) (e := 1)
      (fun a => by simpa only [hc] using pow_card_eq_one' (x := a))
      (by simpa using hc) C.subtype C.subtype_injective

theorem product_primeRank : primeRank 3 Product = 2 := by
  rw [primeRank_prod_eq_add, a4_primeRank]

end BinaryPermutation.TerminalOrthogonal.FourBlockResidual

namespace BinaryPermutation.TerminalOrthogonal.FourBlockResidual
open Theory.SpecificGroups.SymmetricEight
abbrev S8 := Equiv.Perm (Fin 8)
abbrev H := A6ShadowTwoLocals.fourStabilizer
abbrev P := alternatingGroup (Fin 8) ⊓ H
abbrev R := Theory.SpecificGroups.SymmetricEight.FourBlockResidual.fourBlockResidual
noncomputable def blockHom : Product →* S8 :=
  (alternatingGroup (Fin 8)).subtype.comp
    Theory.SpecificGroups.SymmetricEight.FourBlockResidual.blockAlternatingHom

theorem blockHom_injective : Function.Injective blockHom := by
  intro a b h
  have he := (Equiv.permCongrHom (@finSumFinEquiv 4 4)).injective h
  have hp := @Equiv.Perm.sumCongrHom_injective (Fin 4) (Fin 4)
    ((a.1 : Equiv.Perm (Fin 4)), (a.2 : Equiv.Perm (Fin 4)))
    ((b.1 : Equiv.Perm (Fin 4)), (b.2 : Equiv.Perm (Fin 4))) he
  exact Prod.ext (Subtype.ext (congrArg Prod.fst hp))
    (Subtype.ext (congrArg Prod.snd hp))

theorem blockHom_range : blockHom.range = R := by
  rw [blockHom, MonoidHom.range_comp]
  rfl

noncomputable def productEquiv : Product ≃* R :=
  (MonoidHom.ofInjective blockHom_injective).trans (MulEquiv.subgroupCongr blockHom_range)

@[simp] theorem productEquiv_apply (a : Product) : (productEquiv a : S8) = blockHom a := rfl

theorem R_le_P : R ≤ P :=
  Theory.SpecificGroups.SymmetricEight.FourBlockResidual.fourBlockResidual_le

theorem R_le_H : R ≤ H := R_le_P.trans inf_le_right

theorem R_card : Nat.card R = 144 := by
  rw [← Nat.card_congr productEquiv.toEquiv, product_card]

theorem R_primeRank : primeRank 3 R = 2 := by
  rw [← Theory.GroupTheory.primeRank_equiv 3 productEquiv, product_primeRank]

theorem R_primeToResidual : primeToResidual 3 R = ⊤ := by
  have h := map_primeToResidual (p := 3) productEquiv
  rw [product_primeToResidual, map_top_of_surjective _ productEquiv.surjective] at h
  exact h.symm

theorem R_le_embedded_primeToResidual {J : Subgroup S8} (hJ : R ≤ J) :
    R ≤ (primeToResidual 3 J).map J.subtype := by
  have he : primeToResidual 3 (R.subgroupOf J) = ⊤ := by
    let e := (subgroupOfEquivOfLe hJ).symm
    have h := map_primeToResidual (p := 3) e
    rw [R_primeToResidual, map_top_of_surjective _ e.surjective] at h
    exact h.symm
  have h := map_mono (f := J.subtype) (le_primeToResidual_of_eq_top 3 (R.subgroupOf J) he)
  rwa [map_subgroupOf_eq_of_le hJ] at h

theorem stabilizer_primeRank {J : Subgroup S8} (hJ : R ≤ J) : primeRank 3 J = 2 := by
  apply le_antisymm
  · apply primeRank_le_two_of_cube_not_dvd
    intro hd
    have h := hd.trans J.card_subgroup_dvd_card
    rw [A6ShadowTwoLocals.card_s8] at h
    norm_num at h
  · rw [← R_primeRank]
    exact Theory.GroupTheory.primeRank_le_of_injective 3
      (inclusion hJ) (inclusion_injective hJ)

theorem H_primeRank : primeRank 3 H = 2 := stabilizer_primeRank R_le_H

theorem P_primeRank : primeRank 3 P = 2 := stabilizer_primeRank R_le_P

end BinaryPermutation.TerminalOrthogonal.FourBlockResidual

namespace BinaryPermutation.TerminalOrthogonal.FourBlockResidual
open Theory.SpecificGroups.SymmetricEight
abbrev Klein := alternatingGroup.kleinFour (Fin 4)
instance : Klein.Normal := alternatingGroup.normal_kleinFour (by simp)
abbrev CoreProduct : Subgroup Product := Klein.prod Klein

theorem klein_card : Nat.card Klein = 4 :=
  alternatingGroup.kleinFour_card_of_card_eq_four (by simp)

theorem coreProduct_card : Nat.card CoreProduct = 16 := by
  rw [Nat.card_congr (Klein.prodEquiv Klein).toEquiv, Nat.card_prod, klein_card]

private def fourKlein : Fin 4 → Equiv.Perm (Fin 4) :=
  ![1, Equiv.swap 0 1 * Equiv.swap 2 3, Equiv.swap 0 2 * Equiv.swap 1 3,
    Equiv.swap 0 3 * Equiv.swap 1 2]

private theorem fourKlein_even : ∀ a, fourKlein a ∈ A4 := by
  change ∀ a, Equiv.Perm.sign (fourKlein a) = 1
  decide

private def fourKleinAlt (a : Fin 4) : A4 := ⟨fourKlein a, fourKlein_even a⟩

private theorem fourKlein_mem : ∀ a, fourKleinAlt a ∈ Klein := by
  intro a
  change fourKleinAlt a ∈ (alternatingGroup.kleinFour (Fin 4) : Set A4)
  rw [alternatingGroup.coe_kleinFour_of_card_eq_four (by simp)]
  revert a
  decide

private theorem blockHom_fourKlein : ∀ a b,
    blockHom (fourKleinAlt a, fourKleinAlt b) = FourBlockCoreAction.kleinPerm a b := by
  decide

theorem kleinGroup_card : Nat.card FourBlockCoreAction.kleinGroup = 16 := by
  let f : Fin 4 × Fin 4 → FourBlockCoreAction.kleinGroup :=
    fun x => ⟨FourBlockCoreAction.kleinPerm x.1 x.2, x.1, x.2, rfl⟩
  have hf : Function.Bijective f := by
    constructor
    · intro x y h
      have hi : Function.Injective (fun x : Fin 4 × Fin 4 =>
          FourBlockCoreAction.kleinPerm x.1 x.2) := by decide
      exact hi (congrArg Subtype.val h)
    · rintro ⟨x, a, b, rfl⟩
      exact ⟨(a, b), rfl⟩
  rw [← Nat.card_congr (Equiv.ofBijective f hf)]
  norm_num [Nat.card_prod]

theorem coreProduct_image : CoreProduct.map blockHom = FourBlockCoreAction.kleinGroup := by
  symm
  apply Subgroup.eq_of_le_of_card_ge
  · rintro x ⟨a, b, rfl⟩
    exact ⟨(fourKleinAlt a, fourKleinAlt b), ⟨fourKlein_mem a, fourKlein_mem b⟩,
      blockHom_fourKlein a b⟩
  · rw [kleinGroup_card, ← Nat.card_congr
      (CoreProduct.equivMapOfInjective blockHom blockHom_injective).toEquiv,
      coreProduct_card]

theorem kleinGroup_le_R : FourBlockCoreAction.kleinGroup ≤ R := by
  rw [← coreProduct_image, ← blockHom_range]
  exact map_le_range (f := blockHom) (H := CoreProduct)

instance kleinGroup_elementary : IsElementaryAbelian 2 FourBlockCoreAction.kleinGroup where
  is_comm.comm := by
    rintro ⟨x, a, b, rfl⟩ ⟨y, c, d, rfl⟩
    apply Subtype.ext
    exact (by decide : ∀ a b c d, FourBlockCoreAction.kleinPerm a b *
      FourBlockCoreAction.kleinPerm c d = FourBlockCoreAction.kleinPerm c d *
        FourBlockCoreAction.kleinPerm a b) a b c d
  exponent_dvd_p := by
    rw [Monoid.exponent_dvd_iff_forall_pow_eq_one]
    rintro ⟨x, a, b, rfl⟩
    apply Subtype.ext
    exact (by decide : ∀ a b, FourBlockCoreAction.kleinPerm a b ^ 2 = 1) a b

abbrev E16 : Subgroup R := FourBlockCoreAction.kleinGroup.subgroupOf R

instance E16_normal : E16.Normal := by
  change (FourBlockCoreAction.kleinGroup.subgroupOf R).Normal
  rw [← FourBlockCoreAction.fourStabilizer_pCoreIn]
  exact normal_subgroupOf_of_le_normalizer
    (R_le_H.trans (H.le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image H (pCore 2 H))))

instance E16_elementary : IsElementaryAbelian 2 E16 :=
  IsElementaryAbelian.subgroupOf kleinGroup_le_R

theorem E16_card : Nat.card E16 = 16 := by
  rw [Nat.card_congr (subgroupOfEquivOfLe kleinGroup_le_R).toEquiv, kleinGroup_card]

theorem a4_quotient_card : Nat.card (A4 ⧸ Klein) = 3 := by
  have h : Nat.card A4 = Nat.card (A4 ⧸ Klein) * Nat.card Klein :=
    card_eq_card_quotient_mul_card_subgroup Klein
  rw [a4_card, klein_card] at h
  omega

instance a4_quotient_commutative : IsMulCommutative (A4 ⧸ Klein) :=
  (isCyclic_of_prime_card a4_quotient_card).isMulCommutative

instance a4_quotient_elementary : IsElementaryAbelian 3 (A4 ⧸ Klein) where
  exponent_dvd_p := by
    rw [Monoid.exponent_dvd_iff_forall_pow_eq_one]
    intro x
    simpa only [a4_quotient_card] using pow_card_eq_one' (x := x)

abbrev E9 := (A4 ⧸ Klein) × (A4 ⧸ Klein)

def productQuotientMap : Product →* E9 :=
  (QuotientGroup.mk' Klein).prodMap (QuotientGroup.mk' Klein)

theorem productQuotientMap_surjective : Function.Surjective productQuotientMap :=
  (QuotientGroup.mk'_surjective Klein).prodMap (QuotientGroup.mk'_surjective Klein)

theorem productQuotientMap_ker : productQuotientMap.ker = CoreProduct := by
  ext x
  simp [productQuotientMap, MonoidHom.mem_ker, Prod.ext_iff, QuotientGroup.eq_one_iff, CoreProduct, Subgroup.mem_prod]

noncomputable def quotientMap : R →* E9 := productQuotientMap.comp productEquiv.symm.toMonoidHom

theorem quotientMap_surjective : Function.Surjective quotientMap :=
  productQuotientMap_surjective.comp productEquiv.symm.surjective

theorem quotientMap_ker : quotientMap.ker = E16 := by
  ext x
  change productQuotientMap (productEquiv.symm x) = 1 ↔ (x : S8) ∈ FourBlockCoreAction.kleinGroup
  rw [← MonoidHom.mem_ker, productQuotientMap_ker, ← coreProduct_image]
  constructor
  · intro hx
    exact ⟨productEquiv.symm x, hx, by simp [← productEquiv_apply]⟩
  · rintro ⟨a, ha, he⟩
    have : productEquiv a = x := Subtype.ext he
    simpa [← this] using ha

noncomputable def quotientEquiv : R ⧸ E16 ≃* E9 :=
  (QuotientGroup.quotientMulEquivOfEq quotientMap_ker.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective quotientMap quotientMap_surjective)

@[simp] theorem quotientEquiv_mk (x : R) :
    quotientEquiv (QuotientGroup.mk' E16 x) = quotientMap x := rfl

theorem E9_card : Nat.card E9 = 9 := by
  rw [Nat.card_prod, a4_quotient_card]

instance E9_elementary : IsElementaryAbelian 3 E9 where
  exponent_dvd_p := by
    rw [Monoid.exponent_dvd_iff_forall_pow_eq_one]
    intro x
    apply Prod.ext <;> exact Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
      (IsElementaryAbelian.exponent_dvd_p 3 (A4 ⧸ Klein)) _

theorem quotient_card : Nat.card (R ⧸ E16) = 9 := by
  rw [Nat.card_congr quotientEquiv.toEquiv, E9_card]

instance quotient_elementary : IsElementaryAbelian 3 (R ⧸ E16) where
  is_comm.comm x y := quotientEquiv.injective (by simp [mul_comm])
  exponent_dvd_p := by
    rw [Monoid.exponent_dvd_iff_forall_pow_eq_one]
    intro x
    apply quotientEquiv.injective
    rw [map_pow, map_one]
    exact Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
      (IsElementaryAbelian.exponent_dvd_p 3 E9) _

end BinaryPermutation.TerminalOrthogonal.FourBlockResidual

namespace BinaryPermutation.TerminalOrthogonal.FourBlockResidual
open Theory.SpecificGroups.SymmetricEight
open Equiv

private def triAlt (a b c : Fin 4) : A4 :=
  if h : a ≠ b ∧ b ≠ c then
    ⟨swap a b * swap b c, by
      rw [Perm.mem_alternatingGroup, map_mul, Perm.sign_swap h.1, Perm.sign_swap h.2]
      decide⟩
  else 1

private def blockTriple (a b c : Fin 8) : Product :=
  let t := triAlt ⟨a.val % 4, Nat.mod_lt _ (by decide)⟩
    ⟨b.val % 4, Nat.mod_lt _ (by decide)⟩ ⟨c.val % 4, Nat.mod_lt _ (by decide)⟩
  if a.val / 4 = 0 then (t, 1) else (1, t)

private theorem triple_embedding : ∀ a b c : Fin 8,
    a ≠ b → b ≠ c → a.val / 4 = b.val / 4 → b.val / 4 = c.val / 4 →
    blockHom (blockTriple a b c) = swap a b * swap b c := by decide

private theorem triple_mem_R (a b c : Fin 8) (hab : a ≠ b) (hbc : b ≠ c)
    (h₁ : a.val / 4 = b.val / 4) (h₂ : b.val / 4 = c.val / 4) :
    swap a b * swap b c ∈ R := by
  rw [← triple_embedding a b c hab hbc h₁ h₂, ← blockHom_range]
  exact ⟨_, rfl⟩

private def sidePoint (s : Bool) (i : Fin 4) : Fin 8 :=
  if s then Fin.natAdd 4 i else Fin.castAdd 4 i

private def sidePerm (s : Bool) : Perm (Fin 4) →* S8 :=
  (Equiv.permCongrHom (@finSumFinEquiv 4 4)).toMonoidHom.comp
    ((Perm.sumCongrHom (Fin 4) (Fin 4)).comp
      (if s then MonoidHom.inr _ _ else MonoidHom.inl _ _))

private theorem sidePerm_swap : ∀ s a b,
    sidePerm s (swap a b) = swap (sidePoint s a) (sidePoint s b) := by decide

private theorem sidePoint_injective : ∀ s, Function.Injective (sidePoint s) := by decide
private theorem sidePoint_block : ∀ s i j,
    (sidePoint s i).val / 4 = (sidePoint s j).val / 4 := by decide

private theorem conjugate_side_mem (g : S8) (hg : g ∈ H) (s : Bool) (a : A4) :
    g * sidePerm s a.val * g⁻¹ ∈ R := by
  let f : A4 →* S8 := (MulAut.conj g).toMonoidHom.comp
    ((sidePerm s).comp A4.subtype)
  have htop : R.comap f = ⊤ := by
    apply top_unique
    rw [← alternatingGroup.closure_isThreeCycles_eq_top, closure_le]
    intro x hx
    obtain ⟨i, hi⟩ := Finset.card_pos.mp (by rw [hx.card_support]; decide)
    have hne : i ≠ x.val i := (Perm.mem_support.mp hi).symm
    have hne' := x.val.injective.ne hne
    change g * sidePerm s x.val * g⁻¹ ∈ R
    rw [hx.eq_swap_mul_swap_iff_mem_support.mpr hi, map_mul, sidePerm_swap, sidePerm_swap]
    have he (a b c : Fin 8) :
        g * (swap a b * swap b c) * g⁻¹ = swap (g a) (g b) * swap (g b) (g c) := by
      calc
        _ = (g * swap a b * g⁻¹) * (g * swap b c * g⁻¹) := by simp [mul_assoc]
        _ = _ := by
          rw [Equiv.mul_swap_eq_swap_mul g a b, Equiv.mul_swap_eq_swap_mul g b c]
          simp
    rw [he]
    exact triple_mem_R _ _ _ (g.injective.ne ((sidePoint_injective s).ne hne))
      (g.injective.ne ((sidePoint_injective s).ne hne'))
      ((hg _ _).mpr (sidePoint_block s _ _)) ((hg _ _).mpr (sidePoint_block s _ _))
  exact show a ∈ R.comap f from htop ▸ mem_top _

theorem H_normalizes_R : H ≤ normalizer (R : Set S8) := by
  apply Subgroup.le_normalizer_iff.mpr
  intro g hg x hx
  rw [← blockHom_range] at hx
  obtain ⟨a, rfl⟩ := hx
  have he : blockHom a = sidePerm false a.1.val * sidePerm true a.2.val := by
    change blockHom a = blockHom (a.1, 1) * blockHom (1, a.2)
    rw [← map_mul]
    simp
  rw [he]
  have hl := conjugate_side_mem g hg false a.1
  have hr := conjugate_side_mem g hg true a.2
  simpa only [mul_assoc, inv_mul_cancel_left] using R.mul_mem hl hr

instance R_normal_in_H : (R.subgroupOf H).Normal :=
  normal_subgroupOf_of_le_normalizer H_normalizes_R

instance R_normal_in_P : (R.subgroupOf P).Normal :=
  normal_subgroupOf_of_le_normalizer (inf_le_right.trans H_normalizes_R)

theorem R_index : R.index = 280 := by
  have h := R.card_mul_index
  rw [R_card, A6ShadowTwoLocals.card_s8] at h
  omega

theorem R_relIndex_coprime (J : Subgroup S8) (hJ : R ≤ J) :
    Nat.Coprime 3 (R.subgroupOf J).index := by
  apply (show Nat.Coprime 3 R.index by rw [R_index]; decide).coprime_dvd_right
  exact relIndex_dvd_index_of_le hJ

theorem embedded_primeToResidual_eq (J : Subgroup S8) (hRJ : R ≤ J)
    (hJH : J ≤ H) : (primeToResidual 3 J).map J.subtype = R := by
  let : (R.subgroupOf J).Normal :=
    normal_subgroupOf_of_le_normalizer (hJH.trans H_normalizes_R)
  apply le_antisymm _ (R_le_embedded_primeToResidual hRJ)
  have h := map_mono (f := J.subtype)
    (primeToResidual_le (R.subgroupOf J) (R_relIndex_coprime J hRJ))
  rwa [map_subgroupOf_eq_of_le hRJ] at h

theorem H_residual : (primeToResidual 3 H).map H.subtype = R :=
  embedded_primeToResidual_eq H R_le_H le_rfl

theorem P_residual : (primeToResidual 3 P).map P.subtype = R :=
  embedded_primeToResidual_eq P R_le_P inf_le_right

noncomputable def residualEquiv (J : Subgroup S8) (hRJ : R ≤ J) (hJH : J ≤ H) :
    primeToResidual 3 J ≃* Product :=
  ((primeToResidual 3 J).equivMapOfInjective J.subtype J.subtype_injective).trans
    ((MulEquiv.subgroupCongr (embedded_primeToResidual_eq J hRJ hJH)).trans productEquiv.symm)

end BinaryPermutation.TerminalOrthogonal.FourBlockResidual
