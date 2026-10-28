module

public import CFSG.Quasithin.ChapterE.Section06.InvariantSubspaces.BlockSelection.Residual.LowRankIndex.Contracts
public import Theory.GroupTheory.OddPrimeRankOneSylow
public import Theory.GroupTheory.SpecificGroups.KleinFourAut
public import Theory.GroupTheory.PResidual.SubnormalCoreAction

/-!
# The normal A₃ index calculation

The binary module of an alternating-three block has order four.  Its literal
conjugation action extends along the relative normalizer, and hence to every
ambient normalizer of the block.  The target automorphism group has order six;
the nontrivial A₃ image and cyclic ambient Sylow-three subgroups then force a
three-prime relative index. More precisely, two-perfection gives `[U,L] = U`,
so the induced action of the order-three quotient is nontrivial and has kernel
exactly `O₂(L)`. Choose an element of order three in L and extend its cyclic
subgroup to a Sylow subgroup of H. Cyclicity makes that Sylow action faithful:
any nontrivial kernel would contain its unique subgroup of order three. Its
order therefore divides six and is at most three, so the Sylow subgroup lies
in L. This proves the required coprimality without an A₄ identification.

Source: Aschbacher--Smith, C.1.7 and C.1.12--13, printed pp.123--125,
and the proof of E.6.14, printed p.251 (PDF p.262).
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterE.Section06.InvariantSubspaces.BlockSelection

open CFSG.Quasithin.ChapterC

variable {G : Type*} [Group G]
variable {L H : Subgroup G}

private theorem blockFixed_map_normalizer (n : normalizer (L : Set G)) :
    (blockFixed L).map
        (MulAut.characteristic (blockU L) (L.normalizerMonoidHom n)).toMonoidHom =
      blockFixed L := by
  apply Subgroup.map_subtype_inj.mp
  rw [Subgroup.map_map]
  have hcomp :
      (blockU L).subtype.comp
          (MulAut.characteristic (blockU L) (L.normalizerMonoidHom n)).toMonoidHom =
        (L.normalizerMonoidHom n).toMonoidHom.comp (blockU L).subtype := by
    ext u
    rfl
  rw [hcomp, ← Subgroup.map_map, blockFixed_map]
  rw [Subgroup.map_inf _ _ (L.normalizerMonoidHom n).toMonoidHom
    (L.normalizerMonoidHom n).injective]
  rw [characteristic_iff_map_eq.mp inferInstance (L.normalizerMonoidHom n),
    characteristic_iff_map_eq.mp centerCharacteristic (L.normalizerMonoidHom n)]

private def normalizerBlockAut (n : normalizer (L : Set G)) : MulAut (BlockModule L) :=
  QuotientGroup.congr (blockFixed L) (blockFixed L)
    (MulAut.characteristic (blockU L) (L.normalizerMonoidHom n))
    (by
      change (blockFixed L).map
        (MulAut.characteristic (blockU L) (L.normalizerMonoidHom n)).toMonoidHom =
        blockFixed L
      exact blockFixed_map_normalizer n)

private def normalizerBlockAction : normalizer (L : Set G) →* MulAut (BlockModule L) :=
  { toFun := fun n =>
      normalizerBlockAut n
    map_one' := by
      apply MulEquiv.ext
      intro x
      induction x using Quotient.inductionOn with
      | h u =>
        change normalizerBlockAut (L := L) 1 (QuotientGroup.mk' (blockFixed L) u) = _
        rw [normalizerBlockAut, QuotientGroup.congr_mk']
        simp
    map_mul' := by
      intro n m
      apply MulEquiv.ext
      intro x
      induction x using Quotient.inductionOn with
      | h u =>
        change normalizerBlockAut (L := L) (n * m) (QuotientGroup.mk' (blockFixed L) u) =
          (normalizerBlockAut (L := L) n * normalizerBlockAut (L := L) m)
            (QuotientGroup.mk' (blockFixed L) u)
        change normalizerBlockAut (L := L) (n * m) (QuotientGroup.mk' (blockFixed L) u) =
          normalizerBlockAut (L := L) n
            (normalizerBlockAut (L := L) m (QuotientGroup.mk' (blockFixed L) u))
        rw [normalizerBlockAut, normalizerBlockAut, normalizerBlockAut,
          QuotientGroup.congr_mk', QuotientGroup.congr_mk', QuotientGroup.congr_mk']
        simp [MulAut.characteristic] }

private theorem normalizerBlockAction_apply (n : normalizer (L : Set G))
    (u : blockU L) :
    normalizerBlockAction n (QuotientGroup.mk' (blockFixed L) u) =
      QuotientGroup.mk' (blockFixed L)
        (MulAut.characteristic (blockU L) (L.normalizerMonoidHom n) u) := by
  change normalizerBlockAut n (QuotientGroup.mk' (blockFixed L) u) = _
  rw [normalizerBlockAut, QuotientGroup.congr_mk']

private def relativeNormalizerHom (hLH : L ≤ H) (hN : (L.subgroupOf H).Normal) :
    H →* normalizer (L : Set G) where
  toFun h :=
    ⟨(h : G), (normal_subgroupOf_iff_le_normalizer hLH).mp hN h.property⟩
  map_one' := rfl
  map_mul' _ _ := rfl

private def subgroupNormalizerHom : L →* normalizer (L : Set G) where
  toFun l := ⟨(l : G), Subgroup.le_normalizer l.property⟩
  map_one' := rfl
  map_mul' _ _ := rfl

private def intrinsicBlockAction : L →* MulAut (BlockModule L) :=
  normalizerBlockAction.comp subgroupNormalizerHom

private theorem intrinsicBlockAction_apply (l : L) (u : blockU L) :
    intrinsicBlockAction l (QuotientGroup.mk' (blockFixed L) u) =
      QuotientGroup.mk' (blockFixed L) (blockConjugate L l u) := by
  rw [intrinsicBlockAction, MonoidHom.comp_apply, normalizerBlockAction_apply]
  rfl

private def ambientBlockAction (hLH : L ≤ H) (hN : (L.subgroupOf H).Normal) :
    H →* MulAut (BlockModule L) :=
  normalizerBlockAction.comp (relativeNormalizerHom hLH hN)

private theorem blockU_commutator_eq {K : Type*} [Group K] (h : IsShort K) :
    ⁅blockU K, (⊤ : Subgroup K)⁆ = blockU K := by
  let := h.finite
  exact Subgroup.commutator_isPPerfect_idempotent (⊤ : Subgroup K) (pCore 2 K)
    (h.twoPerfect.of_surjective (Subgroup.topEquiv (G := K)).symm.toMonoidHom
      (Subgroup.topEquiv (G := K)).symm.surjective)
    pCore_isPGroup (by rw [Subgroup.normalizer_eq_top])

private theorem alternatingThree_quotient_card (h : IsAlternatingBlock L 3) :
    Nat.card (L ⧸ pCore 2 L) = 3 := by
  obtain ⟨e⟩ := h.2.2.quotient_iso
  rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup]
  norm_num

/-- The literal action is faithful modulo the two-core. -/
private theorem intrinsic_action_range_card (h : IsAlternatingBlock L 3) :
    Nat.card (intrinsicBlockAction (G := G) (L := L)).range = 3 ∧
      (intrinsicBlockAction (G := G) (L := L)).ker = pCore 2 L := by
  let hs : IsShort L := h.2.1
  let : Finite L := hs.finite
  let : IsElementaryAbelian 2 (blockU L) := hs.elementary
  let σ := intrinsicBlockAction (G := G) (L := L)
  have hσ (l : L) (u : blockU L) :
      σ l (QuotientGroup.mk' (blockFixed L) u) =
        QuotientGroup.mk' (blockFixed L) (blockConjugate L l u) :=
    intrinsicBlockAction_apply l u
  have hker : pCore 2 L ≤ σ.ker := hs.core_le_moduleAction_ker σ hσ
  have hdiv : Nat.card σ.range ∣ 3 := by
    calc
      Nat.card σ.range = σ.ker.index := (Subgroup.index_ker σ).symm
      _ ∣ (pCore 2 L).index := Subgroup.index_dvd_of_le hker
      _ = 3 := by rw [Subgroup.index_eq_card, alternatingThree_quotient_card h]
  have hnontriv : σ ≠ 1 := by
    intro he
    have hfix (l : L) (u : blockU L) :
        QuotientGroup.mk' (blockFixed L) (blockConjugate L l u) =
          QuotientGroup.mk' (blockFixed L) u := by
      rw [← hσ l u, he]
      rfl
    have hcomm : ⁅blockU L, (⊤ : Subgroup L)⁆ ≤ center L := by
      apply commutator_le.mpr
      intro u hu l hl
      let u' : blockU L := ⟨u, hu⟩
      have heq := QuotientGroup.eq.mp (hfix l u')
      have hc : ((blockConjugate L l u' : blockU L) : L)⁻¹ * (u' : L) ∈
          (blockFixed L).map (blockU L).subtype := by
        exact mem_map_of_mem _ heq
      rw [blockFixed_map] at hc
      have hc' : ((blockConjugate L l u' : blockU L) : L)⁻¹ * (u' : L) ∈
          center L := hc.2
      have heq' : (u' : L)⁻¹ * l * (u' : L) * l⁻¹ ∈ center L := by
        simpa [blockConjugate, mul_assoc] using (center L).inv_mem hc'
      have huinv : (u' : L)⁻¹ = (u' : L) := by
        apply inv_eq_of_mul_eq_one_left
        simpa [pow_two] using congrArg Subtype.val
          (Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
            (IsElementaryAbelian.exponent_dvd_p 2 (blockU L)) u')
      change (u' : L) * l * (u' : L)⁻¹ * l⁻¹ ∈ center L
      simpa [commutatorElement_def, huinv, mul_assoc] using heq'
    have hle : blockU L ≤ center L := by
      rw [← blockU_commutator_eq hs]
      exact hcomm
    apply hs.blockFixed_ne_top
    apply top_unique
    intro u hu
    exact hle u.property
  rcases (Nat.dvd_prime (by decide : Nat.Prime 3)).mp hdiv with h1 | h3
  · have hrange : σ.range = ⊥ := σ.range.eq_bot_iff_card.mpr h1
    exact False.elim (hnontriv (σ.range_eq_bot_iff.mp hrange))
  · have hindexrange : σ.ker.index = 3 := by
      rw [Subgroup.index_ker, h3]
    have hindexcore : (pCore 2 L).index = 3 := by
      rw [Subgroup.index_eq_card, alternatingThree_quotient_card h]
    have hkerEq : σ.ker = pCore 2 L := by
      apply le_antisymm
      · by_contra hnele
        have hneq : pCore 2 L ≠ σ.ker := by
          intro heq
          exact hnele (heq ▸ le_rfl)
        have hlt : pCore 2 L < σ.ker := lt_of_le_of_ne hker hneq
        have hslt := Subgroup.index_strictAnti hlt
        rw [hindexrange, hindexcore] at hslt
        omega
      · exact hker
    exact ⟨h3, hkerEq⟩

private def blockInclusion (hLH : L ≤ H) : L →* H where
  toFun l := ⟨(l : G), hLH l.property⟩
  map_one' := rfl
  map_mul' _ _ := rfl

private theorem ambient_restrict_eq_intrinsic (hLH : L ≤ H)
    (hN : (L.subgroupOf H).Normal) :
    (ambientBlockAction hLH hN).comp (blockInclusion hLH) =
      intrinsicBlockAction (G := G) (L := L) := by
  apply MonoidHom.ext
  intro l
  apply MulEquiv.ext
  intro v
  induction v using Quotient.inductionOn with
  | h u =>
      change normalizerBlockAction
          (relativeNormalizerHom hLH hN (blockInclusion hLH l))
          (QuotientGroup.mk' (blockFixed L) u) =
        normalizerBlockAction (subgroupNormalizerHom l)
          (QuotientGroup.mk' (blockFixed L) u)
      rw [normalizerBlockAction_apply, normalizerBlockAction_apply]
      rfl

/-- A finite cyclic group has a unique subgroup of order three. -/
private theorem three_torsion_mem_zpowers {P : Type*} [Group P] [Finite P] [IsCyclic P]
    (x y : P) (hx : x ^ 3 = 1) (hy : orderOf y = 3) : x ∈ zpowers y := by
  let : CommGroup P := IsCyclic.commGroup
  let T := (powMonoidHom 3 : P →* P).ker
  have hT : Nat.card T ≤ 3 := by
    rw [IsCyclic.card_powMonoidHom_ker]
    exact Nat.gcd_le_right _ (by decide)
  have hyT : zpowers y ≤ T := zpowers_le.mpr (by
    change y ^ 3 = 1
    rw [← hy]
    exact pow_orderOf_eq_one y)
  have heq : zpowers y = T := eq_of_le_of_card_ge hyT (by
    rw [Nat.card_zpowers, hy]
    exact hT)
  rw [heq]
  exact hx

private theorem cyclic_three_action_injective {P A : Type*} [Group P] [Group A]
    [Finite P] [IsCyclic P] (hP : IsPGroup 3 P) (f : P →* A)
    (x : P) (hx : orderOf x = 3) (hfx : f x ≠ 1) : Function.Injective f := by
  apply (MonoidHom.ker_eq_bot_iff f).mp
  by_contra hn
  have hk : Nontrivial f.ker := Finite.one_lt_card_iff_nontrivial.mp
    (f.ker.one_lt_card_iff_ne_bot.mpr hn)
  obtain ⟨n, hn, hc⟩ := (hP.to_subgroup f.ker).nontrivial_iff_card.mp hk
  have hd : 3 ∣ Nat.card f.ker := by
    rw [hc]
    exact dvd_pow_self 3 (by omega)
  obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' 3 hd
  have hyP : orderOf (y : P) = 3 :=
    (orderOf_injective f.ker.subtype f.ker.subtype_injective y).trans hy
  have hxY := three_torsion_mem_zpowers x (y : P) (hx ▸ pow_orderOf_eq_one x) hyP
  exact hfx ((zpowers_le.mpr y.property : zpowers (y : P) ≤ f.ker) hxY)

/-- A normal alternating-three block has three-prime relative index whenever
the containing subgroup has three-rank at most one. -/
theorem alternatingThreeNormalIndexInput (G : Type*) [Group G] [Finite G] :
    AlternatingThreeNormalIndexInput G := by
  intro H L hLH hL hN hrank
  let : Finite H := Finite.of_injective H.subtype Subtype.coe_injective
  let : Finite L := Finite.of_injective L.subtype Subtype.coe_injective
  let : IsElementaryAbelian 2 (blockU L) := hL.2.1.elementary
  let : IsElementaryAbelian 2 (BlockModule L) := hL.2.1.module_elementary
  let : Nontrivial (BlockModule L) := hL.2.1.module_nontrivial
  have hmodule : Nat.card (BlockModule L) = 4 :=
    hL.module_card_odd (by decide)
  let : IsKleinFour (BlockModule L) := by
    constructor
    · exact hmodule
    · exact IsElementaryAbelian.exponent_eq_prime
  have hAut : Nat.card (MulAut (BlockModule L)) = 6 :=
    IsKleinFour.card_mulAut (BlockModule L)
  let σL := intrinsicBlockAction (G := G) (L := L)
  have hσLker : σL.ker = pCore 2 L :=
    (intrinsic_action_range_card hL).2
  let σH := ambientBlockAction hLH hN
  have hσrestrict : σH.comp (blockInclusion hLH) = σL := by
    exact ambient_restrict_eq_intrinsic hLH hN
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := L) 3 (by
    rw [← alternatingThree_quotient_card hL]
    exact Subgroup.card_dvd_of_surjective (QuotientGroup.mk' (pCore 2 L))
      (QuotientGroup.mk'_surjective _))
  let xH : H := blockInclusion hLH x
  have hxH : orderOf xH = 3 :=
    (orderOf_injective (blockInclusion hLH)
      (Subgroup.inclusion_injective hLH) x).trans hx
  have hxact : σH xH ≠ 1 := by
    intro he
    have hxker : x ∈ σL.ker := by
      change σL x = 1
      rw [← hσrestrict]
      exact he
    rw [hσLker] at hxker
    have hcop := (pCore_isPGroup (p := 2) (G := L)).orderOf_coprime
      (by decide : Nat.Coprime 2 3) (⟨x, hxker⟩ : pCore 2 L)
    have horder : orderOf (⟨x, hxker⟩ : pCore 2 L) = 3 :=
      (orderOf_injective (pCore 2 L).subtype Subtype.val_injective _).symm.trans hx
    rw [horder] at hcop
    norm_num at hcop
  have hxp : IsPGroup 3 (zpowers xH) := IsPGroup.of_card (n := 1)
    (by simpa only [Nat.card_zpowers, pow_one] using hxH)
  obtain ⟨P, hxP⟩ := hxp.exists_le_sylow
  let : IsCyclic P := P.isCyclic_of_odd_of_primeRank_le_one (by decide) hrank
  let xP : P := ⟨xH, hxP (mem_zpowers xH)⟩
  let f := σH.comp (P : Subgroup H).subtype
  have hinj : Function.Injective f := cyclic_three_action_injective P.isPGroup' f xP
    ((orderOf_injective (P : Subgroup H).subtype Subtype.val_injective xP).symm.trans hxH)
    hxact
  have hdiv : Nat.card P ∣ 6 := hAut ▸ Subgroup.card_dvd_of_injective f hinj
  obtain ⟨n, hn⟩ := P.isPGroup'.exists_card_eq
  have hcop : Nat.Coprime (Nat.card P) 2 := by
    rw [hn]
    exact (by decide : Nat.Coprime 3 2).pow_left n
  have hsmall : Nat.card P ≤ 3 := Nat.le_of_dvd (by decide)
    (hcop.dvd_of_dvd_mul_left hdiv)
  have heq : zpowers xH = (P : Subgroup H) := eq_of_le_of_card_ge hxP (by
    rwa [Nat.card_zpowers, hxH])
  have hPL : (P : Subgroup H) ≤ L.subgroupOf H := by
    rw [← heq]
    exact zpowers_le.mpr x.property
  exact (Nat.Prime.coprime_iff_not_dvd (by decide : Nat.Prime 3)).mpr
    (fun hd => P.not_dvd_index (hd.trans (Subgroup.index_dvd_of_le hPL)))

end CFSG.Quasithin.ChapterE.Section06.InvariantSubspaces.BlockSelection
