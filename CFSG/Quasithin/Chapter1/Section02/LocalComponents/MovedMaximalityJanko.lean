module
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.MovedMaximality
public import Theory.SpecificGroups.Janko1.PerfectSubgroupCore
public import Theory.SpecificGroups.Janko1.Model.InvolutionCentralizer.Identification
public import Theory.SpecificGroups.Janko1.Model.Certification.InvolutionFusion
public import Theory.GroupTheory.PerfectCentralCoverAbelianSylow
public import Theory.SpecificGroups.PSL2.OddAutomorphismRank
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.Restriction
public import Theory.SpecificGroups.Suzuki.StandardSubgroups
public import Theory.SpecificGroups.SL2.OddProjectiveNonsolvable
public import Theory.SpecificGroups.PSL2.RootTwoRank
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.IndexTwo.SmallSylow

/-!
# The J₁ containing case for moved local components

A perfect subgroup of the actual J₁ matrix group has central two-core by
its Sylow order eight. Abelian Sylow transfer kills this core. The actual
involution centralizer is C₂ × A₅, so a nontrivial perfect subgroup
centralizing an involution is A₅.

For a subgroup in the moved-component four-model list, the certified J₁
order excludes binary PSL₂ other than A₅ and excludes Suzuki. An odd-prime
PSL₂ local component is simple and normalized by the elementary full Sylow.
Unless it is A₅, its Sylow action is faithful by the centralizer calculation,
contradicting the prime-field automorphism two-rank bound. The remaining
J₁ model fills the containing group.

Restricting the original Sylow to the containing component and transporting
through its literal two-core quotient proves the Chapter 1 chain statement.
Together with the existing rank-one exclusions, this leaves only a
Sylow-invariant proper overcomponent. Exclusion of that case is still
required for source 1.2.8(3).

Source: Aschbacher--Smith, A.3.12(15), printed pp.47--48, and
1.2.8(2--3), printed pp.506--507 of `refs/quasithin.pdf`.
-/

public section

open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter1.Section02.MovedMaximality
attribute [local irreducible] Janko1.matrixGroup Janko1.matrixA Janko1.matrixB

private theorem janko_perfect_twoCore_eq_bot (B : Subgroup Janko1.Model) [Group.IsPerfect B] :
    pCore 2 B = ⊥ := by
  let S : Sylow 2 B := Classical.choice inferInstance
  obtain ⟨T,hST⟩ := (S.isPGroup'.map B.subtype).exists_le_sylow
  let := Janko1.SylowTwo.elementary T
  have hc : IsMulCommutative S := .of_comm fun x y => by
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun t : T => (t : Janko1.Model))
      (mul_comm' (⟨x,hST (mem_map_of_mem B.subtype x.property)⟩ : T)
        ⟨y,hST (mem_map_of_mem B.subtype y.property)⟩)
  have hk := PerfectCentralCovering.not_dvd_card_kernel_of_abelian_sylow
    (QuotientGroup.mk' (pCore 2 B))
    (by rw [QuotientGroup.ker_mk']; exact Janko1.perfect_subgroup_pCore_two_le_center B) S hc
  rw [QuotientGroup.ker_mk'] at hk
  exact card_eq_one.mp (pCore_isPGroup.card_eq_or_dvd.resolve_right hk)

private theorem perfect_first_trivial {P : Type*} [Group P] [Group.IsPerfect P]
    (f : P →* Janko1.InvolutionCentralizer.ProductModel) (x : P) : (f x).1 = 1 := by
  let a := (MonoidHom.fst _ _).comp f
  let := Group.IsPerfect.range a
  have hs : Subsingleton a.range := Group.IsPerfect.subsingleton_of_isMulCommutative
  exact congrArg Subtype.val (hs.elim (a.rangeRestrict x) 1)

private theorem janko_perfect_involution_centralizer
    (B : Subgroup Janko1.Model) [Group.IsPerfect B] [Nontrivial B]
    (z : Janko1.Model) (hz : orderOf z = 2)
    (hBz : B ≤ centralizer ({z} : Set Janko1.Model)) :
    Nonempty (B ≃* alternatingGroup (Fin 5)) := by
  obtain ⟨g,hg⟩ := Janko1.involution_fusion_of_card Janko1.card_model z hz
  change (MulAut.conj g) z = Janko1.a at hg
  let j : B →* Janko1.InvolutionCentralizer.subgroup :=
    ((MulAut.conj g).toMonoidHom.comp B.subtype).codRestrict _ (by
      intro b
      apply mem_centralizer_singleton_iff.mpr
      have hb := congrArg (MulAut.conj g) (mem_centralizer_singleton_iff.mp (hBz b.property))
      change (MulAut.conj g) b * Janko1.a = Janko1.a * (MulAut.conj g) b
      simpa only [map_mul,hg] using hb)
  have hj : Function.Injective j := fun a b he => Subtype.ext
    ((MulAut.conj g).injective (congrArg Subtype.val he))
  let f := Janko1.InvolutionCentralizer.productEquiv.toMonoidHom.comp j
  have hf : Function.Injective f := Janko1.InvolutionCentralizer.productEquiv.injective.comp hj
  let a : B →* alternatingGroup (Fin 5) := (MonoidHom.snd _ _).comp f
  have ha : Function.Injective a := by
    intro x y hxy
    apply hf
    apply Prod.ext
    · rw [perfect_first_trivial f x,perfect_first_trivial f y]
    · exact hxy
  have ht : a.range = ⊤ := by
    by_contra hn
    let := alternatingGroup.isSolvable_subgroup_of_equiv_five
      (MulEquiv.refl _) a.range hn
    exact Group.IsPerfect.not_isSolvable B
      (Group.isSolvable_of_isSolvable_injective
        (f := a.rangeRestrict) (fun x y he => ha (congrArg Subtype.val he)))
  exact ⟨MulEquiv.ofBijective a ⟨ha,MonoidHom.range_eq_top.mp ht⟩⟩


private theorem janko_normalized_nonA5_aut_rank
    (S : Sylow 2 Janko1.Model) (B : Subgroup Janko1.Model)
    [Group.IsPerfect B] [Nontrivial B]
    (hn : (S : Subgroup Janko1.Model) ≤ normalizer (B : Set Janko1.Model))
    (hnot : ¬ Nonempty (B ≃* alternatingGroup (Fin 5))) :
    3 ≤ primeRank 2 (MulAut B) := by
  let f : S →* MulAut B := B.normalizerMonoidHom.comp (inclusion hn)
  have hf : Function.Injective f := by
    apply (MonoidHom.ker_eq_bot_iff _).mp
    by_contra hk
    have hkp : IsPGroup 2 f.ker := S.isPGroup'.to_subgroup _
    have hd : 2 ∣ Nat.card f.ker := hkp.card_eq_or_dvd.resolve_left
      (fun hc => hk (card_eq_one.mp hc))
    obtain ⟨z,hz⟩ := exists_prime_orderOf_dvd_card' 2 hd
    have hzg : orderOf (((z : S) : Janko1.Model)) = 2 := by
      rw [Subgroup.orderOf_coe,Subgroup.orderOf_coe,hz]
    have hzc : ((z : S) : Janko1.Model) ∈ centralizer (B : Set Janko1.Model) := by
      have hh : inclusion hn (z : S) ∈ B.normalizerMonoidHom.ker := z.property
      rw [normalizerMonoidHom_ker] at hh
      exact hh
    apply hnot
    apply janko_perfect_involution_centralizer B _ hzg
    intro b hb
    exact mem_centralizer_singleton_iff.mpr (hzc b hb)
  let := Janko1.SylowTwo.elementary S
  have hr : 3 ≤ primeRank 2 S := by
    rw [← S.primeRank_eq]
    exact IsElementaryAbelian.primeRank_ge_of_card S.toSubgroup (Janko1.SylowTwo.card S)
  exact hr.trans (_root_.primeRank_le_of_injective 2 f hf)

variable {G : Type*} [Group G] [Finite G]

private theorem local_simple_normalized_of_abelian_sylow
    (S : Sylow 2 G) [IsMulCommutative S] {B : Subgroup G}
    (hB : B ∈ ChapterA.Section03.localCComponents S)
    [IsSimpleGroup B] [Group.IsPerfect B] :
    (S : Subgroup G) ≤ normalizer (B : Set G) := by
  let H := B ⊔ (S : Subgroup G)
  let D := B.subgroupOf H
  let e : D ≃* B := subgroupOfEquivOfLe le_sup_left
  let : IsSimpleGroup D := e.isSimpleGroup
  let : Group.IsPerfect D := hB.perfect
  have hz : center D = ⊥ := (inferInstance : (center D).Normal).eq_bot_or_eq_top.resolve_right
    (fun he => Group.IsPerfect.not_isMulCommutative D (center_eq_top_iff.mp he))
  let : IsQuasisimple D := ⟨((QuotientGroup.quotientMulEquivOfEq hz).trans
    QuotientGroup.quotientBot).isSimpleGroup⟩
  have hD : IsComponent H D := ⟨hB.subnormal,inferInstance⟩
  let U := S.subtype (show (S : Subgroup G) ≤ H from le_sup_right)
  obtain ⟨P,hP⟩ := U.exists_subgroupOf_eq_of_subnormal D hD.1
  have hp := P.ne_bot_of_dvd_card
    (IndexTwo.two_dvd_card_of_not_isSolvable (Group.IsPerfect.not_isSolvable D))
  let : Nontrivial P := (nontrivial_iff_ne_bot _).mpr hp
  obtain ⟨x,hx,hx1⟩ := (P : Subgroup D).exists_ne_one_of_nontrivial
  have hxS : ((x : H) : G) ∈ (S : Subgroup G) := by
    rw [hP] at hx
    exact hx
  intro s hs
  let t : H := ⟨s,(show (S : Subgroup G) ≤ H from le_sup_right) hs⟩
  have hn : D.conjBy t = D := by
    by_contra hne
    have hc := (hD.map_conj t).commutator_eq_bot_of_ne hD hne
    have hfix : (MulAut.conj t) (x : H) = x := by
      apply Subtype.ext
      change s * ((x : H) : G) * s⁻¹ = (x : H)
      have he := congrArg (fun u : S => (u : G))
        (isMulCommutative_iff.mp (inferInstance : IsMulCommutative S)
          (⟨s,hs⟩ : S) ⟨x,hxS⟩)
      change s * ((x : H) : G) = ((x : H) : G) * s at he
      rw [he,mul_inv_cancel_right]
    have hxD : (x : H) ∈ D.conjBy t := hfix ▸ mem_map_of_mem
      (MulAut.conj t).toMonoidHom x.property
    have hxc : x ∈ center D := mem_center_iff.mpr fun y => Subtype.ext
      ((commutator_eq_bot_iff_le_centralizer.mp hc hxD) y y.property)
    exact hx1 (mem_bot.mp (hz ▸ hxc))
  have ht := mem_normalizer_iff_map_conj_eq.mpr hn
  rw [← subgroupOf_normalizer_eq (show B ≤ H from le_sup_left)] at ht
  exact ht


private theorem alternating_five_psl4 {X : Type*} [Group X]
    (e : X ≃* alternatingGroup (Fin 5)) : ClassicalGroup.IsPSL X 2 4 := by
  have hc : Nat.card (GaloisField 2 2) = 4 := by
    rw [GaloisField.card 2 2 (by decide)]; norm_num
  obtain ⟨f⟩ := Matrix.ProjectiveSpecialLinearGroup.equiv_alternatingGroup_of_card_four hc
  exact ⟨GaloisField 2 2, inferInstance, inferInstance, hc, ⟨e.trans f.symm⟩⟩

private theorem janko_local_eq_top_of_moved_model
    (S : Sylow 2 Janko1.Model) (B : Subgroup Janko1.Model)
    (hB : B ∈ ChapterA.Section03.localCComponents S)
    (hm : NonnormalCComponentModel (B ⧸ pCore 2 B))
    (hnot : ¬ ClassicalGroup.IsPSL (B ⧸ pCore 2 B) 2 4) : B = ⊤ := by
  let d : B.subgroupOf (B ⊔ (S : Subgroup Janko1.Model)) ≃* B :=
    subgroupOfEquivOfLe le_sup_left
  let := hB.perfect
  let : Group.IsPerfect B := Group.IsPerfect.ofSurjective (f := d.toMonoidHom) d.surjective
  let : Nontrivial (B.subgroupOf (B ⊔ (S : Subgroup Janko1.Model))) :=
    (nontrivial_iff_ne_bot _).mpr hB.ne_bot
  let : Nontrivial B := d.injective.nontrivial
  let e : (B ⧸ pCore 2 B) ≃* B :=
    (QuotientGroup.quotientMulEquivOfEq (janko_perfect_twoCore_eq_bot B)).trans
      QuotientGroup.quotientBot
  have hnotB : ¬ ClassicalGroup.IsPSL B 2 4 := fun h => hnot (h.of_mulEquiv e)
  have hd : Nat.card B ∣ 175560 := by
    simpa only [Janko1.card_model] using B.card_subgroup_dvd_card
  cases hm.of_mulEquiv e.symm with
  | linear_even n hn hmodel =>
    obtain ⟨F,_,_,hF,⟨f⟩⟩ := hmodel
    let := Fintype.ofFinite F
    let : CharP F 2 := charP_of_card_eq_prime_pow
      (by simpa only [Nat.card_eq_fintype_card] using hF)
    have hc : Nat.card B = 2^n * ((2^n)^2-1) := by
      rw [Nat.card_congr f.toEquiv,
        ← Nat.card_congr (Theory.PSL2.sl2QuotientEquiv F).toEquiv,
        GorensteinWalter.sl2_card_formula,hF]
    have hdiv : 2^n ∣ 175560 := (hc ▸ dvd_mul_right (2^n) ((2^n)^2-1)).trans hd
    have hnle : n ≤ 3 := by
      by_contra! hgt
      have hh : 16 ∣ 175560 := (pow_dvd_pow 2 hgt).trans hdiv
      norm_num at hh
    have hn' : n = 2 ∨ n = 3 := by omega
    rcases hn' with rfl | rfl
    · exact (hnotB ⟨F,inferInstance,inferInstance,hF,⟨f⟩⟩).elim
    · rw [hc] at hd
      norm_num at hd
  | suzuki m hm hmodel =>
    obtain ⟨f⟩ := hmodel
    have hroot := (BenderSuzuki.MatrixGroups.SuzukiRootSubgroup m).card_subgroup_dvd_card
    rw [BenderSuzuki.MatrixGroups.suzukiRootSubgroup_card m (by omega),
      ← Nat.card_congr f.toEquiv] at hroot
    have hh : 64 ∣ 175560 := (show 64 ∣ (2^(2*m+1))^2 by
      rw [← pow_mul]
      exact pow_dvd_pow 2 (show 6 ≤ (2*m+1)*2 by omega)).trans (hroot.trans hd)
    norm_num at hh
  | linear_prime p hp ho hmodel =>
    let : Fact p.Prime := ⟨hp⟩
    obtain ⟨F,_,_,hF,⟨f⟩⟩ := hmodel
    have hlarge : 3 < Nat.card F :=
      Matrix.ProjectiveSpecialLinearGroup.card_gt_three_of_odd_of_not_isSolvable
        (hF ▸ ho) (fun hs => by
          let := hs
          exact Group.IsPerfect.not_isSolvable B
            (Group.isSolvable_of_isSolvable_injective (f := f.toMonoidHom) f.injective))
    let : IsSimpleGroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) F) :=
      Matrix.ProjectiveSpecialLinearGroup.rank_two_simple hlarge
    let : IsSimpleGroup B := f.isSimpleGroup
    let := Janko1.SylowTwo.elementary S
    have hn := local_simple_normalized_of_abelian_sylow S hB
    have hr := janko_normalized_nonA5_aut_rank S B hn
      (fun he => hnotB (alternating_five_psl4 he.some))
    rw [primeRank_equiv 2 (MulAut.congr f)] at hr
    have hu := Theory.PSL2.prime_card_automorphism_two_rank F hF (by omega : 3 < p)
    omega
  | janko hmodel =>
    exact B.eq_top_of_card_eq (Nat.card_congr hmodel.some.toEquiv)


/-- A containing J₁ quotient admits no proper local component in the moved
four-model list with non-PSL₂(4) intrinsic quotient. The original full Sylow
and component inclusion are retained. -/
theorem eq_of_janko_quotient (T : Sylow 2 G) {B K : Subgroup G}
    (hB : B ∈ ChapterA.Section03.localCComponents T) (hK : K.IsCComponent)
    (hBK : B ≤ K) (hm : NonnormalCComponentModel (B ⧸ pCore 2 B))
    (hnot : ¬ ClassicalGroup.IsPSL (B ⧸ pCore 2 B) 2 4)
    (eK : (K ⧸ pCore 2 K) ≃* Janko1.Model) : B = K := by
  obtain ⟨S,hS,hlocal⟩ := ChapterA.Section03.SourceEmbeddings.exists_local_sylow_restriction
    T hB hBK hK.subnormal
  let f : K →* Janko1.Model := eK.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 K))
  have hf : Function.Surjective f := eK.surjective.comp (QuotientGroup.mk'_surjective _)
  have hk : f.ker = pCore 2 K := by
    rw [MonoidHom.ker_comp_of_injective _ _ eK.injective,QuotientGroup.ker_mk']
  let := pCore_isNilpotent (p := 2) (G := K)
  let : Group.IsSolvable f.ker := hk ▸ inferInstance
  let D := (B.subgroupOf K).map f
  have hl : D ∈ ChapterA.Section03.localCComponents (S.mapSurjective hf) :=
    localCComponents_map_of_solvable_ker hlocal f
  have hker : IsPGroup 2 (f.subgroupMap (B.subgroupOf K)).ker := by
    rw [ker_subgroupMap,hk]
    exact pCore_isPGroup.comap_subtype
  let a : (B ⧸ pCore 2 B) ≃* (D ⧸ pCore 2 D) :=
    (QuotientGroup.congr _ _ (subgroupOfEquivOfLe hBK).symm
      (pCore_map_iso 2 (subgroupOfEquivOfLe hBK).symm)).trans
        (MonoidHom.quotientPCoreEquivOfSurjective (f.subgroupMap (B.subgroupOf K))
          (f.subgroupMap_surjective _) hker)
  have ht : D = ⊤ := janko_local_eq_top_of_moved_model (S.mapSurjective hf) D hl
    (hm.of_mulEquiv a.symm) (fun h => hnot (h.of_mulEquiv a))
  have hsup : B.subgroupOf K ⊔ pCore 2 K = ⊤ := by
    have hc := congrArg (comap f) ht
    rw [show D = (B.subgroupOf K).map f from rfl,comap_map_eq,hk,comap_top] at hc
    exact hc
  have hKM : K ≤ B ⊔ (T : Subgroup G) := by
    have hle : (⊤ : Subgroup K) ≤ (B ⊔ (T : Subgroup G)).subgroupOf K := by
      rw [←hsup]
      refine sup_le (comap_mono le_sup_left) ?_
      exact (pCore_isPGroup.le_sylow_of_normal S).trans (by
        rw [hS]; exact comap_mono le_sup_right)
    intro k hkK
    exact hle (show (⟨k,hkK⟩ : K) ∈ (⊤ : Subgroup K) from mem_top _)
  have he := hB.eq_of_le (hK.subgroupOf hKM) (comap_mono hBK)
  simpa only [map_subgroupOf_eq_of_le (show B ≤ B ⊔ (T : Subgroup G) from le_sup_left),
    map_subgroupOf_eq_of_le hKM] using congrArg (map (B ⊔ (T : Subgroup G)).subtype) he


private def intrinsic_quotient_equiv {K H : Subgroup G} (hKH : K ≤ H) :
    ((K.subgroupOf H) ⧸ pCore 2 (K.subgroupOf H)) ≃* (K ⧸ pCore 2 K) :=
  QuotientGroup.congr _ _ (subgroupOfEquivOfLe hKH)
    (pCore_map_iso 2 (subgroupOfEquivOfLe hKH))

/-- The J₁ exclusion in the literal Chapter 1 local family. -/
theorem local_chain_eq_of_janko_quotient (T : Sylow 2 G) {B K : Subgroup G}
    (hB : B ∈ L G (T : Subgroup G)) (hK : K ∈ L G (T : Subgroup G)) (hBK : B ≤ K)
    (hm : NonnormalCComponentModel (B ⧸ pCore 2 B))
    (hnot : ¬ ClassicalGroup.IsPSL (B ⧸ pCore 2 B) 2 4)
    (hmodel : Nonempty ((K ⧸ pCore 2 K) ≃* Janko1.Model)) : B = K := by
  let H := K ⊔ (T : Subgroup G)
  have hBH : B ≤ H := hBK.trans le_sup_left
  let S := T.subtype (show (T : Subgroup G) ≤ H from le_sup_right)
  have hb : B.subgroupOf H ∈ ChapterA.Section03.localCComponents S :=
    ((mem_LIn_iff_subgroupOf le_sup_right hBH).mp ⟨hBH,hB⟩).1
  let eB := intrinsic_quotient_equiv hBH
  let eK := intrinsic_quotient_equiv (show K ≤ H from le_sup_left)
  have he : B.subgroupOf H = K.subgroupOf H := eq_of_janko_quotient S hb hK.1 (comap_mono hBK)
    (hm.of_mulEquiv eB) (fun hh => hnot (hh.of_mulEquiv eB.symm))
    (eK.trans hmodel.some)
  simpa only [map_subgroupOf_eq_of_le hBH,
    map_subgroupOf_eq_of_le (show K ≤ H from le_sup_left)] using congrArg (map H.subtype) he

/-- A strict overcomponent of a moved non-PSL₂(4) local component is
normalized by the original full Sylow. The remaining source embedding
restriction must exclude this alternative to prove maximality. -/
theorem moved_local_chain_eq_or_normalized
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) {B K : Subgroup G}
    (hB : B ∈ L G (T : Subgroup G)) (hK : K ∈ L G (T : Subgroup G)) (hBK : B ≤ K)
    (hm : B < conjugateSpanBy B (T : Subgroup G))
    (hnot : ¬ ClassicalGroup.IsPSL (B ⧸ pCore 2 B) 2 4) :
    B = K ∨ (T : Subgroup G) ≤ normalizer (K : Set G) := by
  rcases local_chain_eq_or_normalized_or_janko hG T hB hK hBK hnot with he | hn | hj
  · exact Or.inl he
  · exact Or.inr hn
  · exact Or.inl (local_chain_eq_of_janko_quotient T hB hK hBK
      (moved_local_model hG T hB hm) hnot hj)

end CFSG.Quasithin.Chapter1.Section02.MovedMaximality
