module
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.ExtraspecialFourOvergroups
public import CFSG.Quasithin.ChapterC.Section02.NormalCoreSetup
public import Theory.GroupTheory.MaximalTwoLocalCore
public import CFSG.Quasithin.ChapterA.Section01.RankActions.SourceActions
public import CFSG.Quasithin.Chapter1.Section01QuasisimpleInvolutions.Ambient

/-!
# The original core in an escaping four-group centralizer

Let x lie outside V₁ in the selected elementary central four-group D.
If C_G(x) escapes H, its literal Sylow subgroup S = C_T(x) has index two
in T and acts reducibly on the original extraspecial Frattini quotient.
O₂(H) acts trivially on that quotient. Since T acts irreducibly, the
stabilizer of a proper invariant subgroup is exactly S; hence O₂(H) ≤ S.
This uses the established T-action directly, retaining the original
quotient kernel and avoiding any new R₁-action premise.

The normal intersection J = H ∩ C_G(x) consequently has O₂(J) = O₂(H).
Maximality of H identifies both N_G(O₂(H)) and C(G,O₂(H)) with H. For
every J ≤ G₀ ≤ C_G(x), restriction and the literal product J = KS
construct all of C.2.3, including radicality and the Sylow condition in
the normal closure. Strict overgroups have nontrivial two-core contained
in O₂(H), and L₁ is not normal in any of them.

Separately, the original U = [U,K] and A.1.26 centralize the odd core of
C_G(x). The same original 1.1.5 data makes its intersection with H trivial,
so that odd core vanishes. The last theorem applies these deductions to
the actual D selected from 14.7.25. The three-core and component analysis
of the overgroups, the TI conclusion and the extraspecial exclusion remain
open; no local recognition conclusion is assumed here.

Source: Aschbacher–Smith, refs/quasithin.pdf, 14.7.26, printed pp.1052–1053;
C.2.3, p.144; A.1.26(1), pp.25–26; 1.1.5(1–2), pp.501–502.
-/

public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Subgroup Representation Theory.GroupTheory
open scoped IsMulCommutative Pointwise commutatorElement
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction
open Chapter12.Section08 CriticalFusion.Source Chapter1
open ChapterI.Section06To08
open Chapter14.Section04.LargerDimension.LocalAction.Components
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3}

private theorem frattini_action_core_trivial
    (hn : (T : Subgroup G) ≤ normalizer (K F : Set G))
    (t : T) (ht : (t : G) ∈ F.H.pCoreIn 2)
    (a : XiFrattiniQuotient (K F)) :
    xiFrattiniAction (T : Subgroup G) (K F) hn t a = a := by
  have htcore : (⟨t,F.invariant 1 t.property⟩ : F.H) ∈ pCore 2 F.H := by
    obtain ⟨q,hq,heq⟩ := ht
    exact (show q = ⟨t,F.invariant 1 t.property⟩ from Subtype.ext heq) ▸ hq
  have htz : starMap F ⟨t,F.invariant 1 t.property⟩ = 1 :=
    (QuotientGroup.eq_one_iff _).mpr htcore
  induction a using QuotientGroup.induction_on with | H a =>
    induction a using QuotientGroup.induction_on with | H k =>
      change xiFrattiniAction (T : Subgroup G) (K F) hn t
        (QuotientGroup.mk' _ (QuotientGroup.mk' _ k)) = _
      simp only [xiFrattiniAction,MonoidHom.comp_apply,quotientAut_apply_mk]
      apply congrArg (QuotientGroup.mk' _)
      apply (residualStarEquiv F).injective
      apply Subtype.ext
      change _ = (residualStarEquiv F (QuotientGroup.mk' (pCore 2 (K F)) k) : HStar F.H)
      erw [residualStarEquiv_mk,residualStarEquiv_mk]
      change starMap F
        ((⟨t,F.invariant 1 t.property⟩ : F.H) * ⟨k,K_le_H F k.property⟩ *
          (⟨t,F.invariant 1 t.property⟩ : F.H)⁻¹) = _
      simp only [map_mul,map_inv,htz,one_mul,inv_one,mul_one]

private theorem kernel_le_index_two_of_reducible
    {A E : Type*} [Group A] [Finite A] [Group E]
    (α : A →* MulAut E) (S : Subgroup A) (hi : S.index = 2)
    (hirr : ∀ B : Subgroup E,
      (∀ a : A, ∀ b ∈ B, α a b ∈ B) → B = ⊥ ∨ B = ⊤)
    (B : Subgroup E) (hb : B ≠ ⊥) (ht : B ≠ ⊤)
    (hs : ∀ s : S, ∀ b ∈ B, α s b ∈ B) : α.ker ≤ S := by
  let C := (MulAction.stabilizer (MulAut E) B).comap α
  have hSC : S ≤ C := by
    intro s hs'
    change α s • B = B
    change B.map (α s).toMonoidHom = B
    apply le_antisymm
    · rintro _ ⟨b,hb',rfl⟩
      exact hs ⟨s,hs'⟩ b hb'
    · intro b hb'
      refine ⟨α s⁻¹ b,hs ⟨s⁻¹,S.inv_mem hs'⟩ b hb',?_⟩
      change (α s * α s⁻¹) b = b
      rw [←map_mul,mul_inv_cancel,map_one]
      rfl
  have hC : C ≠ ⊤ := by
    intro he
    apply (hirr B ?_).elim hb ht
    intro a b hb'
    have ha : a ∈ C := he ▸ mem_top a
    have hae : B.map (α a).toMonoidHom = B := ha
    exact hae ▸ mem_map_of_mem (α a).toMonoidHom hb'
  have hindex : C.index ≠ 1 := fun he => hC (index_eq_one.mp he)
  have hm : S.relIndex C * C.index = 2 := by rw [relIndex_mul_index hSC,hi]
  have hr : S.relIndex C = 1 := by
    have hd : C.index ∣ 2 := ⟨S.relIndex C,by simpa only [Nat.mul_comm] using hm.symm⟩
    have htwo : C.index = 2 := ((Nat.dvd_prime Nat.prime_two).mp hd).resolve_left hindex
    rw [htwo] at hm
    omega
  have hCS : C ≤ S := relIndex_eq_one.mp hr
  intro a ha
  apply hCS
  change α a • B = B
  rw [show α a = 1 from ha,one_smul]

/-- Reducibility at the literal outside Sylow centralizer places the full
original two-core in that centralizer. -/
theorem extraspecial_four_core_le_sylow
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (earlier : ResidualNormalizer.LocalControl.Earlier14710.{u})
    (he : Nonempty (((K F) ⧸ pCore 2 (K F)) ≃* HeisenbergPrime 3))
    (D : Subgroup G) [IsElementaryAbelian 2 D]
    (hZD : F.Vi 1 ≤ D) (hDK : D ≤ (center (K F)).map (K F).subtype)
    (hcard : Nat.card D = 4) (hDT : D ≤ (T : Subgroup G))
    (hND : normalizer (D : Set G) = F.H) (hnc : ¬ D ≤ centralizer (T : Set G))
    {x : G} (hx : x ∈ D) (hxZ : x ∉ F.Vi 1)
    (hout : ¬ centralizer ({x} : Set G) ≤ F.H) :
    F.H.pCoreIn 2 ≤ (T : Subgroup G) ⊓ centralizer ({x} : Set G) := by
  let S := (T : Subgroup G) ⊓ centralizer ({x} : Set G)
  let hn := (F.invariant 1).trans (H_normalizes_K F)
  let α := xiFrattiniAction (T : Subgroup G) (K F) hn
  obtain ⟨A,hAb,hAt,hAs⟩ := extraspecial_four_frattini_reducible
    d h hab structural previous faithful earlier he D hZD hDK hcard hDT hND hx hxZ hout
  have hi : (S.subgroupOf (T : Subgroup G)).index = 2 :=
    extraspecial_four_centralizer_index D hZD hcard hDT hND hnc hx hxZ
  have hirr := (extraspecial_residual_mem_Xi h hab structural previous faithful he).irreducible
  have hk : α.ker ≤ S.subgroupOf (T : Subgroup G) :=
    kernel_le_index_two_of_reducible α _ hi hirr A hAb hAt (by
      intro s a ha
      exact hAs ⟨s,s.property⟩ a ha)
  have hQT : F.H.pCoreIn 2 ≤ (T : Subgroup G) := by
    simpa only [Sylow.coe_subtype,map_subgroupOf_eq_of_le (show (T : Subgroup G) ≤ F.H from F.invariant 1)]
      using pCoreIn_le_sylow F.H (T.subtype (F.invariant 1))
  intro q hq
  apply hk (x := ⟨q,hQT hq⟩)
  change α ⟨q,hQT hq⟩ = 1
  ext a
  exact frattini_action_core_trivial hn ⟨q,hQT hq⟩ hq a

/-- The intersection in the original outside centralizer has exactly O₂(H).
The normalizer of that core, and its characteristic-normalizer closure,
are the original maximal two-local H. -/
theorem extraspecial_four_core_eq
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (earlier : ResidualNormalizer.LocalControl.Earlier14710.{u})
    (he : Nonempty (((K F) ⧸ pCore 2 (K F)) ≃* HeisenbergPrime 3))
    (D : Subgroup G) [IsElementaryAbelian 2 D]
    (hZD : F.Vi 1 ≤ D) (hDK : D ≤ (center (K F)).map (K F).subtype)
    (hcard : Nat.card D = 4) (hDT : D ≤ (T : Subgroup G))
    (hND : normalizer (D : Set G) = F.H) (hnc : ¬ D ≤ centralizer (T : Set G))
    {x : G} (hx : x ∈ D) (hxZ : x ∉ F.Vi 1)
    (hout : ¬ centralizer ({x} : Set G) ≤ F.H) :
    (F.H ⊓ centralizer ({x} : Set G)).pCoreIn 2 = F.H.pCoreIn 2 ∧
      normalizer (F.H.pCoreIn 2 : Set G) = F.H ∧
      (F.H.pCoreIn 2).characteristicNormalizerClosure = F.H := by
  have hQ := extraspecial_four_core_le_sylow d h hab structural previous faithful earlier he
    D hZD hDK hcard hDT hND hnc hx hxZ hout
  have hJ := (extraspecial_four_centralizer_sylow d h hab structural previous faithful earlier he
    D hZD hDK hcard hDT hND hx hxZ).1
  have hn : F.H ≤ normalizer ((F.H ⊓ centralizer ({x} : Set G) : Subgroup G) : Set G) := by
    rw [hJ]
    exact hND.ge.trans (normalizer_le_normalizer_centralizer D)
  have hmax := (extraspecial_source_14721 d h hab structural previous faithful earlier he).2.2.1
  have hN := maximalTwoLocal_normalizer_core hmax
  refine ⟨le_antisymm (pCoreIn_mono_of_normalizes inf_le_left hn) ?_,hN,
    maximalTwoLocal_characteristicNormalizer_core hmax⟩
  exact le_pCoreIn_of_normalizes (isPGroup_pCoreIn 2 F.H)
    (le_inf (pCoreIn_le 2 F.H) (hQ.trans inf_le_right)) (inf_le_left.trans hN.ge)

/-- The literal intersection H ∩ C_G(x) is generated by K and C_T(x). -/
private theorem four_intersection_product {D : Subgroup G}
    (hDK : D ≤ (center (K F)).map (K F).subtype) {x : G} (hx : x ∈ D) :
    K F ⊔ ((T : Subgroup G) ⊓ centralizer ({x} : Set G)) =
      F.H ⊓ centralizer ({x} : Set G) := by
  have hKC : K F ≤ centralizer ({x} : Set G) := by
    rw [map_center_subtype_eq_inf_centralizer] at hDK
    intro k hk
    exact mem_centralizer_singleton_iff.mpr ((hDK hx).2 k hk)
  apply le_antisymm
  · exact sup_le (le_inf (K_le_H F) hKC)
      (le_inf (inf_le_left.trans (F.invariant 1)) inf_le_right)
  · rintro y ⟨hyH,hyC⟩
    rw [residual_product F] at hyH
    have hm : y ∈ (K F : Set G) * ((T : Subgroup G) : Set G) := by
      rw [←coe_mul_of_right_le_normalizer_left (K F) (T : Subgroup G)
        ((F.invariant 1).trans (H_normalizes_K F))]
      exact hyH
    obtain ⟨k,hk,t,ht,rfl⟩ := hm
    have htC := (centralizer ({x} : Set G)).mul_mem
      ((centralizer ({x} : Set G)).inv_mem (hKC hk)) hyC
    rw [inv_mul_cancel_left] at htC
    exact mul_mem (mem_sup_left hk) (mem_sup_right ⟨ht,htC⟩)

/-- Every actual overgroup of H ∩ C_G(x) in C_G(x) satisfies C.2.3 with
the original O₂(H), its exact normalizer and characteristic-normalizer closure. -/
theorem extraspecial_four_overgroup_pushingUp_setup
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (earlier : ResidualNormalizer.LocalControl.Earlier14710.{u})
    (he : Nonempty (((K F) ⧸ pCore 2 (K F)) ≃* HeisenbergPrime 3))
    (D : Subgroup G) [IsElementaryAbelian 2 D]
    (hZD : F.Vi 1 ≤ D) (hDK : D ≤ (center (K F)).map (K F).subtype)
    (hcard : Nat.card D = 4) (hDT : D ≤ (T : Subgroup G))
    (hND : normalizer (D : Set G) = F.H) (hnc : ¬ D ≤ centralizer (T : Set G))
    {x : G} (hx : x ∈ D) (hxZ : x ∉ F.Vi 1)
    (hout : ¬ centralizer ({x} : Set G) ≤ F.H)
    (G₀ : Subgroup G) (hJG : F.H ⊓ centralizer ({x} : Set G) ≤ G₀)
    (hGC : G₀ ≤ centralizer ({x} : Set G)) :
    normalizer ((F.H.pCoreIn 2).subgroupOf G₀ : Set G₀) =
        (F.H ⊓ centralizer ({x} : Set G)).subgroupOf G₀ ∧
      ((F.H.pCoreIn 2).subgroupOf G₀).characteristicNormalizerClosure =
        (F.H ⊓ centralizer ({x} : Set G)).subgroupOf G₀ ∧
      RadicalExclusions.PushingUpSetup KnownSimple.IsKnownSimple G₀ (F.H.pCoreIn 2)
        (F.H ⊓ centralizer ({x} : Set G)) := by
  let C := centralizer ({x} : Set G)
  let J := F.H ⊓ C
  let Q := F.H.pCoreIn 2
  have hQ := extraspecial_four_core_le_sylow d h hab structural previous faithful earlier he
    D hZD hDK hcard hDT hND hnc hx hxZ hout
  obtain ⟨hcore,hN,hchar⟩ := extraspecial_four_core_eq d h hab structural previous faithful earlier he
    D hZD hDK hcard hDT hND hnc hx hxZ hout
  have hQJ : Q ≤ J := le_inf (pCoreIn_le 2 F.H) (hQ.trans inf_le_right)
  have hQG : Q ≤ G₀ := hQJ.trans hJG
  have hmax := (extraspecial_source_14721 d h hab structural previous faithful earlier he).2.2.1
  have hQne : Q ≠ ⊥ := maximalTwoLocal_core_ne_bot hmax
  have hQne₀ : Q.subgroupOf G₀ ≠ ⊥ := by
    intro heq
    apply hQne
    simpa only [map_subgroupOf_eq_of_le hQG,Subgroup.map_bot] using
      congrArg (map G₀.subtype) heq
  have hHJ : F.H.subgroupOf G₀ = J.subgroupOf G₀ := by
    ext g
    exact ⟨fun hg => ⟨hg,hGC g.property⟩,fun hg => hg.1⟩
  have hN₀ : normalizer (Q.subgroupOf G₀ : Set G₀) = J.subgroupOf G₀ := by
    rw [←subgroupOf_normalizer_eq hQG,hN,hHJ]
  have hchar₀ : (Q.subgroupOf G₀).characteristicNormalizerClosure = J.subgroupOf G₀ := by
    apply le_antisymm
    · rw [←hHJ]
      exact characteristicNormalizerClosure_subgroupOf_le hQG hchar.le
    · rw [←hN₀]
      exact normalizer_le_characteristicNormalizerClosure_self _ hQne₀
  refine ⟨hN₀,hchar₀,?_⟩
  have hC := (extraspecial_four_centralizer_source_setup
    d h hab structural previous faithful earlier he D hZD hDK hcard hDT hND hx hxZ).1
  have hG : IsSQTK KnownSimple.IsKnownSimple G₀ :=
    (IsSQTK.equiv (subgroupOfEquivOfLe hGC)).mp (hC.subgroup (G₀.subgroupOf C))
  have hS : IsSylowIn 2 ((T : Subgroup G) ⊓ C) G₀ :=
    IsSylowIn.restrict (H := C)
      (extraspecial_four_centralizer_sylow d h hab structural previous faithful earlier he
        D hZD hDK hcard hDT hND hx hxZ).2.2.2.2.2
      ((le_inf (inf_le_left.trans (F.invariant 1)) inf_le_right).trans hJG) hGC
  obtain ⟨P,hP⟩ := hS
  have hprod := four_intersection_product hDK hx
  apply ChapterC.pushingUpSetup_of_normal_core P hG
    (X := K F) (le_sup_left.trans hprod.le) hJG
    (inf_le_left.trans (H_normalizes_K F)) (K_twoPerfect F)
  · rw [hP]
    exact le_inf (inf_le_left.trans (F.invariant 1)) inf_le_right
  · rw [hP,hprod]
    exact hcore.symm
  · exact hQne
  · exact hchar₀.le


/-- The original commutator module centralizes the full odd core of the
outside involution centralizer. The same 1.1.5 data then kills that core. -/
theorem extraspecial_four_oddCore_eq_bot
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (earlier : ResidualNormalizer.LocalControl.Earlier14710.{u})
    (he : Nonempty (((K F) ⧸ pCore 2 (K F)) ≃* HeisenbergPrime 3))
    (D : Subgroup G) [IsElementaryAbelian 2 D]
    (hZD : F.Vi 1 ≤ D) (hDK : D ≤ (center (K F)).map (K F).subtype)
    (hcard : Nat.card D = 4) (hDT : D ≤ (T : Subgroup G))
    (hND : normalizer (D : Set G) = F.H)
    {x : G} (hx : x ∈ D) (hxZ : x ∉ F.Vi 1) : pPrimeCore 2 (centralizer ({x} : Set G)) = ⊥ := by
  let C := centralizer ({x} : Set G)
  let := h.chosen.elementary
  let := hab
  let := elementary_U F
  obtain ⟨hC,_,z,hzo,hzpow,P,hP,h115⟩ := extraspecial_four_centralizer_source_setup
    d h hab structural previous faithful earlier he D hZD hDK hcard hDT hND hx hxZ
  have hKC : K F ≤ C := by
    rw [map_center_subtype_eq_inf_centralizer] at hDK
    intro k hk
    exact mem_centralizer_singleton_iff.mpr ((hDK hx).2 k hk)
  have hUC : F.U ≤ C := ((span_le_residual_core h hab).trans (pCoreIn_le 2 (K F))).trans hKC
  let : IsElementaryAbelian 2 (F.U.subgroupOf C) := IsElementaryAbelian.subgroupOf hUC
  have hp : IsPPerfect 2 ((K F).subgroupOf C) := (K_twoPerfect F).of_surjective
    (subgroupOfEquivOfLe hKC).symm.toMonoidHom (subgroupOfEquivOfLe hKC).symm.surjective
  have hcomm : ⁅F.U.subgroupOf C,(K F).subgroupOf C⁆ = F.U.subgroupOf C := by
    apply map_injective C.subtype_injective
    rw [map_commutator,map_subgroupOf_eq_of_le hUC,map_subgroupOf_eq_of_le hKC,commutator_U h F]
  have hcent := commutator_eq_bot_iff_le_centralizer.mp
    (ChapterA.lemma_A_1_26_1_of_stronglyQuasithin hC.stronglyQuasithin
      ((K F).subgroupOf C) (F.U.subgroupOf C) hp hcomm)
  have hzU : z ∈ F.U := ((F.le_seed 1).trans (le_conjugateSpanBy V F.H))
    (hzpow ▸ mem_zpowers z)
  have hzC : z ∈ C := hUC hzU
  apply bot_unique
  intro r hr
  have hcentral : z * (r : G) = (r : G) * z :=
    (congrArg Subtype.val (hcent (show (⟨z,hzC⟩ : C) ∈ F.U.subgroupOf C from hzU) r hr)).symm
  have hrH : (r : G) ∈ F.H := h115.centralizer_le
    (mem_centralizer_singleton_iff.mpr hcentral.symm)
  have hr0 : (⟨r,hrH⟩ : F.H.subgroupOf C) ∈
      (pPrimeCore 2 C).subgroupOf (F.H.subgroupOf C) := hr
  rw [h115.oddCore_intersection_eq_bot] at hr0
  exact mem_bot.mpr (congrArg Subtype.val (mem_bot.mp hr0))


/-- A strict overgroup has nontrivial two-core contained in the original
O₂(H), and its original point residual is not normal. -/
theorem extraspecial_four_strict_overgroup_geometry
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (earlier : ResidualNormalizer.LocalControl.Earlier14710.{u})
    (he : Nonempty (((K F) ⧸ pCore 2 (K F)) ≃* HeisenbergPrime 3))
    (D : Subgroup G) [IsElementaryAbelian 2 D]
    (hZD : F.Vi 1 ≤ D) (hDK : D ≤ (center (K F)).map (K F).subtype)
    (hcard : Nat.card D = 4) (hDT : D ≤ (T : Subgroup G))
    (hND : normalizer (D : Set G) = F.H) (hnc : ¬ D ≤ centralizer (T : Set G))
    {x : G} (hx : x ∈ D) (hxZ : x ∉ F.Vi 1)
    (hout : ¬ centralizer ({x} : Set G) ≤ F.H)
    (G₀ : Subgroup G) (hJG : F.H ⊓ centralizer ({x} : Set G) < G₀)
    (hGC : G₀ ≤ centralizer ({x} : Set G)) :
    G₀ ∈ H G ∧ G₀.pCoreIn 2 ≤ F.H.pCoreIn 2 ∧
      G₀ ⊓ normalizer (F.Li L 1 : Set G) = F.H ⊓ centralizer ({x} : Set G) ∧
      ¬ ((F.Li L 1).subgroupOf G₀).Normal := by
  let C := centralizer ({x} : Set G)
  let J := F.H ⊓ C
  have hxJ : x ∈ J := ⟨K_le_H F ((hDK.trans (map_subtype_le _)) hx),
    mem_centralizer_singleton_iff.mpr rfl⟩
  have hxo : orderOf x = 2 := orderOf_eq_prime
    (elemPow_eq_one_of_isElementaryAbelian (A := D) x hx)
    (fun hx1 => hxZ (hx1 ▸ (F.Vi 1).one_mem))
  have hXQ : zpowers x ≤ G₀.pCoreIn 2 := le_pCoreIn_of_normalizes
    (IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers,hxo]; decide))
    (zpowers_le.mpr (hJG.le hxJ)) (hGC.trans (by
      simpa only [zpowers_eq_closure,centralizer_closure] using
        Subgroup.centralizer_le_normalizer (zpowers x : Set G)))
  have hG : G₀ ∈ H G := by
    intro hbot
    have hx1 := mem_bot.mp (hbot ▸ hXQ (mem_zpowers x))
    simp [hx1] at hxo
  have hcore := (extraspecial_four_core_eq d h hab structural previous faithful earlier he
    D hZD hDK hcard hDT hND hnc hx hxZ hout).1
  have hS : IsSylowIn 2 ((T : Subgroup G) ⊓ C) G₀ := IsSylowIn.restrict (H := C)
    (extraspecial_four_centralizer_sylow d h hab structural previous faithful earlier he
      D hZD hDK hcard hDT hND hx hxZ).2.2.2.2.2
    ((le_inf (inf_le_left.trans (F.invariant 1)) inf_le_right).trans hJG.le) hGC
  obtain ⟨P,hP⟩ := hS
  have hcoreS : G₀.pCoreIn 2 ≤ (T : Subgroup G) ⊓ C := hP ▸ pCoreIn_le_sylow G₀ P
  have hcoreJ : G₀.pCoreIn 2 ≤ J := hcoreS.trans
    (le_inf (inf_le_left.trans (F.invariant 1)) inf_le_right)
  have hcoreQ : G₀.pCoreIn 2 ≤ F.H.pCoreIn 2 := hcore ▸
    le_pCoreIn_of_normalizes (isPGroup_pCoreIn 2 G₀) hcoreJ
      (hJG.le.trans (G₀.le_normalizer.trans
        (normalizer_le_normalizer_characteristic_image G₀ (pCore 2 G₀))))
  have hL : normalizer (F.Li L 1 : Set G) = F.H :=
    (extraspecial_core_normalizer_eq d h hab structural previous faithful he).2.trans
      (extraspecial_source_14721 d h hab structural previous faithful earlier he).1
  have hN : G₀ ⊓ normalizer (F.Li L 1 : Set G) = J := by
    rw [hL]
    exact le_antisymm (le_inf inf_le_right (inf_le_left.trans hGC)) (le_inf hJG.le inf_le_left)
  refine ⟨hG,hcoreQ,hN,?_⟩
  have hLG : F.Li L 1 ≤ G₀ := (pointResidual_le F).trans
    ((le_sup_left.trans (four_intersection_product hDK hx).le).trans hJG.le)
  intro hn
  have hGN := (normal_subgroupOf_iff_le_normalizer hLG).mp hn
  have hGJ : G₀ ≤ J := hN ▸ le_inf le_rfl hGN
  exact hJG.not_ge hGJ


/-- Apply the full core and C.2.3 reductions to the four-group selected from
14.7.25. Every extra input comes from the original group and flag. -/
theorem extraspecial_center_four_core_reduction
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (earlier : ResidualNormalizer.LocalControl.Earlier14710.{u})
    (he : Nonempty (((K F) ⧸ pCore 2 (K F)) ≃* HeisenbergPrime 3)) :
    ∃ D : Subgroup G, F.Vi 1 ≤ D ∧ D ≤ (center (K F)).map (K F).subtype ∧
      Nat.card D = 4 ∧ D ≤ (T : Subgroup G) ∧ normalizer (D : Set G) = F.H ∧
      (IsTISubgroup D ∨ (IsElementaryAbelian 2 D ∧
        ∃ x ∈ D, x ∉ F.Vi 1 ∧ ¬ centralizer ({x} : Set G) ≤ F.H ∧
          pPrimeCore 2 (centralizer ({x} : Set G)) = ⊥ ∧
          F.H.pCoreIn 2 ≤ (T : Subgroup G) ⊓ centralizer ({x} : Set G) ∧
          (F.H ⊓ centralizer ({x} : Set G)).pCoreIn 2 = F.H.pCoreIn 2 ∧
          ∀ G₀ : Subgroup G, F.H ⊓ centralizer ({x} : Set G) < G₀ →
            G₀ ≤ centralizer ({x} : Set G) →
            RadicalExclusions.PushingUpSetup KnownSimple.IsKnownSimple G₀ (F.H.pCoreIn 2)
              (F.H ⊓ centralizer ({x} : Set G)) ∧
            G₀ ∈ H G ∧ G₀.pCoreIn 2 ≤ F.H.pCoreIn 2 ∧
              G₀ ⊓ normalizer (F.Li L 1 : Set G) = F.H ⊓ centralizer ({x} : Set G) ∧
              ¬ ((F.Li L 1).subgroupOf G₀).Normal)) := by
  classical
  obtain ⟨D,hZD,hDK,hcard,hDT,hND,hcases⟩ := extraspecial_center_four_ti_reduction
    d h hab structural previous faithful earlier he
  refine ⟨D,hZD,hDK,hcard,hDT,hND,?_⟩
  rcases hcases with ht | ⟨hele,_,hnc⟩
  · exact Or.inl ht
  let := hele
  by_cases ht : IsTISubgroup D
  · exact Or.inl ht
  have hout := (extraspecial_four_ti_iff_centralizer_containment
    d h hab structural previous faithful earlier he D hZD hDK hcard hDT hND hnc).not.mp ht
  push Not at hout
  obtain ⟨x,hx,hxZ,hout⟩ := hout
  refine Or.inr ⟨hele,x,hx,hxZ,hout,
    extraspecial_four_oddCore_eq_bot d h hab structural previous faithful earlier he
      D hZD hDK hcard hDT hND hx hxZ,
    extraspecial_four_core_le_sylow d h hab structural previous faithful earlier he
      D hZD hDK hcard hDT hND hnc hx hxZ hout,
    (extraspecial_four_core_eq d h hab structural previous faithful earlier he
      D hZD hDK hcard hDT hND hnc hx hxZ hout).1,?_⟩
  intro G₀ hJG hGC
  exact ⟨(extraspecial_four_overgroup_pushingUp_setup d h hab structural previous faithful earlier he
    D hZD hDK hcard hDT hND hnc hx hxZ hout G₀ hJG.le hGC).2.2,
    extraspecial_four_strict_overgroup_geometry d h hab structural previous faithful earlier he
      D hZD hDK hcard hDT hND hnc hx hxZ hout G₀ hJG hGC⟩

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction
