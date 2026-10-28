module
public import CFSG.Quasithin.Chapter13.Section03.SourceCompletion.OriginalWeakClosure
public import CFSG.Quasithin.ChapterE.GenerationKnownSimple
public import Theory.GroupTheory.TwoLocalCharacteristicControl
/-!
# Original unitary containment for all small-generation overgroups

The original module's proved fusion and binary fixed-space theorem rule
out weak-closure escape at every index at most two. Its original Sylow
centralizer identifies the two-core of LT, and source uniqueness over LT
controls the normalizer of that core. The complete KnownSimple attainment
and E.3.35 theorem therefore put every actual H(T) member with n(H)≤2 in M.

The final source consumer constructs its SQTK input from the original
simple QTKE group and the nontrivial two-core of H. No E-generation,
attainment, weak-closure or containment conclusion is assumed.
Source: Aschbacher–Smith13.3.19(3), printed p.896.
-/

public section
open Subgroup Theory.GroupTheory Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section03.SourceCompletion
open ChapterE
variable {G:Type*} [Group G] [Finite G]

/-- The actual module action forces every escape index to exceed two. -/
theorem unitary_globalW_gt_two {V T:Subgroup G} [IsElementaryAbelian 2 V]
    (hTN:T≤normalizer (V:Set G))
    (hinter:∀g:G,V⊓V.map (MulAut.conj g).toMonoidHom≠⊥→
      ⁅V,V.map (MulAut.conj g).toMonoidHom⁆=⊥)
    (hr:(3:ℕ∞)<globalR V)
    (I:Subgroup (Automizer V)) [I.Normal]
    (e:I≃*Atlas.G2.Natural.BinaryNormalizer.Derived)
    (E:Additive V≃ₗ[ZMod 2]Atlas.G2.Natural.Space (ZMod 2))
    (he:∀(l:I) v,E (automizerRepresentation V l v)=
      Atlas.G2.Natural.derivedAction (ZMod 2) (e l) (E v)) :
    (2:ℕ∞)<globalW V T := by
  have hd:Module.finrank (ZMod 2) (Additive V)=6:=
    E.finrank_eq.trans (Atlas.G2.Natural.finrank_space (ZMod 2))
  have hc:=Module.natCard_eq_pow_finrank (K:=ZMod 2) (V:=Additive V)
  rw [Nat.card_zmod,hd] at hc
  have hV:rank V=6 := by
    change Nat.log 2 (Nat.card (Additive V))=6
    rw [hc,Nat.log_pow (by decide:1<2)]
  have hbound:(3:ℕ∞)≤globalW V T := by
    apply le_iInf;intro i;apply le_iInf;intro hnot
    have hi:3 ≤ i := by
      by_contra hn
      apply hnot
      refine le_inf (indexedWeakClosure_le _ _ _) ?_
      rw [weakClosure_eq_sSup_gamma]
      apply sSup_le
      rintro A ⟨⟨g,hAW,hindex⟩,hAT⟩
      let W:=V.map (MulAut.conj g).toMonoidHom
      let B:=offenderNormalizer V g
      have :IsElementaryAbelian 2 W:=IsElementaryAbelian.map _
      have hAB:A≤B:=le_inf hAW (hAT.trans hTN)
      have hcor:subgroupCorank W A=i := by
        change Nat.log 2 (A.relIndex (V.map (MulAut.conj g).toMonoidHom))=i
        rw [hindex,Nat.log_pow (by decide)]
      have hadd:=offender_corank_add hAB (show B≤W from inf_le_left)
      have hsmall:subgroupCorank W B≤2:=by omega
      exact hAB.trans (small_corank_normalizer_centralizes hV hinter hr
        (binaryG2_automizer_row V I e E he) g hsmall)
    exact_mod_cast hi
  exact lt_of_lt_of_le (by norm_num) hbound

/-- E.3.35 applied to the actual source core and uniqueness subgroup. -/
theorem small_generation_overgroup_le_of_unitary_bounds
    (T:Sylow 2 G) (L V M H:Subgroup G) [IsElementaryAbelian 2 V]
    (hne:V≠⊥) (hVT:V≤T) (hTN:(T:Subgroup G)≤normalizer (V:Set G))
    (hLN:L≤normalizer (V:Set G))
    (hsyl:(T:Subgroup G)⊓centralizer (V:Set G)=(L⊔(T:Subgroup G)).pCoreIn 2)
    (hu:∀N:Subgroup G,IsMaximalTwoLocal N→L⊔(T:Subgroup G)≤N→N=M)
    (hH:IsSQTK KnownSimple.IsKnownSimple H) (hTH:(T:Subgroup G)≤H)
    (hw:(2:ℕ∞)<globalW V (T:Subgroup G)) (hr:(3:ℕ∞)<globalR V)
    (hn:generationParameter H≤2) : H≤M := by
  have hLTN:L⊔(T:Subgroup G)≤normalizer (V:Set G):=sup_le hLN hTN
  have hlocal:IsTwoLocal (normalizer (V:Set G)):=
    ⟨V,hne,IsElementaryAbelian.isPGroup 2 V,rfl⟩
  obtain ⟨N,hNV,hN⟩:=Finite.exists_le_maximal hlocal
  have heq:=hu N hN (hLTN.trans hNV)
  have hM:IsMaximalTwoLocal M:=heq ▸ hN
  have hNVM:normalizer (V:Set G)≤M:=heq ▸ hNV
  have hVQ:V≤(L⊔(T:Subgroup G)).pCoreIn 2 := by
    rw [←hsyl]
    exact le_inf hVT (le_centralizer_iff_isMulCommutative.mpr inferInstance)
  have hQne:(L⊔(T:Subgroup G)).pCoreIn 2≠⊥:=fun h=>hne (le_bot_iff.mp (h ▸ hVQ))
  have huniq:maximalTwoLocalOvergroups (normalizer
      (((T:Subgroup G)⊓centralizer (V:Set G):Subgroup G):Set G))={M} := by
    rw [hsyl]
    exact unique_twoLocal_overgroup_normalizer
      (isPGroup_pCoreIn 2 _) hQne
      ((L⊔(T:Subgroup G)).le_normalizer.trans
        (normalizer_le_normalizer_characteristic_image _ (pCore 2 _))) hM hu
  apply SourceContainment.le_of_sqtk_knownSimple
    (show HypothesisE322 V T from ⟨hne,hVT,hTN⟩) (T.subtype hTH) hH huniq
  · exact inf_le_right.trans ((Subgroup.centralizer_le_normalizer _).trans hNVM)
  · simpa only [Sylow.coe_subtype,map_subgroupOf_eq_of_le hTH] using
      (show (T:Subgroup G)⊓centralizer (V:Set G)≤(T:Subgroup G) from inf_le_left)
  · exact lt_min (lt_of_le_of_lt (by exact_mod_cast hn) hw)
      (lt_of_le_of_lt (by exact_mod_cast (show generationParameter H≤3 from by omega)) hr)

open Atlas.G2.Natural.BinaryPointFlag
/-- Original13.3.19(3), retaining only the genuine prior module/flag and
ambient source data. The complete KnownSimple E-generation theorem supplies
attainment internally for every original H-overgroup of T. -/
theorem unitary_small_generation_overgroup_le_of_original_module
    (D:ChapterF.Section09.Setup G) (M:Subgroup G)
    [IsElementaryAbelian 2 D.V]
    (e:inducedAutomizer D.V D.L≃*Atlas.G2.Natural.BinaryNormalizer.Derived)
    (E0:Additive D.V≃ₗ[F]Atlas.G2.Natural.Space F)
    (he0:∀(l:inducedAutomizer D.V D.L) v,E0 (automizerRepresentation D.V l v)=
      Atlas.G2.Natural.derivedAction F (e l) (E0 v))
    (hUV:D.Vplus≤D.V) (hZV:D.V₁≤D.V)
    (hTZ:(D.T:Subgroup G)≤normalizer (D.V₁:Set G))
    (hTU:(D.T:Subgroup G)≤normalizer (D.Vplus:Set G))
    (hZ:Nat.card D.V₁=2) (hU:Nat.card D.Vplus=8)
    (hres:pResidual 2 D.L=⊤)
    (hTL:(D.T:Subgroup G)≤normalizer (D.L:Set G))
    (hcharL:generalizedFitting D.L=pCore 2 D.L)
    (hVLT:D.V≤D.LT) (hred:IsPReduced 2 (D.V.subgroupOf D.LT))
    (hsyl:(D.T:Subgroup G)⊓centralizer (D.V:Set G)=D.LT.pCoreIn 2)
    (hcharH:generalizedFitting D.H=pCore 2 D.H)
    (hcontrol:D.H⊓normalizer (D.Vplus:Set G)≤normalizer (D.V:Set G))
    (hNL:normalizer (D.V:Set G)≤normalizer (D.L:Set G))
    (hfaith:D.L⊓centralizer (D.V:Set G)≤D.L.pCoreIn 2)
    (hu:∀N:Subgroup G,IsMaximalTwoLocal N→D.LT≤N→N=M)
    (hout:¬D.H≤M)
    (hcomm:∀g∈D.H,⁅D.V,D.V.map (MulAut.conj g).toMonoidHom⁆≤
      D.V⊓D.V.map (MulAut.conj g).toMonoidHom →
      ⁅D.V,D.V.map (MulAut.conj g).toMonoidHom⁆=⊥)
    (B:Subgroup G) (hBV:B≤D.V)
    (hTB:(D.T:Subgroup G)≤normalizer (B:Set G)) (hB:Nat.card B=4)
    (hr:(3:ℕ∞)<globalR D.V) (hHfull:D.H=normalizer (D.V₁:Set G))
    (hm:⁅D.QH,B⁆≠⊥)
    (hG:IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (H:Subgroup G) (hH:H∈Chapter1.HOver G (D.T:Set G))
    (hn:generationParameter H≤2) : H≤M := by
  obtain ⟨_,hinter,_⟩:=unitary_weakClosure_of_original_module D M e E0 he0 hUV hZV
    hTZ hTU hZ hU hres hTL hcharL hVLT hred hsyl hcharH hcontrol hNL hfaith hu hout
    hcomm B hBV hTB hB hr hHfull hm
  have hLTN:D.LT≤normalizer (D.V:Set G):=
    (normal_subgroupOf_iff_le_normalizer hVLT).mp hred.normal
  have hTN:(D.T:Subgroup G)≤normalizer (D.V:Set G):=le_sup_right.trans hLTN
  have hLN:D.L≤normalizer (D.V:Set G):=le_sup_left.trans hLTN
  have hne:D.V≠⊥ := by
    intro h
    have hz:D.V₁=⊥:=le_bot_iff.mp (h ▸ hZV)
    rw [hz,Subgroup.card_bot] at hZ
    omega
  have hVQ:D.V≤D.LT.pCoreIn 2:=le_pCoreIn_of_normalizes
    (IsElementaryAbelian.isPGroup 2 D.V) hVLT hLTN
  have hVT:D.V≤(D.T:Subgroup G) := by
    rw [←hsyl] at hVQ
    exact hVQ.trans inf_le_left
  let I:=inducedAutomizer D.V D.L
  have :(D.L.subgroupOf (normalizer (D.V:Set G))).Normal:=
    (normal_subgroupOf_iff_le_normalizer hLN).mpr hNL
  have :I.Normal:=Subgroup.Normal.map inferInstance D.V.normalizerMonoidHom.rangeRestrict
    D.V.normalizerMonoidHom.rangeRestrict_surjective
  have hw:=unitary_globalW_gt_two hTN hinter hr I e E0 he0
  have hsqtk:IsSQTK KnownSimple.IsKnownSimple H := by
    let R:=H.pCoreIn 2
    let N:=normalizer (R:Set G)
    have hHN:H≤N:=H.le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image H (pCore 2 H))
    have hnlocal:IsTwoLocal N:=⟨R,hH.1,isPGroup_pCoreIn 2 H,rfl⟩
    exact (IsSQTK.equiv (subgroupOfEquivOfLe hHN)).mp
      ((hG.twoLocal_sqtk hnlocal).subgroup (H.subgroupOf N))
  exact small_generation_overgroup_le_of_unitary_bounds D.T D.L D.V M H
    hne hVT hTN hLN hsyl hu hsqtk
    hH.2 hw hr hn

end CFSG.Quasithin.Chapter13.Section03.SourceCompletion
