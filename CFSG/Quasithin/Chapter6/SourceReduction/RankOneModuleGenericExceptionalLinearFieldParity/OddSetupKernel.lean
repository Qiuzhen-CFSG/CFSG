module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalLinearFieldParity.OddSetupGeometry
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalLinearFieldParity.OddSetupCartanFree
public import Theory.GroupTheory.GeneralizedFitting.ProductKernel

/-!
# The F.8 quotient-kernel bound in odd field degree

G.2.2 puts O₂(HD_L) in the normal core of C_{HD_L}(V/Z₁). Every element
of this core normalizes V, whose full normalizer lies in N_G(L) by the
original maximal-local uniqueness theorem. Consequently the core cannot
contain the exceptional residual O²(H).

In the proved product HD_L/O₂(HD_L) ≃ (H/O₂(H)) × D_L, the first factor
has centerless quasisimple F*. The natural Cartan action on V/Z₁ is
faithful: any nontrivial Cartan subgroup generates V by commutators.
The normal-product lemma therefore makes the kernel image trivial.
This proves F.8.1(c) on the literal quotient, using neither global TI
nor abelianness of the normalizer span. Those geometric obligations and
5.1.16(2) remain with qt-d-1222-linear-field-parity.

Source: Aschbacher–Smith 5.1.17, printed p.641, using 3.2.3 and G.2.2
(refs/quasithin.pdf).
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped commutatorElement

namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.LinearParity
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L W H A B : Subgroup G} {n : ℕ}

/-- Maximal-local uniqueness controls the full normalizer of the selected module. -/
theorem fundamental_module_normalizer_le
    (D : Chapter3.Section02.FundamentalSetup KnownSimple.IsKnownSimple T L)
    (hTL : (T : Subgroup G) ≤ normalizer (L : Set G)) :
    normalizer (D.moduleSubgroup : Set G) ≤ normalizer (L : Set G) := by
  let := D.module_elementary
  let M := normalizer (D.moduleSubgroup : Set G)
  have hV : D.moduleSubgroup ≤ M.pCoreIn 2 :=
    le_pCoreIn_of_normalizes (IsElementaryAbelian.isPGroup 2 D.moduleSubgroup)
      D.moduleSubgroup.le_normalizer le_rfl
  have hcore : pCore 2 M ≠ ⊥ := by
    intro he
    rw [Subgroup.pCoreIn,he,Subgroup.map_bot] at hV
    exact D.module_ne_bot (bot_unique hV)
  obtain ⟨R,hR,hMR⟩ := exists_maximalTwoLocal_overgroup_of_twoCore_ne_bot M hcore
  have hu := D.lemma_3_2_3_uniqueness
    (Chapter1.Section02.nonsolvable_uniqueness_knownSimple D.simpleQTKE T D.maximal)
  have horbit : Chapter3.Section02.localOrbit T L = L :=
    le_antisymm (iSup_conjugates_le_of_le_normalizer _ _ _ le_rfl hTL)
      (le_componentOrbit _ _)
  have he : R = normalizer (L : Set G) := by
    have hh := hu.2.2 R hR (D.join_normalizes_module.trans hMR)
    simpa only [Chapter3.Section02.FundamentalSetup.maximalLocal,horbit] using hh
  exact he ▸ hMR

private theorem g2_core_le_quotientCentralizer_core
    {E : ChapterF.Section08.Setup G} (hg : ChapterG.Section02.Setup.Hypothesis E) :
    pCore 2 E.H ≤ (E.quotientCentralizer hg.H_le E.V).normalCore := by
  rw [← E.quotientCentralizer_span hg.H_le (hg.V_le_T.trans (le_sup_right.trans hg.local_le))]
  intro x hx
  apply (E.mem_quotientCentralizer_iff hg.H_le E.U (hg.U_le_H.trans hg.H_le) x).mpr
  intro u hu
  exact hg.commutator_U_core_le_point
    (commutator_mem_commutator hu (mem_map_of_mem E.H.subtype hx))

private theorem quotientCentralizer_le_module_normalizer
    {E : ChapterF.Section08.Setup G} (hg : ChapterG.Section02.Setup.Hypothesis E) :
    (E.quotientCentralizer hg.H_le E.V).map E.H.subtype ≤ normalizer (E.V : Set G) := by
  apply le_normalizer_iff_commutator_le_left.mpr
  apply commutator_le.mpr
  rintro v hv x ⟨y,hy,rfl⟩
  exact hg.point_le ((E.mem_quotientCentralizer_iff hg.H_le E.V
    ((hg.V_le_T.trans (le_sup_right.trans hg.local_le)).trans hg.H_le) y).mp hy v hv)

/-- The literal Cartan has trivial kernel on the natural quotient V/Z₁. -/
theorem fundamental_cartan_quotientCentralizer_disjoint
    (D : Chapter3.Section02.FundamentalSetup KnownSimple.IsKnownSimple T L)
    (c : CartanPair T L H A B) (hnat : IsNaturalModule L D.moduleSubgroup n)
    (hg : ChapterG.Section02.Setup.Hypothesis (setup T L D.moduleSubgroup H A))
    (a : A)
    (ha : (inclusion (show A ≤ H ⊔ A from le_sup_right) a) ∈
      (setup T L D.moduleSubgroup H A).quotientCentralizer hg.H_le D.moduleSubgroup) : a = 1 := by
  by_contra hne
  let E := setup T L D.moduleSubgroup H A
  let C := zpowers (a : G)
  have hC : C ≠ ⊥ := by
    intro he
    exact hne (Subtype.ext (mem_bot.mp (he ▸ (mem_zpowers (a : G)))))
  have hCA : C ≤ A := zpowers_le.mpr a.property
  have hCQ : C ≤ (E.quotientCentralizer hg.H_le E.V).map E.H.subtype :=
    zpowers_le.mpr ⟨inclusion le_sup_right a,ha,rfl⟩
  have hc : ⁅D.moduleSubgroup,C⁆ ≤ E.V₁ := by
    apply commutator_le.mpr
    intro v hv x hx
    obtain ⟨y,hy,rfl⟩ := hCQ hx
    exact (E.mem_quotientCentralizer_iff hg.H_le E.V
      ((hg.V_le_T.trans (le_sup_right.trans hg.local_le)).trans hg.H_le) y).mp hy v hv
  rw [fundamental_cartan_subgroup_commutator D c hnat C hCA hC] at hc
  exact hg.quotient_nonzero (le_antisymm hg.point_le hc)

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.LinearParity

namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.LinearParity
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L W H A B : Subgroup G} {n : ℕ}

/-- The original odd-degree data prove the normal-core bound of F.8.1(c). -/
theorem fundamental_quotient_kernel
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (c : CartanPair T L H A B) (hodd : Odd n)
    (hK : residual H ∈ Chapter1.LStar G (T : Subgroup G))
    (hnf : ¬ ChapterA.Section04.IsFaithfulSignalizerType (residual H))
    (hm : ClassicalGroup.IsPSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 3 4)
    (D : Chapter3.Section02.FundamentalSetup KnownSimple.IsKnownSimple T L)
    (hnat : IsNaturalModule L D.moduleSubgroup n) :
    ((setup T L D.moduleSubgroup H A).quotientCentralizer
      (fundamental_g2 h hH c hodd hK hnf D hnat).H_le D.moduleSubgroup).normalCore ≤
        pCore 2 (H ⊔ A : Subgroup G) := by
  let E := setup T L D.moduleSubgroup H A
  let J := H ⊔ A
  let hg := fundamental_g2 h hH c hodd hK hnf D hnat
  let N : Subgroup J := (E.quotientCentralizer hg.H_le D.moduleSubgroup).normalCore
  let hNN : N.Normal := (E.quotientCentralizer hg.H_le D.moduleSubgroup).normalCore_normal
  change N ≤ pCore 2 J
  let q := QuotientGroup.mk' (pCore 2 J)
  have hq := QuotientGroup.mk'_surjective (pCore 2 J)
  have hQN : pCore 2 J ≤ N := g2_core_le_quotientCentralizer_core hg
  have hNM : N.map J.subtype ≤ normalizer (L : Set G) :=
    (map_mono (E.quotientCentralizer hg.H_le E.V).normalCore_le).trans
      ((quotientCentralizer_le_module_normalizer hg).trans
        (fundamental_module_normalizer_le D h.sylow_normalizes))
  obtain ⟨e,he⟩ := odd_join_quotient_product h hH c hodd hK hnf hm
  let P := (N.map q).map e.symm.toMonoidHom
  let : (N.map q).Normal := Normal.map hNN q hq
  let : P.Normal := Normal.map inferInstance e.symm.toMonoidHom e.symm.surjective
  have hP (x : H) (a : A) :
      (QuotientGroup.mk' (pCore 2 H) x,a) ∈ P ↔
        (⟨(x : G)*(a : G),mul_mem_sup x.property a.property⟩ : J) ∈ N := by
    change _ ∈ (N.map q).map e.symm.toMonoidHom ↔ _
    rw [mem_map_equiv]
    change e (QuotientGroup.mk' (pCore 2 H) x,a) ∈ N.map q ↔ _
    rw [he]
    change _ ∈ (N.map q).comap q ↔ _
    rw [comap_map_eq_self (show q.ker ≤ N by simpa only [q,QuotientGroup.ker_mk'] using hQN)]
  let F := generalizedFitting (H ⧸ pCore 2 H)
  have hFm := residual_coreQuotient_fitting_model hH.1.1.2 hm
  have hFqs : IsQuasisimple F := by
    obtain ⟨k,_,_,_,⟨f⟩⟩ := hFm
    exact IsQuasisimple.of_mulEquiv f.symm
  let := hFqs
  have hFZ : center F = ⊥ := by
    obtain ⟨k,_,_,_,⟨f⟩⟩ := hFm
    let : Group.IsPerfect (Matrix.SpecialLinearGroup (Fin 3) k) := Atlas.sl_perfect 3 (by decide)
    apply (center F).eq_bot_iff_forall.mpr
    intro x hx
    apply f.injective
    rw [map_one]
    have hh : f x ∈ center (Matrix.ProjectiveSpecialLinearGroup (Fin 3) k) := by
      rw [mem_center_iff]
      intro y
      obtain ⟨y,rfl⟩ := f.surjective y
      simpa only [map_mul] using congrArg f (mem_center_iff.mp hx y)
    simpa only [Group.IsPerfect.center_quotient_center_eq_bot
      (Matrix.SpecialLinearGroup (Fin 3) k),mem_bot] using hh
  have hFP : ¬ F ≤ P.comap (MonoidHom.inl (H ⧸ pCore 2 H) A) := by
    intro hle
    apply hH.1.2
    rw [← residual_sup_sylow T H hH.1.1.2]
    apply sup_le ?_ h.sylow_normalizes
    rintro x ⟨k,hk,rfl⟩
    have hqk : QuotientGroup.mk' (pCore 2 H) k ∈ F := by
      rw [show F = (pResidual 2 H).map (QuotientGroup.mk' (pCore 2 H)) from
        residual_coreQuotient_generalizedFitting hH.1.1.2 hm]
      exact mem_map_of_mem _ hk
    have hn := (hP k 1).mp (hle hqk)
    apply hNM
    exact ⟨_,hn,by simp⟩
  have hAP : ∀ a : A, (1,a) ∈ P → a = 1 := by
    intro a ha
    have hn := (hP 1 a).mp (by simpa only [map_one] using ha)
    apply fundamental_cartan_quotientCentralizer_disjoint D c hnat hg a
    have hn' : inclusion (show A ≤ J from le_sup_right) a ∈ N := by
      have he : inclusion (show A ≤ J from le_sup_right) a =
          (⟨(1 : H) * (a : G),mul_mem_sup (1 : H).property a.property⟩ : J) := by
        apply Subtype.ext
        simp
      exact he.symm ▸ hn
    exact (E.quotientCentralizer hg.H_le E.V).normalCore_le hn'
  have hPbot := normal_product_eq_bot_of_fitting_and_right F rfl hFZ P hFP hAP
  have hNbot : N.map q = ⊥ :=
    (Subgroup.map_eq_bot_iff_of_injective _ e.symm.injective).mp hPbot
  simpa only [q,QuotientGroup.ker_mk'] using (Subgroup.map_eq_bot_iff _).mp hNbot

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.LinearParity
