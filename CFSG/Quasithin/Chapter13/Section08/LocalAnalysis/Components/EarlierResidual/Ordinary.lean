module
public import CFSG.Quasithin.Chapter13.Section03.PointResidualImage.PrimeDivisors
public import CFSG.Quasithin.Chapter13.Section03.PointResidualImage.NaturalNormalization
public import CFSG.Quasithin.Chapter13.Section08.SourceCompletion.Fitting.Orders
public import CFSG.Quasithin.Chapter13.Section08.SourceCompletion.LocalModels.Chosen
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.SolvableExclusion.Residual.Inputs
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.TransvectionModules.Recognition.Solvable.OneFactor.ResidualTransport
public import CFSG.Quasithin.Chapter13.Section07.ModelExclusions.Theta

public import Theory.GroupTheory.UniqueLocalResidualKernel
public import Theory.GroupTheory.SylowNormalizerOvergroup

/-!
# Original ordinary residual source for the component analysis

The original maximal-local hypothesis supplies theta(M)=L, characteristic
two of every outside overgroup J, and trivial two-core in the join L∨J.
The natural point action then places each two-perfect Y normal in J inside
L₁. Its actual cubic quotient and Sylow normalization recover Y=1 or Y=L₁.
This proves every ordinary Conclusion1339 clause, preserving normality
relative to J and the literal action on V. No Source1339 premise is used.

The covered kernel calculation is a separate obligation in Assembly.lean.
Source: Aschbacher–Smith 13.3.8–9, printed pp.886–887, used in 13.8.12–16,
printed pp.950–952.
-/

public section
open scoped IsMulCommutative
open Subgroup
namespace CFSG.Quasithin.Chapter13.Section08.Components.EarlierResidual
open TransvectionRecognition.Component.ModelExtension
open ComponentSieve.FieldComponents.LinearThree.Geometry.CoveredProduct.ResidualPlacement
open SourceCompletion SolvableExclusion.Residual
open Section03.PointResidualImage TransvectionRecognition.Solvable.OneFactor
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ M G₁ J Y : Subgroup G}
  (d : LocalSetup T L V V₁ V₂ V₃ M G₁)
  (h : Chapter12.Section02.Hypothesis1221 KnownSimple.IsKnownSimple T L)
include d h

theorem theta_normalizer : closure {x:G | x∈M ∧ orderOf x=3} = L :=
  (localNaturalSetup d).source_theta_normalizer h
    (fun X _ _ => ChapterA.Section02.theoremA_knownSimple (G := X))
    (fun X _ _ => ChapterA.Section02.theoremC_knownSimple (G := X))

theorem outside_join_core (hJ : J ∈ Chapter1.HOutside G (T:Set G) (M:Set G)) :
    pCore 2 (L ⊔ J : Subgroup G) = ⊥ := by
  have hu := (h.sylow_normalized_maximal_unique d.normalizes_L
    (fun X _ _ => ChapterA.Section02.theoremA_knownSimple (G := X))
    (fun X _ _ => ChapterA.Section02.theoremC_knownSimple (G := X))).2
  have hc := sup_twoCore_eq_bot_of_unique (L ⊔ (T:Subgroup G)) J M
    (fun N hN hLN => (hu N hN hLN).trans d.local_normalizer.symm) hJ.2
  have he : (L ⊔ (T:Subgroup G)) ⊔ J = L ⊔ J := by
    rw [sup_assoc, sup_eq_right.mpr (show (T:Subgroup G) ≤ J from hJ.1.2)]
  exact he ▸ hc

omit d in
theorem outside_characteristic_two (hJ : J ∈ Chapter1.HOutside G (T:Set G) (M:Set G)) :
    centralizer (pCore 2 J : Set J) ≤ pCore 2 J :=
  Chapter1.mem_He_iff.mp (Chapter1.lemma_1_1_4_6 T (h.simpleQTKE.evenCharacteristic T) hJ.1)

theorem one_le_component : one L (T:Subgroup G) V₁ ≤ L := by
  have htheta : closure {x:G | x∈one L (T:Subgroup G) V₁ ∧ orderOf x=3} = one L (T:Subgroup G) V₁ :=
    Section07.ModelExclusions.point_residual_cubic_generated (localNaturalSetup d)
  have hBM : one L (T:Subgroup G) V₁ ≤ M :=
    ((one_le L (T:Subgroup G) V₁).trans inf_le_left).trans
      (sup_le (d.local_normalizer.symm ▸ L.le_normalizer)
        (d.local_normalizer.symm ▸ d.normalizes_L))
  rw [←htheta]
  apply (closure_le _).mpr
  rintro x ⟨hx,ho⟩
  exact theta_normalizer d h ▸ subset_closure ⟨hBM hx,ho⟩

/-- Ordinary point placement, with the original ambient source hypotheses. -/
theorem ordinary_placement
    (eL : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6))
    (hJ : J ∈ Chapter1.HOutside G (T:Set G) (M:Set G))
    (hYJ : Y ≤ J) (hp : IsPPerfect 2 Y) (hn : (Y.subgroupOf J).Normal)
    (v : G) (hv : v∈V₁) (hne : v∉V⊓centralizer (L:Set G))
    (hfix : Y ≤ M⊓centralizer ({v}:Set G)) : Y ≤ one L (T:Subgroup G) V₁ := by
  let := local_elementary d
  let α := d.local_quotient.toMonoidHom.comp (QuotientGroup.mk' (centralCore L))
  have hα : Function.Surjective α := d.local_quotient.surjective.comp (QuotientGroup.mk'_surjective _)
  let e : Additive V ≃ₗ[ZMod 2] BinaryPermutation.natural (Fin 6) :=
    d.coordinate.toAdditiveLeft.toLinearEquiv (ZMod.map_smul _)
  have hLP : L ≤ M⊓normalizer (V:Set G) :=
    le_inf (d.local_normalizer.symm ▸ L.le_normalizer) (le_sup_left.trans d.normalizes_V)
  have hPL : M⊓normalizer (V:Set G) ≤ normalizer (L:Set G) := by
    rw [←d.local_normalizer]; exact inf_le_left
  have hY : Y ≤ M⊓normalizer (V:Set G) :=
    le_inf (hfix.trans inf_le_left) (hfix.trans (source_point_normalizes d hv hne))
  have hnY : J ≤ normalizer (Y:Set G) := (normal_subgroupOf_iff_le_normalizer hYJ).mp hn
  have hQT : L.pCoreIn 2 ≤ T := (isPGroup_pCoreIn 2 L).le_sylow_of_normalized T
    (d.normalizes_L.trans (normalizer_le_normalizer_characteristic_image L (pCore 2 L)))
  have hvV : v∈V := (d.line_le_plane.trans (d.plane_le_seed.trans d.seed_le)) hv
  have hv0 : v≠1 := by intro he; exact hne (he ▸ one_mem _)
  let w : Additive V := Additive.ofMul ⟨v,hvV⟩
  have hw : w≠0 := by
    intro he
    exact hv0 (congrArg (fun z:Additive V => z.toMul.val) he)
  have hYL : Y ≤ L := le_component_of_theta_and_core_free_join M L V J Y hLP hPL α hα eL e
    (fun l w => d.conjugation l w.toMul) (theta_normalizer d h) hp hY hYJ hnY
    (hQT.trans hJ.1.2) (outside_join_core d h hJ) (outside_characteristic_two h hJ)
    w hw (hfix.trans inf_le_right)
  have hline : zpowers v = V₁ := by
    have he : zpowers (⟨v,hv⟩:V₁) = ⊤ :=
      zpowers_eq_top_of_prime_card d.line_card (by intro hh; exact hv0 (congrArg Subtype.val hh))
    have hh := congrArg (Subgroup.map V₁.subtype) he
    simpa only [MonoidHom.map_zpowers,subtype_apply,←MonoidHom.range_eq_map,range_subtype] using hh
  have hYC : Y ≤ centralizer (V₁:Set G) := by
    rw [←hline,zpowers_eq_closure,centralizer_closure]
    exact hfix.trans inf_le_right
  have hYP : Y ≤ parabolic L (T:Subgroup G) V₁ :=
    le_inf (hYL.trans le_sup_left) (hYC.trans (Subgroup.centralizer_le_normalizer _))
  have hr : residual Y = Y := by
    change (pResidual 2 Y).map Y.subtype = Y
    rw [(pResidual_eq_top_iff 2 Y).mpr hp,←MonoidHom.range_eq_map,range_subtype]
  exact hr ▸ embedded_pResidual_mono 2 hYP

/-- The cubic quotient recovers the actual ordinary residual, using only
normality relative to the outside group J. -/
theorem ordinary_eq_bot_or_one
    (hm : Nonempty ((L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6)))
    (hJ : J ∈ Chapter1.HOutside G (T:Set G) (M:Set G))
    (hYJ : Y ≤ J) (hp : IsPPerfect 2 Y) (hn : (Y.subgroupOf J).Normal)
    (hv : ∃v∈V₁, v∉V⊓centralizer (L:Set G) ∧ Y≤M⊓centralizer ({v}:Set G)) :
    Y=⊥ ∨ Y=one L (T:Subgroup G) V₁ := by
  obtain ⟨eL⟩ := hm
  obtain ⟨v,hv,hne,hfix⟩ := hv
  have hY := ordinary_placement d h eL hJ hYJ hp hn v hv hne hfix
  have hnY : J ≤ normalizer (Y:Set G) := (normal_subgroupOf_iff_le_normalizer hYJ).mp hn
  let B := one L (T:Subgroup G) V₁
  have hcore : Source.QH B ≤ T := (isPGroup_pCoreIn 2 B).le_sylow_of_normalized T
    ((T_normalizes_one L _ V₁ d.line_stable).trans
      (normalizer_le_normalizer_characteristic_image B (pCore 2 B)))
  let : Fact (Nat.Prime (Nat.card (B ⧸ pCore 2 B))) :=
    ⟨(LocalFitting.ordinary_core_card d ⟨eL⟩).symm ▸ Nat.prime_three⟩
  rcases (Source.starImage B Y).eq_bot_or_eq_top_of_prime_card with hb | ht
  · left
    exact eq_of_starImage_eq B Y ⊥ hY bot_le hp (by intro N _ _; exact Subsingleton.elim _ _)
      (hcore.trans (hJ.1.2.trans hnY)) (by intro x _; rw [mem_normalizer_iff]; intro y; simp)
      (by simpa only [Source.starImage,bot_subgroupOf,Subgroup.map_bot] using hb)
  · right
    exact eq_of_starImage_eq B Y B hY le_rfl hp (isPPerfect_embedded_pResidual 2 _)
      (hcore.trans (hJ.1.2.trans hnY)) ((pCoreIn_le 2 B).trans B.le_normalizer) (by
        simpa only [Source.starImage,subgroupOf_self,
          map_top_of_surjective _ (QuotientGroup.mk'_surjective _)] using ht)

/-- All clauses of 13.3.9 in the ordinary case, without an added residual source input. -/
theorem ordinary_source
    (hm : Nonempty ((L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6))) :
    Source1339 L (one L (T:Subgroup G) V₁) (plus L (T:Subgroup G) V₁) T M V V₁ := by
  intro _ J Y hJ hYJ hp hn hv
  rcases ordinary_eq_bot_or_one d h hm hJ hYJ hp hn hv with hb | he
  · exact Or.inl hb
  · refine Or.inr ⟨?_,?_,fun _ => he,?_⟩
    · rw [he]
      exact (one_le_component d h).trans (le_inf (d.local_normalizer.symm ▸ L.le_normalizer)
        (le_sup_left.trans d.normalizes_V))
    · rw [he]
    · intro hc
      obtain ⟨eL⟩ := hm
      have hh := Nat.card_congr (centerCongr eL).toEquiv
      rw [hc.2.1,alternatingGroup.center_eq_bot (by simp),card_bot] at hh
      omega
end CFSG.Quasithin.Chapter13.Section08.Components.EarlierResidual

