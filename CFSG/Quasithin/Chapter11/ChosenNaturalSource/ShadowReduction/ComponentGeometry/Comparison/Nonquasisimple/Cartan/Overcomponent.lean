module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Comparison.Nonquasisimple.Frattini.Radical
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components.Membership
public import CFSG.Quasithin.ChapterA.Section03.SQTKStructure.NoncentralFitting.TwoRank
public import Theory.SpecificGroups.PSL2.PrimeFieldTwoRank

/-!
# The residual overcomponent in the actual normalizer

Write J = N_Kz(R₁)^∞ and N = N_G(R₁). The full Sylow and original
seed identify O₂(N) with R₁. Relative radicality in KzR₁ places O₂(J)
inside R₁, so the literal inclusion into N/O₂(N) has kernel exactly
O₂(J). The representative equation for its image equivalence is retained.

The original PSL₂(p) quotient therefore makes J a local C-component.
Source 1.2.4 constructs its unique containing component K₀, normal in N.
The image of J has two-rank two, excluding every nonquasisimple K₀/O₂(K₀)
by A.3.6. This includes the SL₂(p)/E_(p²) alternative mentioned in the
printed proof; no solvable kernel is silently discarded.

The original chosen-flag applications feed Cartan.lean. The residual
model is supplied by Frattini.Catalogue; final nonquasisimple assembly
remains with qt-d-1222-comparison-nonquasisimple.
Source: Aschbacher--Smith, 11.4.2, printed p.777, and 1.2.4, p.505.
-/

set_option backward.isDefEq.respectTransparency false
public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Comparison.Cartan
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    {D : Chapter12.Section02.ChosenModule T L V} {E : Closure.Geometry D}

private theorem radical_le_sylow : E.R₁ ≤ (T : Subgroup G) := by
  change (E.L₁ ⊔ (T : Subgroup G)).pCoreIn 2 ≤ (T : Subgroup G)
  simpa only [Sylow.coe_subtype, map_subgroupOf_eq_of_le le_sup_right] using
    pCoreIn_le_sylow (E.L₁ ⊔ (T : Subgroup G)) (T.subtype le_sup_right)

/-- The original seed and full Sylow normalize their two-core R₁. -/
theorem seedJoin_normalizes_radical :
    E.L₁ ⊔ (T : Subgroup G) ≤ normalizer (E.R₁ : Set G) :=
  (E.L₁ ⊔ (T : Subgroup G)).le_normalizer.trans
    (normalizer_le_normalizer_characteristic_image _ (pCore 2 _))

/-- The full ambient normalizer has exactly the source two-core R₁. -/
theorem radical_normalizer_core :
    (normalizer (E.R₁ : Set G)).pCoreIn 2 = E.R₁ := by
  apply le_antisymm
  · exact pCoreIn_le_of_sylow_le T le_sup_right seedJoin_normalizes_radical
  · exact le_pCoreIn_of_normalizes (isPGroup_pCoreIn 2 _)
      E.R₁.le_normalizer le_rfl

private theorem sylow_normalizes_point (h : EarlierGeometry E) :
    (T : Subgroup G) ≤ normalizer (E.Kz : Set G) :=
  h.sylow_le_pointCentralizer.trans (le_normalizer_conjugateSpanBy _ _)

/-- The original full Sylow preserves the literal normalizer residual. -/
theorem normalizerResidual_sylow_invariant (h : EarlierGeometry E) :
    (T : Subgroup G) ≤ normalizer (normalizerResidual E : Set G) := by
  have hTN : (T : Subgroup G) ≤ normalizer (normalizer (E.R₁ : Set G) : Set G) :=
    (le_sup_right.trans seedJoin_normalizes_radical).trans
      (normalizer (E.R₁ : Set G)).le_normalizer
  exact ((le_inf (sylow_normalizes_point h) hTN).trans
    inf_normalizer_le_normalizer_inf).trans
      (normalizer_le_normalizer_characteristic_image _ (solvableResidual _))

/-- Relative radicality in KzR₁ puts the residual two-core inside R₁. -/
theorem normalizerResidual_core_le_radical (h : EarlierGeometry E) :
    (normalizerResidual E).pCoreIn 2 ≤ E.R₁ := by
  let A := E.Kz ⊓ normalizer (E.R₁ : Set G)
  let W := Frattini.pointRadicalJoin E ⊓ normalizer (E.R₁ : Set G)
  have hWK : W ≤ normalizer (E.Kz : Set G) := inf_le_left.trans
    (sup_le E.Kz.le_normalizer (radical_le_sylow.trans (sylow_normalizes_point h)))
  have hWA : W ≤ normalizer (A : Set G) :=
    (le_inf hWK (inf_le_right.trans (normalizer (E.R₁ : Set G)).le_normalizer)).trans
      inf_normalizer_le_normalizer_inf
  have hWJ : W ≤ normalizer (normalizerResidual E : Set G) :=
    hWA.trans (normalizer_le_normalizer_characteristic_image A (solvableResidual A))
  have hJW : normalizerResidual E ≤ W := le_inf
    (normalizerResidual_le.trans le_sup_left) ((Closure.residualIn_le _).trans inf_le_right)
  exact (pCoreIn_mono_of_normalizes hJW hWJ).trans_eq (Frattini.relative_normalizer_core h)

private theorem residual_perfect : Group.IsPerfect (normalizerResidual E) :=
  Group.IsPerfect.map _

private theorem quasi_psl {A : Type*} [Group A] [Group.IsPerfect A]
    {p : ℕ} (hp : 3 < p) (hm : ClassicalGroup.IsPSL A 2 p) : IsQuasisimple A := by
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := hm
  let : IsSimpleGroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) F) :=
    Matrix.ProjectiveSpecialLinearGroup.rank_two_simple (by omega)
  let : IsSimpleGroup A := e.isSimpleGroup
  have hz : center A = ⊥ :=
    (IsSimpleGroup.eq_bot_or_eq_top_of_normal (center A) inferInstance).resolve_right
      (fun he => Group.IsPerfect.not_isMulCommutative A (center_eq_top_iff.mp he))
  exact ⟨((QuotientGroup.quotientMulEquivOfEq hz).trans QuotientGroup.quotientBot).isSimpleGroup⟩

/-- The actual PSL₂ residual quotient supplies local-family membership. -/
theorem ofFlag_residual_mem_local (S : D.NonbinaryNaturalInput)
    {c : LocalGeometry.Coordinates D S.field} (f : LocalGeometry.InvariantFlag c)
    (X : Subgroup G) (z : G) (H : Subgroup G)
    (h : EarlierGeometry (ofFlag S f X z H)) {p : ℕ} (hp : 3 < p)
    (hm : ClassicalGroup.IsPSL (normalizerResidual (ofFlag S f X z H) ⧸
      pCore 2 (normalizerResidual (ofFlag S f X z H))) 2 p) :
    normalizerResidual (ofFlag S f X z H) ∈ Chapter1.L G (T : Subgroup G) := by
  let E := ofFlag S f X z H
  let B := normalizerResidual E
  let W := B ⊔ (T : Subgroup G)
  let A := B.subgroupOf W
  let : Group.IsPerfect B := residual_perfect
  let : IsQuasisimple (B ⧸ pCore 2 B) := quasi_psl hp hm
  have hpB : IsPPerfect 2 B := by
    intro N hN hP
    let := hN
    by_contra hne
    let : Nontrivial (B ⧸ N) := QuotientGroup.nontrivial_iff.mpr hne
    exact Group.IsPerfect.not_isNilpotent (B ⧸ N) hP.isNilpotent
  have ht := isCComponent_top_of_isPPerfect_of_quasisimple_quotient
    (pCore 2 B) pCore_isPGroup hpB
  let eA : B ≃* A := (subgroupOfEquivOfLe (show B ≤ W from le_sup_left)).symm
  have htA : (⊤ : Subgroup A).IsCComponent := by
    simpa only [map_top_of_surjective eA.toMonoidHom eA.surjective] using ht.map_equiv eA
  have hnA : A.Normal := normal_subgroupOf_of_le_normalizer
    (sup_le B.le_normalizer (normalizerResidual_sylow_invariant h))
  have hA : A.IsCComponent := by
    simpa only [← MonoidHom.range_eq_map, range_subtype] using htA.map_subtype hnA.isSubnormal
  refine ⟨hA, ⟨T.subtype le_sup_right, ?_⟩, ?_⟩
  · simp only [Sylow.coe_subtype, map_subgroupOf_eq_of_le le_sup_right]
  · have hR : E.R₁ ≤ W.pCoreIn 2 := le_pCoreIn_of_normalizes (isPGroup_pCoreIn 2 _)
      (radical_le_sylow.trans le_sup_right)
      (sup_le ((Closure.residualIn_le _).trans inf_le_right)
        (le_sup_right.trans seedJoin_normalizes_radical))
    intro he
    apply f.V_ne_bot 0
    exact bot_unique ((E.V₁_le.trans (f.seed_le_Ri S 0)).trans (he ▸ hR))

/-- Source 1.2.4 constructs the unique normal containing component inside N_G(R₁). -/
theorem ofFlag_exists_unique_normal_overcomponent (S : D.NonbinaryNaturalInput)
    {c : LocalGeometry.Coordinates D S.field} (f : LocalGeometry.InvariantFlag c)
    (X : Subgroup G) (z : G) (H : Subgroup G)
    (h : EarlierGeometry (ofFlag S f X z H)) {p : ℕ} (hp : 3 < p)
    (hm : ClassicalGroup.IsPSL (normalizerResidual (ofFlag S f X z H) ⧸
      pCore 2 (normalizerResidual (ofFlag S f X z H))) 2 p) :
    ∃ K₀ : Subgroup G,
      Source.NormalComponentIn (normalizer ((ofFlag S f X z H).R₁ : Set G)) K₀ ∧
      normalizerResidual (ofFlag S f X z H) ≤ K₀ ∧
      ∀ J : Subgroup G,
        Source.ComponentIn (normalizer ((ofFlag S f X z H).R₁ : Set G)) J →
        normalizerResidual (ofFlag S f X z H) ≤ J → J = K₀ := by
  let E := ofFlag S f X z H
  have hRne : E.R₁ ≠ ⊥ := by
    intro he
    exact f.V_ne_bot 0 (bot_unique (he ▸ E.V₁_le.trans (f.seed_le_Ri S 0)))
  have hTN : (T : Subgroup G) ≤ normalizer (E.R₁ : Set G) :=
    le_sup_right.trans seedJoin_normalizes_radical
  exact LocalGeometry.Components.exists_unique_normal_component
    (S.source.simpleQTKE.twoLocal_sqtk ⟨E.R₁,hRne,isPGroup_pCoreIn 2 _,rfl⟩)
    ⟨T.subtype hTN, by rw [Sylow.coe_subtype,map_subgroupOf_eq_of_le hTN]⟩
    ((Closure.residualIn_le _).trans inf_le_right)
    (ofFlag_residual_mem_local S f X z H h hp hm) (normalizerResidual_sylow_invariant h)


/-- Inclusion into the actual normalizer followed by its two-core quotient. -/
@[expose] def residualNormalizerProjection (E : Closure.Geometry D) :
    normalizerResidual E →* (normalizer (E.R₁ : Set G) ⧸ pCore 2 (normalizer (E.R₁ : Set G))) :=
  (QuotientGroup.mk' (pCore 2 (normalizer (E.R₁ : Set G)))).comp
    (inclusion ((Closure.residualIn_le _).trans inf_le_right))

/-- The kernel of inclusion into N/O₂(N) is the residual’s intrinsic two-core. -/
theorem residualNormalizerProjection_ker (h : EarlierGeometry E) :
    (residualNormalizerProjection E).ker = pCore 2 (normalizerResidual E) := by
  let N := normalizer (E.R₁ : Set G)
  let i : normalizerResidual E →* N :=
    inclusion ((Closure.residualIn_le _).trans inf_le_right)
  have hk : IsPGroup 2 (residualNormalizerProjection E).ker := by
    change IsPGroup 2 ((QuotientGroup.mk' (pCore 2 N)).comp i).ker
    rw [← MonoidHom.comap_ker, QuotientGroup.ker_mk']
    exact pCore_isPGroup.comap_of_injective i (inclusion_injective _)
  apply le_antisymm (show (residualNormalizerProjection E).ker ≤ pCore 2 (normalizerResidual E) from
    le_sSup ⟨inferInstance,hk⟩)
  intro x hx
  apply (QuotientGroup.eq_one_iff (i x)).mpr
  have hr := normalizerResidual_core_le_radical h (mem_map_of_mem _ hx)
  rw [← radical_normalizer_core (E := E)] at hr
  obtain ⟨n, hn, he⟩ := hr
  exact (show n = i x from Subtype.ext he) ▸ hn

/-- The residual quotient is identified with its actual image in N/O₂(N). -/
@[expose] def residualNormalizerQuotientEquiv (h : EarlierGeometry E) :
    (normalizerResidual E ⧸ pCore 2 (normalizerResidual E)) ≃*
      (residualNormalizerProjection E).range :=
  QuotientGroup.liftEquiv _ (residualNormalizerProjection E).rangeRestrict_surjective
    (by rw [MonoidHom.ker_rangeRestrict]; exact (residualNormalizerProjection_ker h).symm)

/-- The image equivalence retains the literal inclusion and quotient maps. -/
theorem residualNormalizerQuotientEquiv_mk (h : EarlierGeometry E)
    (x : normalizerResidual E) :
    (residualNormalizerQuotientEquiv h (QuotientGroup.mk' (pCore 2 (normalizerResidual E)) x)).val =
      residualNormalizerProjection E x := by
  exact congrArg Subtype.val (QuotientGroup.liftEquiv_mk _ _ _ x)

private theorem psl_two_rank {A : Type*} [Group A] [Finite A] {p : ℕ} [Fact p.Prime]
    (hp : 3 < p) (hm : ClassicalGroup.IsPSL A 2 p) : primeRank 2 A = 2 := by
  classical
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := hm
  let : Fintype F := Fintype.ofFinite F
  let eF : F ≃+* ZMod p := FiniteField.ringEquivOfCardEq (by
    rw [← Nat.card_eq_fintype_card, hF, ZMod.card])
  rw [primeRank_equiv 2 (e.trans (GorensteinWalter.psl2RingEquiv eF))]
  exact Theory.PSL2.primeField_two_rank hp

/-- R₁'s normality preserves the residual's whole PSL₂ quotient inside
N/O₂(N). Its two-rank excludes every nonquasisimple containing component,
including the elementary odd-kernel extension in the printed argument. -/
theorem ofFlag_overcomponent_quasisimple (S : D.NonbinaryNaturalInput)
    {c : LocalGeometry.Coordinates D S.field} (f : LocalGeometry.InvariantFlag c)
    (X : Subgroup G) (z : G) (H : Subgroup G)
    (h : EarlierGeometry (ofFlag S f X z H)) {p : ℕ} [Fact p.Prime] (hp : 3 < p)
    (hm : ClassicalGroup.IsPSL (normalizerResidual (ofFlag S f X z H) ⧸
      pCore 2 (normalizerResidual (ofFlag S f X z H))) 2 p)
    {K₀ : Subgroup G}
    (hK : Source.ComponentIn (normalizer ((ofFlag S f X z H).R₁ : Set G)) K₀)
    (hBK : normalizerResidual (ofFlag S f X z H) ≤ K₀) :
    IsQuasisimple (K₀ ⧸ pCore 2 K₀) := by
  let E := ofFlag S f X z H
  let N := normalizer (E.R₁ : Set G)
  let q := QuotientGroup.mk' (pCore 2 N)
  let K' := K₀.subgroupOf N
  let Kbar := K'.map q
  let Bbar := (residualNormalizerProjection E).range
  have hRne : E.R₁ ≠ ⊥ := by
    intro he
    exact f.V_ne_bot 0 (bot_unique (he ▸ E.V₁_le.trans (f.seed_le_Ri S 0)))
  have hN := S.source.simpleQTKE.twoLocal_sqtk ⟨E.R₁,hRne,isPGroup_pCoreIn 2 _,rfl⟩
  have hQ := ChapterE.Structure.sqtk_two_quotient hN (pCore 2 N) pCore_isPGroup
  let : Group.IsNilpotent (pCore 2 N) := pCore_isNilpotent
  have hKb : Kbar.IsCComponent := hK.2.map_quotient (pCore 2 N)
  have hBKb : Bbar ≤ Kbar := by
    rintro y ⟨x,rfl⟩
    exact mem_map_of_mem q (hBK x.property)
  have hr : 2 ≤ primeRank 2 Kbar := by
    have hbr : primeRank 2 Bbar = 2 := by
      rw [← primeRank_equiv 2 (residualNormalizerQuotientEquiv h)]
      exact psl_two_rank hp hm
    exact hbr.symm.le.trans (primeRank_mono 2 hBKb)
  let : IsQuasisimple Kbar :=
    ChapterA.Section03.NoncentralFitting.quasisimple_of_two_le_two_rank
      hQ (pCore_quotient_pCore_eq_bot 2) hKb hr
  let e := QuotientGroup.congr _ _ (subgroupOfEquivOfLe hK.1)
    (pCore_map_iso 2 (subgroupOfEquivOfLe hK.1))
  exact IsQuasisimple.of_mulEquiv ((cComponentTwoCoreQuotientEquiv hK.2).symm.trans e)


/-- The original flag seed lies in the literal normalizer residual. -/
theorem ofFlag_seed_le_residual (S : D.NonbinaryNaturalInput)
    {c : LocalGeometry.Coordinates D S.field} (f : LocalGeometry.InvariantFlag c)
    (X : Subgroup G) (z : G) (H : Subgroup G) :
    (ofFlag S f X z H).L₁ ≤ normalizerResidual (ofFlag S f X z H) := by
  let : Group.IsPerfect (ofFlag S f X z H).L₁ := LocalGeometry.localResidual_perfect _
  exact le_map_solvableResidual_of_isPerfect _ _
    (le_inf (le_conjugateSpanBy _ _) (le_sup_left.trans seedJoin_normalizes_radical))

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Comparison.Cartan
