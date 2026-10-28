module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanGlobalPrimeSylowComponents
public import Theory.GroupTheory.PResidual.NormalizedImageContainment
public import Theory.SpecificGroups.Alternating.FiveProperSubgroups
public import Theory.SpecificGroups.SL2.CardFourEquiv
public import Theory.GroupTheory.SolvableRadical.SolvableKernel

public import Theory.GroupTheory.ConjugateSpanSylow

/-!
# The common overgroup in the changed-Sylow argument

In original 5.2.2 let X = ⟨N_G(T₀),H⟩, where T₀ = N_T(R). The
index-two local containment theorem supplies the unique C-component of
X containing R. Its T-conjugate span is normal in X and contains both
the original residual and the changed conjugate span. The literal
changed local group R T₁ contains the nontrivial core of G₀T₀B.

The source exclusion of an L₂(4) original residual uses the actual
normalizing Sylow intersection: the residual's two-core normalizes R,
so R has a proper nonsolvable image in the quotient. Every proper
subgroup of A₅ is solvable, giving the contradiction.

The last theorem applies the explicit 5.1.13 implication to G₀T₀B.
The equality of original and changed residuals and the changed source
hypotheses remain explicit. Their construction, the smaller-Sylow
exclusion, and final normalization stay with
qt-d-1222-rankone-cartan-local-to-global. No field parameters are compared
by these results.

Source: Aschbacher--Smith 1.2.4--5 and 5.2.2, pp.505--506,648--649.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Prime
variable {G : Type*} [Group G] [Finite G]

/-- The source common overgroup has a unique component containing R.
Its T-orbit is normal and contains the original residual. -/
theorem LocalData.common_normal_component
    {T : Sylow 2 G} {L W H A B D R : Subgroup G} {n p : ℕ}
    (d : LocalData T L H B D R) (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (c : CartanPair T L H A B) (hd : CartanPrimeActor A H p D)
    (hz : (generated L H D R).pCoreIn 2 ≠ ⊥) :
    let X := normalizer (normalizingSylow T R : Set G) ⊔ H
    ∃ I : Subgroup G, R ≤ I ∧ I ≤ X ∧ (I.subgroupOf X).IsCComponent ∧
      normalizingSylow T R ≤ normalizer (I : Set G) ∧
      (∀ J : Subgroup G, J ≤ X → (J.subgroupOf X).IsCComponent → R ≤ J → J = I) ∧
      residual H ≤ conjugateSpanBy I (T : Subgroup G) ∧
      conjugateSpanBy I (T : Subgroup G) ≤ X ∧
      ((conjugateSpanBy I (T : Subgroup G)).subgroupOf X).Normal := by
  let X := normalizer (normalizingSylow T R : Set G) ⊔ H
  have hX := d.common_normal_overgroup h hH c hd hz
  have hTX : (T : Subgroup G) ≤ X := (show (T : Subgroup G) ≤ H from hH.1.1.2).trans le_sup_right
  have hT₀X : normalizingSylow T R ≤ X := inf_le_left.trans hTX
  have hRX : R ≤ X := d.right_le_residual.trans ((map_subtype_le _).trans le_sup_right)
  have hQ := Chapter3.sqtk_of_mem_H h.qtke hX.1
  have hQbar : IsSQTK KnownSimple.IsKnownSimple (X ⧸ pCore 2 X) := by
    refine ⟨?_, hQ.isKGroup.quotient _⟩
    intro q hq ho
    let : Fact q.Prime := ⟨hq⟩
    exact (primeRank_quotient_le_of_isTwoGroup q ho (pCore 2 X) pCore_isPGroup).trans
      (hQ.stronglyQuasithin q hq ho)
  let S := T.subtype hTX
  have hS : (S : Subgroup X).map X.subtype = (T : Subgroup G) :=
    map_subgroupOf_eq_of_le hTX
  have hi : ((normalizingSylow T R).subgroupOf X).relIndex (S : Subgroup X) ≤ 2 := by
    change ((normalizingSylow T R).comap X.subtype).relIndex (S : Subgroup X) ≤ 2
    rw [relIndex_comap, hS]
    exact (d.normalizingSylow_index hH.1.1.2 c hd hz).le
  have hlocal : R.subgroupOf X ∈ Chapter1.L X ((normalizingSylow T R).subgroupOf X) :=
    (Chapter1.mem_LIn_iff_subgroupOf hT₀X hRX).mp ⟨hRX,d.right_mem_local_family h hH⟩
  obtain ⟨K,hK,hu⟩ := Chapter1.Section02.index_le_two_local_component_source hQbar S
    (show (normalizingSylow T R).subgroupOf X ≤ (S : Subgroup X) from
      subgroupOf_mono X inf_le_left) hi hlocal
  let I := K.map X.subtype
  have hIX : I ≤ X := map_subtype_le _
  have hIK : I.subgroupOf X = K := comap_map_eq_self_of_injective X.subtype_injective K
  have hRI : R ≤ I := by
    simpa only [map_subgroupOf_eq_of_le hRX] using map_mono (f := X.subtype) hK.2
  have hnorm : normalizingSylow T R ≤ normalizer (I : Set G) := by
    have hn := cComponent_le_normalizer_of_unique hK.1 hK.2
      (fun J hJ hRJ => hu J ⟨hJ,hRJ⟩)
      (S := (normalizingSylow T R).subgroupOf X)
      (by rw [← subgroupOf_normalizer_eq hRX]; exact subgroupOf_mono X inf_le_right)
    rw [← hIK, ← subgroupOf_normalizer_eq hIX] at hn
    intro x hx
    exact hn (show (⟨x,hT₀X hx⟩ : X) ∈ (normalizingSylow T R).subgroupOf X from hx)
  have horbit : (conjugateSpanBy K (S : Subgroup X)).Normal :=
    conjugateSpanBy_sylow_normal K S
      (Chapter1.Section02.proposition_1_2_1_three_orbit_source hQbar hK.1)
  have hmap : (conjugateSpanBy K (S : Subgroup X)).map X.subtype =
      conjugateSpanBy I (T : Subgroup G) := by
    rw [map_conjugateSpanBy, hS]
  have hJX : conjugateSpanBy I (T : Subgroup G) ≤ X :=
    conjugateSpanBy_le hIX (hTX.trans X.le_normalizer)
  refine ⟨I,hRI,hIX,hIK.symm ▸ hK.1,hnorm,?_,?_,hJX,?_⟩
  · intro J hJX hJ hRJ
    have he := hu (J.subgroupOf X) ⟨hJ,subgroupOf_mono X hRJ⟩
    calc
      J = (J.subgroupOf X).map X.subtype :=
        (map_subgroupOf_eq_of_le (show J ≤ X from hJX)).symm
      _ = K.map X.subtype := congrArg (map X.subtype) he
      _ = I := rfl
  · rw [d.residual_eq_conjugateSpan]
    exact conjugateSpanBy_le (hRI.trans (le_conjugateSpanBy I _))
      (le_normalizer_conjugateSpanBy I _)
  · change ((conjugateSpanBy I (T : Subgroup G)).subgroupOf X).Normal
    rw [← hmap]
    change ((conjugateSpanBy K (S : Subgroup X)).map X.subtype |>.comap X.subtype).Normal
    rw [comap_map_eq_self_of_injective X.subtype_injective]
    exact horbit

/-- The changed local group has nontrivial core, escapes the original M,
and lies in both literal source overgroups. -/
theorem LocalData.changedSylow_overgroups
    {T : Sylow 2 G} {L W H A B D R : Subgroup G} {n p : ℕ}
    (d : LocalData T L H B D R) (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (c : CartanPair T L H A B) (hd : CartanPrimeActor A H p D)
    (hz : (generated L H D R).pCoreIn 2 ≠ ⊥)
    (P : Sylow 2 (extension T L H B D R))
    (hTP : normalizingSylow T R ≤
      (P : Subgroup (extension T L H B D R)).map (extension T L H B D R).subtype) :
    let T₁ := (P : Subgroup (extension T L H B D R)).map (extension T L H B D R).subtype
    let H₀ := R ⊔ T₁
    H₀ ∈ Chapter1.HOver G (T₁ : Set G) ∧
      extension T L H B D R ∈ Chapter1.HOver G (H₀ : Set G) ∧
      normalizer (normalizingSylow T R : Set G) ⊔ H ∈ Chapter1.HOver G (H₀ : Set G) ∧
      ¬ H₀ ≤ normalizer (L : Set G) ∧
      T₁ ≤ normalizer (L : Set G) := by
  let E := extension T L H B D R
  let T₁ := (P : Subgroup E).map E.subtype
  let H₀ := R ⊔ T₁
  have hT₁N : T₁ ≤ normalizer (normalizingSylow T R : Set G) :=
    d.overgroup_two_subgroup_normalizes hH.1.1.2 c hd hz (P.isPGroup'.map E.subtype) hTP
  have hHE : H₀ ≤ E := sup_le
    (le_sup_left.trans (le_sup_right.trans (le_sup_left.trans le_sup_left)))
    (map_subtype_le _)
  have hcore : E.pCoreIn 2 ≤ H₀ := (pCoreIn_le_sylow E P).trans le_sup_right
  have hne : H₀.pCoreIn 2 ≠ ⊥ := by
    intro he
    exact d.extension_core_ne_bot hz (bot_unique
      (((le_inf hcore le_rfl).trans (inf_pCoreIn_le_of_le 2 hHE)).trans he.le))
  have hX := d.common_normal_overgroup h hH c hd hz
  exact ⟨⟨hne,fun _ hx => mem_sup_right hx⟩,⟨d.extension_core_ne_bot hz,hHE⟩,
    ⟨hX.1,sup_le (d.right_le_residual.trans ((map_subtype_le _).trans le_sup_right))
      (hT₁N.trans le_sup_left)⟩,
    (fun he => d.right_outside (le_sup_left.trans he)),
    hT₁N.trans (d.normalizingSylow_normalizer_le h hH c hd hz)⟩

/-- The actual two-residual of the changed local group is its orbit span
of the original perfect right factor. -/
theorem LocalData.changedSylow_residual_eq_conjugateSpan
    {T : Sylow 2 G} {L W H B D R : Subgroup G} {n : ℕ} {κ : GroupClass}
    (d : LocalData T L H B D R) (h : Input κ T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (P : Sylow 2 (extension T L H B D R)) :
    let T₁ := (P : Subgroup (extension T L H B D R)).map (extension T L H B D R).subtype
    residual (R ⊔ T₁) = conjugateSpanBy R T₁ := by
  let T₁ := (P : Subgroup (extension T L H B D R)).map (extension T L H B D R).subtype
  let H₀ := R ⊔ T₁
  let : Group.IsPerfect R := Chapter1.mem_L_isPerfect (d.right_mem_local_family h hH)
  let e := subgroupOfEquivOfLe (show R ≤ H₀ from le_sup_left)
  let : Group.IsPerfect (R.subgroupOf H₀) := Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective
  let : Group.IsNilpotent (H₀ ⧸ pResidual 2 H₀) := (isPGroup_quotient_pResidual 2).isNilpotent
  have hR : R ≤ residual H₀ := by
    have hh := le_of_isPerfect_of_solvable_quotient (R.subgroupOf H₀) (pResidual 2 H₀)
    simpa only [map_subgroupOf_eq_of_le (show R ≤ H₀ from le_sup_left)] using
      map_mono (f := H₀.subtype) hh
  exact embedded_pResidual_eq_conjugateSpanBy R T₁ H₀ hR (P.isPGroup'.map _) rfl

/-- Both the original residual and the changed conjugate span lie in the
same normal component orbit in the common-normal overgroup. -/
theorem LocalData.changedSylow_common_component
    {T : Sylow 2 G} {L W H A B D R : Subgroup G} {n p : ℕ}
    (d : LocalData T L H B D R) (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (c : CartanPair T L H A B) (hd : CartanPrimeActor A H p D)
    (hz : (generated L H D R).pCoreIn 2 ≠ ⊥)
    (P : Sylow 2 (extension T L H B D R))
    (hTP : normalizingSylow T R ≤
      (P : Subgroup (extension T L H B D R)).map (extension T L H B D R).subtype) :
    let T₁ := (P : Subgroup (extension T L H B D R)).map (extension T L H B D R).subtype
    let X := normalizer (normalizingSylow T R : Set G) ⊔ H
    ∃ I : Subgroup G, R ≤ I ∧ I ≤ X ∧ (I.subgroupOf X).IsCComponent ∧
      normalizingSylow T R ≤ normalizer (I : Set G) ∧
      (∀ J : Subgroup G, J ≤ X → (J.subgroupOf X).IsCComponent → R ≤ J → J = I) ∧
      let Kplus := conjugateSpanBy I (T : Subgroup G)
      residual H ≤ Kplus ∧ Kplus ≤ X ∧ (Kplus.subgroupOf X).Normal ∧
        T₁ ≤ normalizer (Kplus : Set G) ∧ conjugateSpanBy R T₁ ≤ Kplus := by
  let T₁ := (P : Subgroup (extension T L H B D R)).map (extension T L H B D R).subtype
  let X := normalizer (normalizingSylow T R : Set G) ⊔ H
  obtain ⟨I,hRI,hIX,hI,hTI,hu,hKJ,hJX,hJn⟩ := d.common_normal_component h hH c hd hz
  have hT₁X : T₁ ≤ X :=
    (d.overgroup_two_subgroup_normalizes hH.1.1.2 c hd hz
      (P.isPGroup'.map _) hTP).trans le_sup_left
  have hn : T₁ ≤ normalizer (conjugateSpanBy I (T : Subgroup G) : Set G) :=
    hT₁X.trans ((normal_subgroupOf_iff_le_normalizer hJX).mp hJn)
  exact ⟨I,hRI,hIX,hI,hTI,hu,hKJ,hJX,hJn,hn,
    conjugateSpanBy_le (hRI.trans (le_conjugateSpanBy I _)) hn⟩

/-- A proper nonsolvable right factor survives the two-core quotient,
excluding the L₂(4) alternative for the original residual. -/
theorem LocalData.residual_not_linear_four
    {T : Sylow 2 G} {L W H A B D R : Subgroup G} {n p : ℕ}
    (d : LocalData T L H B D R) (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (c : CartanPair T L H A B) (hd : CartanPrimeActor A H p D)
    (hz : (generated L H D R).pCoreIn 2 ≠ ⊥) :
    ¬ ClassicalGroup.IsPSL ((residual H) ⧸ pCore 2 (residual H)) 2 4 := by
  intro hm
  let K := residual H
  let q := QuotientGroup.mk' (pCore 2 K)
  let Rk := R.subgroupOf K
  have hRK : R < K := d.right_lt_residual hH.1.1.2 c hd hz
  have hcore : K.pCoreIn 2 ≤ normalizingSylow T R := by
    obtain ⟨Q,hQ⟩ := NormalSylowQuotientAction.intersection_sylow T K
      (hH.1.1.2.trans (le_normalizer_residual H))
    have hc := pCoreIn_le_sylow K Q
    rw [hQ,subgroupOf_map_subtype,←d.S_intersection_residual] at hc
    exact hc.trans (inf_le_left.trans (d.sourceS_le_normalizingSylow h hH))
  have hnorm : q.ker ≤ normalizer (Rk : Set K) := by
    rw [QuotientGroup.ker_mk', ← subgroupOf_normalizer_eq hRK.le]
    intro x hx
    exact (hcore (mem_map_of_mem K.subtype hx)).2
  have hk : IsPGroup 2 q.ker := by rw [QuotientGroup.ker_mk']; exact pCore_isPGroup
  have hp : IsPPerfect 2 (⊤ : Subgroup K) :=
    (isPPerfect_embedded_pResidual 2 H).of_surjective
      (topEquiv (G := K)).symm.toMonoidHom (topEquiv (G := K)).symm.surjective
  have hproper : Rk.map q ≠ ⊤ := by
    intro he
    have ht : (⊤ : Subgroup K) ≤ Rk :=
      isPPerfect_le_of_map_le_of_kernel_normalizes q ⊤ Rk hp hk hnorm (by rw [he]; exact le_top)
    exact hRK.not_ge (subgroupOf_eq_top.mp (top_unique ht))
  obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
  let ea := e.trans ((Matrix.ProjectiveSpecialLinearGroup.equiv_alternatingGroup_of_card_four hF).some)
  let : Group.IsSolvable (Rk.map q) :=
    alternatingGroup.isSolvable_subgroup_of_equiv_five ea _ hproper
  let : Group.IsNilpotent q.ker := hk.isNilpotent
  let : Group.IsSolvable ((Rk.map q).comap q) := isSolvable_comap_of_solvable_ker q _
  let : Group.IsSolvable Rk := Group.isSolvable_of_isSolvable_injective
    (f := inclusion (le_comap_map q Rk)) (inclusion_injective _)
  exact d.right_nonsolvable (Group.isSolvable_of_isSolvable_injective
    (f := (subgroupOfEquivOfLe hRK.le).symm.toMonoidHom)
    (subgroupOfEquivOfLe hRK.le).symm.injective)

/-- Apply the original local 5.1.13 implication to the literal changed
overgroup. The changed source input and residual comparison are retained
as explicit obligations of the final 5.2.2 assembly in this task. -/
theorem LocalData.changedSylow_escape_impossible
    {T U : Sylow 2 G} {L W W₁ H A B B₁ D R : Subgroup G} {n p : ℕ}
    (d : LocalData T L H B D R) (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (c : CartanPair T L H A B) (hd : CartanPrimeActor A H p D)
    (hz : (generated L H D R).pCoreIn 2 ≠ ⊥)
    (P : Sylow 2 (extension T L H B D R))
    (hTP : normalizingSylow T R ≤
      (P : Subgroup (extension T L H B D R)).map (extension T L H B D R).subtype)
    (hU : (U : Subgroup G) =
      (P : Subgroup (extension T L H B D R)).map (extension T L H B D R).subtype)
    (h513 : SourceLocalCartanEscape KnownSimple.IsKnownSimple G)
    (h₁ : Input KnownSimple.IsKnownSimple U L W₁ n)
    (hH₀ : R ⊔ (U : Subgroup G) ∈ Chapter3.HStar (U : Subgroup G) (normalizer (L : Set G)))
    (hk₀ : 1 < ChapterE.generationParameter (R ⊔ (U : Subgroup G) : Subgroup G))
    (c₀ : CartanPair U L (R ⊔ (U : Subgroup G)) A B₁)
    (hres : residual (R ⊔ (U : Subgroup G)) = residual H) : False := by
  let H₀ := R ⊔ (U : Subgroup G)
  let E := extension T L H B D R
  have hE : E ∈ Chapter1.HOver G (H₀ : Set G) := by
    simpa only [H₀,hU] using (d.changedSylow_overgroups h hH c hd hz P hTP).2.1
  have hmove : ¬ A ⊓ E ≤ normalizer (residual H₀ : Set G) := by
    intro hn
    apply h.prime_actor_not_normalizes hH hd
    rw [← hres]
    exact (le_inf hd.le_cartan (le_sup_left.trans (le_sup_left.trans le_sup_left))).trans hn
  have he := h513 U L W₁ n h₁ H₀ hH₀ hk₀ A B₁ c₀ E hE hmove
  have hm : ClassicalGroup.IsPSL ((residual H₀) ⧸ pCore 2 (residual H₀)) 2 4 := by
    let e := (pResidual 2 H₀).equivMapOfInjective H₀.subtype H₀.subtype_injective
    exact he.2.1.of_mulEquiv (QuotientGroup.congr _ _ e (pCore_map_iso 2 e)).symm
  rw [hres] at hm
  exact d.residual_not_linear_four h hH c hd hz hm

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Prime
