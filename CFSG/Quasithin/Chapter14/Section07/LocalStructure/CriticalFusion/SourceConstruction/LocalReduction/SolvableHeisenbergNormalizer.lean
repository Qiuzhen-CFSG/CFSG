module
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.SolvableHeisenbergResidual

/-!
# Normality of a solvable local Heisenberg residual in its overgroups

Let I be an actual solvable member of the original H_z, with normal point
residual L₁ and Heisenberg star residual. A proper invariant Frattini line
would supply two T-normalized cubic lifts generating O²(I). The established
solvable cubic containment places both in N_G(L), contradicting I's escape.
Thus the actual T-action is irreducible, and its literal quotient transport
puts the embedded O²(I) in Ξ(G,T).

The complete intrinsic embedding theorem makes this residual normal in every
two-local overgroup of I: each nonnormal alternative, including Held, has an
odd complement of order nine rather than 27. Hence its normalizer is the
unique maximal two-local containing I. The application supplies these facts
for the original minimal solvable witness, in particular normality in the
full original point normalizer. It does not identify I with that normalizer
or assert the terminal solvable exclusion.

Source: Aschbacher–Smith, 14.7.15(2–4) and its application in 14.7.27,
printed pp.1047,1054–1055, refs/quasithin.pdf. The actual earlier structural,
faithful classification and Baumann inputs retain their existing producers.
-/

public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction
open Chapter12.Section08 CriticalFusion.Source Chapter1
open Chapter14.Section04.LargerDimension.LocalAction.Components
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3}

/-- The actual Sylow action on the local residual Frattini quotient is irreducible. -/
theorem local_solvable_heisenberg_frattini_irreducible
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (I : Subgroup G) (hI : I ∈ F.Hz L (normalizer (L : Set G)))
    (hs : Group.IsSolvable I)
    (hn : ((F.Li L 1).subgroupOf I).Normal)
    (he : Nonempty (pResidual 2 (HStar I) ≃* HeisenbergPrime 3))
    (J : Subgroup ((pResidual 2 (HStar I)) ⧸ frattini (pResidual 2 (HStar I))))
    (hJ : ∀ a : ((T : Subgroup G).subgroupOf I).map (QuotientGroup.mk' (pCore 2 I)),
      ∀ x ∈ J, quotientAut (frattini (pResidual 2 (HStar I)))
        (MulAut.conjNormal (a : HStar I)) x ∈ J) :
    J = ⊥ ∨ J = ⊤ := by
  by_contra! hne
  obtain ⟨e⟩ := he
  let P := pResidual 2 (HStar I)
  let q := QuotientGroup.mk' (pCore 2 I)
  let S := T.subtype (F.sylow_le_of_mem_Hz hI)
  let : IsExtraspecial 3 P :=
    (HeisenbergPrime.isExtraspecial (by decide : 3 ≠ 2)).of_mulEquiv e.symm
  have hP : Nat.card P = 27 := (Nat.card_congr e.toEquiv).trans (HeisenbergPrime.card (p := 3))
  have heP : Monoid.exponent P = 3 :=
    (Monoid.exponent_eq_of_mulEquiv e).trans (HeisenbergPrime.exponent (by decide : 3 ≠ 2))
  have hk : IsPGroup 2 q.ker := by
    rw [QuotientGroup.ker_mk']
    exact pCore_isPGroup
  obtain ⟨A,B,hAB,hA,hB⟩ := IsExtraspecial.exists_cubic_lifts_of_stable_frattini_line
    q (QuotientGroup.mk'_surjective _) hk hP heP
    (S : Subgroup I) S.isPGroup' J hne.1 hne.2 hJ
  have hIL : I ≤ normalizer (F.Li L 1 : Set G) := by
    rw [←normal_subgroupOf_iff_le_normalizer (F.Li_one_le_of_mem_Hz hI)]
    exact hn
  have contained (A : Subgroup I) (hp : IsPPerfect 2 A)
      (hAT : (S : Subgroup I) ≤ normalizer (A : Set I))
      (hc : Nat.card (A ⧸ pCore 2 A) = 3) :
      A.map I.subtype ≤ normalizer (L : Set G) := by
    let eA := equivMapOfInjective A I.subtype I.subtype_injective
    apply local_solvable_cubic_containment h hab structural previous faithful I hI hs
      (A.map I.subtype) (map_subtype_le A) ((map_subtype_le A).trans hIL)
      (hp.of_surjective eA.toMonoidHom eA.surjective)
    · have hh := (map_mono hAT).trans (le_normalizer_map I.subtype)
      simpa only [S,Sylow.coe_subtype,map_subgroupOf_eq_of_le (F.sylow_le_of_mem_Hz hI)] using hh
    · exact (Nat.card_congr (QuotientGroup.congr _ _ eA (pCore_map_iso 2 eA)).toEquiv).symm.trans hc
  have hAM := contained A hA.1 hA.2.1 hA.2.2.2.2.2
  have hBM := contained B hB.1 hB.2.1 hB.2.2.2.2.2
  apply hI.2.2
  have hgen := congrArg (Subgroup.map I.subtype) (pResidual_sup_sylow_eq_top S)
  rw [Subgroup.map_sup,←MonoidHom.range_eq_map,range_subtype,
    Sylow.coe_subtype,map_subgroupOf_eq_of_le (F.sylow_le_of_mem_Hz hI)] at hgen
  rw [←hgen,←hAB,Subgroup.map_sup]
  exact sup_le (sup_le hAM hBM) (h.sylow_normalizes structural)

private def localResidualStarEquiv (I : Subgroup G) :
    ((pResidual 2 I) ⧸ pCore 2 (pResidual 2 I)) ≃* pResidual 2 (HStar I) :=
  (QuotientGroup.quotientMulEquivOfEq
    (pCore_subnormal_eq_comap 2 (inferInstance : (pResidual 2 I).Normal).isSubnormal)).trans
    (pResidualQuotientEquiv 2 (pCore 2 I))

private theorem localResidualStarEquiv_mk (I : Subgroup G) (x : pResidual 2 I) :
    (localResidualStarEquiv I (QuotientGroup.mk' (pCore 2 (pResidual 2 I)) x) : HStar I) =
      QuotientGroup.mk' (pCore 2 I) (x : I) := by
  dsimp only [localResidualStarEquiv,MulEquiv.trans_apply]
  change (pResidualQuotientEquiv 2 (pCore 2 I)
    (QuotientGroup.mk' ((pCore 2 I).subgroupOf (pResidual 2 I)) x) : HStar I) = _
  rw [pResidualQuotientEquiv_mk]

private def localResidualFrattiniEquiv (I : Subgroup G) :
    XiFrattiniQuotient (pResidual 2 I) ≃*
      ((pResidual 2 (HStar I)) ⧸ frattini (pResidual 2 (HStar I))) :=
  QuotientGroup.congr _ _ (localResidualStarEquiv I)
    (frattini_map_mulEquiv _)

private theorem localResidualFrattiniEquiv_action (I : Subgroup G)
    (S : Subgroup I) (hn : S ≤ normalizer (pResidual 2 I : Set I))
    (s : S) (x : XiFrattiniQuotient (pResidual 2 I)) :
    localResidualFrattiniEquiv I (xiFrattiniAction S (pResidual 2 I) hn s x) =
      quotientAut (frattini (pResidual 2 (HStar I)))
        (MulAut.conjNormal (QuotientGroup.mk' (pCore 2 I) (s : I)))
        (localResidualFrattiniEquiv I x) := by
  induction x using QuotientGroup.induction_on with | H x =>
    induction x using QuotientGroup.induction_on with | H k =>
      change localResidualFrattiniEquiv I (xiFrattiniAction S (pResidual 2 I) hn s
        (QuotientGroup.mk' _ (QuotientGroup.mk' _ k))) =
          quotientAut (frattini (pResidual 2 (HStar I)))
            (MulAut.conjNormal (QuotientGroup.mk' (pCore 2 I) (s : I)))
            (localResidualFrattiniEquiv I (QuotientGroup.mk' _ (QuotientGroup.mk' _ k)))
      simp only [xiFrattiniAction,MonoidHom.comp_apply,quotientAut_apply_mk,
        localResidualFrattiniEquiv,QuotientGroup.congr_mk']
      apply congrArg (QuotientGroup.mk' _)
      apply Subtype.ext
      rw [localResidualStarEquiv_mk]
      change QuotientGroup.mk' (pCore 2 I) _ =
        QuotientGroup.mk' (pCore 2 I) (s : I) * (localResidualStarEquiv I _) *
          (QuotientGroup.mk' (pCore 2 I) (s : I))⁻¹
      rw [localResidualStarEquiv_mk,←map_inv,←map_mul,←map_mul]
      rfl

/-- The minimal local's residual belongs to the ambient solvable uniqueness family. -/
theorem local_solvable_heisenberg_residual_mem_Xi
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (I : Subgroup G) (hI : I ∈ F.Hz L (normalizer (L : Set G)))
    (hs : Group.IsSolvable I)
    (hn : ((F.Li L 1).subgroupOf I).Normal)
    (he : Nonempty (pResidual 2 (HStar I) ≃* HeisenbergPrime 3)) :
    (pResidual 2 I).map I.subtype ∈ Xi G (T : Subgroup G) := by
  let S := T.subtype (F.sylow_le_of_mem_Hz hI)
  have hmapS : (S : Subgroup I).map I.subtype = (T : Subgroup G) := by
    rw [Sylow.coe_subtype,map_subgroupOf_eq_of_le (F.sylow_le_of_mem_Hz hI)]
  rw [←hmapS,mem_Xi_map_iff I.subtype I.subtype_injective]
  have hgen := pResidual_sup_sylow_eq_top S
  have hmap : (pResidual 2 I ⊔ (S : Subgroup I)).map I.subtype = I := by
    rw [hgen,←MonoidHom.range_eq_map,range_subtype]
  have hj : pResidual 2 I ⊔ (S : Subgroup I) ∈ Chapter1.H I := by
    change (pResidual 2 I ⊔ (S : Subgroup I)).pCoreIn 2 ≠ ⊥
    intro hz
    apply hI.1.1
    rw [←hmap,←map_pCoreIn_of_injective 2 _ I.subtype I.subtype_injective,hz,Subgroup.map_bot]
  let e := (localResidualStarEquiv I).trans he.some
  have hRn : (S : Subgroup I) ≤ normalizer (pResidual 2 I : Set I) := le_normalizer_of_normal
  refine ⟨isPPerfect_pResidual 2,hRn,hj,⟨3,by decide,by decide,Or.inr
    ⟨(HeisenbergPrime.isExtraspecial (by decide : 3 ≠ 2)).of_mulEquiv e.symm,
      (Nat.card_congr e.toEquiv).trans (HeisenbergPrime.card (p := 3)),
      (Monoid.exponent_eq_of_mulEquiv e).trans
        (HeisenbergPrime.exponent (by decide : 3 ≠ 2))⟩⟩,?_⟩
  intro A hA
  let eF := localResidualFrattiniEquiv I
  have hinv : ∀ a : ((T : Subgroup G).subgroupOf I).map (QuotientGroup.mk' (pCore 2 I)),
      ∀ x ∈ A.map eF.toMonoidHom,
      quotientAut (frattini (pResidual 2 (HStar I)))
        (MulAut.conjNormal (a : HStar I)) x ∈ A.map eF.toMonoidHom := by
    intro a x hx
    obtain ⟨s,hs,heq⟩ := a.property
    obtain ⟨y,hy,rfl⟩ := hx
    rw [←heq]
    change quotientAut (frattini (pResidual 2 (HStar I)))
      (MulAut.conjNormal (QuotientGroup.mk' (pCore 2 I) s))
      (localResidualFrattiniEquiv I y) ∈ A.map eF.toMonoidHom
    rw [←localResidualFrattiniEquiv_action I (S : Subgroup I) hRn ⟨s,hs⟩]
    exact mem_map_of_mem eF.toMonoidHom (hA ⟨s,hs⟩ y hy)
  rcases local_solvable_heisenberg_frattini_irreducible h hab structural previous faithful
      I hI hs hn he (A.map eF.toMonoidHom) hinv with hb | ht
  · exact Or.inl ((map_eq_bot_iff_of_injective A eF.injective).mp hb)
  · right
    have hh := congrArg (Subgroup.comap eF.toMonoidHom) ht
    simpa only [comap_map_eq_self_of_injective (f := eF.toMonoidHom) eF.injective,comap_top] using hh

/-- The local residual is normal in every two-local overgroup, including the
full original point normalizer. The nonnormal catalogue has the wrong odd order. -/
theorem local_solvable_heisenberg_normal_in_twoLocal
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (I : Subgroup G) (hI : I ∈ F.Hz L (normalizer (L : Set G)))
    (hs : Group.IsSolvable I)
    (hn : ((F.Li L 1).subgroupOf I).Normal)
    (he : Nonempty (pResidual 2 (HStar I) ≃* HeisenbergPrime 3))
    (M : Subgroup G) (hM : IsTwoLocal M) (hIM : I ≤ M) :
    (((pResidual 2 I).map I.subtype).subgroupOf M).Normal := by
  let R := (pResidual 2 I).map I.subtype
  have hX := local_solvable_heisenberg_residual_mem_Xi h hab structural previous faithful I hI hs hn he
  have hTM := (F.sylow_le_of_mem_Hz hI).trans hIM
  have hT : IsSylowIn 2 (T : Subgroup G) M := by
    refine ⟨T.subtype hTM,?_⟩
    simp only [Sylow.coe_subtype,map_subgroupOf_eq_of_le hTM]
  let eR := (pResidual 2 I).equivMapOfInjective I.subtype I.subtype_injective
  let e := (QuotientGroup.congr _ _ eR.symm (pCore_map_iso 2 eR.symm)).trans
    ((localResidualStarEquiv I).trans he.some)
  have hq : XiOddQuotient 3 (XiQuotient R) := Or.inr
    ⟨(HeisenbergPrime.isExtraspecial (by decide : 3 ≠ 2)).of_mulEquiv e.symm,
      (Nat.card_congr e.toEquiv).trans (HeisenbergPrime.card (p := 3)),
      (Monoid.exponent_eq_of_mulEquiv e).trans (HeisenbergPrime.exponent (by decide : 3 ≠ 2))⟩
  let b := XiEmbedding.localInput_of_mem_Xi hX hT
    (sup_le ((map_subtype_le _).trans hIM) hTM) (by decide : Odd 3) hq
    (default : Sylow 3 R)
  rcases b.adequate_knownSimple (h.source.simpleQTKE.twoLocal_sqtk hM) hT with hn | ⟨J,_,_,_,ha⟩
  · exact hn
  · have hplane : Nonempty (((default : Sylow 3 R) : Subgroup R).map R.subtype ≃*
        XiEmbedding.Plane 3) := by
      rcases ha with ha | ha
      · exact ha.1
      · exact ha.2.1
    obtain ⟨ep⟩ := hplane
    have h27 : Nat.card (((default : Sylow 3 R) : Subgroup R).map R.subtype) = 27 :=
      (Nat.card_congr b.complementQuotientEquiv.toEquiv).trans
        ((Nat.card_congr e.toEquiv).trans (HeisenbergPrime.card (p := 3)))
    have h9 := (Nat.card_congr ep.toEquiv).trans (XiEmbedding.plane_card 3)
    omega

/-- The actual local residual has a unique maximal two-local normalizer. -/
theorem local_solvable_heisenberg_normalizer_unique
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (I : Subgroup G) (hI : I ∈ F.Hz L (normalizer (L : Set G)))
    (hs : Group.IsSolvable I)
    (hn : ((F.Li L 1).subgroupOf I).Normal)
    (he : Nonempty (pResidual 2 (HStar I) ≃* HeisenbergPrime 3)) :
    IsMaximalTwoLocal (normalizer ((pResidual 2 I).map I.subtype : Set G)) ∧
      {M : Subgroup G | IsMaximalTwoLocal M ∧ I ≤ M} =
        {normalizer ((pResidual 2 I).map I.subtype : Set G)} := by
  let R := (pResidual 2 I).map I.subtype
  have hX := local_solvable_heisenberg_residual_mem_Xi h hab structural previous faithful I hI hs hn he
  have hcore : R.pCoreIn 2 ≠ ⊥ := hX.pCoreIn_ne_bot
    (fun _ hM _ hN hNM hn => lemma_1_1_3_1 hM hN hNM hn)
    (lemma_1_1_4_6 T (h.source.simpleQTKE.evenCharacteristic T))
  let S := T.subtype (F.sylow_le_of_mem_Hz hI)
  have hgen : R ⊔ (T : Subgroup G) = I := by
    have hh := congrArg (Subgroup.map I.subtype) (pResidual_sup_sylow_eq_top S)
    simpa only [Subgroup.map_sup,S,Sylow.coe_subtype,
      map_subgroupOf_eq_of_le (F.sylow_le_of_mem_Hz hI),
      ←MonoidHom.range_eq_map,range_subtype] using hh
  have hh := Chapter1.Section03.normalizer_unique_of_normal_in_maximalTwoLocals
    R (T : Subgroup G) hX.invariant
    (fun he => hcore (by change (pCore 2 R).map R.subtype = ⊥; rw [he,Subgroup.map_bot]))
    (fun M hM hRM => local_solvable_heisenberg_normal_in_twoLocal h hab structural previous faithful
      I hI hs hn he M hM.1 (hgen ▸ hRM))
  simpa only [hgen] using hh

/-- Apply the genuine local irreducibility and complete embedding theorem to
an original minimal solvable witness. Its residual is normal in the full H,
while the original quotient and proper-local distinction are retained. -/
theorem original_solvable_proper_heisenberg_normal
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (earlier : ResidualNormalizer.LocalControl.Earlier14710.{u})
    (hs : Group.IsSolvable F.H) :
    ∃ I : Subgroup G, I < F.H ∧ I ∈ F.Hz L (normalizer (L : Set G)) ∧
      Group.IsSolvable I ∧
      (∀ D : Subgroup G, F.Li L 1 ⊔ (T : Subgroup G) ≤ D → D < I →
        D ≤ normalizer (L : Set G)) ∧
      ((F.Li L 1).subgroupOf I).Normal ∧
      Nonempty (pResidual 2 (HStar I) ≃* HeisenbergPrime 3) ∧
      (pResidual 2 I).map I.subtype ∈ Xi G (T : Subgroup G) ∧
      (((pResidual 2 I).map I.subtype).subgroupOf F.H).Normal ∧
      IsMaximalTwoLocal (normalizer ((pResidual 2 I).map I.subtype : Set G)) ∧
      {M : Subgroup G | IsMaximalTwoLocal M ∧ I ≤ M} =
        {normalizer ((pResidual 2 I).map I.subtype : Set G)} := by
  obtain ⟨I,hIH,hI,hIs,hmin,hn,he⟩ := original_solvable_proper_heisenberg_residual
    d h hab structural previous faithful earlier hs
  have hpoint : F.Vi 1 ≠ ⊥ := by
    intro hz
    have hc := F.card 1 (by decide)
    rw [hz,card_bot] at hc
    norm_num at hc
  have hH : IsTwoLocal F.H := ⟨F.Vi 1,hpoint,
    IsPGroup.of_card (p := 2) (n := 1) (F.card 1 (by decide)),rfl⟩
  exact ⟨I,hIH,hI,hIs,hmin,hn,he,
    local_solvable_heisenberg_residual_mem_Xi h hab structural previous faithful I hI hIs hn he,
    local_solvable_heisenberg_normal_in_twoLocal h hab structural previous faithful I hI hIs hn he
      F.H hH hIH.le,
    local_solvable_heisenberg_normalizer_unique h hab structural previous faithful I hI hIs hn he⟩

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction
