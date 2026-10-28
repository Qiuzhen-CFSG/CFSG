module
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceDoubledSymplecticCartan
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceDoubledSymplecticSixCartan
public import CFSG.Quasithin.Chapter4.Section02.RankOneReciprocalEscape.Ranks
public import Theory.GroupTheory.CComponent.OddRankNormal
public import Theory.SpecificGroups.SymplecticFour.OddFieldActors.Cubic
public import Theory.SpecificGroups.Alternating.TwoThreeCycles

/-!
# Reciprocal escape for both paired symplectic rows

The central quotient of the original L/O₂(L) has three-rank at least two:
the nonbinary marking uses two orthogonal cubic subgroups, and the A₆
marking uses two disjoint three-cycles. In the contrary reciprocal branch,
L becomes a nonnormal C-component of an SQTK group. Its two-core quotient
is then centerless, and the commuting-conjugate three-rank bound forces
normality, contradicting the source index two. Thus the actual preimage
of F*(H/O₂(H)) escapes N_G(L) for both original markings.

The last theorem retains the whole doubled orbit in the same witness's
residual two-core, with its commutator and fixed-subgroup properties.
The seed is never identified with that orbit. These are the reciprocal
and residual inputs to the remaining ordinary/constrained exclusions,
not a completed Hall-faithfulness or weak-closure theorem.

Source: Aschbacher--Smith A.3.8(3), 4.2.5--8 and 4.4.6,
printed pp.46,609--610,620; used in 7.3.4, p.699, refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped Pointwise IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open ChapterB.QuasisimpleSource Chapter4 Chapter4.Section04 Chapter4.Section02.RankOneReciprocalEscape
open Chapter7.NormalizedSource Theory.SpecificGroups.SymplecticFour
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V)

private theorem normal_of_central_core_cubic_rank
    {Q : Type*} [Group Q] [Finite Q]
    (hQ : IsSQTK KnownSimple.IsKnownSimple Q) {B : Subgroup Q}
    (hB : B.IsCComponent) [IsQuasisimple (B ⧸ pCore 2 B)]
    (hr : 2 ≤ primeRank 3 ((B ⧸ pCore 2 B) ⧸ center (B ⧸ pCore 2 B))) : B.Normal := by
  by_contra hn
  have hz := coreQuotient_center_eq_bot_of_nonnormal hQ hB hn
  have he : ((B ⧸ pCore 2 B) ⧸ center (B ⧸ pCore 2 B)) ≃* (B ⧸ pCore 2 B) :=
    (QuotientGroup.quotientMulEquivOfEq hz).trans QuotientGroup.quotientBot
  rw [primeRank_congr 3 he] at hr
  exact hn (hB.normal_of_coprime_core_center_primeRank (by decide : Odd 3)
    (by rw [hz]; simp) hr (hQ.stronglyQuasithin 3 (by decide) (by decide)))

private theorem sourceOrbit_reciprocal_escape_of_cubic_rank
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hr : 2 ≤ primeRank 3 ((L ⧸ pCore 2 L) ⧸ center (L ⧸ pCore 2 L)))
    (A : Subgroup G)
    (hA : A ≤ normalizer (L : Set G) ⊓ centralizer (D.sourceOrbit : Set G))
    (ho : Odd (Nat.card A))
    (hnot : ¬ UniqueMaximalOvergroup (oddActorResidual L A) (normalizer (L : Set G))) :
    EscapeCase L V A := by
  have hc := (le_sectionCentralizer_iff A L).mp
    (hA.trans (by simpa only [←D.sourceOrbit_eq] using
      D.doubledOrbit_relative_centralizer_le_sectionCentralizer h))
  have hM := D.doubledNormalizer_unique h
  have hu : UniqueMaximalOvergroup (L ⊔ (T : Subgroup G)) (normalizer (L : Set G)) :=
    ⟨hM.1,sup_le L.le_normalizer D.sylow_normalizes_component,hM.2⟩
  obtain ⟨J,H,W,hw,hh⟩ := reciprocal_case_of_not_unique h.toHypothesis1221 D hu
    A hc.1 hc.2 ho ((hA.trans inf_le_right).trans
      (centralizer_le (by rw [D.sourceOrbit_eq]; exact le_componentOrbit V T))) hnot
  refine ⟨J,H,W,hw,?_⟩
  intro hf
  obtain ⟨hB,hcomp,hnorm,hi,_⟩ := hh hf
  have hLH : L ≤ H := hB ▸ (map_subtype_le _).trans inf_le_right
  let e := QuotientGroup.congr _ _ (subgroupOfEquivOfLe hLH)
    (pCore_map_iso 2 (subgroupOfEquivOfLe hLH))
  let := h.quasisimple
  let : IsQuasisimple ((L.subgroupOf H) ⧸ pCore 2 (L.subgroupOf H)) :=
    IsQuasisimple.of_mulEquiv e.symm
  have hr' : 2 ≤ primeRank 3 (((L.subgroupOf H) ⧸ pCore 2 (L.subgroupOf H)) ⧸
      center ((L.subgroupOf H) ⧸ pCore 2 (L.subgroupOf H))) := by
    rwa [primeRank_congr 3 (centerQuotientCongr e)]
  let : (L.subgroupOf H).Normal := normal_of_central_core_cubic_rank
    hw.2.2.2.2.2.2.1.sqtk hcomp hr'
  rw [normalizer_eq_top] at hnorm
  rw [←hnorm,index_top] at hi
  norm_num at hi

/-- The actual nonbinary symplectic marking gives the reciprocal Fitting escape. -/
theorem sourceOrbit_symplectic_reciprocal_escape
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (F : BinaryField)
    (hmodel : Nonempty (ActionEquiv (D.seedRepresentation.comp D.componentImage.subtype)
      (Representation.restrictScalars (k := ZMod 2) (symplecticNatural (k := F.Carrier) 2))))
    (A : Subgroup G)
    (hA : A ≤ normalizer (L : Set G) ⊓ centralizer (D.sourceOrbit : Set G))
    (ho : Odd (Nat.card A))
    (hnot : ¬ UniqueMaximalOvergroup (oddActorResidual L A) (normalizer (L : Set G))) :
    EscapeCase L V A := by
  let := h.quasisimple
  obtain ⟨m⟩ := hmodel
  let : Nontrivial (Sp F.Carrier) := m.groupEquiv.symm.toEquiv.nontrivial
  let r := m.groupEquiv.toMonoidHom.comp D.componentQuotientHom
  have hr : Function.Surjective r := m.groupEquiv.surjective.comp D.componentQuotientHom_surjective
  have hk : r.ker = center (L ⧸ pCore 2 L) := by
    have hh := IsQuasisimple.comap_center_of_surjective r hr
    rw [EvenProjective.center_eq_bot,MonoidHom.comap_bot] at hh
    exact hh
  let e := (QuotientGroup.quotientMulEquivOfEq hk.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective r hr)
  apply D.sourceOrbit_reciprocal_escape_of_cubic_rank h _ A hA ho hnot
  rw [primeRank_congr 3 e]
  exact OddFieldActors.cubic_rank

/-- The genuine A₆ seed marking gives the same reciprocal Fitting escape. -/
theorem sourceOrbit_six_reciprocal_escape
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmodel : Nonempty (ActionEquiv (D.seedRepresentation.comp D.componentImage.subtype)
      (alternatingNatural 6)))
    (A : Subgroup G)
    (hA : A ≤ normalizer (L : Set G) ⊓ centralizer (D.sourceOrbit : Set G))
    (ho : Odd (Nat.card A))
    (hnot : ¬ UniqueMaximalOvergroup (oddActorResidual L A) (normalizer (L : Set G))) :
    EscapeCase L V A := by
  let := h.quasisimple
  obtain ⟨m⟩ := hmodel
  let r := m.groupEquiv.toMonoidHom.comp D.componentQuotientHom
  have hr : Function.Surjective r := m.groupEquiv.surjective.comp D.componentQuotientHom_surjective
  have hk : r.ker = center (L ⧸ pCore 2 L) := by
    have hh := IsQuasisimple.comap_center_of_surjective r hr
    rw [alternatingGroup.center_eq_bot (by norm_num : 4 ≤ Nat.card (Fin 6)),MonoidHom.comap_bot] at hh
    exact hh
  let e := (QuotientGroup.quotientMulEquivOfEq hk.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective r hr)
  apply D.sourceOrbit_reciprocal_escape_of_cubic_rank h _ A hA ho hnot
  rw [primeRank_congr 3 e]
  exact alternatingGroup.TwoThreeCycles.two_le_primeRank (by decide)

/-- The same pushing-up witness retains the whole orbit in the residual core,
with its fixed subgroup trivial. The seed is not identified with the orbit. -/
theorem sourceOrbit_whole_pushingUp_residual_data
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation)
    {A J H W : Subgroup G}
    (hA : A ≤ normalizer (L : Set G) ⊓ centralizer (D.sourceOrbit : Set G))
    (ho : Odd (Nat.card A)) (hw : Witness L V A J H W) :
    let R := (solvableResidual (L ⊓ H : Subgroup G)).map (L ⊓ H).subtype
    (H ⊓ normalizer (L : Set G)) ≤ normalizer (R : Set G) ∧
      D.sourceOrbit ≤ J.pCoreIn 2 ∧ D.sourceOrbit ≤ R.pCoreIn 2 ∧
      D.sourceOrbit = ⁅D.sourceOrbit,R⁆ ∧
      D.sourceOrbit ⊓ centralizer (R : Set G) = ⊥ := by
  let R := (solvableResidual (L ⊓ H : Subgroup G)).map (L ⊓ H).subtype
  have hcore := (D.doubledOrbit_oddActorResidual_cover h A
    (by simpa only [←D.sourceOrbit_eq] using hA) ho).2.2.1
  have hWJ : D.sourceOrbit ≤ J.pCoreIn 2 := by
    rw [D.sourceOrbit_eq]
    exact hcore.trans hw.2.1.1
  have hWH : D.sourceOrbit ≤ H := hWJ.trans ((pCoreIn_le 2 J).trans hw.2.2.2.1)
  rcases hw with ⟨_,_,_,_,_,_,hc,hcover,hn,_,_,_⟩
  have hRN := (normal_subgroupOf_iff_le_normalizer hc.component_le).mp hn
  have hWM : D.sourceOrbit ≤ normalizer (L : Set G) :=
    D.sourceOrbit_weakClosure_setup.le_sylow.trans D.sylow_normalizes_component
  have hWR : D.sourceOrbit ≤ normalizer (R : Set G) := (le_inf hWH hWM).trans hRN
  have hLC : L.pCoreIn 2 ≤ centralizer (D.sourceOrbit : Set G) := by
    apply (pCoreIn_mono_of_normalizes (show L ≤ L ⊔ (T : Subgroup G) from le_sup_left)
      (sup_le L.le_normalizer D.sylow_normalizes_component)).trans
    simpa only [D.fundamentalSetup_module,Chapter3.Section02.localJoin,D.localOrbit_eq,
      ←D.sourceOrbit_eq] using (D.fundamentalSetup h.toHypothesis1221).core_centralizes_module
  have hcomm : D.sourceOrbit = ⁅D.sourceOrbit,R⁆ := by
    have hh := D.doubledOrbit_commutator_component h
    rw [←D.sourceOrbit_eq] at hh
    exact hh.trans (commutator_eq_of_product_centralizing_factor hcover (le_centralizer_iff.mp hLC))
  have hWF : D.sourceOrbit ≤ R := hcomm ▸ le_normalizer_iff_commutator_le_right.mp hWR
  have hWFcore : D.sourceOrbit ≤ R.pCoreIn 2 := le_pCoreIn_of_normalizes
    (IsElementaryAbelian.isPGroup 2 D.sourceOrbit) hWF
    (((map_subtype_le _).trans inf_le_left).trans D.sourceOrbit_component_normalizes)
  refine ⟨hRN,hWJ,hWFcore,hcomm,?_⟩
  apply bot_unique
  intro x hx
  apply (D.sourceOrbit_whole_fixed_eq_bot h hmany hnon).le
  refine ⟨hx.1,?_⟩
  intro y hy
  obtain ⟨f,hf,c,hc,he⟩ := hcover.subset hy
  have hfx := hx.2 f hf
  have hcx := (le_centralizer_iff.mp hLC) hx.1 c hc
  rw [←he,mul_assoc,hcx,←mul_assoc,hfx,mul_assoc]

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
