module
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.ExtraspecialCubicQuotient
public import CFSG.Quasithin.ChapterF.Section06.Basic
public import Theory.GroupTheory.PResidual.Restriction
public import Theory.GroupTheory.ConjugateSpanNormalizer
public import Theory.GroupTheory.ConjugateSpanSupplement
public import Theory.GroupTheory.SymmetricThreeTwoCoreStructure

/-!
# The original plane vertex in the cubic amalgam

The literal plane action identifies P = L₂T and P/O₂(P) with S₃.
Fixing the point as well as the plane gives exactly the original Sylow T.
Thus P and any cubic Sylow overgroup inside G₁ form a Goldschmidt triple
in their generated subgroup. The L₂-orbit of V₁ spans precisely V₂.

In the normal-point branch, an escaping Y cannot normalize L₂C_D(W),
where D = ⟨P,YT⟩ and W = ⟨V₁^D⟩: that would make Y preserve V₂ and
hence normalize L. The later module transports this to D/C_D(W).

Source: Aschbacher–Smith, 14.5.3--6, printed pp.1013--1014;
normal-point geometry in 14.7.15, printed p.1047, refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction
open Chapter12.Section08 CriticalFusion.Source
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3}

omit [Finite G] in
private theorem cubic_P_eq : F.P L = (L ⊔ (T : Subgroup G)) ⊓ F.Gi 2 := by
  ext x
  simp only [InvariantFlag.P, mem_inf, mem_iInf]
  constructor
  · exact fun hx => ⟨hx.1,hx.2 2 ⟨le_rfl,by decide⟩⟩
  · rintro ⟨hx,h2⟩
    refine ⟨hx,fun i hi => ?_⟩
    have : i = 2 := by omega
    subst i
    exact h2

/-- The plane parabolic retains the original two-residual L₂. -/
theorem plane_parabolic_residual
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u}) :
    (pResidual 2 (F.P L)).map (F.P L).subtype = F.Li L 2 := by
  have hLT : (pResidual 2 (L ⊔ (T : Subgroup G) : Subgroup G)).map
      (L ⊔ (T : Subgroup G)).subtype = L :=
    embedded_pResidual_join_pGroup L _ ((pResidual_eq_top_iff 2 L).mp h.residual)
      T.isPGroup' (h.sylow_normalizes structural)
  have hN : L ⊓ F.Gi 2 ≤ F.P L := by
    rw [cubic_P_eq]
    exact inf_le_inf_right _ le_sup_left
  have hR : (pResidual 2 (F.P L)).map (F.P L).subtype ≤ L ⊓ F.Gi 2 :=
    le_inf ((embedded_pResidual_mono 2 (show F.P L ≤ L ⊔ (T : Subgroup G) from inf_le_left)).trans_eq hLT)
      ((map_subtype_le _).trans (F.P_le_G₂ (by decide) L h.chosen.normalizes))
  have he := embedded_pResidual_eq_of_le_of_residual_le 2 hN hR
  simpa [InvariantFlag.Li] using he.symm

/-- The flag-defined parabolic is precisely L₂T, with the original Sylow. -/
theorem plane_parabolic_eq_join
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u}) :
    F.P L = F.Li L 2 ⊔ (T : Subgroup G) := by
  have he := congrArg (map (F.P L).subtype)
    (pResidual_sup_sylow_eq_top (T.subtype (F.binary_sylow_le_P L)))
  rw [Subgroup.map_sup,plane_parabolic_residual h structural,
    Sylow.coe_subtype,map_subgroupOf_eq_of_le (F.binary_sylow_le_P L),
    ←MonoidHom.range_eq_map,range_subtype] at he
  exact he.symm

/-- Conjugation on the literal plane identifies the full two-core quotient. -/
def planeParabolicQuotientEquiv
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u}) :
    (F.P L ⧸ pCore 2 (F.P L)) ≃* Equiv.Perm (Fin 3) := by
  let := h.chosen.elementary
  let f := F.binaryPermutationAction (by decide) L h.chosen.normalizes
  have hf : Function.Surjective f :=
    F.binaryPermutationAction_surjective (by decide) L h.chosen.normalizes (h.full_LT_action structural)
  have hk : f.ker = pCore 2 (F.P L) :=
    (F.binaryPermutationAction_ker (by decide) L h.chosen.normalizes).trans
      (F.binaryPlaneAction_ker_eq_twoCore (by decide) L h.chosen.normalizes
        (h.full_LT_action structural) (h.centralizer_LT structural))
  exact (QuotientGroup.quotientMulEquivOfEq hk.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective f hf)

/-- Fixing the point as well as the remaining flag cuts gives exactly T. -/
theorem plane_parabolic_inf_point
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u}) :
    F.P L ⊓ F.H = (T : Subgroup G) := by
  let := h.chosen.elementary
  let A := F.P L ⊓ F.H
  let j := inclusion (show A ≤ L ⊔ (T : Subgroup G) from inf_le_left.trans inf_le_left)
  let f := (F.binarySeedAction L h.chosen.normalizes).comp j
  have hp : IsPGroup 2 (F.binaryFullFlag.comap f) :=
    (F.binaryFullFlag_isPGroup.comap_of_ker_isPGroup
      (F.binarySeedAction L h.chosen.normalizes)
      (F.binarySeedAction_ker_isPGroup L h.chosen.normalizes (h.centralizer_LT structural))).comap_of_injective
        j (inclusion_injective _)
  have he : F.binaryFullFlag.comap f = ⊤ := by
    apply top_unique
    intro x _ i v
    have hxi : (x : G) ∈ F.Gi i := by
      by_cases hi : i < 3
      · by_cases hi0 : i = 0
        · subst i
          have hz : F.Vi 0 = ⊥ := card_eq_one.mp (by simpa using F.card 0 (by decide))
          change (x : G) ∈ normalizer (F.Vi 0 : Set G)
          rw [hz,normalizer_eq_top]
          trivial
        · by_cases hi1 : i = 1
          · subst i
            exact x.property.2
          · have hi2 : i = 2 := by omega
            subst i
            exact (F.P_le_G₂ (by decide) L h.chosen.normalizes) x.property.1
      · have hv : F.Vi i = V := le_antisymm (F.le_seed i)
          (F.last.ge.trans (F.monotone (by omega)))
        change (x : G) ∈ normalizer (F.Vi i : Set G)
        rw [hv]
        exact F.P_le_seed_normalizer L h.chosen.normalizes x.property.1
    exact (mem_normalizer_iff.mp hxi (v : G)).symm
  have hA : IsPGroup 2 A := (he ▸ hp).of_equiv Subgroup.topEquiv
  exact T.is_maximal' hA (le_inf (F.binary_sylow_le_P L) (F.invariant 1))

/-- The second plane vertex and any S₃ overgroup inside G₁ form the
literal source Goldschmidt triple in their generated subgroup. -/
theorem cubic_goldschmidt_triple
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (Y : Subgroup G) (hYH : Y ≤ F.H)
    (he : Nonempty (((Y ⊔ (T : Subgroup G) : Subgroup G) ⧸
      pCore 2 (Y ⊔ (T : Subgroup G) : Subgroup G)) ≃* Equiv.Perm (Fin 3))) :
    let D := F.P L ⊔ (Y ⊔ (T : Subgroup G))
    ChapterF.IsGoldschmidtTriple ((F.P L).subgroupOf D)
      ((Y ⊔ (T : Subgroup G)).subgroupOf D) := by
  let D := F.P L ⊔ (Y ⊔ (T : Subgroup G))
  have hP : F.P L ≤ D := le_sup_left
  have hY : Y ⊔ (T : Subgroup G) ≤ D := le_sup_right
  have hinter : F.P L ⊓ (Y ⊔ (T : Subgroup G)) = (T : Subgroup G) :=
    le_antisymm ((inf_le_inf_left _ (sup_le hYH (F.invariant 1))).trans_eq
      (plane_parabolic_inf_point h structural))
      (le_inf (F.binary_sylow_le_P L) le_sup_right)
  let eP := subgroupOfEquivOfLe hP
  let eY := subgroupOfEquivOfLe hY
  refine ⟨?_,⟨(QuotientGroup.congr _ _ eP (pCore_map_iso 2 eP)).trans
    (planeParabolicQuotientEquiv h structural)⟩,
    ⟨(QuotientGroup.congr _ _ eY (pCore_map_iso 2 eY)).trans he.some⟩,
    T.subtype ((F.binary_sylow_le_P L).trans hP),?_⟩
  · rw [←subgroupOf_sup hP hY,subgroupOf_self]
  · exact congrArg (fun A : Subgroup G => A.subgroupOf D) hinter

/-- The original plane is generated by the L₂-conjugates of the original point. -/
theorem plane_eq_point_residual_span
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u}) :
    conjugateSpanBy (F.Vi 1) (F.Li L 2) = F.Vi 2 := by
  let C := conjugateSpanBy (F.Vi 1) (F.Li L 2)
  have hC : C ≤ F.Vi 2 := conjugateSpanBy_le (F.monotone (by decide : 1 ≤ 2))
    ((F.Li_le L 2).trans inf_le_right)
  have h2 : 2 ≤ Nat.card C := by
    have hc := card_le_of_le (le_conjugateSpanBy (F.Vi 1) (F.Li L 2))
    simpa only [F.card 1 (by decide),pow_one] using hc
  have h4 : Nat.card C ≤ 4 := by
    simpa only [F.card 2 (by decide), show (2 : ℕ) ^ 2 = 4 from rfl] using card_le_of_le hC
  have hd : Nat.card C ∣ 4 := by simpa only [F.card 2 (by decide), show (2 : ℕ) ^ 2 = 4 from rfl] using card_dvd_of_le hC
  have h3 : Nat.card C ≠ 3 := by intro he; norm_num [he] at hd
  have hc : Nat.card C = 2 ∨ Nat.card C = 4 := by omega
  rcases hc with hc | hc
  · have he : F.Vi 1 = C := eq_of_le_of_card_ge (le_conjugateSpanBy _ _) (by rw [hc,F.card 1 (by decide)]; rfl)
    have hLH : F.Li L 2 ≤ F.H := by
      change F.Li L 2 ≤ normalizer (F.Vi 1 : Set G)
      rw [he]
      exact le_normalizer_conjugateSpanBy _ _
    have hPH : F.P L ≤ F.H := by
      rw [plane_parabolic_eq_join h structural]
      exact sup_le hLH (F.invariant 1)
    have hPT : F.P L = (T : Subgroup G) := by
      rw [←plane_parabolic_inf_point h structural,inf_eq_left.mpr hPH]
    have hi := SymmetricThreeTwoCore.sylow_index_three
      (planeParabolicQuotientEquiv h structural) (T.subtype (F.binary_sylow_le_P L))
    change (T : Subgroup G).relIndex (F.P L) = 3 at hi
    rw [hPT,relIndex_self] at hi
    omega
  · exact eq_of_le_of_card_ge hC (by change Nat.card (F.Vi 2) ≤ Nat.card C; rw [hc,F.card 2 (by decide)]; rfl)

/-- Preserving the original point residual and plane preserves their natural seed. -/
theorem point_plane_normalizer_le
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (A : Subgroup G) (hn : A ≤ normalizer (F.Li L 1 : Set G))
    (hc : A ≤ normalizer (F.Vi 2 : Set G)) :
    A ≤ normalizer (L : Set G) := by
  let := h.chosen.elementary
  let := F.localKernel_tilde_seed_elementary
  have uniqueness : Uniqueness127 KnownSimple.IsKnownSimple.{u} := by
    intro D _ _ hD S N hN
    exact Chapter1.Section02.nonsolvable_uniqueness_knownSimple hD S hN
  apply le_trans _ (h.seed_normalizer_le structural uniqueness)
  rw [←F.seed_eq_plane_span L (by decide) h.chosen.normalizes
    (F.invariant_subgroup_of_ambient_natural h.naturalMarking (by decide))]
  exact normalizes_conjugateSpanBy _ _ A hc hn


/-- In the normal-point branch an escaping actor cannot normalize L₂ even
modulo the centralizer of the point span in the newly generated group. -/
theorem cubic_plane_normalizer_obstruction_of_normalizes_point
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (Y : Subgroup G) (hYH : Y ≤ F.H)
    (hYL : Y ≤ normalizer (F.Li L 1 : Set G)) (hout : ¬ Y ≤ normalizer (L : Set G)) :
    let D := F.P L ⊔ (Y ⊔ (T : Subgroup G))
    let W := conjugateSpanBy (F.Vi 1) D
    ¬ Y ≤ normalizer ((F.Li L 2 ⊔ (D ⊓ centralizer (W : Set G)) : Subgroup G) : Set G) := by
  let D := F.P L ⊔ (Y ⊔ (T : Subgroup G))
  let W := conjugateSpanBy (F.Vi 1) D
  let C := D ⊓ centralizer (W : Set G)
  have hXD : F.Li L 2 ≤ D := by
    change F.Li L 2 ≤ F.P L ⊔ (Y ⊔ (T : Subgroup G))
    rw [plane_parabolic_eq_join h structural]
    exact le_sup_left.trans le_sup_left
  have hplane : F.Vi 2 ≤ W := by
    rw [←plane_eq_point_residual_span h structural]
    exact conjugateSpanBy_mono le_rfl hXD
  have hCplane : C ≤ normalizer (F.Vi 2 : Set G) :=
    (inf_le_right.trans (centralizer_le hplane)).trans (Subgroup.centralizer_le_normalizer _)
  have hspan : conjugateSpanBy (F.Vi 1) (F.Li L 2 ⊔ C) = F.Vi 2 := by
    apply le_antisymm
    · exact conjugateSpanBy_le (F.monotone (by decide : 1 ≤ 2))
        (sup_le ((F.Li_le L 2).trans inf_le_right) hCplane)
    · rw [←plane_eq_point_residual_span h structural]
      exact conjugateSpanBy_mono le_rfl le_sup_left
  change ¬ Y ≤ normalizer ((F.Li L 2 ⊔ C : Subgroup G) : Set G)
  intro hnorm
  apply hout
  apply point_plane_normalizer_le h structural Y hYL
  rw [←hspan]
  exact normalizes_conjugateSpanBy _ _ Y hYH hnorm

/-- The original full point-normality interface. -/
theorem cubic_plane_normalizer_obstruction
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (hn : ((F.Li L 1).subgroupOf F.H).Normal)
    (Y : Subgroup G) (hYH : Y ≤ F.H) (hout : ¬ Y ≤ normalizer (L : Set G)) :
    let D := F.P L ⊔ (Y ⊔ (T : Subgroup G))
    let W := conjugateSpanBy (F.Vi 1) D
    ¬ Y ≤ normalizer ((F.Li L 2 ⊔ (D ⊓ centralizer (W : Set G)) : Subgroup G) : Set G) := by
  apply cubic_plane_normalizer_obstruction_of_normalizes_point h structural Y hYH _ hout
  exact hYH.trans ((normal_subgroupOf_iff_le_normalizer
    ((F.Li_le L 1).trans inf_le_right)).mp hn)

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction
