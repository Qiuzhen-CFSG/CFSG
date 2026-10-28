module
public import CFSG.Quasithin.Chapter15.Section02.SourcePlaneUniqueness.CharacteristicTwo.SmallActionsSource.MarkedAssembly
public import CFSG.Quasithin.Chapter15.Section02.SourcePlaneUniqueness.CharacteristicTwo.SmallActionsSource.MarkedResiduals
public import CFSG.Quasithin.Chapter15.Section02.SourcePlaneUniqueness.CharacteristicTwo.SmallActionsSource.ResidualExclusion

/-!
# Source small-action assembly with the distinguished factors

The marked centralizers on the original noncentral chief module yield a
ResidualPair whose factors are literally their embedded two-residuals.
The pair discharges all relative-normality, cubic-quotient, generation and
conjugacy premises of the arbitrary-seed15.2.22 exclusion. Thus its second
factor is the original K₂ from Notation15.2.9. A separate constructor chooses
an existing noncentral chief factor and produces the complete15.2.21(1)
output, with MI = Mc ∩ I, without a supplied split or quotient marking.

Only the genuine preceding source inputs remain explicit; their final
discharge belongs to the plane-uniqueness assembly. The component and
terminal consumers already proved in NaturalPair use the same corrected
small-action family and retain no local small-action premise.

Source: Aschbacher--Smith, Notation15.2.9 and15.2.21--22,
printed pp.1110,1114--1115; refs/quasithin.pdf.
-/

@[expose] public section
open Subgroup Representation Representation.BinaryOffender NoncentralChiefRefinement Stellmacher Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section02.SmallActionsSource
open Section01 Section03 Section03.InitialSource ChapterA.Section05To06 ChapterD ChapterD.UniqueFactor
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc V H ZS I E : Subgroup G}
variable {hsource : ChosenSmallSource T M Mc V}
variable (d : PlaneUniquenessPreceding hsource H ZS)
include d

/-- The literal residuals of the two chief-plane centralizers form the pair. -/
noncomputable def chief_residual_pair {W : Type*} [AddCommGroup W]
    [Module (ZMod 2) W] {ρ : Representation (ZMod 2) H W}
    (c : ChiefWreathCoordinates ρ) (hk : c.actor.ker = pCore 2 H)
    (hI : PlaneEscapes Mc ZS I)
    (hjoin : (TerminalLinear.KS H T ZS).subgroupOf H = c.factor 1 ⊔ c.factor ChiefWreath.flip)
    (t : G) (ht : t ∈ (T : Subgroup G)) (htS : t ∉ smallActionS T ZS) :
    ResidualPair (T : Subgroup G) (smallActionS T ZS) (smallActionK H) t := by
  let A := fun i => (c.residualFactor i).map H.subtype
  have hKS : TerminalLinear.KS H T ZS = (ChiefWreath.base.comap c.actor).map H.subtype := by
    rw [←c.factor_sup_eq_base,←hjoin,map_subgroupOf_eq_of_le]
    exact sup_le (map_subtype_le _) (inf_le_left.trans d.geometry.outside.1.1.2)
  have hR : pResidual 2 H ≤ ChiefWreath.base.comap c.actor := by
    rw [←c.factor_sup_eq_base,←hjoin]
    intro x hx
    exact (show smallActionK H ≤ TerminalLinear.KS H T ZS from le_sup_left)
      (mem_map_of_mem H.subtype hx)
  have hn (i) : TerminalLinear.KS H T ZS ≤ normalizer (A i : Set G) := by
    rw [hKS]
    exact (map_mono (c.residualFactor_normalizes i)).trans
      ((c.residualFactor i).le_normalizer_map H.subtype)
  have hmem (i) : A i ∈ normalCubicResiduals (smallActionK H) := by
    have hm := c.residualFactor_mem (hk ▸ (pCore_isPGroup (p := 2) (G := H))) hR i
    have he := (c.residualFactor i).equivMapOfInjective H.subtype H.subtype_injective
    refine ⟨map_mono hm.1,normal_subgroupOf_of_le_normalizer
      ((show smallActionK H ≤ TerminalLinear.KS H T ZS from le_sup_left).trans (hn i)),
      hm.2.2.1.of_surjective he.toMonoidHom he.surjective,?_⟩
    exact (Nat.card_congr (QuotientGroup.congr _ _ he (pCore_map_iso 2 he)).toEquiv).symm.trans hm.2.2.2
  have ha (i) : A i = smallActionK ((c.factor i).map H.subtype) :=
    map_embedded_pResidual 2 (c.factor i) H.subtype
  refine ⟨smallActionK ((c.factor 1).map H.subtype),
    smallActionK ((c.factor ChiefWreath.flip).map H.subtype),ht,htS,
    (ha 1) ▸ hmem 1,(ha ChiefWreath.flip) ▸ hmem ChiefWreath.flip,?_,?_,?_⟩
  · rw [←ha 1,←ha ChiefWreath.flip,←Subgroup.map_sup,c.residualFactors_span hR]
  · have hh := chief_residual_map_conj c (⟨t,d.geometry.outside.1.1.2 ht⟩ : H) 1
    rw [outside_chief_permutation d c hI hjoin t ht htS,mul_one] at hh
    exact hh
  · rw [←ha 1]
    exact (show smallActionS T ZS ≤ TerminalLinear.KS H T ZS from le_sup_right).trans (hn 1)

/-- The actual marked centralizers, rather than arbitrary Sylow overgroups,
construct the original split interface. -/
noncomputable def chief_marked_split {W : Type*} [AddCommGroup W]
    [Module (ZMod 2) W] {ρ : Representation (ZMod 2) H W}
    (c : ChiefWreathCoordinates ρ) (hk : c.actor.ker = pCore 2 H)
    (hI : PlaneEscapes Mc ZS I)
    (hjoin : (TerminalLinear.KS H T ZS).subgroupOf H = c.factor 1 ⊔ c.factor ChiefWreath.flip)
    (t : G) (ht : t ∈ (T : Subgroup G)) (htS : t ∉ smallActionS T ZS) :
    SmallActionSplit (T : Subgroup G) (smallActionS T ZS) (smallActionK H) := by
  let p := chief_residual_pair d c hk hI hjoin t ht htS
  refine ⟨(c.factor 1).map H.subtype,(c.factor ChiefWreath.flip).map H.subtype,
    p.K₁,p.K₂,t,ht,htS,?_,p.span,p.first.1,p.second.1,p.conjugate,
    p.normalized,p.second_normalized inf_le_left (d.escape_index hI).2⟩
  have hh := congrArg (Subgroup.map H.subtype) hjoin
  rw [map_subgroupOf_eq_of_le (show TerminalLinear.KS H T ZS ≤ H from
    sup_le (map_subtype_le _) (inf_le_left.trans d.geometry.outside.1.1.2)),Subgroup.map_sup] at hh
  exact hh

/-- A noncentral chief factor exists, so the source conclusion is produced
without any factor, split, action-kernel or quotient premise. MI is Mc ∩ I. -/
theorem source_15_2_21_1_conclusion
    (horbit : smallActionKc H Mc = smallActionK H ∨
      ∃ L : Subgroup G, L ∈ Chapter1.L G T ∧
        smallActionKc H Mc = componentOrbit L (T : Subgroup G))
    (hI : PlaneEscapes Mc ZS I)
    (hnot : ¬ IsSmallActionIrreducible (smallActionS T ZS) (smallActionK H)) :
    Nonempty (SmallAction21OneConclusion (T : Subgroup G) (smallActionS T ZS)
      (smallActionK H) (smallActionKc H Mc) ZS (Mc ⊓ I)) := by
  let h := hsource.prepared
  let := h.elementary
  let U := (conjugateSpan H V).subgroupOf H
  let := (h.chief_data hsource.ambient T hsource.empty hsource.maximal hsource.centralizing H d.geometry.outside).1
  let : IsElementaryAbelian 2 U := IsElementaryAbelian.subgroupOf
    (show conjugateSpan H V ≤ H by
      rw [UniqueFactor.conjugateSpan_eq]
      exact conjugateSpanBy_le_self ((h.inside_core H d.geometry.outside).trans (twoCore_le H)))
  obtain ⟨s⟩ := SeriesOn.exists_series U
  have hcount := (h.chief_data hsource.ambient T hsource.empty hsource.maximal hsource.centralizing H d.geometry.outside).2 s
  obtain ⟨i,j,hij,hi,hj⟩ := s.one_lt_noncentralCount_iff.mp (by omega)
  obtain ⟨c⟩ := chief_wreath_coordinates d s i hi
  obtain ⟨t,ht,htS⟩ : ∃ t ∈ (T : Subgroup G), t ∉ smallActionS T ZS := by
    by_contra hn
    push Not at hn
    have hh : smallActionS T ZS = (T : Subgroup G) := le_antisymm inf_le_left hn
    have hidx : (smallActionS T ZS).relIndex (T : Subgroup G) = 2 := (d.escape_index hI).2
    rw [hh,relIndex_self] at hidx
    omega
  exact ⟨⟨chief_marked_split d c (c.kernel.trans (chief_action_kernel_eq_core d s i hi)) hI
    (chief_marked_join d hI hnot s i hi c) t ht htS,
    orbit_centralizes_of_reducible d horbit hI hnot,
    orbit_residual_MI_of_reducible d horbit hI hnot⟩⟩

/-- Source15.2.22 with its original marked second factor, and no pair premise. -/
theorem source_15_2_22_marked_from_preceding
    (hI : PlaneEscapes Mc ZS I) (hfit : generalizedFitting I = pCore 2 I)
    (hnot : ¬ IsSmallActionIrreducible (smallActionS T ZS) (smallActionK H))
    (seed : Seed M I (smallActionS T ZS) E)
    (hC : IsSmallActionThreePrime (M ⊓ centralizer (V : Set G)))
    (eNI : PlaneUniquenessPreceding.OmegaAction.intersectionImage hsource I ≃* Equiv.Perm (Fin 3)) :
    let h := hsource.prepared
    let := h.elementary
    let U := (conjugateSpan H V).subgroupOf H
    let := (h.chief_data hsource.ambient T hsource.empty hsource.maximal hsource.centralizing H d.geometry.outside).1
    let : IsElementaryAbelian 2 U := IsElementaryAbelian.subgroupOf
      (show conjugateSpan H V ≤ H by
        rw [UniqueFactor.conjugateSpan_eq]
        exact conjugateSpanBy_le_self ((h.inside_core H d.geometry.outside).trans (twoCore_le H)))
    SourceCases.Omega (imageRepresentation M V hsource.prepared.normalized) →
    ∀ (s : SeriesOn U) (i : Fin s.series.length), ¬ s.Central i →
    ∀ c : ChiefWreathCoordinates (s.factorRepresentation i),
      ¬ ⁅E,smallActionK ((c.factor ChiefWreath.flip).map H.subtype)⁆ ≤
        E ⊓ smallActionK ((c.factor ChiefWreath.flip).map H.subtype) := by
  let h := hsource.prepared
  let := h.elementary
  let U := (conjugateSpan H V).subgroupOf H
  let := (h.chief_data hsource.ambient T hsource.empty hsource.maximal hsource.centralizing H d.geometry.outside).1
  let : IsElementaryAbelian 2 U := IsElementaryAbelian.subgroupOf
    (show conjugateSpan H V ≤ H by
      rw [UniqueFactor.conjugateSpan_eq]
      exact conjugateSpanBy_le_self ((h.inside_core H d.geometry.outside).trans (twoCore_le H)))
  dsimp only
  intro ho s i hi c
  obtain ⟨t,ht,htS⟩ : ∃ t ∈ (T : Subgroup G), t ∉ smallActionS T ZS := by
    by_contra hn
    push Not at hn
    have hh : smallActionS T ZS = (T : Subgroup G) := le_antisymm inf_le_left hn
    have hidx : (smallActionS T ZS).relIndex (T : Subgroup G) = 2 := (d.escape_index hI).2
    rw [hh,relIndex_self] at hidx
    omega
  let p := chief_residual_pair d c
    (c.kernel.trans (chief_action_kernel_eq_core d s i hi)) hI
    (chief_marked_join d hI hnot s i hi c) t ht htS
  exact source_15_2_22_from_preceding d hI hfit seed hC eNI p ho

end CFSG.Quasithin.Chapter15.Section02.SmallActionsSource
