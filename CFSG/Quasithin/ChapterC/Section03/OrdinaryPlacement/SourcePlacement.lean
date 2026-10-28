module
public import CFSG.Quasithin.ChapterC.Section03.OrdinaryPlacement.SourceNormality
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.SourceOrbits
public import Theory.GroupTheory.CentralProductRadicalAction
public import Theory.GroupTheory.CComponent.FixedOrbitClosure
public import Theory.GroupTheory.PRadical.NormalComponentImages

/-!
# Literal ordinary-component placement in C.2.8

After excluding the four nonnormal component models, the original radical
preserves the ordinary factor. Its action therefore transfers to the perfect
coordinate projection. The two-core of that projection lies in R, so the
projection normalizes R and belongs to M. Perfect projection then places it
inside the original span. Invariance under M and C-component orbit minimality
identify it with that entire span.

The resulting placement retains the original L, R and V. The Sylow-orbit
identity uses the actual inclusion of a Sylow subgroup of M. No normalization
of L by M is assumed. These are C.3.2–4, printed pp.149–150; the later local
classification proving quasisimplicity of the span quotient is separate.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterC.HypothesisC28
variable {G : Type*} [Group G] [Finite G]
variable {H M L R V : Subgroup G}

private theorem perfect_normal_subgroup_span_eq
    (hL : (L.subgroupOf M).IsCComponent) (hLM : L ≤ M)
    (P : Subgroup G) [Group.IsPerfect P] (hne : P ≠ ⊥)
    (hP : P ≤ conjugateSpanBy L M)
    (hn : M ≤ normalizer (P : Set G)) : P = conjugateSpanBy L M := by
  have hPM := hP.trans (conjugateSpanBy_le_self hLM)
  let D := P.subgroupOf M
  let : Group.IsPerfect D := Group.IsPerfect.ofSurjective
    (f := (subgroupOfEquivOfLe hPM).symm.toMonoidHom)
    (subgroupOfEquivOfLe hPM).symm.surjective
  have hDne : D ≠ ⊥ := by
    intro he
    have hh := congrArg (map M.subtype) he
    exact hne (by simpa only [D,map_subgroupOf_eq_of_le hPM,Subgroup.map_bot] using hh)
  have he : componentOrbit (L.subgroupOf M) (⊤ : Subgroup M) =
      (conjugateSpanBy L M).subgroupOf M := by
    apply map_injective M.subtype_injective
    change (⨆ t : (⊤ : Subgroup M),
      (L.subgroupOf M).map (MulAut.conj (t : M)).toMonoidHom).map M.subtype = _
    rw [←conjugateSpanBy_eq_iSup_conj,map_conjugateSpanBy,
      map_subgroupOf_eq_of_le hLM,←MonoidHom.range_eq_map,range_subtype,
      map_subgroupOf_eq_of_le (conjugateSpanBy_le_self hLM)]
  have htop : (⊤ : Subgroup M) ≤ normalizer (D : Set M) := by
    intro m _ p
    exact hn m.property (p : G)
  have hDE := hL.orbit_eq_of_normalized_perfect hDne
    (he ▸ subgroupOf_mono M hP) htop (le_top.trans htop)
  have hh := congrArg (map M.subtype) (hDE.trans he)
  simpa only [D,map_subgroupOf_eq_of_le hPM,
    map_subgroupOf_eq_of_le (conjugateSpanBy_le_self hLM)] using hh

/-- The projection calculation on a normal ordinary factor, with the actual radical. -/
theorem ordinary_span_le_of_normal
    (h : HypothesisC28 KnownSimple.IsKnownSimple H M L R V)
    (K : Subgroup H) (hK : IsComponent H K) [K.Normal] :
    (conjugateSpanBy L M).subgroupOf H ≤ K := by
  let A := (conjugateSpanBy L M).subgroupOf H
  let B := M.subgroupOf H
  let C := centralizer (K : Set H)
  let U := R.subgroupOf H
  have hAH := (conjugateSpanBy_le_self h.component_le).trans h.local_le
  have hRH := h.radical_le.trans h.local_le
  obtain ⟨P,Q,hPK,hQC,hP,hQ,hAP,hPA,hnc,hcore,hBP⟩ := h.ordinary_span_projection K hK
  let := hP
  have hBP' : B ≤ normalizer (P : Set H) := by
    simpa only [normalizer_eq_top,inf_top_eq] using hBP
  have hBA : B ≤ normalizer (A : Set H) := by
    intro b hb a
    exact le_normalizer_conjugateSpanBy L M hb (a : G)
  have hUR : U ≤ B := subgroupOf_mono H h.radical_le
  have hAU : A ≤ normalizer (U : Set H) := by
    intro a ha r
    exact h.span_normalizes_radical ha (r : G)
  have hcomm : ⁅P,U⁆ ≤ P.pCoreIn 2 :=
    perfect_projection_radical_commutator A P C U
      (hPK.trans (le_centralizer_iff.mp le_rfl))
      (hAP.trans (sup_le le_sup_left (hQC.trans le_sup_right)))
      (hPA.trans (sup_le le_sup_left (hQC.trans le_sup_right)))
      (hUR.trans hBA) hAU (hUR.trans hBP')
      (le_normalizer_of_normal.trans (normalizer_le_normalizer_centralizer K))
      h.radical_isTwoGroup.comap_subtype
  have hPU : P ≤ normalizer (U : Set H) :=
    le_normalizer_iff_commutator_le_right.mpr (hcomm.trans hcore)
  have hNU : normalizer (U : Set H) ≤ B := by
    rw [←subgroupOf_normalizer_eq hRH]
    intro x hx
    exact h.normalizer_le ⟨x.property,hx⟩
  have hPB : P ≤ B := hPU.trans hNU
  have hPeA : P ≤ A := perfect_projection_le_of_normalizes P Q A
    (hPK.trans (le_centralizer_iff.mp hQC)) hAP hPA (hPB.trans hBA)
  have hne : P ≠ ⊥ := by
    intro he
    exact hnc (by rw [he,commutator_bot_right])
  let D := P.map H.subtype
  have hD : D ≤ conjugateSpanBy L M := by
    simpa only [A,map_subgroupOf_eq_of_le hAH] using map_mono (f := H.subtype) hPeA
  have hDn : M ≤ normalizer (D : Set G) := by
    intro m hm
    exact P.le_normalizer_map H.subtype
      (mem_map_of_mem H.subtype (hBP' (show (⟨m,h.local_le hm⟩:H) ∈ B from hm)))
  let : Group.IsPerfect D := Group.IsPerfect.map H.subtype
  have hDne : D ≠ ⊥ := fun he => hne
    ((map_eq_bot_iff_of_injective P H.subtype_injective).mp he)
  have he := perfect_normal_subgroup_span_eq h.component h.component_le D hDne hD hDn
  have hEq : P = A := by
    apply map_injective H.subtype_injective
    rw [map_subgroupOf_eq_of_le hAH]
    exact he
  exact hEq.symm.le.trans hPK

/-- The whole original span lies in the same original ordinary component. -/
theorem ordinary_span_le
    (h : HypothesisC28 KnownSimple.IsKnownSimple H M L R V)
    (K : Subgroup H) (hK : IsComponent H K) :
    (conjugateSpanBy L M).subgroupOf H ≤ K := by
  let := h.ordinary_component_normal K hK
  exact h.ordinary_span_le_of_normal K hK

/-- C.3.2, on the original L and its literal inclusion in H. -/
theorem ordinary_component_contains_original
    (h : HypothesisC28 KnownSimple.IsKnownSimple H M L R V)
    (K : Subgroup H) (hK : IsComponent H K) : L.subgroupOf H ≤ K :=
  (subgroupOf_mono H (le_conjugateSpanBy L M)).trans (h.ordinary_span_le K hK)

/-- C.3.4 retains the actual moved module in R intersect K. -/
theorem ordinary_module_placement
    (h : HypothesisC28 KnownSimple.IsKnownSimple H M L R V)
    (K : Subgroup H) (hK : IsComponent H K) :
    V.subgroupOf H ≤ R.subgroupOf H ⊓ K ∧
      ¬ V.subgroupOf H ≤ centralizer (K : Set H) := by
  refine ⟨le_inf ?_ ?_,h.ordinary_module_not_centralizes K hK⟩
  · exact subgroupOf_mono H (h.module_le_center_radical.trans (map_subtype_le _))
  · exact (subgroupOf_mono H h.module_le).trans (h.ordinary_span_le K hK)

/-- Every Sylow two-subgroup of the original M generates the full component orbit. -/
theorem span_eq_sylow_span
    (h : HypothesisC28 KnownSimple.IsKnownSimple H M L R V) (T : Sylow 2 M) :
    conjugateSpanBy L M = conjugateSpanBy L ((T : Subgroup M).map M.subtype) := by
  have hM : IsSQTK KnownSimple.IsKnownSimple M := (IsSQTK.equiv (subgroupOfEquivOfLe h.local_le)).mp
    (h.sqtk.subgroup (M.subgroupOf H))
  have hQ : IsSQTK KnownSimple.IsKnownSimple (M ⧸ pCore 2 M) := by
    refine ⟨?_,hM.isKGroup.quotient _⟩
    intro p hp ho
    let : Fact p.Prime := ⟨hp⟩
    exact (primeRank_quotient_le_of_isTwoGroup p ho _ pCore_isPGroup).trans
      (hM.stronglyQuasithin p hp ho)
  let D := conjugateSpanBy (L.subgroupOf M) (T : Subgroup M)
  let : D.Normal := conjugateSpanBy_sylow_normal _ T
    (Chapter1.Section02.proposition_1_2_1_three_orbit_source hQ h.component)
  have he : conjugateSpanBy (L.subgroupOf M) (⊤ : Subgroup M) = D :=
    le_antisymm (conjugateSpanBy_le (le_conjugateSpanBy _ _)
      le_normalizer_of_normal)
      (conjugateSpanBy_le (le_conjugateSpanBy _ _)
        (le_top.trans (le_normalizer_conjugateSpanBy _ _)))
  have hh := congrArg (map M.subtype) he
  simpa only [D,map_conjugateSpanBy,map_subgroupOf_eq_of_le h.component_le,
    ←MonoidHom.range_eq_map,range_subtype] using hh

/-- The source Sylow choice can contain the original radical, retaining its map to G. -/
theorem exists_source_sylow_span
    (h : HypothesisC28 KnownSimple.IsKnownSimple H M L R V) :
    ∃ T : Sylow 2 M, R ≤ (T : Subgroup M).map M.subtype ∧
      conjugateSpanBy L M = conjugateSpanBy L ((T : Subgroup M).map M.subtype) := by
  obtain ⟨T,hRT⟩ := (h.radical_isTwoGroup.comap_subtype (K := M)).exists_le_sylow
  refine ⟨T,?_,h.span_eq_sylow_span T⟩
  intro r hr
  exact mem_map_of_mem M.subtype
    (hRT (show (⟨r,h.radical_le hr⟩ : M) ∈ R.subgroupOf M from hr))

/-- The actual intersection with the normal component is radical in that component. -/
theorem ordinary_radical_intersection_isRadical
    (h : HypothesisC28 KnownSimple.IsKnownSimple H M L R V)
    (K : Subgroup H) (hK : IsComponent H K) :
    IsPRadical 2 ((R.subgroupOf H).subgroupOf K) := by
  let := h.ordinary_component_normal K hK
  refine ⟨?_,normal_intersection_relative_core K (R.subgroupOf H) h.isRadical⟩
  intro he
  have hz : R.subgroupOf H ⊓ K = ⊥ := by
    have hh := congrArg (map K.subtype) he
    simpa only [subgroupOf_map_subtype,Subgroup.map_bot] using hh
  exact h.ordinary_radical_intersection_not_centralizes K hK (by rw [hz]; exact bot_le)

/-- The source span lies in the literal component normalizer of R intersect K. -/
theorem ordinary_span_le_radical_intersection_normalizer
    (h : HypothesisC28 KnownSimple.IsKnownSimple H M L R V)
    (K : Subgroup H) (hK : IsComponent H K) :
    (conjugateSpanBy L M).subgroupOf H ≤
      K ⊓ normalizer ((R.subgroupOf H ⊓ K : Subgroup H) : Set H) := by
  let := h.ordinary_component_normal K hK
  refine le_inf (h.ordinary_span_le K hK) ?_
  apply (le_inf ?_ le_normalizer_of_normal).trans inf_normalizer_le_normalizer_inf
  intro a ha r
  exact h.span_normalizes_radical ha (r : G)

end CFSG.Quasithin.ChapterC.HypothesisC28
