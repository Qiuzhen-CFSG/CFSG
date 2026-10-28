module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.LinearShadow.ParameterComponent.Recognition.Seed
public import CFSG.Quasithin.ChapterE.Section02.Structure.OriginalPaired
public import CFSG.Quasithin.ChapterE.Section02.Structure.ComponentModels.Paired

/-!
# The original paired component modulo its two-core

For the constructed component, nonnormality forces the source maximal core,
the solvable radical of H, and O₂(H) to coincide. Its normalizer has index
two in H. Distinct conjugates of a C-component intersect in the radical;
thus any odd subgroup meets the two conjugate component factors disjointly.
The quotient equivalence retains the ambient inclusion K ≤ H and the
literal quotient map, for the model sieve and Hall construction.

These conclusions use the original counterexample and preceding n ≤ s.
They do not assume a Lie-type identification or ambient normality of K.
Source: Aschbacher--Smith, E.2.2 and 11.3.5, printed pp.215--216,771--772.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ParameterComponent
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    {D : Chapter12.Section02.ChosenModule T L V} {S : D.NonbinaryNaturalInput}
    {U₁ : Submodule (ZMod 2) D.chosenCentralQuotient} {H K : Subgroup G}

omit [Finite G] in
theorem ComponentSeed.intrinsic_supplement (s : ComponentSeed T H K)
    (hTH : (T : Subgroup G) ≤ H) :
    K.subgroupOf H ⊔ (T.subtype hTH : Subgroup H) = ⊤ := by
  apply map_injective H.subtype_injective
  rw [Subgroup.map_sup, map_subgroupOf_eq_of_le s.component.1,
    Sylow.coe_subtype, map_subgroupOf_eq_of_le hTH, s.supplement,
    ← MonoidHom.range_eq_map, range_subtype]

omit [Finite G] in
private theorem intrinsic_quasisimple (s : ComponentSeed T H K) :
    IsQuasisimple (K.subgroupOf H ⧸ pCore 2 (K.subgroupOf H)) := by
  let := s.quasisimple
  let e := (subgroupOfEquivOfLe s.component.1).symm
  exact IsQuasisimple.of_mulEquiv (QuotientGroup.congr _ _ e (pCore_map_iso 2 e))

theorem ComponentSeed.paired_radical_eq_twoCore (s : ComponentSeed T H K)
    (h : Hypothesis1131At D S U₁ H) (p : Preceding1133 D S U₁ H)
    (hc : ¬ Proposition1132At D S U₁ H)
    (hs : (S.field.degree : ℕ∞) ≤ @ChapterE.globalS G _ V D.elementary)
    (hn : ¬ (K.subgroupOf H).Normal) : solvableRadical H = pCore 2 H := by
  let P := T.subtype h.outside.1.1.2
  have hP := outside_minimalParabolic h (weakClosure_not_le_core_of_counterexample h p hc)
  have hsolv := counterexample_not_solvable h p hc hs
  have hcore := ChapterE.Structure.PairedCore.source
    (fun X _ _ => ChapterA.Section02.theoremA_knownSimple (G := X))
    (outside_sqtk h) P hP hsolv s.component.2 (intrinsic_quasisimple s)
    (ComponentSeed.intrinsic_supplement s h.outside.1.1.2) hn
  exact (ChapterB.minimalParabolic_nonsolvable_core_eq_radical P hP hsolv).symm.trans hcore

theorem ComponentSeed.paired_normalizer_index (s : ComponentSeed T H K)
    (h : Hypothesis1131At D S U₁ H) (p : Preceding1133 D S U₁ H)
    (hc : ¬ Proposition1132At D S U₁ H)
    (hs : (S.field.degree : ℕ∞) ≤ @ChapterE.globalS G _ V D.elementary)
    (hn : ¬ (K.subgroupOf H).Normal) :
    (normalizer (K.subgroupOf H : Set H)).index = 2 := by
  exact (ChapterE.Structure.source_original_component_normal_or_index_two
    ChapterA.Section02.theoremA_knownSimple (outside_sqtk h) (T.subtype h.outside.1.1.2)
    (outside_minimalParabolic h (weakClosure_not_le_core_of_counterexample h p hc))
    (counterexample_not_solvable h p hc hs) (K.subgroupOf H) s.component.2
    (ComponentSeed.intrinsic_supplement s h.outside.1.1.2)).resolve_left hn

private theorem inf_le_radical {X : Type*} [Group X] [Finite X] {B C : Subgroup X}
    (hB : B.IsCComponent) (hC : C.IsCComponent) (hne : B ≠ C) :
    B ⊓ C ≤ solvableRadical X := by
  let q := QuotientGroup.mk' (solvableRadical X)
  have hr := solvableRadical_quotient_solvableRadical (G := X)
  have hb := hB.map_quotient (solvableRadical X)
  have hc := hC.map_quotient (solvableRadical X)
  have hcomm := hb.commutator_eq_bot_of_ne_of_solvableRadical_eq_bot hr hc
    (fun he => hne (hB.eq_of_map_quotient_eq hC _ he))
  have hd := hb.disjoint_of_commutator_eq_bot_of_solvableRadical_eq_bot hr hcomm
  intro x hx
  exact (QuotientGroup.eq_one_iff x).mp (disjoint_def.mp hd
    (mem_map_of_mem q hx.1) (mem_map_of_mem q hx.2))

theorem ComponentSeed.paired_intersection_le_twoCore (s : ComponentSeed T H K)
    (h : Hypothesis1131At D S U₁ H) (p : Preceding1133 D S U₁ H)
    (hc : ¬ Proposition1132At D S U₁ H)
    (hs : (S.field.degree : ℕ∞) ≤ @ChapterE.globalS G _ V D.elementary)
    (t : G) (htH : t ∈ H) (htK : t ∉ normalizer (K : Set G)) :
    K ⊓ K.map (MulAut.conj t).toMonoidHom ≤ H.pCoreIn 2 := by
  let J := K.subgroupOf H
  let u : H := ⟨t,htH⟩
  have hmap : (J.map (MulAut.conj u).toMonoidHom).map H.subtype =
      K.map (MulAut.conj t).toMonoidHom := by
    rw [map_map]
    change J.map ((MulAut.conj t).toMonoidHom.comp H.subtype) = _
    rw [← map_map, map_subgroupOf_eq_of_le s.component.1]
  have hne : J ≠ J.map (MulAut.conj u).toMonoidHom := by
    intro he
    apply htK
    apply mem_normalizer_iff_map_conj_eq.mpr
    have hh := congrArg (map H.subtype) he
    rw [map_subgroupOf_eq_of_le s.component.1, hmap] at hh
    exact hh.symm
  have hn : ¬ J.Normal := by
    intro hn
    let := hn
    exact hne (mem_normalizer_iff_map_conj_eq.mp (show u ∈ normalizer (J : Set H) by
      rw [normalizer_eq_top]; trivial)).symm
  have hle := inf_le_radical s.component.2 (s.component.2.map_equiv (MulAut.conj u)) hne
  rw [s.paired_radical_eq_twoCore h p hc hs hn] at hle
  have hh := map_mono (f := H.subtype) hle
  rw [Subgroup.map_inf _ _ _ H.subtype_injective,
    map_subgroupOf_eq_of_le s.component.1, hmap] at hh
  exact hh

theorem ComponentSeed.paired_odd_factors_disjoint (s : ComponentSeed T H K)
    (h : Hypothesis1131At D S U₁ H) (p : Preceding1133 D S U₁ H)
    (hc : ¬ Proposition1132At D S U₁ H)
    (hs : (S.field.degree : ℕ∞) ≤ @ChapterE.globalS G _ V D.elementary)
    (A : Subgroup G) (hodd : Odd (Nat.card A))
    (t : G) (htH : t ∈ H) (htK : t ∉ normalizer (K : Set G)) :
    Disjoint (A ⊓ K) ((A ⊓ K).map (MulAut.conj t).toMonoidHom) := by
  have hdis : Disjoint A (H.pCoreIn 2) := by
    obtain ⟨n,hn⟩ := (isPGroup_pCoreIn 2 H).exists_card_eq
    apply disjoint_of_coprime_natCard
    rw [hn]
    exact (Nat.coprime_two_right.mpr hodd).pow_right n
  apply disjoint_def.mpr
  intro x hx hy
  exact disjoint_def.mp hdis hx.1 (s.paired_intersection_le_twoCore h p hc hs t htH htK
    ⟨hx.2, map_mono (f := (MulAut.conj t).toMonoidHom) inf_le_right hy⟩)

omit [Finite G] in
def ComponentSeed.intrinsicQuotientEquiv (s : ComponentSeed T H K) :
    (K ⧸ pCore 2 K) ≃* (K.subgroupOf H ⧸ pCore 2 (K.subgroupOf H)) :=
  let e := (subgroupOfEquivOfLe s.component.1).symm
  QuotientGroup.congr _ _ e (pCore_map_iso 2 e)

def ComponentSeed.quotientImageEquivOfCore (s : ComponentSeed T H K)
    (R : Subgroup H) [R.Normal] (hR : R = pCore 2 H) :
    (K ⧸ pCore 2 K) ≃* (K.subgroupOf H).map (QuotientGroup.mk' R) := by
  subst R
  exact (ComponentSeed.intrinsicQuotientEquiv s).trans (cComponentTwoCoreQuotientEquiv s.component.2)

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ParameterComponent
