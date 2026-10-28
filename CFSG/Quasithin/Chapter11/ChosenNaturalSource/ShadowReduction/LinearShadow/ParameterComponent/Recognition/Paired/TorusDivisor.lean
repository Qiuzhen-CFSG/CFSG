module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.LinearShadow.ParameterComponent.Recognition.Paired.PrimeExclusion
public import Theory.SpecificGroups.SL2.EvenBorelResidual
public import Theory.GroupTheory.QuotientIntersection

/-!
# The split-torus divisor in the original component overlap

The HStar maximality identifies H ∩ N_G(L) with the unique Sylow maximal
subgroup of H. In the paired case the maximal core is O₂(H). The image of
the component in this quotient is simple, and its maximal intersection
is the normalizer of its prescribed Sylow subgroup.

An actual PSL₂(2^k) marking identifies this normalizer with the binary
Borel, of order 2^k(2^k - 1). Divisibility lifts through the quotient and
both original inclusions, yielding 2^k - 1 in the order of
H ∩ N_G(L) ∩ K. The model-indexed variant retains any positive exponent;
the original interface specializes it to k = generationParameter H.

Source: Aschbacher--Smith, E.2.2 and 11.3.5(2), printed pp.215--216,
771--772. TorusApplication consumes this result to construct the actual
prime Hall factor. PSL₂ recognition at the actual generation minimum
remains with the parameter-component owner.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ParameterComponent

private theorem linear_normalizer_card {X : Type*} [Group X] [Finite X]
    (P : Sylow 2 X) (f : ℕ) (hm : ClassicalGroup.IsPSL X 2 (2 ^ f)) :
    Nat.card (normalizer (P : Set X)) = 2 ^ f * (2 ^ f - 1) := by
  obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
  let : Fintype F := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow (p := 2) (f := f)
    (by simpa only [Nat.card_eq_fintype_card] using hF)
  let Q := P.mapSurjective (f := e.toMonoidHom) e.surjective
  have he : (normalizer (P : Set X)).map e.toMonoidHom = normalizer (Q : Set PSL(2,F)) := by
    change (normalizer ((P : Subgroup X) : Set X)).map e.toMonoidHom = _
    rw [map_normalizer_eq_of_bijective (P : Subgroup X) e.bijective]
    rfl
  let d := (e.subgroupMap (normalizer (P : Set X))).trans (MulEquiv.subgroupCongr he)
  rw [Nat.card_congr d.toEquiv,
    Nat.card_congr (Matrix.ProjectiveSpecialLinearGroup.EvenBorelResidual.sylowNormalizerEquiv F Q).toEquiv,
    Matrix.ProjectiveSpecialLinearGroup.EvenBorelResidual.card_borel, hF]

private theorem paired_borel_divisor {X : Type*} [Group X] [Finite X]
    (hX : IsStronglyQuasithin X) (P : Sylow 2 X)
    (hP : ChapterB.IsMinimalParabolicOver P ⊤)
    (J : Subgroup X) (hJ : IsComponent X J) [IsSimpleGroup J]
    (hgen : J ⊔ (P : Subgroup X) = ⊤)
    (hm : ChapterF.Source.IsRankOneModel J) (d : ℕ)
    (hd : ∀ Q : Sylow 2 J, d ∣ Nat.card (normalizer (Q : Set J))) :
    d ∣ Nat.card (ChapterB.minimalParabolicMax P hP ⊓ J : Subgroup X) := by
  have heven : 2 ∣ Nat.card J := by
    by_contra hn
    have ho : Odd (Nat.card J) := Nat.not_even_iff_odd.mp (by
      simpa only [even_iff_two_dvd] using hn)
    let := hJ.2
    exact Group.IsPerfect.not_isSolvable J (odd_order_theorem J ho)
  have hb := ChapterE.Witnesses.PairedBender.component_borel_intersection P hP J hJ heven
    (ChapterE.Structure.generating_component_orbit_eq_residual hX P hJ hgen) hm
  obtain ⟨Q,hQ⟩ := P.exists_subgroupOf_eq_of_subnormal J hJ.1
  rw [←hQ] at hb
  let M := ChapterB.minimalParabolicMax P hP
  have he : Nat.card (M ⊓ J : Subgroup X) = Nat.card (M.subgroupOf J) := by
    rw [← subgroupOf_map_subtype M J, card_map_of_injective J.subtype_injective]
  rw [he,hb]
  exact hd Q

variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    {D : Chapter12.Section02.ChosenModule T L V} {S : D.NonbinaryNaturalInput}
    {U₁ : Submodule (ZMod 2) D.chosenCentralQuotient} {H K : Subgroup G}

private theorem overlap_eq_maximal (h : Hypothesis1131At D S U₁ H)
    (hP : ChapterB.IsMinimalParabolicOver (T.subtype h.outside.1.1.2) ⊤) :
    (normalizer (L : Set G)).subgroupOf H =
      ChapterB.minimalParabolicMax (T.subtype h.outside.1.1.2) hP := by
  let B := H ⊓ normalizer (L : Set G)
  have hi := Chapter3.HStar.unique_maximal T D.sylow_normalizes_component h.outside
  have hBne : B.subgroupOf H ≠ ⊤ := by
    intro he
    have hm := congrArg (map H.subtype) he
    rw [map_subgroupOf_eq_of_le inf_le_left, ← MonoidHom.range_eq_map,range_subtype] at hm
    exact hi.2.1.lt.ne hm
  have hcoat : IsCoatom (B.subgroupOf H) := by
    refine ⟨hBne,?_⟩
    intro Y hY
    have hy : B < Y.map H.subtype := by
      rw [←map_subgroupOf_eq_of_le (show B ≤ H from inf_le_left)]
      exact (map_lt_map_iff_of_injective H.subtype_injective).mpr hY
    have he := (hi.2.1.eq_or_eq hy.le (map_subtype_le Y)).resolve_left hy.ne'
    apply map_injective H.subtype_injective
    rw [he,←MonoidHom.range_eq_map,range_subtype]
  have hle : B.subgroupOf H ≤ ChapterB.minimalParabolicMax (T.subtype h.outside.1.1.2) hP := by
    apply hP.1.le_maximal
      ⟨(ChapterB.minimalParabolicMax_spec _ hP).2,
        (ChapterB.minimalParabolicMax_spec _ hP).1.covBy_top⟩
    · intro x hx
      exact ⟨x.property,D.sylow_normalizes_component hx⟩
    · exact hcoat.lt_top
  have he := (hcoat.le_iff.mp hle).resolve_left (ChapterB.minimalParabolicMax_spec _ hP).1.ne_top
  simpa only [B,inf_subgroupOf_left] using he.symm

/-- The actual component overlap contains the full split-torus divisor.
Pass through H/O₂(H), identify its component intersection with the rank-one
Borel, and lift divisibility through the original quotient and inclusions. -/
theorem ComponentSeed.paired_rankOne_overlap_divisor (s : ComponentSeed T H K)
    (h : Hypothesis1131At D S U₁ H) (pr : Preceding1133 D S U₁ H)
    (hc : ¬ Proposition1132At D S U₁ H)
    (hs : (S.field.degree : ℕ∞) ≤ @ChapterE.globalS G _ V D.elementary)
    (hn : ¬ (K.subgroupOf H).Normal)
    (hm : (∃ f : ℕ, 0 < f ∧ ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 2 (2 ^ f)) ∨
      ∃ m : ℕ, Nonempty ((K ⧸ pCore 2 K) ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m))
    (d : ℕ) (hd : ∀ Q : Sylow 2 (K ⧸ pCore 2 K),
      d ∣ Nat.card (normalizer (Q : Set (K ⧸ pCore 2 K)))) :
    d ∣
      Nat.card ((H ⊓ normalizer (L : Set G)) ⊓ K : Subgroup G) := by
  let P := T.subtype h.outside.1.1.2
  let J := K.subgroupOf H
  have hP := outside_minimalParabolic h (weakClosure_not_le_core_of_counterexample h pr hc)
  have hsolv := counterexample_not_solvable h pr hc hs
  have hgen := ComponentSeed.intrinsic_supplement s h.outside.1.1.2
  let R := ChapterB.minimalParabolicCore P hP
  let q := QuotientGroup.mk' R
  have hq := QuotientGroup.mk'_surjective R
  have hcore : R = pCore 2 H :=
    (ChapterB.minimalParabolic_nonsolvable_core_eq_radical P hP hsolv).trans
      (s.paired_radical_eq_twoCore h pr hc hs hn)
  let e := ComponentSeed.quotientImageEquivOfCore s R hcore
  have hi := ChapterE.Structure.source_component_simple_image P hP hsolv J s.component.2 hgen
  let : IsSimpleGroup (J.map q) := hi.1
  let M := (normalizer (L : Set G)).subgroupOf H
  have hM := overlap_eq_maximal h hP
  have hMstar : M.map q = ChapterB.minimalParabolicMax (P.mapSurjective hq)
      (ChapterE.Structure.source_star_minimal_core_free P hP).1 := by
    rw [show M = ChapterB.minimalParabolicMax P hP from hM]
    exact ChapterB.minimalParabolicMax_map_core P hP q hq (by rw [QuotientGroup.ker_mk'])
  have hkM : q.ker ≤ M := by
    rw [QuotientGroup.ker_mk',hcore]
    exact (pCore_isPGroup.le_sylow_of_normal P).trans
      (fun x hx => D.sylow_normalizes_component hx)
  have hmj : (M ⊓ J).map q = M.map q ⊓ J.map q := by
    rw [inf_comm M J,map_inf_of_ker_le q J M hkM,inf_comm]
  have himage : ChapterF.Source.IsRankOneModel (J.map q) := by
    rcases hm with ⟨f,hf,hm⟩ | ⟨m,⟨em⟩⟩
    · exact .linear f hf (hm.of_mulEquiv e.symm)
    · exact .suzuki m ⟨e.symm.trans em⟩
  have hdiv : ∀ Q : Sylow 2 (J.map q), d ∣ Nat.card (normalizer (Q : Set (J.map q))) := by
    intro Q
    let Q' := Q.mapSurjective (f := e.symm.toMonoidHom) e.symm.surjective
    have he : (normalizer (Q : Set (J.map q))).map e.symm.toMonoidHom =
        normalizer (Q' : Set (K ⧸ pCore 2 K)) := by
      change (normalizer ((Q : Subgroup (J.map q)) : Set (J.map q))).map _ = _
      rw [map_normalizer_eq_of_bijective _ e.symm.bijective]
      rfl
    have hh := hd Q'
    rw [←he,card_map_of_injective e.symm.injective] at hh
    exact hh
  have hd := paired_borel_divisor
    (ChapterE.Structure.source_star_sqtk ChapterA.Section02.theoremA_knownSimple
      (outside_sqtk h) P hP hsolv).stronglyQuasithin
    (P.mapSurjective hq) (ChapterE.Structure.source_star_minimal_core_free P hP).1
    (J.map q) hi.2.1 hi.2.2.2 himage d hdiv
  rw [←hMstar,←hmj] at hd
  have hd' := hd.trans ((M ⊓ J).card_map_dvd q)
  have he : (M ⊓ J).map H.subtype = (H ⊓ normalizer (L : Set G)) ⊓ K := by
    rw [Subgroup.map_inf _ _ _ H.subtype_injective,
      show J.map H.subtype = K from map_subgroupOf_eq_of_le s.component.1]
    congr 1
    exact (subgroupOf_map_subtype (normalizer (L : Set G)) H).trans (inf_comm _ _)
  rw [←he,card_map_of_injective H.subtype_injective]
  exact hd'

/-- The split-torus divisor for the literal PSL₂ model, at its independent exponent. -/
theorem ComponentSeed.paired_linear_overlap_torus_dvd_of_model (s : ComponentSeed T H K)
    (h : Hypothesis1131At D S U₁ H) (pr : Preceding1133 D S U₁ H)
    (hc : ¬ Proposition1132At D S U₁ H)
    (hs : (S.field.degree : ℕ∞) ≤ @ChapterE.globalS G _ V D.elementary)
    (hn : ¬ (K.subgroupOf H).Normal)
    {f : ℕ} (hf : 0 < f)
    (hm : ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 2 (2 ^ f)) :
    2 ^ f - 1 ∣
      Nat.card ((H ⊓ normalizer (L : Set G)) ⊓ K : Subgroup G) := by
  apply s.paired_rankOne_overlap_divisor h pr hc hs hn (.inl ⟨f,hf,hm⟩) (2^f-1)
  intro Q
  rw [linear_normalizer_card Q f hm]
  exact dvd_mul_left _ _

/-- Specialization to the original generation minimum. -/
theorem ComponentSeed.paired_linear_overlap_torus_dvd (s : ComponentSeed T H K)
    (h : Hypothesis1131At D S U₁ H) (pr : Preceding1133 D S U₁ H)
    (hc : ¬ Proposition1132At D S U₁ H)
    (hs : (S.field.degree : ℕ∞) ≤ @ChapterE.globalS G _ V D.elementary)
    (hn : ¬ (K.subgroupOf H).Normal)
    (hm : ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 2 (2 ^ ChapterE.generationParameter H)) :
    2 ^ ChapterE.generationParameter H - 1 ∣
      Nat.card ((H ⊓ normalizer (L : Set G)) ⊓ K : Subgroup G) := by
  have hf : 0 < ChapterE.generationParameter H := by
    have := degree_le_parameter h pr hc hs
    have := S.nonbinary
    omega
  exact s.paired_linear_overlap_torus_dvd_of_model h pr hc hs hn hf hm

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ParameterComponent
