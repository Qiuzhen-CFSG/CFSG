module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.LinearShadow.ParameterComponent.Recognition.Models.StarSource
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.LinearShadow.ParameterComponent.Recognition.Source
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Generation.Automizer.Source
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Generation.Doubling.Source
public import CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels.Source.ClassicalCartan
public import CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels.Source.ComponentBorels
public import CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels.Source.ExchangedClauses

/-!
# Recognition of the model field from the original Hall action

The complete Hall--Cartan witness is constructed at the literal binary-model
exponent f, independently of k = generationParameter H. Faithfulness of its
original Hall actor bounds f by the automizer parameter. If the actor preserves
V, this gives f ≤ n; if it moves V, the actual doubled natural module gives
f ≤ 2n and its weak-closure geometry gives k = 2n. Together with k ≤ f and
n ≤ k, these bounds prove k = f in every surviving binary source row.

The normal catalogue keeps its literal star image. The paired catalogue keeps
K/O₂(K), its prescribed Sylow and the same exchange data. The odd Suzuki
exponent excludes the doubled alternative in that paired row. The final
catalogue constructs the original component and faithful maximal overcomponent
with all model exponents equal to the actual generation parameter.

For PSL₂ this also completes the original residual-component conclusion,
including V ≤ O₂(H): the existing paired Cartan exclusion and doubled-module
contradiction give f = k = n and K = O²(H), with its own quotient, relative
C-component property, Sylow supplement and escape from N_G(L).

The preceding OddKernelNormalizer input retains its producer
qt-d-1222-natural-odd-kernel-normalizer. Preceding1133, the global-s value and
the 11.0.4 residual/cubic clauses retain their local-geometry producers and
final discharge by qt-d-1222-shadow-linear-geometry. The Suzuki, unitary and
rank-two model/FF exclusions still belong to the parameter-component owner;
this module does not assert unconditional 11.3.5--6.

Source: Aschbacher--Smith, 11.2.1 and 11.3.4--6, printed pp.767,771--773;
the marked structural alternatives of E.2.2, pp.215--216. The proof uses the
actual source hypotheses, not an equality across an arbitrary solvable kernel.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory Representation
open CFSG.Quasithin.ChapterB.QuasisimpleSource
open CFSG.Quasithin.ChapterE CFSG.Quasithin.ChapterB
open CFSG.Quasithin.ChapterE.Section06.FixedPointBounds
open CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.ParabolicCartan
open CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ParameterComponent
open LocalGeometry
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V H K : Subgroup G}
    {D : Chapter12.Section02.ChosenModule T L V} {S : D.NonbinaryNaturalInput}
    {U₁ : Submodule (ZMod 2) D.chosenCentralQuotient}

/-- The faithful original Cartan actor bounds its own marked field exponent
by the automizer parameter of any normalized subgroup containing V. -/
theorem model_field_le_automizer {H : Subgroup G} (hTH : (T : Subgroup G) ≤ H)
    (hP : IsMinimalParabolicOver (T.subtype hTH) ⊤) {f : ℕ}
    (d : IntrinsicHallCartanData (T.subtype hTH) hP f)
    (hfaith : d.witness.abelianGroup.map H.subtype ⊓ centralizer (V : Set G) = ⊥)
    (J U : Subgroup G) (hTJ : (T : Subgroup G) ≤ J)
    (hBJ : d.witness.abelianGroup.map H.subtype ≤ J)
    (hJU : J ≤ normalizer (U : Set G)) (hVU : V ≤ U) :
    f ≤ nPrime (inducedAutomizer U J) := by
  let K := J.subgroupOf H
  have hBK : d.witness.abelianGroup ≤ K := map_le_iff_le_comap.mp hBJ
  have hSK : (d.witness.sylow : Subgroup H) ≤ K := by
    rw [d.sylow_eq]
    exact comap_mono hTJ
  let wK := MarkedModels.restrictWitness d.witness K hBK hSK
  let emb : K →* J := (H.subtype.comp K.subtype).codRestrict J (fun x => x.property)
  have hi : Function.Injective emb := by
    intro x y he
    have he' : ((x : H) : G) = ((y : H) : G) :=
      congrArg (fun z : J => (z : G)) he
    exact Subtype.ext (Subtype.ext he')
  let R := T.subtype hTJ
  have hR : (wK.sylow : Subgroup K).map emb = R := by
    apply map_injective J.subtype_injective
    rw [map_map]
    change (((d.witness.sylow : Subgroup H).subgroupOf K).map
      (H.subtype.comp K.subtype)) = ((T : Subgroup G).subgroupOf J).map J.subtype
    rw [← map_map, map_subgroupOf_eq_of_le hSK, d.sylow_eq]
    change ((T : Subgroup G).subgroupOf H).map H.subtype =
      ((T : Subgroup G).subgroupOf J).map J.subtype
    rw [map_subgroupOf_eq_of_le hTH, map_subgroupOf_eq_of_le hTJ]
  let w := MarkedModels.embedWitness wK emb hi R hR
  have hw : w.cyclicGroup.map J.subtype = d.witness.cyclicGroup.map H.subtype := by
    change ((d.witness.cyclicGroup.subgroupOf K).map emb).map J.subtype = _
    rw [map_map]
    change (d.witness.cyclicGroup.subgroupOf K).map (H.subtype.comp K.subtype) = _
    rw [← map_map, map_subgroupOf_eq_of_le (d.witness.cyclic_le.trans hBK)]
  apply faithful_cartan_bound hJU w
  rw [hw]
  apply le_bot_iff.mp
  exact (inf_le_inf (map_mono d.witness.cyclic_le) (centralizer_le hVU)).trans hfaith.le

private theorem central_corank (c : LocalGeometry.Coordinates D S.field) :
    ChapterE.subgroupCorank V (V ⊓ centralizer (L : Set G)) =
      S.field.degree * Module.finrank S.field.Carrier c.Space := by
  rw [←c.preimage_bot,WeakClosure.Parameters.NaturalDimensions.pullback_corank D S c]
  rw [(Submodule.quotEquivOfEqBot (⊥ : Submodule S.field.Carrier c.Space) rfl).finrank_eq]

private theorem doubled_parameter_eq_twice
    (h : Hypothesis1131At D S U₁ H) (pr : Preceding1133 D S U₁ H)
    (hc : ¬ Proposition1132At D S U₁ H)
    {c : LocalGeometry.Coordinates D S.field} (F : InvariantFlag c)
    (hpoint : c.binarySubspace (F.space 0) = U₁)
    (d : WeakClosure.Generation.DoubledNatural D S)
    (hu : generationParameter H ≤ 2*S.field.degree) :
    generationParameter H = 2*S.field.degree := by
  obtain ⟨m,hm⟩ := d
  cases c with
  | sl3 a => exact Doubled.source_parameter_eq_twice h pr hc ⟨m,hm⟩ a F hpoint hu
  | sp4 a =>
    have hd := central_corank (LocalGeometry.Coordinates.sl3 m)
    have hd' := central_corank (LocalGeometry.Coordinates.sp4 a)
    rw [WeakClosure.Parameters.NaturalDimensions.field_dimension] at hd hd'
    change subgroupCorank V (V ⊓ centralizer (L : Set G)) = S.field.degree*3 at hd
    change subgroupCorank V (V ⊓ centralizer (L : Set G)) = S.field.degree*4 at hd'
    have := S.field.degree_pos
    omega
  | g2 a =>
    have hd := central_corank (LocalGeometry.Coordinates.sl3 m)
    have hd' := central_corank (LocalGeometry.Coordinates.g2 a)
    rw [WeakClosure.Parameters.NaturalDimensions.field_dimension] at hd hd'
    change subgroupCorank V (V ⊓ centralizer (L : Set G)) = S.field.degree*3 at hd
    change subgroupCorank V (V ⊓ centralizer (L : Set G)) = S.field.degree*6 at hd'
    have := S.field.degree_pos
    omega

/-- Faithfulness bounds the model exponent itself. If its Hall actor moves V,
the doubled weak closure gives the reverse bound at the actual minimum. -/
theorem parameter_eq_field_of_source_hall
    (h : Hypothesis1131At D S U₁ H) (pr : Preceding1133 D S U₁ H)
    (hc : ¬ Proposition1132At D S U₁ H)
    (hs : (S.field.degree : ℕ∞) ≤ @ChapterE.globalS G _ V D.elementary)
    (hcontrol : WeakClosure.Generation.OddKernelNormalizer (T := T) (L := L) (V := V))
    {c : LocalGeometry.Coordinates D S.field} (F : InvariantFlag c)
    (hpoint : c.binarySubspace (F.space 0) = U₁)
    (hP : IsMinimalParabolicOver (T.subtype h.outside.1.1.2) ⊤) {f : ℕ}
    (d : IntrinsicHallCartanData (T.subtype h.outside.1.1.2) hP f)
    (hm : minimalParabolicMax (T.subtype h.outside.1.1.2) hP =
      (normalizer (L : Set G)).subgroupOf H)
    (hf : generationParameter H ≤ f) :
    generationParameter H = f ∧
      (f = S.field.degree ∨ (f = 2*S.field.degree ∧ WeakClosure.Generation.DoubledNatural D S)) := by
  have hl := degree_le_parameter h pr hc hs
  have hlarge : 1 < generationParameter H := S.nonbinary.trans_le hl
  have hfaith := WeakClosure.Generation.hall_faithful D S hcontrol h.outside hlarge hP d hm
  let B := d.witness.abelianGroup.map H.subtype
  have hBH : B ≤ H := map_subtype_le _
  have hBM : B ≤ normalizer (L : Set G) :=
    map_le_iff_le_comap.mpr (d.hall_le.trans hm.le)
  by_cases hn : B ≤ normalizer (V : Set G)
  · have hu : f ≤ S.field.degree :=
      (model_field_le_automizer h.outside.1.1.2 hP d hfaith
        (normalizer (L : Set G) ⊓ normalizer (V : Set G)) V
        (le_inf D.sylow_normalizes_component S.sylow_normalizes)
        (le_inf hBM hn) inf_le_right le_rfl).trans
        (WeakClosure.Generation.Automizer.seed_nPrime_le D S)
    exact ⟨by omega,.inl (by omega)⟩
  · have hrows : WeakClosure.Generation.OtherRowsNormalize D S := by
      intro J hJ hrow
      exact (Preliminary.intersection_normalizes D S hrow J hJ).trans inf_le_right
    obtain ⟨m⟩ := WeakClosure.Generation.linear_of_moving D S hrows h.outside hBH hBM hn
    have hfixedB := WeakClosure.Generation.fixed_eq_bot_of_moving D S m hBM hn
    have hfixed : V ⊓ centralizer (H : Set G) = ⊥ :=
      le_bot_iff.mp ((inf_le_inf_left V (centralizer_le hBH)).trans hfixedB.le)
    have hJ := WeakClosure.Generation.thompson_of_fixed_eq_bot D S h.outside hfixed
    have hproper : V ≠ Source.conjugateSpan (normalizer (L : Set G)) V := by
      intro he
      apply hn
      apply hBM.trans
      rw [he]
      exact le_normalizer_componentOrbit V _
    have hd := WeakClosure.Generation.Doubling.doublingStep D S ⟨m⟩ hJ hproper
    have hu : f ≤ 2*S.field.degree :=
      (model_field_le_automizer h.outside.1.1.2 hP d hfaith
        (normalizer (L : Set G)) (Source.conjugateSpan (normalizer (L : Set G)) V)
        D.sylow_normalizes_component hBM
        (le_normalizer_componentOrbit V _) (le_componentOrbit V _)).trans
        (WeakClosure.Generation.Automizer.doubled_nPrime_le D S hd)
    have he := doubled_parameter_eq_twice h pr hc F hpoint hd (hf.trans hu)
    exact ⟨by omega,.inr ⟨by omega,hd⟩⟩

private theorem sourceKernel_eq_core {X : Type*} [Group X] [Finite X]
    (P : Sylow 2 X) (hP : ChapterB.IsMinimalParabolicOver P ⊤)
    (hs : ¬ Group.IsSolvable X) :
    sourceKernel (ChapterB.minimalParabolicMax P hP) =
      ChapterB.minimalParabolicCore P hP := by
  let M := ChapterB.minimalParabolicMax P hP
  have hM := ChapterB.minimalParabolicMax_spec P hP
  refine le_antisymm ?_ ?_
  · rcases ChapterB.minimalParabolic_normal_subgroup_dichotomy P hP M.normalCore with h | h
    · exact h
    · exact (hM.1.ne_top (top_unique (h ▸ sup_le hM.2 M.normalCore_le))).elim
  · rw [ChapterB.minimalParabolic_nonsolvable_core_eq_radical P hP hs]
    apply normal_le_normalCore.mpr
    let : Group.IsNilpotent (P : Subgroup X) := P.isPGroup'.isNilpotent
    rcases eq_top_or_exists_le_coatom (solvableRadical X ⊔ (P : Subgroup X)) with h | ⟨N,hN,hle⟩
    · exact (hs (Group.isSolvable_of_normal_sup_eq_top _ _ h)).elim
    · have he := ChapterB.minimalParabolicMax_unique P hP hN (le_sup_right.trans hle)
      exact (le_sup_left.trans hle).trans_eq he

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

/-- The complete Hall witness is built at the given literal PSL₂ exponent,
with the prescribed Sylow and maximal overlap unchanged in either normality branch. -/
theorem ComponentSeed.linear_source_hall
    (s : ComponentSeed T H K)
    (h : Hypothesis1131At D S U₁ H) (pr : Preceding1133 D S U₁ H)
    (hc : ¬ Proposition1132At D S U₁ H)
    (hs : (S.field.degree : ℕ∞) ≤ @ChapterE.globalS G _ V D.elementary)
    {f : ℕ} (hf : 2 ≤ f)
    (hm : ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 2 (2 ^ f)) :
    let P := T.subtype h.outside.1.1.2
    let hP := outside_minimalParabolic h (weakClosure_not_le_core_of_counterexample h pr hc)
    Nonempty (IntrinsicHallCartanData P hP f) := by
  let P := T.subtype h.outside.1.1.2
  let hP := outside_minimalParabolic h (weakClosure_not_le_core_of_counterexample h pr hc)
  let B := K.subgroupOf H
  let M := minimalParabolicMax P hP
  let R := sourceKernel M
  let := s.quasisimple
  let : IsQuasisimple (B ⧸ pCore 2 B) := IsQuasisimple.of_mulEquiv s.intrinsicQuotientEquiv
  have hns := counterexample_not_solvable h pr hc hs
  have hgen := s.intrinsic_supplement h.outside.1.1.2
  have hrad : solvableRadical H = pCore 2 H := by
    by_cases hn : B.Normal
    · let : IsSimpleGroup (K ⧸ pCore 2 K) := by
        obtain ⟨F,_,_,hF,⟨a⟩⟩ := hm
        let : IsSimpleGroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) F) :=
          Matrix.ProjectiveSpecialLinearGroup.rank_two_simple (by
            rw [hF]
            exact Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) hf)
        exact a.isSimpleGroup
      exact s.radical_eq_twoCore_of_normal_simple h.outside.1.1.2 hn
    · exact s.paired_radical_eq_twoCore h pr hc hs hn
  have hR : R = pCore 2 H := (sourceKernel_eq_core P hP hns).trans
    ((minimalParabolic_nonsolvable_core_eq_radical P hP hns).trans hrad)
  let e := s.quotientImageEquivOfCore R hR
  have hmodel : ClassicalGroup.IsPSL (sourceImage M B) 2 (2 ^ f) := hm.of_mulEquiv e.symm
  have hborel := source_component_linear_borel_model ChapterA.Section02.theoremA_knownSimple
    (outside_sqtk h) P hP hns B s.component.2 hgen hf hmodel
  by_cases hn : B.Normal
  · let := hn
    exact bender_intrinsic_at P hP (by omega) s.component.2
      (source_single_clauses P hP hns B s.component.2 inferInstance hgen) (.inl hborel)
  · exact exchanged_intrinsic_at P hP (by omega) s.component.2 inferInstance
      (source_exchanged_clauses (fun X _ _ => ChapterA.Section02.theoremA_knownSimple (G := X))
        (outside_sqtk h) P hP hns s.component.2 inferInstance hgen hn) hborel

/-- The actual PSL₂ model exponent equals n(H), including V≤O₂(H) and paired
components. The only added source input is the preceding odd-kernel normalizer theorem. -/
theorem ComponentSeed.linear_field_eq_parameter_of_odd_kernel
    (s : ComponentSeed T H K)
    (h : Hypothesis1131At D S U₁ H) (pr : Preceding1133 D S U₁ H)
    (hc : ¬ Proposition1132At D S U₁ H)
    (hs : (S.field.degree : ℕ∞) ≤ @ChapterE.globalS G _ V D.elementary)
    (hcontrol : WeakClosure.Generation.OddKernelNormalizer (T := T) (L := L) (V := V))
    {c : LocalGeometry.Coordinates D S.field} (F : InvariantFlag c)
    (hpoint : c.binarySubspace (F.space 0) = U₁)
    {f : ℕ} (hf : 2 ≤ f)
    (hm : ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 2 (2 ^ f)) :
    generationParameter H = f ∧
      (f = S.field.degree ∨ (f = 2*S.field.degree ∧ WeakClosure.Generation.DoubledNatural D S)) := by
  let P := T.subtype h.outside.1.1.2
  let hP := outside_minimalParabolic h (weakClosure_not_le_core_of_counterexample h pr hc)
  obtain ⟨d⟩ := s.linear_source_hall h pr hc hs hf hm
  exact parameter_eq_field_of_source_hall h pr hc hs hcontrol F hpoint hP d
    (overlap_eq_maximal h hP).symm (s.linear_parameter_le h pr hc hs hf hm)

/-- Close the normal PSL₂ source row, including its original-core branch.
The output retains the actual residual and its own quotient at the source degree. -/
theorem ComponentSeed.conclusion_of_normal_linear_odd_kernel
    (s : ComponentSeed T H K)
    (h : Hypothesis1131At D S U₁ H) (pr : Preceding1133 D S U₁ H)
    (hc : ¬ Proposition1132At D S U₁ H)
    (hs : (S.field.degree : ℕ∞) ≤ @ChapterE.globalS G _ V D.elementary)
    (hcontrol : WeakClosure.Generation.OddKernelNormalizer (T := T) (L := L) (V := V))
    {c : LocalGeometry.Coordinates D S.field} (F : InvariantFlag c)
    (hpoint : c.binarySubspace (F.space 0) = U₁)
    (hn : (K.subgroupOf H).Normal) {f : ℕ} (hf : 2 ≤ f)
    (hm : ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 2 (2 ^ f)) :
    f = S.field.degree ∧ K = residual H ∧ Conclusion S H := by
  have he := (s.linear_field_eq_parameter_of_odd_kernel h pr hc hs hcontrol F hpoint hf hm).1
  have hr : RankOneReduction S H :=
    ⟨K,s.component,s.span,he.symm ▸ hm,fun _ => s.normal_iff_eq_residual.mp hn⟩
  have hgen := WeakClosure.Generation.Doubling.conclusion_of_automizer_bounds D S
    hcontrol (WeakClosure.Generation.Automizer.automizerBounds D S) h.outside
  have ho := Doubled.source_parameter_component h pr hc F hpoint hr hgen hs
  exact ⟨he.symm.trans ho.parameter,s.normal_iff_eq_residual.mp hn,ho⟩

/-- The literal PSL₂ source model now completes the parameter/component conclusion
in both normality branches. Its exponent is never assumed to equal n(H). -/
theorem ComponentSeed.conclusion_of_linear_odd_kernel
    (s : ComponentSeed T H K)
    (h : Hypothesis1131At D S U₁ H) (pr : Preceding1133 D S U₁ H)
    (hc : ¬ Proposition1132At D S U₁ H)
    {c : LocalGeometry.Coordinates D S.field} (F : InvariantFlag c)
    (hpoint : c.binarySubspace (F.space 0) = U₁)
    (hs : @ChapterE.globalS G _ V D.elementary = WeakClosure.Parameters.naturalParameter D S c)
    (hcontrol : WeakClosure.Generation.OddKernelNormalizer (T := T) (L := L) (V := V))
    {f : ℕ} (hf : 2 ≤ f)
    (hm : ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 2 (2 ^ f))
    (hres : ∀ r : ℕ, r.Prime →
      ((Source.IsSL (L ⧸ pCore 2 L) 3 (2 ^ S.field.degree) ∧
          r ∣ 2 ^ S.field.degree - 1 ∧ 3 < r) ∨
        (Source.IsSp (L ⧸ pCore 2 L) 2 (2 ^ S.field.degree) ∧
          r ∣ (2 ^ S.field.degree) ^ 2 - 1)) →
      primeToResidual r (normalizer (L : Set G)) =
        L.subgroupOf (normalizer (L : Set G)))
    (hcubic : Source.IsSL (L ⧸ pCore 2 L) 3 (2 ^ S.field.degree) →
      Even S.field.degree → ∀ x ∈ normalizer (L : Set G), orderOf x = 3 → x ∈ L) :
    f = S.field.degree ∧ K = residual H ∧ Conclusion S H := by
  have hgen := WeakClosure.Generation.Doubling.conclusion_of_automizer_bounds D S
    hcontrol (WeakClosure.Generation.Automizer.automizerBounds D S) h.outside
  obtain ⟨_,hsn,_⟩ := source_marking_and_parameter h pr hc c hs hgen
  have hs' : (S.field.degree : ℕ∞) ≤ @ChapterE.globalS G _ V D.elementary := hsn.symm.le
  have he := (s.linear_field_eq_parameter_of_odd_kernel h pr hc hs' hcontrol F hpoint hf hm).1
  have ho := s.conclusion_of_source_linear_model h pr hc F hpoint hs hgen
    (he.symm ▸ hm) hres hcubic
  exact ⟨he.symm.trans ho.2.parameter,ho⟩

/-- Every normal binary source row has its Hall witness at the marked field
exponent. The same source argument identifies that exponent with n(H). -/
theorem ComponentSeed.normal_binary_field_eq_parameter_of_odd_kernel
    (s : ComponentSeed T H K)
    (h : Hypothesis1131At D S U₁ H) (pr : Preceding1133 D S U₁ H)
    (hc : ¬ Proposition1132At D S U₁ H)
    (hs : (S.field.degree : ℕ∞) ≤ @ChapterE.globalS G _ V D.elementary)
    (hcontrol : WeakClosure.Generation.OddKernelNormalizer (T := T) (L := L) (V := V))
    {c : LocalGeometry.Coordinates D S.field} (F : InvariantFlag c)
    (hpoint : c.binarySubspace (F.space 0) = U₁)
    (hn : (K.subgroupOf H).Normal) {f : ℕ} (hf : 2 ≤ f)
    (hm : let P := T.subtype h.outside.1.1.2
      let hP := outside_minimalParabolic h (weakClosure_not_le_core_of_counterexample h pr hc)
      let I := sourceImage (minimalParabolicMax P hP) (K.subgroupOf H)
      ClassicalGroup.IsPSL I 2 (2 ^ f) ∨ ClassicalGroup.IsPSU I 3 (2 ^ f) ∨
        ClassicalGroup.IsPSL I 3 (2 ^ f) ∨ ClassicalGroup.IsPSp I 2 (2 ^ f) ∨
        ∃ m : ℕ, 1 ≤ m ∧ f = 2*m+1 ∧
          Nonempty (I ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m)) :
    generationParameter H = f ∧
      (f = S.field.degree ∨ (f = 2*S.field.degree ∧ WeakClosure.Generation.DoubledNatural D S)) := by
  let P := T.subtype h.outside.1.1.2
  let hP := outside_minimalParabolic h (weakClosure_not_le_core_of_counterexample h pr hc)
  let B := K.subgroupOf H
  let := hn
  let := s.quasisimple
  let : IsQuasisimple (B ⧸ pCore 2 B) := IsQuasisimple.of_mulEquiv s.intrinsicQuotientEquiv
  have hns := counterexample_not_solvable h pr hc hs
  have hgen := s.intrinsic_supplement h.outside.1.1.2
  have hlarge : 1 < generationParameter H := S.nonbinary.trans_le (degree_le_parameter h pr hc hs)
  have hdata : generationParameter H ≤ f ∧ Nonempty (IntrinsicHallCartanData P hP f) := by
    rcases hm with hm | hm | hm | hm | ⟨m,hm,he,heq⟩
    · exact (normal_classical_intrinsic ChapterA.Section02.theoremA_knownSimple
        (outside_sqtk h) P hP hns hlarge B s.component.2 inferInstance hgen (.inl ⟨hf,hm⟩)).2
    · exact (normal_classical_intrinsic ChapterA.Section02.theoremA_knownSimple
        (outside_sqtk h) P hP hns hlarge B s.component.2 inferInstance hgen (.inr (.inl ⟨hf,hm⟩))).2
    · exact (normal_classical_intrinsic ChapterA.Section02.theoremA_knownSimple
        (outside_sqtk h) P hP hns hlarge B s.component.2 inferInstance hgen
        (.inr (.inr ⟨by omega,hm⟩))).2
    · exact (normal_symplectic_intrinsic ChapterA.Section02.theoremA_knownSimple
        (outside_sqtk h) P hP hns B s.component.2 inferInstance hgen (by omega) hm).2
    · rw [he]
      exact (normal_suzuki_intrinsic P hP hns B s.component.2 inferInstance hgen (by omega) heq).2
  obtain ⟨hu,⟨d⟩⟩ := hdata
  exact parameter_eq_field_of_source_hall h pr hc hs hcontrol F hpoint hP d
    (overlap_eq_maximal h hP).symm hu

/-- The constructed normal catalogue is now indexed by the actual generation
parameter. Higher-rank models remain on the literal star image. -/
theorem ComponentSeed.normal_binary_models_at_parameter
    (s : ComponentSeed T H K)
    (h : Hypothesis1131At D S U₁ H) (pr : Preceding1133 D S U₁ H)
    (hc : ¬ Proposition1132At D S U₁ H)
    (hs : (S.field.degree : ℕ∞) ≤ @ChapterE.globalS G _ V D.elementary)
    (hcontrol : WeakClosure.Generation.OddKernelNormalizer (T := T) (L := L) (V := V))
    {c : LocalGeometry.Coordinates D S.field} (F : InvariantFlag c)
    (hpoint : c.binarySubspace (F.space 0) = U₁)
    (hn : (K.subgroupOf H).Normal) :
    let P := T.subtype h.outside.1.1.2
    let hP := outside_minimalParabolic h (weakClosure_not_le_core_of_counterexample h pr hc)
    let I := sourceImage (minimalParabolicMax P hP) (K.subgroupOf H)
    let k := generationParameter H
    (k = S.field.degree ∨ (k = 2*S.field.degree ∧ WeakClosure.Generation.DoubledNatural D S)) ∧
      (ClassicalGroup.IsPSL I 2 (2 ^ k) ∨ ClassicalGroup.IsPSU I 3 (2 ^ k) ∨
        ClassicalGroup.IsPSL I 3 (2 ^ k) ∨ ClassicalGroup.IsPSp I 2 (2 ^ k) ∨
        ∃ m : ℕ, 1 ≤ m ∧ k = 2*m+1 ∧
          Nonempty (I ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m)) := by
  obtain ⟨f,hf,_,hm⟩ := s.normal_binary_models h pr hc hs hn
  have he := s.normal_binary_field_eq_parameter_of_odd_kernel h pr hc hs hcontrol F hpoint hn hf hm
  exact ⟨he.1.symm ▸ he.2,he.1.symm ▸ hm⟩

/-- The paired catalogue also has the actual generation parameter as its model
exponent. A Suzuki row has odd degree, so it cannot take the doubled alternative. -/
theorem ComponentSeed.paired_binary_models_at_parameter
    (s : ComponentSeed T H K)
    (h : Hypothesis1131At D S U₁ H) (pr : Preceding1133 D S U₁ H)
    (hc : ¬ Proposition1132At D S U₁ H)
    (hs : (S.field.degree : ℕ∞) ≤ @ChapterE.globalS G _ V D.elementary)
    (hcontrol : WeakClosure.Generation.OddKernelNormalizer (T := T) (L := L) (V := V))
    {c : LocalGeometry.Coordinates D S.field} (F : InvariantFlag c)
    (hpoint : c.binarySubspace (F.space 0) = U₁)
    (hn : ¬ (K.subgroupOf H).Normal) :
    let k := generationParameter H
    (k = S.field.degree ∨ (k = 2*S.field.degree ∧ WeakClosure.Generation.DoubledNatural D S)) ∧
      (ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 2 (2 ^ k) ∨
        (k = S.field.degree ∧ ∃ m : ℕ, 1 ≤ m ∧ k = 2*m+1 ∧
          Nonempty ((K ⧸ pCore 2 K) ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m))) := by
  rcases s.paired_binary_models h pr hc hs hn with ⟨f,hf,_,hm⟩ | ⟨m,hm,hu,⟨eK⟩⟩
  · have he := s.linear_field_eq_parameter_of_odd_kernel h pr hc hs hcontrol F hpoint hf hm
    exact ⟨he.1.symm ▸ he.2,.inl (he.1.symm ▸ hm)⟩
  · let P := T.subtype h.outside.1.1.2
    let hP := outside_minimalParabolic h (weakClosure_not_le_core_of_counterexample h pr hc)
    let B := K.subgroupOf H
    let M := minimalParabolicMax P hP
    let R := sourceKernel M
    let := s.quasisimple
    let : IsQuasisimple (B ⧸ pCore 2 B) := IsQuasisimple.of_mulEquiv s.intrinsicQuotientEquiv
    have hns := counterexample_not_solvable h pr hc hs
    have hgen := s.intrinsic_supplement h.outside.1.1.2
    have hR : R = pCore 2 H := (sourceKernel_eq_core P hP hns).trans
      ((minimalParabolic_nonsolvable_core_eq_radical P hP hns).trans
        (s.paired_radical_eq_twoCore h pr hc hs hn))
    let e := s.quotientImageEquivOfCore R hR
    have hborel := source_component_suzuki_borel_model ChapterA.Section02.theoremA_knownSimple
      (outside_sqtk h) P hP hns B s.component.2 hgen hm ⟨e.symm.trans eK⟩
    obtain ⟨d⟩ := exchanged_intrinsic_at P hP (by omega) s.component.2 inferInstance
      (source_exchanged_clauses (fun X _ _ => ChapterA.Section02.theoremA_knownSimple (G := X))
        (outside_sqtk h) P hP hns s.component.2 inferInstance hgen hn) hborel
    have he := parameter_eq_field_of_source_hall h pr hc hs hcontrol F hpoint hP d
      (overlap_eq_maximal h hP).symm hu
    have he' : generationParameter H = S.field.degree := by
      rcases he.2 with hsmall | ⟨hlarge,_⟩ <;> omega
    exact ⟨.inl he',.inr ⟨he',m,hm,he.1,⟨eK⟩⟩⟩

/-- Apply field recognition to the original component and its actual faithful
maximal overcomponent. All surviving models are now indexed by n(H), while
higher-rank normal models still live on the literal star image. -/
theorem exists_componentSeed_with_models_at_parameter
    (h : Hypothesis1131At D S U₁ H) (pr : Preceding1133 D S U₁ H)
    (hc : ¬ Proposition1132At D S U₁ H)
    (hs : (S.field.degree : ℕ∞) ≤ @ChapterE.globalS G _ V D.elementary)
    (hcontrol : WeakClosure.Generation.OddKernelNormalizer (T := T) (L := L) (V := V))
    {c : LocalGeometry.Coordinates D S.field} (F : InvariantFlag c)
    (hpoint : c.binarySubspace (F.space 0) = U₁) :
    let P := T.subtype h.outside.1.1.2
    let hP := outside_minimalParabolic h (weakClosure_not_le_core_of_counterexample h pr hc)
    let k := generationParameter H
    ∃ K J : Subgroup G, ComponentSeed T H K ∧ K ≤ J ∧
      J ∈ Chapter1.LStar G (T : Subgroup G) ∧
      J ∈ MainForward.faithfulLocalComponents T ∧
      ¬ J ≤ normalizer (L : Set G) ∧ ⁅sourceZ T,J⁆ ≠ ⊥ ∧
      (k = S.field.degree ∨ (k = 2*S.field.degree ∧ WeakClosure.Generation.DoubledNatural D S)) ∧
      (((K.subgroupOf H).Normal ∧
        (let I := sourceImage (minimalParabolicMax P hP) (K.subgroupOf H)
         ClassicalGroup.IsPSL I 2 (2 ^ k) ∨ ClassicalGroup.IsPSU I 3 (2 ^ k) ∨
           ClassicalGroup.IsPSL I 3 (2 ^ k) ∨ ClassicalGroup.IsPSp I 2 (2 ^ k) ∨
           ∃ m : ℕ, 1 ≤ m ∧ k = 2*m+1 ∧
             Nonempty (I ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m))) ∨
       (¬ (K.subgroupOf H).Normal ∧
         (ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 2 (2 ^ k) ∨
           (k = S.field.degree ∧ ∃ m : ℕ, 1 ≤ m ∧ k = 2*m+1 ∧
             Nonempty ((K ⧸ pCore 2 K) ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m))))) := by
  obtain ⟨K,J,s,hKJ,hJ,hf,ho,hm⟩ := exists_componentSeed_with_faithful_maximal h pr hc hs
  refine ⟨K,J,s,hKJ,hJ,hf,ho,hm,?_⟩
  by_cases hn : (K.subgroupOf H).Normal
  · obtain ⟨he,hmodel⟩ := s.normal_binary_models_at_parameter h pr hc hs hcontrol F hpoint hn
    exact ⟨he,.inl ⟨hn,hmodel⟩⟩
  · obtain ⟨he,hmodel⟩ := s.paired_binary_models_at_parameter h pr hc hs hcontrol F hpoint hn
    exact ⟨he,.inr ⟨hn,hmodel⟩⟩

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ParameterComponent
