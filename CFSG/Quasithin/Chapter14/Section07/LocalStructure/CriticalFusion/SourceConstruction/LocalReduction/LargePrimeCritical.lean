module
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.LargePrimeDihedral
public import CFSG.Quasithin.Chapter14.Section06.SourceSuitableChoice.OddCriticalPair.Selection.RankOneReversal
public import Theory.Representation.BinaryOffender.NormalCubic
public import Theory.Representation.BinaryConjugationSection.FullMovement

/-!
# Reciprocal critical geometry in the original minimal five-core obstruction

Normality of the original point residual L₁ makes its literal image a cubic
subgroup. The seed commutator generates U_I, so that cubic fixes no nonzero
vector on U_I/V₁. The retained four-dimensional five-support makes the whole
section larger than a plane. The normal-cubic displacement argument therefore
excludes every rank-one displacement in I/O₂(I).

The full-denominator alternative in F.9 would give a returned conjugate span
whose commutator is a noncentral line. Each actor would then have displacement
at most one, contradicting the preceding exclusion. Thus the original F.9
selection constructs a strict quadratic endpoint with the literal denominator
comparison. Its conjugator leaves the original full point normalizer, since
that normalizer's span is abelian. Reversal retains its product in I and returns
all I-normalized labels by one conjugator.

The final theorem applies this to the same minimal I, quotient action, normal
two-perfect lift and canonical dihedral factors constructed earlier. It retains
the exact quotient kernel and all support data. The selected actor's factor
calculation, both ambient dihedral exclusions, and five-core vanishing remain.

Source: Aschbacher–Smith, 14.7.5–6, printed pp.1043–1045; F.9.13,16–17,
pp.322–324, refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction
open Chapter12.Section08 CriticalFusion.Source ChapterD
open Chapter15.Section03.AbelianAmalgam
open Chapter14.Section06.OddCriticalPair.Selection
open Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure.CriticalTransfer
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3}

private def local_binary_section {I U Z : Subgroup G} [IsElementaryAbelian 2 U]
    (a : LocalQuotientAction I U Z) :
    BinaryConjugationSection I U Z
      (a.representation.comp (QuotientGroup.mk' (pCore 2 I))) where
  section_le := a.le_local
  kernel_le := a.kernel_le
  normalized := a.normalizes
  coordinates := {
    toFun u := Multiplicative.ofAdd (Additive.ofMul (QuotientGroup.mk' (Z.subgroupOf U) u))
    map_one' := (QuotientGroup.mk' (Z.subgroupOf U)).map_one
    map_mul' := (QuotientGroup.mk' (Z.subgroupOf U)).map_mul }
  onto := QuotientGroup.mk'_surjective _
  kernel_eq := QuotientGroup.ker_mk' _
  equivariant i u := (a.conjugation i u).symm

/-- The normal point cubic fixes no vector on the actual local section. -/
theorem local_point_fixedSpace_eq_bot
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (I : Subgroup G) (hLI : F.Li L 1 ≤ I)
    (hn : ((F.Li L 1).subgroupOf I).Normal)
    [IsElementaryAbelian 2 (F.UH I)]
    (a : LocalQuotientAction I (F.UH I) (F.Vi 1)) :
    fixedSpace a.representation
      (((F.Li L 1).subgroupOf I).map (QuotientGroup.mk' (pCore 2 I))) = ⊥ := by
  let := h.chosen.elementary
  let P := ((F.Li L 1).subgroupOf I).map (QuotientGroup.mk' (pCore 2 I))
  have hP : Nat.card P = 3 := local_point_star_card_of_normal h structural I hLI hn
  have hm : ⁅F.UH I,F.Li L 1⁆ = F.UH I :=
    (conjugateSpanBy_eq_commutator_of_seed V I (F.Li L 1) (F.Li L 1)
      hLI ((normal_subgroupOf_iff_le_normalizer hLI).mp hn) le_rfl
      (seed_commutator h F)).symm
  have hgen : subspaceCommutator a.representation ⊤ P = ⊤ := by
    rw [←subspaceCommutator_comp_map]
    apply (local_binary_section a).subspaceCommutator_eq_top_of_movement _ hLI
    rw [commutator_comm,hm,sup_eq_left.mpr a.kernel_le]
  let : IsCyclic P := isCyclic_of_prime_card hP
  obtain ⟨z,hz⟩ := P.isCyclic_iff_exists_zpowers_eq_top.mp inferInstance
  have hfree := CyclicFixedRank.fixedFree_of_commutator_eq_top a.representation z
    (hz.symm ▸ hgen)
  apply bot_unique
  intro v hv
  have hzm : z ∈ P := by rw [←hz]; exact mem_zpowers z
  exact hfree v (hv ⟨z,hzm⟩)

/-- A normal point cubic excludes rank-one displacement throughout the
literal local quotient as soon as its section has dimension greater than two. -/
theorem local_normal_point_no_transvections
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (I : Subgroup G) (hLI : F.Li L 1 ≤ I)
    (hn : ((F.Li L 1).subgroupOf I).Normal)
    [IsElementaryAbelian 2 (F.UH I)]
    (a : LocalQuotientAction I (F.UH I) (F.Vi 1))
    (hdim : 2 < Module.finrank (ZMod 2) (Additive (F.UH I ⧸ (F.Vi 1).subgroupOf (F.UH I)))) :
    ∀ t : HStar I, fixedCodim a.representation (zpowers t) ≠ 1 := by
  let := hn
  let P := ((F.Li L 1).subgroupOf I).map (QuotientGroup.mk' (pCore 2 I))
  let : P.Normal := Normal.map hn _ (QuotientGroup.mk'_surjective _)
  exact no_transvections_of_normal_cubic a.representation P
    (local_point_star_card_of_normal h structural I hLI hn)
    (local_point_fixedSpace_eq_bot h structural I hLI hn a) hdim

private theorem no_returned_line
    {H U Z : Subgroup G} {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    [FiniteDimensional (ZMod 2) W]
    {ρ : Representation (ZMod 2) (HStar H) W}
    (s : ConjugationSection H U Z ρ) (hZ : Nat.card Z = 2)
    (hno : ∀ t, fixedCodim ρ (zpowers t) ≠ 1)
    (t : ReturnedLineAction H U Z) : False := by
  let A := U.map (MulAut.conj t.g).toMonoidHom
  let C := Z.map (MulAut.conj t.g).toMonoidHom
  have hC : Nat.card C = 2 := (card_map_of_injective (MulAut.conj t.g).injective).trans hZ
  have hdim : Module.finrank (ZMod 2) (s.image C) ≤ 1 := by
    simpa only [hC,show Nat.log 2 2 = 1 from by decide] using s.image_finrank_le C
  have hzero (x : HStar H) (hx : x ∈ Chapter13.Section08.Source.starImage H A) :
      ρ x - LinearMap.id = 0 := by
    have hr : LinearMap.range (ρ x - LinearMap.id) ≤ s.image C := by
      rintro _ ⟨v,rfl⟩
      apply s.displacement_mem U A C (commutator_comm U A ▸ t.commutator.le) x hx
      obtain ⟨u,hu⟩ := s.surjective (Multiplicative.ofAdd v)
      exact ⟨u,u.property,congrArg Multiplicative.toAdd hu⟩
    have hd := (Submodule.finrank_mono hr).trans hdim
    have hn := hno x
    rw [fixedCodim_zpowers_eq_displacement_rank] at hn
    exact LinearMap.range_eq_bot.mp (Submodule.finrank_eq_zero.mp (by omega))
  have hcomm : ⁅A,U⁆ ≤ Z := by
    apply commutator_le.mpr
    intro x hx u hu
    let xH : H := ⟨x,t.in_H hx⟩
    have hz := LinearMap.congr_fun (hzero (QuotientGroup.mk' (pCore 2 H) xH)
      (mem_map_of_mem _ hx)) (s.quotient ⟨u,hu⟩).toAdd
    change ρ (QuotientGroup.mk' (pCore 2 H) xH) (s.quotient ⟨u,hu⟩).toAdd -
      (s.quotient ⟨u,hu⟩).toAdd = 0 at hz
    rw [s.displacement] at hz
    exact (s.quotient_eq_zero_iff _).mp hz
  have hCZ : C ≤ Z := by
    change Z.map (MulAut.conj t.g).toMonoidHom ≤ Z
    rw [←t.commutator,commutator_comm]
    exact hcomm
  have hc : C = ⊥ := bot_unique ((le_inf hCZ le_rfl).trans t.disjoint.le)
  rw [hc,card_bot] at hC
  omega

/-- Construct F.9.1 for the same arbitrary member of the original H_z. -/
theorem local_f9_hypothesis
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (I : Subgroup G) (hI : I ∈ F.Hz L (normalizer (L : Set G))) :
    (Chapter12.Section09.NaturalSource.naturalF9Setup F L I).Hypothesis := by
  have uniqueness : Uniqueness127 KnownSimple.IsKnownSimple.{u} := by
    intro D _ _ hD S N hN
    exact Chapter1.Section02.nonsolvable_uniqueness_knownSimple hD S hN
  exact Chapter12.Section09.NaturalSource.abelian_local_f9 h
    ⟨structural,uniqueness,previous⟩ F hab I hI

/-- Every critical conjugator for the local group leaves the original full
point normalizer, since its whole span is abelian. -/
theorem local_critical_endpoint_outside_point
    (hab : IsMulCommutative F.U) (I : Subgroup G) (hIH : I ≤ F.H)
    (hf : (Chapter12.Section09.NaturalSource.naturalF9Setup F L I).Hypothesis)
    (i : hf.CriticalEndpoint) : i.representative ∉ F.H := by
  let := hab
  intro hi
  have hU : F.UH I ≤ F.U := conjugateSpanBy_mono le_rfl hIH
  have hUg : i.conjugate (F.UH I) ≤ F.U := by
    rintro x ⟨u,hu,rfl⟩
    exact (mem_normalizer_iff.mp (le_normalizer_conjugateSpanBy V F.H hi) u).mp (hU hu)
  apply i.noncentral
  apply le_trans _ bot_le
  rw [le_bot_iff,commutator_eq_bot_iff_le_centralizer]
  exact hUg.trans ((le_centralizer F.U).trans
    (Subgroup.centralizer_le (le_conjugateSpanBy V F.H)))

/-- The same local geometry has the original odd critical distance. -/
theorem local_f9_critical_bounds
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (I : Subgroup G) (hI : I ∈ F.Hz L (normalizer (L : Set G)))
    [IsElementaryAbelian 2 (F.UH I)] :
    let hf := local_f9_hypothesis h hab structural previous I hI
    3 ≤ hf.b ∧ Odd hf.b := by
  let D := Chapter12.Section09.NaturalSource.naturalF9Setup F L I
  let hf := local_f9_hypothesis h hab structural previous I hI
  have uniqueness : Uniqueness127 KnownSimple.IsKnownSimple.{u} := by
    intro D _ _ hD S N hN
    exact Chapter1.Section02.nonsolvable_uniqueness_knownSimple hD S hN
  have hcomm : ∀ g : G, D.V ⊓ D.V.map (MulAut.conj g).toMonoidHom ≠ ⊥ →
      ⁅D.V,D.V.map (MulAut.conj g).toMonoidHom⁆ = ⊥ := by
    intro g hg
    have hh := ((h.abelian_source_geometry ⟨structural,uniqueness,previous⟩ F).2.mp hab) g⁻¹
    simpa only [conjugate,inv_inv] using hh (by simpa only [conjugate,inv_inv] using hg)
  exact hf.b_bounds_of_intersecting_conjugates_commute
    ((le_conjugateSpanBy D.V D.H).trans hf.UH_le_QH) hcomm

/-- Normality of the actual cubic gives a strict selected reciprocal endpoint,
on any literal local action of dimension greater than two. -/
theorem local_normal_point_selected_endpoint
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (I : Subgroup G) (hI : I ∈ F.Hz L (normalizer (L : Set G)))
    (hn : ((F.Li L 1).subgroupOf I).Normal)
    [IsElementaryAbelian 2 (F.UH I)]
    (a : LocalQuotientAction I (F.UH I) (F.Vi 1))
    (hdim : 2 < Module.finrank (ZMod 2) (Additive (F.UH I ⧸ (F.Vi 1).subgroupOf (F.UH I)))) :
    let hf := local_f9_hypothesis h hab structural previous I hI
    letI : IsElementaryAbelian 2 (Chapter12.Section09.NaturalSource.naturalF9Setup F L I).UH :=
      inferInstanceAs (IsElementaryAbelian 2 (F.UH I))
    Nonempty (SelectedQuadraticEndpoint hf a) := by
  let D := Chapter12.Section09.NaturalSource.naturalF9Setup F L I
  let hf := local_f9_hypothesis h hab structural previous I hI
  let : IsElementaryAbelian 2 D.UH := inferInstanceAs (IsElementaryAbelian 2 (F.UH I))
  have hcomm : ∀ g : G, D.V ⊓ D.V.map (MulAut.conj g).toMonoidHom ≠ ⊥ →
      ⁅D.V,D.V.map (MulAut.conj g).toMonoidHom⁆ = ⊥ := by
    have uniqueness : Uniqueness127 KnownSimple.IsKnownSimple.{u} := by
      intro D _ _ hD S N hN
      exact Chapter1.Section02.nonsolvable_uniqueness_knownSimple hD S hN
    intro g hg
    have hh := ((h.abelian_source_geometry ⟨structural,uniqueness,previous⟩ F).2.mp hab) g⁻¹
    simpa only [conjugate,inv_inv] using hh (by simpa only [conjugate,inv_inv] using hg)
  have hcore : D.V ≤ D.QH := (le_conjugateSpanBy D.V D.H).trans hf.UH_le_QH
  obtain ⟨hb,ho⟩ := hf.b_bounds_of_intersecting_conjugates_commute hcore hcomm
  rcases full_or_selected D hf rfl a hb ho hcomm with ⟨i,t,_⟩ | hs
  · exact False.elim (no_returned_line (ModuleBound.OriginalF916.conjugationSection a hf.H_centralizes)
      hf.point_card (local_normal_point_no_transvections h structural I
        (fun _ hx => hI.1.2 (Or.inl hx)) hn a hdim) t)
  · exact hs

/-- The original minimal five-core witness now has a strict selected reciprocal
endpoint on the same action as its dihedral factors. No local geometry is an input. -/
theorem local_minimal_five_critical_geometry
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (J : Subgroup G) (hJ : J ∈ F.Hz L (normalizer (L : Set G)))
    (hne : pCore 5 (HStar J) ≠ ⊥) :
    ∃ (I : Subgroup G) (X : Subgroup (HStar I)) (Y : Subgroup I),
      I ≤ J ∧ I ∈ F.Hz L (normalizer (L : Set G)) ∧
      (∀ D : Subgroup G, D ∈ F.Hz L (normalizer (L : Set G)) → D < I →
        pCore 5 (HStar D) = ⊥) ∧
      X.Normal ∧ IsElementaryAbelian 5 X ∧ X = pCore 5 (HStar I) ∧
      (Nat.card X = 5 ∨ Nat.card X = 25) ∧
      (∀ N : Subgroup (HStar I), N.Normal → N ≤ X → N = ⊥ ∨ N = X) ∧
      Y.Normal ∧ IsPPerfect 2 Y ∧ Y ≤ pResidual 2 I ∧
      Y.map (QuotientGroup.mk' (pCore 2 I)) = X ∧
      ((QuotientGroup.mk' (pCore 2 I)).comp Y.subtype).ker = pCore 2 Y ∧
      Nonempty ((Y ⧸ pCore 2 Y) ≃* X) ∧
      ¬ Y.map I.subtype ≤ normalizer (L : Set G) ∧
      I = Y.map I.subtype ⊔ (F.Li L 1 ⊔ (T : Subgroup G)) ∧
      Group.IsSolvable I ∧
      ((F.Li L 1).subgroupOf I).Normal ∧
      Nat.card (((F.Li L 1).subgroupOf I).map (QuotientGroup.mk' (pCore 2 I))) = 3 ∧
      ⁅F.UH I,F.Li L 1⁆ = F.UH I ∧
      ∃ hU : IsElementaryAbelian 2 (F.UH I),
        let := hU
        ∃ a : LocalQuotientAction I (F.UH I) (F.Vi 1),
          ∃ (A : Subgroup I) (R : Subgroup (HStar I)),
            A ≤ (F.Ri L 1).subgroupOf I ∧
            IsElementaryTwo (A.map (QuotientGroup.mk' (pCore 2 I))) ∧
            A.map (QuotientGroup.mk' (pCore 2 I)) ⊓ centralizer (X : Set (HStar I)) = ⊥ ∧
            R ≤ X ⊔ A.map (QuotientGroup.mk' (pCore 2 I)) ∧
            IsElementaryTwo R ∧ Nat.card R = 2 ∧
            IsCubic a.representation R ∧ fixedCodim a.representation R = 2 ∧
            Nat.card (⁅X,R⁆ : Subgroup (HStar I)) = 5 ∧
            Module.finrank (ZMod 2) (subspaceCommutator a.representation ⊤ ⁅X,R⁆) = 4 ∧
            IsCompl (subspaceCommutator a.representation ⊤ ⁅X,R⁆)
              (fixedSpace a.representation (⁅X,R⁆ ⊔ R)) ∧
          let := BinaryGroupAction.action a.representation
          smallSupportGroup (HStar I)
            (Multiplicative (Additive (F.UH I ⧸ (F.Vi 1).subgroupOf (F.UH I)))) 2 = X ∧
          0 < Nat.card (smallSupportFactors (HStar I)
            (Multiplicative (Additive (F.UH I ⧸ (F.Vi 1).subgroupOf (F.UH I)))) 2) ∧
          Nat.card (smallSupportFactors (HStar I)
            (Multiplicative (Additive (F.UH I ⧸ (F.Vi 1).subgroupOf (F.UH I)))) 2) ≤ 2 ∧
          (∀ P : Subgroup (HStar I), IsPPerfect 2 P → P ≤ centralizer (X : Set (HStar I))) ∧
          ∃ (f : CanonicalFiveDihedralFamily (G := HStar I)
              (V := Multiplicative (Additive (F.UH I ⧸ (F.Vi 1).subgroupOf (F.UH I)))))
            (i : smallSupportFactors (HStar I)
              (Multiplicative (Additive (F.UH I ⧸ (F.Vi 1).subgroupOf (F.UH I)))) 2),
            i.val = ⁅X,R⁆ ∧ f.factor i = ⁅X,R⁆ ⊔ R ∧
            X ≤ f.product ∧
            ((F.Li L 1).subgroupOf I).map (QuotientGroup.mk' (pCore 2 I)) ≤
              centralizer (f.product : Set (HStar I)) ∧
            f.product ⊔ ((F.Li L 1 ⊔ (T : Subgroup G)).subgroupOf I).map
              (QuotientGroup.mk' (pCore 2 I)) = ⊤ ∧
            (∀ t : HStar I, fixedCodim a.representation (zpowers t) ≠ 1) ∧
            let : IsElementaryAbelian 2 (Chapter12.Section09.NaturalSource.naturalF9Setup F L I).UH := hU
            ∃ hf : (Chapter12.Section09.NaturalSource.naturalF9Setup F L I).Hypothesis,
              3 ≤ hf.b ∧ Odd hf.b ∧
              ∃ c : SelectedQuadraticEndpoint hf a,
                c.endpoint.representative ∉ F.H ∧
                ∃ r : hf.CriticalEndpoint,
                  r.representative * c.endpoint.representative ∈ I ∧
                  (∀ D : Subgroup G, I ≤ normalizer (D : Set G) →
                    r.conjugate (c.endpoint.conjugate D) = D) := by
  obtain ⟨I,X,Y,hIJ,hI,hproper,hXn,hXp,hcore,hcard,hmin,hYn,hYp,hYle,
      hYm,hYk,he,hout,hgen,hs,hn,hpoint,hm,hU,a,A,R,hAR,hA,hfaith,hR,hRE,hRc,
      hcub,hfixed,hcomm,hmove,hcompl,hcan,hpos,hcount,hcentral,f,i,hi,hfi,hXD,hPD,hfull⟩ :=
    local_minimal_five_dihedral h hab structural previous J hJ hne
  let := hU
  have hdim : 2 < Module.finrank (ZMod 2)
      (Additive (F.UH I ⧸ (F.Vi 1).subgroupOf (F.UH I))) := by
    have hh := Submodule.finrank_le (subspaceCommutator a.representation ⊤ ⁅X,R⁆)
    rw [hmove] at hh
    omega
  have hno := local_normal_point_no_transvections h structural I
    (fun _ hx => hI.1.2 (Or.inl hx)) hn a hdim
  let hf := local_f9_hypothesis h hab structural previous I hI
  obtain ⟨hb,ho⟩ := local_f9_critical_bounds h hab structural previous I hI
  let : IsElementaryAbelian 2 (Chapter12.Section09.NaturalSource.naturalF9Setup F L I).UH := hU
  obtain ⟨c⟩ := local_normal_point_selected_endpoint h hab structural previous I hI hn a hdim
  obtain ⟨r,hprod,hlabels⟩ := c.reversal_with_product hb
  exact ⟨I,X,Y,hIJ,hI,hproper,hXn,hXp,hcore,hcard,hmin,hYn,hYp,hYle,
    hYm,hYk,he,hout,hgen,hs,hn,hpoint,hm,hU,a,A,R,hAR,hA,hfaith,hR,hRE,hRc,
    hcub,hfixed,hcomm,hmove,hcompl,hcan,hpos,hcount,hcentral,f,i,hi,hfi,hXD,hPD,hfull,
    hno,hf,hb,ho,c,local_critical_endpoint_outside_point hab I hI.2.1 hf c.endpoint,
    r,hprod,hlabels⟩

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction
