module
public import CFSG.Quasithin.Chapter7.NormalizedSource.DoubledBinaryPlacedModels
public import CFSG.Quasithin.ChapterF.Section01.RankOneBorels.Unitary.PerfectCore
public import CFSG.Quasithin.MainConverse.EvenLinearLocal.LinearThreeGeometry
public import Theory.SpecificGroups.PSL3.LinearThreeFlags.BinaryThreeSection
public import Theory.SpecificGroups.SymplecticFour.LocalStructure.PerfectTwoNormalizer
public import Theory.AtlasPort.LinearGroups.G2.PerfectTwoNormalizer
public import Theory.SpecificGroups.Triality.PerfectTwoNormalizer
public import Theory.SpecificGroups.ClassicalUnitary.UnitaryFourConverse.PerfectSubgroups
public import Theory.SpecificGroups.ClassicalUnitary.UnitaryFourFormTransport
public import Theory.SpecificGroups.ClassicalUnitary.FivePerfectLocals
public import Theory.SpecificGroups.ReeF4.BinaryThreeSection
public import Theory.SpecificGroups.ReeF4.SubfieldTitsEmbedding

/-!
# Two-local exclusions for the placed binary-three residual

In the original placed-component branch, the full doubled orbit has rank
six and a nontrivial image in the component's central quotient. Its perfect
normalizer still maps onto SL₃(2). Binary PSU₃ has solvable two-local
normalizers. For the binary rank-two families, normalizer coverage places
the perfect image in an actual parabolic residual with binary SL₂ quotient
and two-group kernel. The explicit order-four element of SL₃(2) excludes
this quotient, since every two-subgroup of binary SL₂ has exponent two.

Both nodes, all field parameters and the full Hermitian-form transports
are retained. The PSU₅(4) parabolics are seven-free, the second Ree
parabolic is three-free, and the literal Tits embedding preserves the
local configuration. The small derived models are excluded by seven
or the original rank-six bound. The whole Bender and rank-two rows are
therefore removed; PSL₅(2), PSp₆(2) and the four previously retained
sporadic carriers still require their original module geometry.

The final helper constructs these local data from the full moved orbit
through the literal inclusion and full central quotient. Its chosen-module
application is NonFFSourceDoubledBinaryPlacedLocals; no source two-local
or parabolic hypothesis is added there. Source: Aschbacher--Smith 4.4.12,
printed pp.621--622, used by 7.3.4 and 7.6.1, printed pp.699,702,
refs/quasithin.pdf. The reused matrix and carrier modules retain their
ATLAS attribution and license in LICENSES/ATLAS.txt.
-/

open Subgroup Theory.GroupTheory Matrix
open scoped MatrixGroups IsMulCommutative
public noncomputable section
namespace CFSG.Quasithin.Chapter7.NormalizedSource.DoubledBinaryPlacedLocals

private instance : IsSimpleGroup BinaryLinearThree.Group := by
  let : IsSimpleGroup Matrix.PSL3Two.PSL := Atlas.psl_simple_high_rank 3 (by decide)
  exact Matrix.PSL3Two.equiv.isSimpleGroup

/-- A perfect binary-three covering actor normalizing a nontrivial contained two-subgroup. -/
@[expose] def LocalData (Q : Type*) [Group Q] : Prop :=
  ∃ B P : Subgroup Q, Group.IsPerfect B ∧ IsPGroup 2 P ∧ P ≠ ⊥ ∧
    B ≤ normalizer (P : Set Q) ∧ P ≤ B ∧
    ∃ q : B →* BinaryLinearThree.Group, Function.Surjective q

variable {Q : Type*} [Group Q] [Finite Q]

omit [Finite Q] in
/-- Transport the literal two-local configuration and its quotient together. -/
theorem LocalData.of_mulEquiv {S : Type*} [Group S]
    (h : LocalData Q) (e : Q ≃* S) : LocalData S := by
  obtain ⟨B,P,hB,hP,hne,hn,hPB,q,hq⟩ := h
  let := hB
  let a := B.equivMapOfInjective e.toMonoidHom e.injective
  refine ⟨B.map e.toMonoidHom,P.map e.toMonoidHom,Group.IsPerfect.map _,
    hP.map _,?_,(map_mono hn).trans (P.le_normalizer_map e.toMonoidHom),
    map_mono hPB,q.comp a.symm.toMonoidHom,hq.comp a.symm.surjective⟩
  exact fun he => hne ((map_eq_bot_iff_of_injective P e.injective).mp he)

private theorem two_kernel_of_injective {A H : Type*} [Group A] [Group H]
    (f : A →* H) (hf : Function.Injective f) : IsPGroup 2 f.ker := by
  rw [f.ker_eq_bot_iff.mpr hf]
  exact IsPGroup.of_card (n := 0) (by simp)

/-- The rank-one action puts every nontrivial two-subgroup normalizer in a solvable Borel. -/
theorem LocalData.not_unitary_three (h : LocalData Q) {n : ℕ} (hn : 0 < n) :
    ¬ ClassicalGroup.IsPSU Q 3 (2^n) := by
  intro hm
  obtain ⟨B,P,hB,hP,hne,hN,_,q,hq⟩ := h
  let : Group.IsSolvable (normalizer (P : Set Q)) :=
    ChapterF.Source.Unitary.two_normalizer_solvable hn hm P hP hne
  let : Group.IsSolvable B := Group.isSolvable_of_isSolvable_injective (inclusion_injective hN)
  let : Group.IsPerfect BinaryLinearThree.Group := Atlas.sl_perfect 3 (by decide)
  exact Group.IsPerfect.not_isSolvable BinaryLinearThree.Group
    (Group.isSolvable_of_surjective hq)

omit [Finite Q] in
/-- Both actual linear-three parabolics have the incompatible binary rank-one quotient. -/
theorem LocalData.not_linear_three (h : LocalData Q) {n : ℕ} (hn : 0 < n) :
    ¬ ClassicalGroup.IsPSL Q 3 (2^n) := by
  rintro ⟨F,_,_,hF,⟨e⟩⟩
  obtain ⟨B,P,hB,hP,hne,hN,_,q,hq⟩ := h.of_mulEquiv e
  let := hB
  let : CharP F 2 := Theory.SpecificGroups.SymplecticFour.EvenProjective.charTwo_of_card hF
  obtain ⟨g,point,hg⟩ := MainConverse.LinearThreeGeometry.twoLocal_conjugate_le F hn hF
    (normalizer (P : Set PSL(3,F))) ⟨P,hne,hP,rfl⟩
  let j := (MulAut.conj g).toMonoidHom.comp B.subtype
  have hj : j.range ≤ Matrix.PSL3.RootPlaneGeometry.parabolic F point := by
    rintro _ ⟨a,rfl⟩
    exact hg (mem_map_of_mem _ (hN a.property))
  apply Matrix.PSL3.LinearThree.no_binary_three_quotient_in_parabolic F q hq j
    (two_kernel_of_injective j ((MulAut.conj g).injective.comp B.subtype_injective))
  cases point
  · exact Or.inr hj
  · exact Or.inl hj


omit [Finite Q] in
/-- Both original subgroups and the section survive an injective placement. -/
theorem LocalData.of_injective {S : Type*} [Group S]
    (h : LocalData Q) (f : Q →* S) (hf : Function.Injective f) : LocalData S := by
  obtain ⟨B,P,hB,hP,hne,hn,hPB,q,hq⟩ := h
  let := hB
  let a := B.equivMapOfInjective f hf
  refine ⟨B.map f,P.map f,Group.IsPerfect.map _,hP.map _,?_,
    (map_mono hn).trans (P.le_normalizer_map f),map_mono hPB,
    q.comp a.symm.toMonoidHom,hq.comp a.symm.surjective⟩
  exact fun he => hne ((map_eq_bot_iff_of_injective P hf).mp he)

omit [Finite Q] in
/-- The actual quotient forces seven into the containing group's order. -/
theorem LocalData.seven_dvd (h : LocalData Q) : 7 ∣ Nat.card Q := by
  obtain ⟨B,_,_,_,_,_,_,q,hq⟩ := h
  have hd := (card_dvd_of_surjective q hq).trans B.card_subgroup_dvd_card
  rw [Matrix.PSL3Two.card_SL] at hd
  exact (by decide : 7 ∣ 168).trans hd

omit [Finite Q] in
/-- A rank-one quotient of either symplectic parabolic excludes the section. -/
theorem LocalData.not_symplectic_four (h : LocalData Q) {n : ℕ} :
    ¬ ClassicalGroup.IsPSp Q 2 (2^n) := by
  rintro ⟨F,_,_,hF,⟨e⟩⟩
  let : CharP F 2 := Theory.SpecificGroups.SymplecticFour.EvenProjective.charTwo_of_card hF
  obtain ⟨B,P,hB,hP,hne,hN,_,q,hq⟩ := h.of_mulEquiv
    (e.trans (Theory.SpecificGroups.SymplecticFour.EvenProjective.equiv (F:=F)).symm)
  let := hB
  let f := B.subtype
  obtain ⟨g,hg⟩ := Theory.SpecificGroups.SymplecticFour.twoLocal_parabolic_cover_of_charTwo
    (normalizer (P : Set _)) ⟨P,hne,hP,rfl⟩
  let j := (MulAut.conj g).toMonoidHom.comp f
  have hj : Function.Injective j := (MulAut.conj g).injective.comp B.subtype_injective
  have him : j.range ≤ (normalizer (P : Set _)).map (MulAut.conj g).toMonoidHom := by
    rw [MonoidHom.range_comp]
    exact map_mono (by simpa only [f,range_subtype] using hN)
  let : Group.IsPerfect j.range := Group.IsPerfect.range j
  rcases hg with hg | hg
  · have hl : j.range ≤ Theory.SpecificGroups.SymplecticFour.pointLocal :=
      (le_map_solvableResidual_of_isPerfect _ _ (him.trans hg)).trans
        (Theory.SpecificGroups.SymplecticFour.determinantKernel_solvableResidual_le _)
    let k := j.codRestrict _ (fun x => hl ⟨x,rfl⟩)
    have hk : Function.Injective k := fun x y he => hj (congrArg Subtype.val he)
    let r := (Theory.SpecificGroups.SymplecticFour.pointQuotient (F:=F)).comp k
    apply SpecialLinearGroup.no_binary_three_quotient_of_two_kernel q hq r
    have ht : IsPGroup 2 (Theory.SpecificGroups.SymplecticFour.pointQuotient (F:=F)).ker := by
      rw [Theory.SpecificGroups.SymplecticFour.pointQuotient_ker]
      exact IsElementaryAbelian.isPGroup 2 _
    exact ht.comap_of_injective k hk
  · have hl : j.range ≤ Theory.SpecificGroups.SymplecticFour.planeLocal :=
      (le_map_solvableResidual_of_isPerfect _ _ (him.trans hg)).trans
        (Theory.SpecificGroups.SymplecticFour.determinantKernel_solvableResidual_le _)
    let k := j.codRestrict _ (fun x => hl ⟨x,rfl⟩)
    have hk : Function.Injective k := fun x y he => hj (congrArg Subtype.val he)
    let r := (Theory.SpecificGroups.SymplecticFour.Plane.quotientMap (F:=F)).comp k
    apply SpecialLinearGroup.no_binary_three_quotient_of_two_kernel q hq r
    have ht : IsPGroup 2 (Theory.SpecificGroups.SymplecticFour.Plane.quotientMap (F:=F)).ker := by
      rw [Theory.SpecificGroups.SymplecticFour.Plane.quotientMap_ker]
      exact IsElementaryAbelian.isPGroup 2 _
    exact ht.comap_of_injective k hk

omit [Finite Q] in
/-- The two genuine octonion parabolics have binary rank-one residual quotients. -/
theorem LocalData.not_g2 (h : LocalData Q) {n : ℕ} (hn : 2 ≤ n) :
    ¬ ClassificationModels.IsG2At Q (2^n) := by
  rintro ⟨F,_,_,hF,⟨e⟩⟩
  let : CharP F 2 := Theory.SpecificGroups.SymplecticFour.EvenProjective.charTwo_of_card hF
  obtain ⟨B,P,hB,hP,hne,hN,_,q,hq⟩ := h.of_mulEquiv e
  let := hB
  have hbig : 2 < Nat.card F := by
    rw [hF]
    exact lt_of_lt_of_le (by decide : 2 < 2^2) (Nat.pow_le_pow_right (by decide) hn)
  obtain ⟨g,hg⟩ := Atlas.G2.EvenLocal.NormalizerCover.normalizer_conjugate_le_parabolic P hne hP
  let j := (MulAut.conj g).toMonoidHom.comp B.subtype
  have hj : Function.Injective j := (MulAut.conj g).injective.comp B.subtype_injective
  have him : j.range ≤ (normalizer (P : Set _)).map (MulAut.conj g).toMonoidHom := by
    rw [MonoidHom.range_comp]
    exact map_mono (by simpa only [range_subtype] using hN)
  let : Group.IsPerfect j.range := Group.IsPerfect.range j
  rcases hg with hg | hg
  · have hl : j.range ≤ Atlas.G2.LieParabolicSetup.local₁ := by
      rw [←Atlas.G2.HigherFieldResiduals.parabolic₁_residual hbig]
      exact le_map_solvableResidual_of_isPerfect _ _ (him.trans hg)
    let k := j.codRestrict _ (fun x => hl ⟨x,rfl⟩)
    exact SpecialLinearGroup.no_binary_three_quotient_of_binary_core_quotient q hq k
      (two_kernel_of_injective k (fun x y he => hj (congrArg Subtype.val he)))
      (Atlas.G2.LieParabolicSetup.local₁CoreQuotientEquivPSL.trans
        Atlas.RankOneFieldAutomorphisms.slEquivPSL.symm)
  · have hl : j.range ≤ Atlas.G2.LieParabolicSetup.local₂ := by
      rw [←Atlas.G2.HigherFieldResiduals.parabolic₂_residual hbig]
      exact le_map_solvableResidual_of_isPerfect _ _ (him.trans hg)
    let k := j.codRestrict _ (fun x => hl ⟨x,rfl⟩)
    exact SpecialLinearGroup.no_binary_three_quotient_of_binary_core_quotient q hq k
      (two_kernel_of_injective k (fun x y he => hj (congrArg Subtype.val he)))
      (Atlas.G2.LieParabolicSetup.local₂CoreQuotientEquivPSL.trans
        Atlas.G2.LieParabolicSetup.longSLEquivPSL.symm)

omit [Finite Q] in
/-- The common argument handles both triality nodes and every original binary parameter. -/
theorem LocalData.not_triality (h : LocalData Q) {n : ℕ} (hn : 0 < n) :
    ¬ Triality.Standard.IsTrialityGroupAt (2^n) Q := by
  intro hm
  obtain ⟨e⟩ := (Triality.Standard.isTrialityGroupAt_binary_iff Q n hn).mp hm
  obtain ⟨B,P,hB,hP,hne,hN,_,q,hq⟩ := h.of_mulEquiv e
  let := hB
  obtain ⟨g,a,hg⟩ := Triality.Standard.TwoLocalCover.normalizer_cover n hn P hne hP
  let j := (MulAut.conj g).toMonoidHom.comp B.subtype
  let params := Triality.Standard.binaryParameters n hn
  let D := Triality.Standard.Parabolics.parabolic params a
  let N := (Triality.Standard.Parabolics.localFactor params a).subgroupOf D
  have hj : j.range ≤ D := by
    rintro _ ⟨b,rfl⟩
    exact hg (mem_map_of_mem _ (hN b.property))
  let jD := j.codRestrict D (fun x => hj ⟨x,rfl⟩)
  let : Group.IsPerfect jD.range := Group.IsPerfect.range jD
  let : IsCyclic (D ⧸ N) := Triality.Standard.Parabolics.parabolic_quotient_isCyclic params rfl a
  let : CommGroup (D ⧸ N) := IsCyclic.commGroup
  have hlocal : jD.range ≤ N := le_of_isPerfect_of_solvable_quotient _ _
  let k : B →* Triality.Standard.Parabolics.localFactor params a :=
    j.codRestrict _ (fun x => hlocal ⟨x,rfl⟩)
  have hk : IsPGroup 2 k.ker := two_kernel_of_injective k
    (fun x y he => B.subtype_injective ((MulAut.conj g).injective (congrArg Subtype.val he)))
  cases a with
  | arms =>
    exact SpecialLinearGroup.no_binary_three_quotient_of_binary_core_quotient q hq k hk
      ((Triality.Standard.Parabolics.localFactorArmsQuotientEquivPSL2 params rfl).trans
        (Theory.PSL2.sl2QuotientEquiv (Triality.Standard.ExtensionField params)).symm)
  | central =>
    exact SpecialLinearGroup.no_binary_three_quotient_of_binary_core_quotient q hq k hk
      ((Triality.Standard.Parabolics.localFactorCentralQuotientEquivPSL2 params rfl).trans
        (Theory.PSL2.sl2QuotientEquiv (GaloisField 2 n)).symm)

omit [Finite Q] in
/-- Full Hermitian transport retains the point and plane maps and their two-group kernels. -/
theorem LocalData.not_unitary_four (h : LocalData Q) {n : ℕ} (hn : 0 < n) :
    ¬ ClassicalGroup.IsPSU Q 4 (2^n) := by
  rintro ⟨F,_,_,J,hF,hconj,⟨e⟩⟩
  let : CharP F 2 := Theory.SpecificGroups.ClassicalUnitary.UnitaryFourFormTransport.charP_two n hn hF
  obtain ⟨a⟩ := Theory.SpecificGroups.ClassicalUnitary.UnitaryFourFormTransport.nonempty_projectiveEquiv_standardSU
    J n hn hF hconj
  obtain ⟨B,P,hB,hP,hne,hN,_,q,hq⟩ := h.of_mulEquiv (e.trans a)
  let := hB
  let σ := J.conj
  let hσ := J.conj_involutive
  let F₀ := Theory.SpecificGroups.ClassicalUnitary.UnitaryFourFlag.form F σ hσ
  obtain ⟨g,hg⟩ := Theory.SpecificGroups.ClassicalUnitary.UnitaryFourConverse.TwoLocalCover.twoLocal_parabolic_cover
    σ hσ n hn hF hconj (normalizer (P : Set _)) ⟨P,hne,hP,rfl⟩
  let j := (MulAut.conj g⁻¹).toMonoidHom.comp B.subtype
  have hj : Function.Injective j := (MulAut.conj g⁻¹).injective.comp B.subtype_injective
  have hplace (U : Subgroup F₀.specialSubgroup)
      (hu : normalizer (P : Set _) ≤ U.map (MulAut.conj g).toMonoidHom) : j.range ≤ U := by
    rintro _ ⟨x,rfl⟩
    obtain ⟨y,hy,he⟩ := hu (hN x.property)
    change g⁻¹ * (x : F₀.specialSubgroup) * (g⁻¹)⁻¹ ∈ U
    rw [←he]
    simpa [MulAut.conj_apply,mul_assoc] using hy
  let : Group.IsPerfect j.range := Group.IsPerfect.range j
  rcases hg with hpt | hpl
  · have hl := (le_map_solvableResidual_of_isPerfect _ _ (hplace _ hpt)).trans
      (Theory.SpecificGroups.ClassicalUnitary.UnitaryFourPointResidual.pointParabolic_solvableResidual_le F _)
    let k := j.codRestrict _ (fun x => hl ⟨x,rfl⟩)
    have hk : Function.Injective k := fun x y he => hj (congrArg Subtype.val he)
    let r := (Theory.SpecificGroups.ClassicalUnitary.UnitaryFourPointQuotient.middleEquivSL F σ hσ).toMonoidHom.comp
      ((Theory.SpecificGroups.ClassicalUnitary.UnitaryFourPointQuotient.middleSU F σ hσ).comp k)
    apply SpecialLinearGroup.no_binary_three_quotient_of_two_kernel q hq r
    dsimp only [r]
    rw [MonoidHom.ker_comp_of_injective _ _
      (Theory.SpecificGroups.ClassicalUnitary.UnitaryFourPointQuotient.middleEquivSL F σ hσ).injective,
      ←MonoidHom.comap_ker,Theory.SpecificGroups.ClassicalUnitary.UnitaryFourPointQuotient.middleSU_ker]
    exact (Theory.SpecificGroups.ClassicalUnitary.UnitaryFourConverse.PointParabolic.radical_isTwoGroup F σ hσ).comap_of_injective k hk
  · let k := j.codRestrict _ (fun x => hplace _ hpl ⟨x,rfl⟩)
    have hk : Function.Injective k := fun x y he => hj (congrArg Subtype.val he)
    let r := (Theory.SpecificGroups.ClassicalUnitary.UnitaryFourPlaneLocal.restriction F F₀).comp k
    let d := (GeneralLinearGroup.det (n:=Fin 2) (R:=F)).comp r
    have hd (x : B) : d x = 1 :=
      Abelianization.commutator_subset_ker d Group.IsPerfect.mem_commutator
    let t := r.codRestrict (GeneralLinearGroup.det (n:=Fin 2) (R:=F)).ker hd
    let s := (SpecialLinearGroup.determinantKernelEquiv (Fin 2) F).symm.toMonoidHom.comp t
    have hs : s.ker = r.ker := by
      ext x
      change (SpecialLinearGroup.determinantKernelEquiv (Fin 2) F).symm (t x) = 1 ↔ r x = 1
      rw [MulEquiv.map_eq_one_iff]
      exact Subtype.ext_iff
    apply SpecialLinearGroup.no_binary_three_quotient_of_two_kernel q hq s
    rw [hs]
    exact (Theory.SpecificGroups.ClassicalUnitary.UnitaryFourConverse.PlaneParabolic.kernel_isTwoGroup F σ hσ).comap_of_injective k hk

omit [Finite Q] in
/-- Neither actual PSU₅(4) parabolic has order divisible by seven. -/
theorem LocalData.not_unitary_five (h : LocalData Q) :
    ¬ ClassicalGroup.IsPSU Q 5 4 := by
  rintro ⟨F,_,_,J,hF,hconj,⟨e⟩⟩
  have hcard : Nat.card F = 16 := hF
  let : CharP F 2 := Theory.SpecificGroups.UnitaryFive.charP_two_of_card_sixteen hcard
  obtain ⟨a⟩ := Theory.SpecificGroups.UnitaryFive.projective_equiv_identity_four J hcard hconj
  let J₀ := BenderSuzuki.MatrixGroups.HermitianForm.IdentityGram.identityGram J
  obtain ⟨B,P,hB,hP,hne,hN,_,q,hq⟩ := h.of_mulEquiv (e.trans a)
  let : Finite (BenderSuzuki.MatrixGroups.ProjectiveSpecialUnitaryMatrixGroup J₀) :=
    Theory.SpecificGroups.UnitaryFive.finite_projective J₀
  have h7 : 7 ∣ Nat.card B := by
    have hd := card_dvd_of_surjective q hq
    rw [Matrix.PSL3Two.card_SL] at hd
    exact (by decide : 7 ∣ 168).trans hd
  obtain ⟨W,hw,hi,_,hNW⟩ :=
    Theory.SpecificGroups.UnitaryFive.IsotropicGeometry.projective_twoLocal_stabilizes_isotropic
      J₀ rfl (normalizer (P : Set _)) ⟨P,hne,hP,rfl⟩
  obtain ⟨b,g,hg⟩ := Theory.SpecificGroups.UnitaryFive.IsotropicTransitivity.transitive
    J₀ hcard hconj rfl W hw hi
  have he : Theory.SpecificGroups.UnitaryFive.parabolic J₀ W =
      (if b then Theory.SpecificGroups.UnitaryFive.planeParabolic J₀
        else Theory.SpecificGroups.UnitaryFive.lineParabolic J₀).map
          (MulAut.conj (Theory.SpecificGroups.UnitaryFive.project J₀ g)).toMonoidHom := by
    rw [hg,Theory.SpecificGroups.UnitaryFive.IsotropicGeometry.parabolic_map_action]
    cases b <;> rfl
  have hd := h7.trans (card_dvd_of_le (hN.trans hNW))
  rw [he,card_map_of_injective (MulAut.conj _).injective] at hd
  cases b
  · change 7 ∣ Nat.card (Theory.SpecificGroups.UnitaryFive.lineParabolic J₀) at hd
    rw [Theory.SpecificGroups.UnitaryFive.card_lineParabolic_four J₀ hcard hconj rfl] at hd
    norm_num at hd
  · change 7 ∣ Nat.card (Theory.SpecificGroups.UnitaryFive.planeParabolic J₀) at hd
    rw [Theory.SpecificGroups.UnitaryFive.card_planeParabolic_four J₀ hcard hconj rfl] at hd
    norm_num at hd

omit [Finite Q] in
/-- The linear Ree parabolic has a rank-one quotient; the other is three-free. -/
theorem LocalData.not_ree (h : LocalData Q) {m : ℕ} (hm : 1 ≤ m) :
    ¬ Nonempty (Q ≃* ReeF4.Model m) := by
  rintro ⟨e⟩
  obtain ⟨B,P,hB,hP,hne,hN,_,q,hq⟩ := h.of_mulEquiv e
  let := hB
  obtain ⟨g,s,hg⟩ := ReeF4.ConverseParabolics.normalizer_cover hm P hne hP
  let j := (MulAut.conj g).toMonoidHom.comp B.subtype
  let f := j.codRestrict (ReeF4.ConverseParabolics.parabolic m s)
    (fun x => hg (mem_map_of_mem _ (hN x.property)))
  exact ReeF4.ConverseParabolics.no_binary_three_quotient_in_parabolic q hq hm s f
    (fun x y he => B.subtype_injective ((MulAut.conj g).injective (congrArg Subtype.val he)))

omit [Finite Q] in
/-- The actual Tits embedding retains both subgroups and their normalization. -/
theorem LocalData.not_tits (h : LocalData Q) : ¬ Nonempty (Q ≃* Tits.ParrottGroup) := by
  rintro ⟨e⟩
  obtain ⟨f,hf⟩ := ReeF4.Subfield.exists_tits_embedding 1
  exact ((h.of_mulEquiv e).of_injective f hf).not_ree (by decide) ⟨MulEquiv.refl _⟩


/-- Every rank-two row is excluded by its actual two-local parabolic,
including both small derived endpoints and the Tits group. -/
theorem LocalData.not_rank_two (h : LocalData Q) (hr : 6 ≤ primeRank 2 Q)
    (n : ℕ) : ¬ ClassificationModels.IsRankTwoModel Q n := by
  intro hm
  cases hm with
  | linear hn hm => exact h.not_linear_three hn hm
  | unitary_four hn hm => exact h.not_unitary_four hn hm
  | unitary_five hn hm => exact h.not_unitary_five (by simpa only [hn,Nat.reducePow] using hm)
  | symplectic _ hm => exact h.not_symplectic_four hm
  | g2 hn hm => exact h.not_g2 hn hm
  | triality hn hm => exact h.not_triality hn hm
  | ree_f4 m hm _ he => exact h.not_ree hm he
  | tits _ he => exact h.not_tits he
  | symplectic_derived _ he =>
    have hd := h.seven_dvd
    rw [Nat.card_congr (he.some.trans
      Theory.SpecificGroups.SymplecticFour.Binary.projectiveDerivedEquivAlternatingSix).toEquiv,
      nat_card_alternatingGroup] at hd
    norm_num at hd
  | g2_derived _ he =>
    have hb : primeRank 2 Q ≤ 5 := by
      apply primeRank_le_of_prime_pow_not_dvd
      rw [Nat.card_congr he.some.toEquiv,
        Atlas.G2.DerivedEvenOrder.card_derived_binary (by simp)]
      norm_num
    omega

/-- The higher-rank binary and four sporadic models still requiring their
original module and maximal-local arguments. -/
inductive RemainingPlacedModel (Q : Type*) [Group Q] : Prop
  | linear_five (iso : ClassicalGroup.IsPSL Q 5 2)
  | symplectic_six (iso : ClassicalGroup.IsPSp Q 3 2)
  | sporadic (name : ClassificationModels.SporadicName)
      (row : name = .m24 ∨ name = .j4 ∨ name = .he ∨ name = .ru)
      (iso : Nonempty (Q ≃* name.Carrier))

/-- The local geometry removes the entire Bender and rank-two families from
the already established rank-six placed-component reduction. -/
theorem LocalData.remaining_placed_models (h : LocalData Q)
    (hr : 6 ≤ primeRank 2 Q) (hm : ChapterA.Section02.IsTheoremBModel Q) :
    RemainingPlacedModel Q := by
  have hs : ∃ U : Subgroup Q, ∃ f : U →* BinaryLinearThree.Group, Function.Surjective f := by
    obtain ⟨B,_,_,_,_,_,_,q,hq⟩ := h
    exact ⟨B,q,hq⟩
  cases DoubledBinaryPlacedModels.remaining_placed_models hr hm hs with
  | unitary_three n hn hm => exact (h.not_unitary_three (by omega) hm).elim
  | rank_two n hm => exact (h.not_rank_two hr n hm).elim
  | linear_five hm => exact .linear_five hm
  | symplectic_six hm => exact .symplectic_six hm
  | sporadic name hn hm => exact .sporadic name hn hm

/-- A fully moved nontrivial two-subgroup survives the full central quotient
of a containing group. Its perfect normalizer retains the same binary-three
section. This constructs the actual two-local data used in 4.4.12. -/
theorem localData_of_moved_subgroup
    {G K : Type*} [Group G] [Finite G] [Group K]
    (R W : Subgroup G) [Group.IsPerfect R]
    (hp : IsPGroup 2 W) (hne : W ≠ ⊥) (hWR : W ≤ R)
    (hn : R ≤ normalizer (W : Set G)) (hm : W = ⁅W,R⁆)
    (i : R →* K) (hi : Function.Injective i)
    (e : (R ⧸ pCore 2 R) ≃* BinaryLinearThree.Group) : LocalData (K ⧸ center K) := by
  let j := (QuotientGroup.mk' (center K)).comp i
  let U := W.subgroupOf R
  have hnorm : (⊤ : Subgroup R) ≤ normalizer (U : Set R) := by
    intro x _ y
    exact hn x.property (y : G)
  have hP : IsPGroup 2 (U.map j) := hp.comap_subtype.map j
  have hPne : U.map j ≠ ⊥ := by
    intro hb
    have hk := (map_eq_bot_iff U).mp hb
    have hc : W ≤ centralizer (R : Set G) := by
      intro w hw r hr
      have hz : i (⟨w,hWR hw⟩ : R) ∈ center K :=
        (QuotientGroup.eq_one_iff _).mp (hk hw)
      have he : (⟨r,hr⟩ : R) * ⟨w,hWR hw⟩ = ⟨w,hWR hw⟩ * (⟨r,hr⟩ : R) :=
        hi (by simpa only [map_mul] using mem_center_iff.mp hz (i ⟨r,hr⟩))
      exact congrArg Subtype.val he
    exact hne (hm.trans (commutator_eq_bot_iff_le_centralizer.mpr hc))
  have hk := DoubledBinaryOddPlacement.central_kernel_le_twoCore e i hi
  let b := QuotientGroup.quotientKerEquivRange j
  let q : j.range →* BinaryLinearThree.Group := e.toMonoidHom.comp
    ((QuotientGroup.map j.ker (pCore 2 R) (MonoidHom.id R) hk).comp b.symm.toMonoidHom)
  have hq : Function.Surjective q := by
    intro g
    obtain ⟨r,hrg⟩ := (e.surjective.comp (QuotientGroup.mk'_surjective (pCore 2 R))) g
    refine ⟨j.rangeRestrict r,?_⟩
    have hb : b.symm (j.rangeRestrict r) = QuotientGroup.mk' j.ker r :=
      b.injective (by rw [b.apply_symm_apply]; rfl)
    change e (QuotientGroup.map j.ker (pCore 2 R) (MonoidHom.id R) hk
      (b.symm (j.rangeRestrict r))) = g
    rw [hb]
    exact hrg
  refine ⟨j.range,U.map j,Group.IsPerfect.range j,hP,hPne,?_,map_le_range j U,q,hq⟩
  simpa only [←MonoidHom.range_eq_map] using
    (map_mono (f:=j) hnorm).trans (U.le_normalizer_map j)

end CFSG.Quasithin.Chapter7.NormalizedSource.DoubledBinaryPlacedLocals
