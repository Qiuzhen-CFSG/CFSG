module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Preliminary.Residual.Multiplicity.SuzukiInvariant
public import CFSG.Quasithin.ChapterK.Section01To04.RankOne.SuzukiRecognition.Source
public import Theory.Representation.BinaryOffender.QuasisimpleCentralSection
public import Theory.Representation.BinaryOffender.CubicSection
public import Theory.GroupTheory.GeneralizedFitting.QuasisimpleTransfer

/-!
# The Suzuki endpoint and faithful starred actors on the original full module

An elementary actor normalizing the retained Suzuki component acts on each
invariant Irr⁺ member through the actual component image. Odd outer order
supplies an inner representative; centerlessness makes that representative
an involution. Their quotient centralizes the component and has square one,
so the odd linear centralizer of the Irr⁺ member kills its action.

The component acts faithfully on the literal central quotient I/C_I(J).
Pulling the restricted actor back through the faithful component action
preserves its image rank, cubic action and fixed codimension. Fixed
codimension decreases on passing to I/C_I(J). The genuine Chapter K source
hypotheses now construct natural Suzuki coordinates on this irreducible
quotient and give the lower bound two. Monotonicity lifts that bound to I,
before any splitting of the central extension.

On the original D,S this contradicts the strict constituent ratio drop for
the same moved component, orbit and starred actor. Every starred actor is
therefore faithful on the full marked SL₃ component for every even field
degree. The final theorem selects such an actor and retains its literal
injective conjugation homomorphism. The faithful cubic-containment argument
remains with qt-d-1222-natural-preliminary-source; the source estimate
2/qhat alone does not provide the two-copy premise of A.3.19. Final chapter
assembly remains with qt-d-1222-natural-local-geometry.

Source: Aschbacher--Smith, A.1.41, p.31; D.3.8--9, pp.199--201; K.3.6,
p.457, applied to 11.0.4, p.760, combined manuscript of 1 March 2004.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open Representation.BinaryOffender.Homogeneous
open scoped MatrixGroups IsMulCommutative ENNReal
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Preliminary.SuzukiSupport
variable {H W : Type*} [Group H] [Finite H] [AddCommGroup W] [Module (ZMod 2) W]
  [FiniteDimensional (ZMod 2) W] (ρ : Representation (ZMod 2) H W)

omit [Finite H] in
/-- Literal actor containment on an Irr⁺ section. -/
private theorem restricted_actor_le_component
    {J A : Subgroup H} {I : Submodule (ZMod 2) W}
    (hI : IsIrrPlus ρ J I) (_hAI : A ≤ subspaceStabilizer ρ I)
    (hAJ : A ≤ normalizer (J : Set H)) (hA : IsElementaryAbelian 2 A)
    (hz : center J = ⊥) (ho : Odd (Nat.card (MulAut.Outer J))) :
    restrictedSubgroup ρ I A ≤ restrictedSubgroup ρ I J := by
  let := hA
  rintro _ ⟨a,ha,rfl⟩
  let n : normalizer (J : Set H) := ⟨a,hAJ ha⟩
  have ht : (a : H)^2 = 1 := elemPow_eq_one_of_isElementaryAbelian (a : H) ha
  have hn : n^2 = 1 := Subtype.ext ht
  obtain ⟨j,hj⟩ := involution_inner_of_odd_outer ho (J.normalizerMonoidHom n)
    (by rw [←map_pow,hn,map_one])
  have hcj : Function.Injective (MulAut.conj : J →* MulAut J) :=
    MulAut.conj_injective_of_center_eq_bot hz
  have hj2 : j^2 = 1 := hcj (by rw [map_pow,hj,←map_pow,hn,map_one,map_one])
  have he (x : J) : (a : H) * x * (a : H)⁻¹ = (j : H) * x * (j : H)⁻¹ := by
    exact congrArg Subtype.val (DFunLike.congr_fun hj x).symm
  have hcomm : Commute (a : H) (j : H) := by
    have hh := he j
    simp only [mul_inv_cancel_right] at hh
    exact mul_inv_eq_iff_eq_mul.mp hh
  let c : H := (j : H)⁻¹ * a
  have hc2 : c^2 = 1 := by
    change ((j : H)⁻¹ * (a : H))^2 = 1
    rw [hcomm.symm.inv_left.mul_pow,ht,inv_pow,←Subgroup.coe_pow,hj2,Subgroup.coe_one]
    simp
  have hcJ : c ∈ centralizer (J : Set H) := by
    intro x hx
    have hh := he ⟨x,hx⟩
    change x * c = c * x
    dsimp [c]
    calc
      x * ((j : H)⁻¹ * a) = (j : H)⁻¹ * ((j : H)*x*(j : H)⁻¹) * a := by group
      _ = (j : H)⁻¹ * ((a : H)*x*(a : H)⁻¹) * a := by rw [hh]
      _ = (j : H)⁻¹ * a * x := by group
  have hcI : c ∈ subspaceStabilizer ρ I :=
    (subspaceStabilizer ρ I).mul_mem
      ((subspaceStabilizer ρ I).inv_mem (hI.choose j.property)) a.property
  have hp : IsPGroup 2 (zpowers c) := by
    let : IsElementaryAbelian 2 (zpowers c) := IsElementaryAbelian.zpowers_of_pow_eq_one hc2
    exact IsElementaryAbelian.isPGroup 2 _
  have hfix := Homogeneous.IsIrrPlus.le_fixedSpace_of_twoGroup_centralizes ρ hI hp
    ((zpowers_le).mpr hcJ) ((zpowers_le).mpr hcI)
  refine ⟨⟨j,hI.choose j.property⟩,j.property,?_⟩
  apply subspaceImageRepresentation_injective ρ I
  ext v
  have hh := hfix v.property ⟨c,mem_zpowers c⟩
  have hh' := congrArg (ρ (j : H)) hh
  change ρ (j : H) (ρ c (v : W)) = ρ (j : H) (v : W) at hh'
  change ρ (j : H) (v : W) = ρ (a : H) (v : W)
  simpa only [c,←Module.End.mul_apply,←map_mul,mul_inv_cancel_left] using hh'.symm

omit [Finite H] [FiniteDimensional (ZMod 2) W] in
private theorem quotient_faithful
    {J : Subgroup H} [IsQuasisimple J] {I : Submodule (ZMod 2) W}
    (hI : IsIrrPlus ρ J I) (hz : center J = ⊥) :
    Function.Injective (centralQuotientRepresentation ρ J I hI.choose) := by
  apply (injective_iff_map_eq_one _).mpr
  intro j hj
  have hc := (centralSection_kernel_le_centralizer ρ J J le_rfl I hI
    hI.choose J.le_normalizer (mem_map_of_mem J.subtype hj)).2
  have hjz : j ∈ center J := mem_center_iff.mpr (fun x => Subtype.ext (hc x x.property))
  rwa [hz,mem_bot] at hjz

omit [Finite H] [FiniteDimensional (ZMod 2) W] in
private theorem component_action_faithful
    {J : Subgroup H} [IsQuasisimple J] {I : Submodule (ZMod 2) W}
    (hI : IsIrrPlus ρ J I) (hz : center J = ⊥) :
    Function.Injective (subgroupActionHom ρ I J hI.choose) := by
  apply (injective_iff_map_eq_one _).mpr
  intro j hj
  apply quotient_faithful ρ hI hz
  rw [map_one]
  apply LinearMap.ext
  intro q
  induction q using Submodule.Quotient.induction_on with
  | _ v =>
    have hh := congrArg (fun g => subspaceImageRepresentation ρ I g v) hj
    exact congrArg ((fixedSpace ρ J).comap I.subtype).mkQ hh

/-- Endpoint bound on the literal restricted actor of an invariant Suzuki Irr+ section. -/
theorem restricted_actor_ratio_ge_two
    {J A : Subgroup H} [IsQuasisimple J] {I : Submodule (ZMod 2) W}
    (hJ : IsSQTK KnownSimple.IsKnownSimple J)
    (hI : IsIrrPlus ρ J I) (hAI : A ≤ subspaceStabilizer ρ I)
    (hAJ : A ≤ normalizer (J : Set H)) (hA : IsElementaryAbelian 2 A)
    {r : ℕ} (hr : 0 < r) (e : J ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup r)
    (hsmall : restrictedSubgroup ρ I A ∈ ChapterD.Qhat (subspaceImageRepresentation ρ I)) :
    2 ≤ actionRatio (subspaceImageRepresentation ρ I) (restrictedSubgroup ρ I A) := by
  let : IsSimpleGroup (BenderSuzuki.MatrixGroups.SuzukiMatrixGroup r) :=
    (BenderSuzuki.External.huppert_blackburn_XI_3_6 r hr).1
  let : IsSimpleGroup J := e.isSimpleGroup
  have hz : center J = ⊥ :=
    (IsSimpleGroup.eq_bot_or_eq_top_of_normal _ inferInstance).resolve_right
      (fun hh => Group.IsPerfect.not_isMulCommutative J (center_eq_top_iff.mp hh))
  have ho : Odd (Nat.card (MulAut.Outer J)) := by
    rw [Nat.card_congr (MulAut.outerCongr e).toEquiv]
    exact BenderSuzuki.MatrixGroups.suzuki_odd_outer_index r (by omega)
  let f := subgroupActionHom ρ I J hI.choose
  let σ := (invariantSubspace ρ J I hI.choose).toRepresentation
  let τ := centralQuotientRepresentation ρ J I hI.choose
  let B := (restrictedSubgroup ρ I A).comap f
  have hf : Function.Injective f := component_action_faithful ρ hI hz
  have hBmap : B.map f = restrictedSubgroup ρ I A := by
    apply map_comap_eq_self
    rw [subgroupActionHom_range]
    exact restricted_actor_le_component ρ hI hAI hAJ hA hz ho
  have hB : IsElementaryTwo B := by
    let : IsElementaryAbelian 2 (restrictedSubgroup ρ I A) := hsmall.1.2
    refine ⟨?_,IsElementaryAbelian.comap_of_injective f hf _⟩
    intro hh
    rw [hh,Subgroup.map_bot] at hBmap
    exact hsmall.1.1 hBmap.symm
  have hrank : rank B = rank (restrictedSubgroup ρ I A) := by
    rw [←rank_map_injective f hf,hBmap]
  have hcodim : fixedCodim σ B =
      fixedCodim (subspaceImageRepresentation ρ I) (restrictedSubgroup ρ I A) := by
    have hh := fixedCodim_map_equivariant σ (subspaceImageRepresentation ρ I) f
      (LinearEquiv.refl (ZMod 2) I) (fun _ _ => rfl) B
    rwa [hBmap] at hh
  have hcubic : IsCubic σ B := by
    intro a ha b hb c hc v
    exact hsmall.2.1 (f a) ha (f b) hb (f c) hc v
  have hbound : fixedCodim σ B ≤ 2 * rank B := by
    rw [hcodim,hrank]
    exact (actionRatio_le_nat_iff _ hsmall.1 2).mp hsmall.2.2
  have hτ : cubicRatio τ ≤ 2 := by
    apply (cubicRatio_le_nat_iff τ 2).mpr
    refine ⟨B,hB,cubic_quotient σ (centralSubspace ρ J I hI.choose) hcubic,?_⟩
    have hh := fixedCodim_quotient_add_subrepresentation_le σ
      (centralSubspace ρ J I hI.choose) B
    change fixedCodim τ B + _ ≤ fixedCodim σ B at hh
    omega
  have htop : IsQuasisimple (⊤ : Subgroup J) :=
    IsQuasisimple.of_mulEquiv (topEquiv : (⊤ : Subgroup J) ≃* J).symm
  have hsource : ChapterK.RankOne.SourceHypotheses τ (⊤ : Subgroup J) := by
    refine ⟨hJ,generalizedFitting_eq_top_of_quasisimple,htop,
      quotient_faithful ρ hI hz,?_,hτ⟩
    exact (irreducible_comp_surjective_iff _ topEquiv.surjective τ).mpr hI.choose_spec.2
  have hztop : center (⊤ : Subgroup J) = ⊥ := by
    apply bot_unique
    intro j hj
    have hjz : (j : J) ∈ center J := by
      apply mem_center_iff.mpr
      intro x
      exact congrArg Subtype.val ((mem_center_iff.mp hj) ⟨x,mem_top x⟩)
    apply Subtype.ext
    change (j : J) = 1
    simpa only [hz,mem_bot] using hjz
  let eq : ((⊤ : Subgroup J) ⧸ center (⊤ : Subgroup J)) ≃*
      BenderSuzuki.MatrixGroups.SuzukiMatrixGroup r :=
    (QuotientGroup.quotientMulEquivOfEq hztop).trans
      (QuotientGroup.quotientBot.trans (topEquiv.trans e))
  have hlow := hsource.suzuki_actionRatio_ge_two (hsource.suzukiModel (by omega) eq)
    (by omega) hB
  have hle : actionRatio τ B ≤ actionRatio σ B := by
    apply ENNReal.div_le_div_right
    exact_mod_cast (show fixedCodim τ B ≤ fixedCodim σ B from by
      have hh := fixedCodim_quotient_add_subrepresentation_le σ
        (centralSubspace ρ J I hI.choose) B
      exact (Nat.le_add_right _ _).trans hh)
  have he : actionRatio σ B =
      actionRatio (subspaceImageRepresentation ρ I) (restrictedSubgroup ρ I A) := by
    unfold actionRatio
    rw [hcodim,hrank]
  exact he ▸ hlow.trans hle

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Preliminary.SuzukiSupport


open CFSG.Quasithin.Chapter12.Section02
open CFSG.Quasithin.ChapterB.QuasisimpleSource
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Preliminary
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)

/-- The actual invariant Suzuki constituent has endpoint ratio two, contradicting the strict drop. -/
theorem sl3_fullAction_starred_kernel_eq_bot
    (m : ActionEquiv D.centralQuotientAction (linearNatural S.field 3))
    (heven : Even S.field.degree) :
    letI := fullModule_elementary D S
    let ρ := fullModuleConjugation D S
    let K := (L.subgroupOf (normalizer (L : Set G))).map (actionHom ρ)
    ∀ A : Subgroup (actionImage ρ), A ∈ ChapterD.QhatStar (imageRepresentation ρ) →
      A ⊓ centralizer (K : Set (actionImage ρ)) = ⊥ := by
  let := fullModule_elementary D S
  dsimp only
  intro A hA
  by_contra hn
  obtain ⟨_,J,hJ,_,ho,hcomm,_,_,⟨r,hr,⟨e⟩⟩,hAJ,hX,I,hI,hAI,hsmall,_,_⟩ :=
    sl3_fullAction_starred_nonfaithful_invariant_constituent D S m heven A hA hn
  let := hJ.2
  have hI' : IsIrrPlus (imageRepresentation (fullModuleConjugation D S)) J I := by
    simpa only [hX] using hI
  have hlow := SuzukiSupport.restricted_actor_ratio_ge_two _
    (fullAction_component_sqtk D S J hJ) hI' hAI hAJ hA.1.2.1.2 hr e hsmall
  exact sl3_fullAction_starred_no_endpoint_constituent D S m A (componentOrbit J A)
    (A ⊓ centralizer (((L.subgroupOf (normalizer (L : Set G))).map
      (actionHom (fullModuleConjugation D S))) : Set (actionImage (fullModuleConjugation D S))))
    hA ho inf_le_left hcomm I hI hAI hlow

/-- Every original starred actor acts faithfully on the full marked SL3 component in even degree. -/
theorem sl3_fullAction_starred_faithful
    (m : ActionEquiv D.centralQuotientAction (linearNatural S.field 3))
    (heven : Even S.field.degree) :
    letI := fullModule_elementary D S
    let ρ := fullModuleConjugation D S
    let H := actionImage ρ
    let K := (L.subgroupOf (normalizer (L : Set G))).map (actionHom ρ)
    ∀ A : Subgroup H, A ∈ ChapterD.QhatStar (imageRepresentation ρ) →
      ∃ α : A →* MulAut K, Function.Injective α ∧
        ∀ (a : A) (k : K), (α a k : H) = (a : H) * (k : H) * (a : H)⁻¹ := by
  let := fullModule_elementary D S
  dsimp only
  intro A hA
  exact fullAction_component_actor_faithful D S A
    (sl3_fullAction_starred_kernel_eq_bot D S m heven A hA)

/-- Select a faithful minimal cubic actor on the original full module, with no extra premise. -/
theorem sl3_fullAction_exists_faithful_starred_actor
    (m : ActionEquiv D.centralQuotientAction (linearNatural S.field 3))
    (heven : Even S.field.degree) :
    letI := fullModule_elementary D S
    let ρ := fullModuleConjugation D S
    let H := actionImage ρ
    let K := (L.subgroupOf (normalizer (L : Set G))).map (actionHom ρ)
    ∃ A : Subgroup H, A ∈ ChapterD.QhatStar (imageRepresentation ρ) ∧
      ∃ α : A →* MulAut K, Function.Injective α ∧
        ∀ (a : A) (k : K), (α a k : H) = (a : H) * (k : H) * (a : H)⁻¹ := by
  let := fullModule_elementary D S
  obtain ⟨A,hA⟩ := fullAction_exists_starred_actor D S
  exact ⟨A,hA,sl3_fullAction_starred_faithful D S m heven A hA⟩

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Preliminary
