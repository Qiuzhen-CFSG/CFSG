module
public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceCompletion.BinaryHomogeneity
public import Theory.Representation.BinaryOffender.Homogeneous.Existence

/-!
# A.1.42 and single natural binary chief factors

A faithful irreducible ambient action has zero fixed space for its nontrivial
normal component. A.1.42 selects a homogeneous Irr+ member. When the actual
irreducible component submodules are all isomorphic, its conjugate central
images are isomorphic, so the original two-group stabilizes the selected
subspace. Ambient chief irreducibility then makes it the whole module.

Applying the proved common-actor binary homogeneity and the original flag's
pairwise ratio budget shows every noncentral binary LA-chief factor is a
single irreducible natural L-module. The final theorem consumes the original
reducible B.5.1 hypotheses and the actual SL4/SL5 marking; all intermediate
homogeneity, marking, two-summand and A.1.42 premises are discharged.

Source: Aschbacher--Smith B.5.1, p.101, the assertion that each U_i is an
irreducible natural L-module, and A.1.42, p.32.
-/

@[expose] public noncomputable section
open Representation Representation.BinaryOffender Subgroup Theory.GroupTheory
open scoped ENNReal MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.ChapterB.QuasisimpleSource.SourceCompletion
universe u v
variable {G : Type u} [Group G] {V : Type v} [AddCommGroup V] [Module (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V)

private theorem fixedSpace_eq_bot (hi : IsIrreducible ρ) (hf : Function.Injective ρ)
    (C : Subgroup G) [C.Normal] (hC : C ≠ ⊥) : fixedSpace ρ C = ⊥ := by
  let := hi
  by_contra hn
  exact hC (bot_unique ((le_ker_of_normal_invariants_ne_bot ρ C hn).trans
    ((MonoidHom.ker_eq_bot_iff _).mpr hf).le))

private theorem irrPlus_irreducible_of_fixed_bot (C : Subgroup G)
    (hz : fixedSpace ρ C = ⊥) (I : Submodule (ZMod 2) V)
    (hs : C ≤ subspaceStabilizer ρ I) (hI : IsIrrPlus ρ C I) :
    IsIrreducible (invariantSubspace ρ C I hs).toRepresentation := by
  apply (Subrepresentation.irreducible_iff_isAtom _).mpr
  refine ⟨fun he => hI.ne_bot ρ (congrArg Subrepresentation.toSubmodule he), ?_⟩
  intro J hJ
  have hstab : C ≤ subspaceStabilizer ρ J.toSubmodule := by
    apply le_subspaceStabilizer
    intro c hc v hv
    exact J.apply_mem_toSubmodule ⟨c,hc⟩ hv
  rcases hI.eq_or_le_fixedSpace ρ hstab hJ.le with he | he
  · exact (hJ.ne (Subrepresentation.toSubmodule_injective he)).elim
  · apply Subrepresentation.toSubmodule_injective
    exact bot_unique (he.trans_eq hz)

private def quotientImageEquivOfFixedBot (C : Subgroup G)
    (hz : fixedSpace ρ C = ⊥) (I : Submodule (ZMod 2) V)
    (hs : C ≤ subspaceStabilizer ρ I) :
    (invariantSubspace ρ C I hs).toRepresentation.Equiv
      (Homogeneous.quotientImage ρ C I hs).toRepresentation := by
  let f : I →ₗ[ZMod 2] I.map (fixedSpace ρ C).mkQ :=
    (((fixedSpace ρ C).mkQ).comp I.subtype).codRestrict _ (fun v => ⟨v, v.property, rfl⟩)
  have hf : Function.Bijective f := by
    constructor
    · intro v w he
      apply Subtype.ext
      have hm : v.val - w.val ∈ fixedSpace ρ C := by
        apply (Submodule.Quotient.mk_eq_zero _).mp
        change (fixedSpace ρ C).mkQ (v.val - w.val) = 0
        rw [map_sub, show (fixedSpace ρ C).mkQ v.val = (fixedSpace ρ C).mkQ w.val from
          congrArg Subtype.val he, sub_self]
      rw [hz] at hm
      exact sub_eq_zero.mp hm
    · rintro ⟨q, v, hv, rfl⟩
      exact ⟨⟨v,hv⟩, rfl⟩
  exact .mk (LinearEquiv.ofBijective f hf) (by intro g; apply LinearMap.ext; intro v; rfl)

/-- A.1.42 turns actual component homogeneity into irreducibility when a
two-group together with the component generates the chief actor. -/
theorem irreducible_component_of_homogeneous [FiniteDimensional (ZMod 2) V]
    (hi : IsIrreducible ρ) (hf : Function.Injective ρ)
    (C A : Subgroup G) [C.Normal] [Group.IsPerfect C] (hC : C ≠ ⊥)
    (hA : IsPGroup 2 A) (hgen : C ⊔ A = ⊤)
    (hhom : ∀ U W : Subrepresentation (ρ.comp C.subtype),
      IsIrreducible U.toRepresentation → IsIrreducible W.toRepresentation →
        Nonempty (U.toRepresentation.Equiv W.toRepresentation)) :
    IsIrreducible (ρ.comp C.subtype) := by
  have hz := fixedSpace_eq_bot ρ hi hf C hC
  have hAnorm : A ≤ normalizer C := le_normalizer_of_normal
  obtain ⟨J,hJ⟩ := Homogeneous.exists_isIrrPlusWith_of_faithful ρ hf C A hC hAnorm hA
  let WJ := invariantSubspace ρ C J hJ.invariant
  have hiJ := irrPlus_irreducible_of_fixed_bot ρ C hz J hJ.invariant hJ.isIrrPlus
  have stable (a : A) : J.map (ρ a.val) = J := by
    apply hJ.eq_of_isomorphic_conjugate ρ a
    have hKa := hJ.isIrrPlus.map_normalizer ρ (hJ.normalizes a.property)
    let WK := invariantSubspace ρ C (J.map (ρ a.val)) hKa.choose
    have hiK := irrPlus_irreducible_of_fixed_bot ρ C hz (J.map (ρ a.val)) hKa.choose hKa
    obtain ⟨e⟩ := hhom WJ WK hiJ hiK
    let ei := quotientImageEquivOfFixedBot ρ C hz J hJ.invariant
    let ek := quotientImageEquivOfFixedBot ρ C hz (J.map (ρ a.val)) hKa.choose
    let eq := ei.symm.trans (e.trans ek)
    exact ⟨eq.toLinearEquiv, fun g v => LinearMap.congr_fun (eq.isIntertwining' g) v⟩
  have hsA : A ≤ subspaceStabilizer ρ J := by
    intro a ha
    exact (subspace_map_eq_iff ρ J a).mp (stable ⟨a,ha⟩)
  have hs : (⊤ : Subgroup G) ≤ subspaceStabilizer ρ J := by
    rw [← hgen]
    exact sup_le hJ.invariant hsA
  let P : Subrepresentation ρ := {
    toSubmodule := J
    apply_mem_toSubmodule g v hv := (hs (Subgroup.mem_top g) v).2 hv }
  have hPtop : P = ⊤ := (hi.eq_bot_or_eq_top P).resolve_left
    (fun he => hJ.isIrrPlus.ne_bot ρ (congrArg Subrepresentation.toSubmodule he))
  have hJtop : J = ⊤ := congrArg Subrepresentation.toSubmodule hPtop
  have hWtop : WJ = ⊤ := Subrepresentation.toSubmodule_injective hJtop
  apply isSimpleOrder_iff_isAtom_top.mpr
  rw [← hWtop]
  exact (Subrepresentation.irreducible_iff_isAtom WJ).mp hiJ

/-- A faithful binary chief action is a single natural component module.
The homogeneity and A.1.42 steps are both discharged from earlier B.4.2. -/
theorem binary_chief_natural [Finite G] [FiniteDimensional (ZMod 2) V]
    (hi : IsIrreducible ρ)
    {K : GroupClass.{u}} (hK : IrreducibleBranch.ContainsSimpleTwoGroups K)
    (earlier : SourceInduction.ProjectiveLine.IrreducibleClassificationInput.{u,v} K)
    (C : Subgroup G) [IsQuasisimple C] (hC : IsSQTK K C)
    (hfit : generalizedFitting G = C) (hcore : pCore 2 G = ⊥)
    (hfaith : Function.Injective ρ)
    {d : ℕ} (hd : d = 4 ∨ d = 5) (mark : C ≃* SL(d,ZMod 2))
    (A : Subgroup G) (hA : IsPGroup 2 A) (hgen : C ⊔ A = ⊤)
    (hq : quadraticRatio ρ < 1) (hbound : quadraticRatio ρ ≤ 3 / 4)
    (hfour : d = 4 → quadraticRatio ρ < 3 / 4) :
    IsIrreducible (ρ.comp C.subtype) ∧ IsLinearNatural (ρ.comp C.subtype) BinaryField.two d := by
  let : C.Normal := hfit ▸ generalizedFitting_normal (G := G)
  let : IsSimpleGroup (C ⧸ center C) := IsQuasisimple.simple
  let : Nontrivial C := (QuotientGroup.mk'_surjective (center C)).nontrivial
  have hirr := irreducible_component_of_homogeneous ρ hi hfaith C A
    ((Subgroup.nontrivial_iff_ne_bot C).mp inferInstance) hA hgen
    (binary_chief_homogeneous ρ hi hK earlier C hC hfit hcore hfaith hd mark hq hbound hfour)
  refine ⟨hirr, ?_⟩
  have hsq : IsSQTK K G := (IsSQTK.equiv
    ((MulEquiv.subgroupCongr hgen).trans (topEquiv : (⊤ : Subgroup G) ≃* G))).mp
      (IrreducibleBranch.local_sqtk hK C A hC hA)
  let : IsQuasisimple (generalizedFitting G) := hfit.symm ▸ inferInstance
  have hiF : IsIrreducible (ρ.comp (generalizedFitting G).subtype) := by rwa [hfit]
  obtain ⟨B, hB⟩ := isFFModule_of_quadraticRatio_le_one ρ hq.le
  obtain ⟨B', _, hB'⟩ := hB.exists_bestOffender ρ
  have hc := earlier G V ρ hsq inferInstance hfaith hiF ⟨B', hB'⟩
  have hn := binary_natural_of_ratio ρ hc hd ((MulEquiv.subgroupCongr hfit).trans mark) hq hfour
  rwa [hfit] at hn

/-- The actual flag budget supplies all upper bounds used to exclude mixed
binary types: at most three quarters, strictly less in degree four. -/
theorem binary_flag_ratio_bound [Finite G] [FiniteDimensional (ZMod 2) V]
    {K : GroupClass.{u}} (hK : IrreducibleBranch.ContainsSimpleTwoGroups K)
    (earlier : SourceInduction.ProjectiveLine.IrreducibleClassificationInput.{u,v} K)
    [IsQuasisimple (generalizedFitting G)] (hsq : IsSQTK K (generalizedFitting G))
    (hfaith : Function.Injective ρ) (hcore : pCore 2 G = ⊥)
    {d : ℕ} (hd : d = 4 ∨ d = 5) (mark : generalizedFitting G ≃* SL(d,ZMod 2))
    (f : ReducibleChiefFlag ρ (generalizedFitting G))
    (A : Subgroup G) (hA : IsMinimalBestOffender ρ A) {i : ℕ} (hi : i ∈ f.noncentral) :
    let q := quadraticRatio (imageRepresentation
      (sectionRepresentation ρ (f.chain i) (f.chain (i + 1))))
    q ≤ 3 / 4 ∧ (d = 4 → q < 3 / 4) := by
  have he := f.estimates ρ hfaith inferInstance hcore A hA
  let q := fun k => quadraticRatio (imageRepresentation
    (sectionRepresentation ρ (f.chain k) (f.chain (k + 1))))
  have hq (k : ℕ) (hk : k ∈ f.noncentral) : q k < 1 := (he.2.2.1 k hk).2
  have hqt (k : ℕ) (hk : k ∈ f.noncentral) : q k ≠ ⊤ :=
    ne_top_of_le_ne_top (by simp) (hq k hk).le
  obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp f.multiple
  obtain ⟨j, hj, hij⟩ : ∃ j ∈ f.noncentral, i ≠ j := by
    by_cases hia : i = a
    · exact ⟨b, hb, hia ▸ hab⟩
    · exact ⟨a, ha, hia⟩
  have hlo := binary_flag_ratio_lower ρ hK earlier hsq hcore hd mark f hj (hq j hj).le
  have hl := ENNReal.toReal_mono (hqt j hj) hlo
  have hp := ENNReal.toReal_mono (by norm_num : (1 : ℝ≥0∞) ≠ ⊤) (he.2.2.2.1 i hi j hj hij)
  change (q i + q j).toReal ≤ (1 : ℝ≥0∞).toReal at hp
  rw [ENNReal.toReal_add (hqt i hi) (hqt j hj)] at hp
  constructor
  · apply (ENNReal.toReal_le_toReal (hqt i hi) (ENNReal.div_ne_top (by norm_num) (by norm_num))).mp
    rcases hd with rfl | rfl <;> norm_num [ENNReal.toReal_div] at hl hp ⊢ <;> linarith
  · intro hd4
    subst d
    apply (ENNReal.toReal_lt_toReal (hqt i hi) (ENNReal.div_ne_top (by norm_num) (by norm_num))).mp
    norm_num [ENNReal.toReal_div] at hl hp ⊢
    linarith

/-- Every noncentral factor of the original binary LA-chief flag is a single
irreducible natural L-module. All homogeneity, ratio and A.1.42 premises are
proved from the source flag, the original minimal offender, and full B.4.2. -/
theorem binary_flag_natural [Finite G] [FiniteDimensional (ZMod 2) V]
    {K : GroupClass.{u}} (hK : IrreducibleBranch.ContainsSimpleTwoGroups K)
    (earlier : SourceInduction.ProjectiveLine.IrreducibleClassificationInput.{u,v} K)
    [IsQuasisimple (generalizedFitting G)] (hsq : IsSQTK K (generalizedFitting G))
    (hfaith : Function.Injective ρ) (hcore : pCore 2 G = ⊥)
    {d : ℕ} (hd : d = 4 ∨ d = 5) (mark : generalizedFitting G ≃* SL(d,ZMod 2))
    (f : ReducibleChiefFlag ρ (generalizedFitting G))
    (A : Subgroup G) (hA : IsMinimalBestOffender ρ A)
    (hgen : generalizedFitting G ⊔ A = ⊤) :
    ∀ i ∈ f.noncentral,
      let τ := sectionRepresentation ρ (f.chain i) (f.chain (i + 1))
      IsIrreducible (τ.comp (generalizedFitting G).subtype) ∧
        IsLinearNatural (τ.comp (generalizedFitting G).subtype) BinaryField.two d := by
  have he := f.estimates ρ hfaith inferInstance hcore A hA
  intro i hi
  let τ := sectionRepresentation ρ (f.chain i) (f.chain (i + 1))
  have hf := binary_flag_factor_faithful ρ hd mark f hi
  have hqi := (he.2.2.1 i hi).2
  have hbounds := binary_flag_ratio_bound ρ hK earlier hsq hfaith hcore hd mark f A hA hi
  change quadraticRatio (imageRepresentation τ) < 1 at hqi
  change quadraticRatio (imageRepresentation τ) ≤ 3 / 4 ∧
    (d = 4 → quadraticRatio (imageRepresentation τ) < 3 / 4) at hbounds
  rw [image_ratio_of_faithful τ hf] at hqi hbounds
  exact binary_chief_natural τ (f.irreducible ρ ((f.mem_noncentral i).mp hi).1)
    hK earlier (generalizedFitting G) hsq rfl hcore hf hd mark A
    (hA.1.1.2.isPGroup 2 A) hgen hqi hbounds.1 hbounds.2

/-- Literal original-source application: in either identified binary family,
one LA-chief flag consists entirely of faithful single natural L-factors. -/
theorem binary_source_single_chiefs [Finite G]
    {K : GroupClass.{u}} (hK : IrreducibleBranch.ContainsSimpleTwoGroups K)
    (earlier : SourceInduction.ProjectiveLine.IrreducibleClassificationInput.{u,v} K)
    {L : Subgroup G} (h : QuasisimpleSourceHypothesis ρ K L)
    (hnot : ¬ IsIrrPlus ρ L (moved ρ L))
    {d : ℕ} (hd : d = 4 ∨ d = 5) (mark : L ≃* SL(d,ZMod 2)) :
    ∃ A : Subgroup G, IsMinimalBestOffender ρ A ∧
      ∃ f : ReducibleChiefFlag (ρ.comp (L ⊔ A).subtype) (generalizedFitting ↥(L ⊔ A)),
        ∀ i ∈ f.noncentral,
          let τ := sectionRepresentation (ρ.comp (L ⊔ A).subtype) (f.chain i) (f.chain (i + 1))
          Function.Injective τ ∧ IsIrreducible (τ.comp (generalizedFitting ↥(L ⊔ A)).subtype) ∧
            IsLinearNatural (τ.comp (generalizedFitting ↥(L ⊔ A)).subtype) BinaryField.two d := by
  let := h.finite_module
  let : IsQuasisimple L := h.quasisimple
  let : L.Normal := component_normal_of_fitting_eq_sup_center L h.fitting
  obtain ⟨A, hA, hf⟩ := reducible_source_flag ρ h hnot
  obtain ⟨f⟩ := hf
  refine ⟨A, hA, f, ?_⟩
  let H := L ⊔ A
  let σ := ρ.comp H.subtype
  have hp : IsPGroup 2 A := hA.1.1.2.isPGroup 2 A
  have hfit : generalizedFitting H = L.subgroupOf H :=
    IrreducibleBranch.local_generalizedFitting L A h.fitting h.twoCore hp
  let : IsQuasisimple (L.subgroupOf H) :=
    IsQuasisimple.of_mulEquiv (subgroupOfEquivOfLe (show L ≤ H from le_sup_left)).symm
  let : IsQuasisimple (generalizedFitting H) := hfit.symm ▸ inferInstance
  have hsq : IsSQTK K (generalizedFitting H) := by
    rw [hfit]
    exact (IsSQTK.equiv (subgroupOfEquivOfLe (show L ≤ H from le_sup_left))).mpr h.sqtk
  have hcore : pCore 2 H = ⊥ :=
    IrreducibleBranch.local_twoCore_eq_bot L H h.fitting h.twoCore le_sup_left
  let e := (MulEquiv.subgroupCongr hfit).trans
    ((subgroupOfEquivOfLe (show L ≤ H from le_sup_left)).trans mark)
  have hAH : A ≤ H := le_sup_right
  have hmin : IsMinimalBestOffender σ (A.subgroupOf H) := by
    refine ⟨hA.1.subgroupOf ρ hAH, ?_⟩
    intro B hB hBA
    apply Subgroup.map_injective H.subtype_injective
    rw [map_subgroupOf_eq_of_le hAH]
    apply hA.2 _ (hB.map_subtype ρ)
    refine ⟨(map_mono hBA.1).trans_eq (map_subgroupOf_eq_of_le hAH), ?_⟩
    have hw := hBA.2
    rw [weight_comp_map ρ H.subtype H.subtype_injective,
      weight_comp_map ρ H.subtype H.subtype_injective,
      map_subgroupOf_eq_of_le hAH] at hw
    exact hw
  have hgen : generalizedFitting H ⊔ A.subgroupOf H = ⊤ := by
    rw [hfit]
    apply Subgroup.map_injective H.subtype_injective
    rw [Subgroup.map_sup, map_subgroupOf_eq_of_le (show L ≤ H from le_sup_left),
      map_subgroupOf_eq_of_le hAH]
    exact H.range_subtype.symm.trans H.subtype.range_eq_map
  intro i hi
  exact ⟨binary_flag_factor_faithful σ hd e f hi,
    binary_flag_natural σ hK earlier hsq (h.faithful.comp H.subtype_injective) hcore hd e
      f (A.subgroupOf H) hmin hgen i hi⟩

end CFSG.Quasithin.ChapterB.QuasisimpleSource.SourceCompletion
