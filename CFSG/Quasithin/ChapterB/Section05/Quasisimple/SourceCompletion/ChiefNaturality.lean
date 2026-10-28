module
public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceCompletion.BinaryConstituents

/-!
# Faithful natural constituents on the complete B.5.1 chief flag

In the SL3 branch a hypothetical chief ratio below one half yields a natural
image and hence removes the actual covering kernel. The earlier irreducible
list on this faithful original actor contradicts that ratio. The full flag
budget therefore puts every chief ratio at one half and removes every kernel.

Together with the binary branch, the original reducible source hypotheses now
give one LA-chief flag whose every noncentral factor is faithful and has
natural component constituents. A.2.1, A.3.6 and the full B.4.2 theorem are
explicit genuine earlier inputs. No B.5.1 classification is assumed.

Source: Aschbacher--Smith B.5.1, pp.100–101, (+), (**) and (++), through the
natural-constituent and covering assertions before (I). Aligning constituent
markings, proving single natural chief factors, and the socle induction follow.
-/

@[expose] public noncomputable section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open scoped MatrixGroups ENNReal IsMulCommutative
namespace CFSG.Quasithin.ChapterB.QuasisimpleSource.SourceCompletion
universe u v
variable {G : Type u} [Group G] {V : Type v} [AddCommGroup V] [Module (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V)

theorem linearThree_half_le_ratio {L H : Subgroup G}
    (h : SourceInduction.ProjectiveLine.IrreducibleActionCase ρ L H)
    (F : BinaryField) (mark : L ≃* SL(3,F.Carrier)) : 1 / 2 ≤ quadraticRatio ρ := by
  cases h with
  | binaryLinear d hd _ e _ =>
    exact (no_linearThree_binary_equiv F hd (mark.symm.trans e.groupEquiv)).elim
  | linearThree _ _ _ he => rw [he]
  | linearTwo _ _ _ _ he => rw [he]; norm_num
  | g2 _ _ _ _ _ he => rw [he]; norm_num
  | g2Two _ _ he => rw [he]; norm_num
  | symmetric _ _ _ _ he => rw [he]; norm_num
  | alternatingSix _ _ _ he => rw [he]; norm_num
  | alternatingSeven _ _ _ _ _ he => rw [he]; norm_num
  | tripleSix _ _ he => rw [he]; norm_num
  | orthogonalSix _ _ _ _ he => rw [he]; norm_num
  | exteriorFive _ _ _ _ _ he => rw [he]; norm_num
  | symplectic _ _ _ _ he =>
    rw [he]
    apply (ENNReal.toReal_le_toReal (by norm_num) (ENNReal.div_ne_top (by norm_num) (by norm_num))).mp
    norm_num [ENNReal.toReal_div]
  | symplecticTwo _ he =>
    rw [he]
    apply (ENNReal.toReal_le_toReal (by norm_num) (ENNReal.div_ne_top (by norm_num) (by norm_num))).mp
    norm_num [ENNReal.toReal_div]
  | symmetricEight _ _ he =>
    rw [he]
    apply (ENNReal.toReal_le_toReal (by norm_num) (ENNReal.div_ne_top (by norm_num) (by norm_num))).mp
    norm_num [ENNReal.toReal_div]

theorem linearThree_half_le_of_constituents [Finite G] [FiniteDimensional (ZMod 2) V]
    [Nontrivial V] {K : GroupClass.{u}} (hK : IrreducibleBranch.ContainsSimpleTwoGroups K)
    (earlier : SourceInduction.ProjectiveLine.IrreducibleClassificationInput.{u,v} K)
    (C : Subgroup G) [IsQuasisimple C] (hC : IsSQTK K C)
    (hfit : generalizedFitting G = C) (hcore : pCore 2 G = ⊥)
    (hfaith : Function.Injective ρ) (hdec : FaithfulConstituentDecomposition ρ C)
    (F : BinaryField) (mark : C ≃* SL(3,F.Carrier)) (hq : quadraticRatio ρ ≤ 1) :
    1 / 2 ≤ quadraticRatio ρ := by
  obtain ⟨B, hB, hb⟩ := bounded_constituent_classification ρ hK earlier C hC
    hfit hcore hfaith hq le_rfl
  obtain ⟨W, hi, hf⟩ := hdec.exists_constituent ρ
  obtain ⟨hs, hc, hr⟩ := hb W hi hf
  exact (linearThree_half_le_ratio _ hc F
    ((local_component_equiv ρ C hfit hcore hB.1).trans mark)).trans hr

/-- Faithfulness already proved on the literal section allows A.3.6 and
Clifford theory to be used without replacing its actor by a quotient. -/
theorem faithful_flag_constituents_on_original [Finite G] [FiniteDimensional (ZMod 2) V]
    {K : GroupClass.{u}} (h36 : Chapter1.Section02.A36Input K)
    [IsQuasisimple (generalizedFitting G)] (hsq : IsSQTK K (generalizedFitting G))
    (hcore : pCore 2 G = ⊥)
    (f : ReducibleChiefFlag ρ (generalizedFitting G)) {i : ℕ} (hi : i ∈ f.noncentral)
    (hf : Function.Injective (sectionRepresentation ρ (f.chain i) (f.chain (i + 1)))) :
    FaithfulConstituentDecomposition
      (sectionRepresentation ρ (f.chain i) (f.chain (i + 1))) (generalizedFitting G) := by
  apply faithful_constituent_decomposition _ hf (f.irreducible ρ ((f.mem_noncentral i).mp hi).1)
  apply center_order_of_a36 h36 hsq
  apply (Subgroup.map_eq_bot_iff_of_injective _ (generalizedFitting G).subtype_injective).mp
  apply bot_unique
  have hm : (pCore 2 (generalizedFitting G)).map (generalizedFitting G).subtype ≤ pCore 2 G :=
    le_sSup ⟨ConjAct.normal_of_characteristic_of_normal,
      pCore_isPGroup.map (generalizedFitting G).subtype⟩
  exact hm.trans_eq hcore

/-- In the SL3 branch even a possibly nonfaithful chief section has ratio
at least one half. A hypothetical smaller ratio first removes its actual
covering kernel, and is then contradicted by the earlier irreducible list. -/
theorem linearThree_flag_ratio_lower [Finite G] [FiniteDimensional (ZMod 2) V]
    {K : GroupClass.{u}} (hK : IrreducibleBranch.ContainsSimpleTwoGroups K)
    (hsemisimple : SourceInduction.HighThreeRank.CoverCentralizer.SourceConstruction.SemisimpleInput K)
    (h36 : Chapter1.Section02.A36Input K)
    (earlier : SourceInduction.ProjectiveLine.IrreducibleClassificationInput.{u,v} K)
    [IsQuasisimple (generalizedFitting G)] (hsq : IsSQTK K (generalizedFitting G))
    (hcore : pCore 2 G = ⊥) (hp : IsPGroup 2 (G ⧸ generalizedFitting G))
    (F : BinaryField) (mark : generalizedFitting G ≃* SL(3,F.Carrier))
    (f : ReducibleChiefFlag ρ (generalizedFitting G)) {i : ℕ} (hi : i ∈ f.noncentral) :
    1 / 2 ≤ quadraticRatio (imageRepresentation
      (sectionRepresentation ρ (f.chain i) (f.chain (i + 1)))) := by
  by_contra! hr
  have hf := (half_flag_factor_reconstruction ρ hK hsemisimple h36 earlier
    hsq hcore hp f hi hr.le).1
  have hc := faithful_flag_constituents_on_original ρ h36 hsq hcore f hi hf
  let τ := sectionRepresentation ρ (f.chain i) (f.chain (i + 1))
  have hirr := f.irreducible ρ ((f.mem_noncentral i).mp hi).1
  let := hirr
  let : Nontrivial (↥(f.chain (i + 1)).toSubmodule ⧸
    (sectionLower ρ (f.chain i) (f.chain (i + 1))).toSubmodule) :=
      Subrepresentation.irreducible_module_nontrivial τ
  rw [image_ratio_of_faithful _ hf] at hr
  have hlo := linearThree_half_le_of_constituents τ hK earlier (generalizedFitting G)
    hsq rfl hcore hf hc F mark (hr.le.trans (by norm_num))
  exact (not_lt_of_ge hlo) hr

private theorem half_budget_le_half {x y : ℝ≥0∞}
    (hx : x < 1) (hy : y < 1) (hyl : 1 / 2 ≤ y) (hxy : x + y ≤ 1) : x ≤ 1 / 2 := by
  have hxt : x ≠ ⊤ := ne_top_of_le_ne_top (by simp) hx.le
  have hyt : y ≠ ⊤ := ne_top_of_le_ne_top (by simp) hy.le
  have hl := ENNReal.toReal_mono hyt hyl
  have hh := ENNReal.toReal_mono (by norm_num : (1 : ℝ≥0∞) ≠ ⊤) hxy
  rw [ENNReal.toReal_add hxt hyt] at hh
  apply (ENNReal.toReal_le_toReal hxt (by norm_num)).mp
  norm_num [ENNReal.toReal_div] at hl hh ⊢
  linarith

/-- Every noncentral SL3 chief factor is faithful on its original actor and
has actual natural constituents; the full flag budget forces ratio one half. -/
theorem linearThree_flag_all_natural [Finite G] [FiniteDimensional (ZMod 2) V]
    {K : GroupClass.{u}} (hK : IrreducibleBranch.ContainsSimpleTwoGroups K)
    (hsemisimple : SourceInduction.HighThreeRank.CoverCentralizer.SourceConstruction.SemisimpleInput K)
    (h36 : Chapter1.Section02.A36Input K)
    (earlier : SourceInduction.ProjectiveLine.IrreducibleClassificationInput.{u,v} K)
    [IsQuasisimple (generalizedFitting G)] (hsq : IsSQTK K (generalizedFitting G))
    (hfaith : Function.Injective ρ) (hcore : pCore 2 G = ⊥)
    (hp : IsPGroup 2 (G ⧸ generalizedFitting G))
    (F : BinaryField) (mark : generalizedFitting G ≃* SL(3,F.Carrier))
    (f : ReducibleChiefFlag ρ (generalizedFitting G))
    (A : Subgroup G) (hA : IsMinimalBestOffender ρ A) :
    ∀ i ∈ f.noncentral,
      Function.Injective (sectionRepresentation ρ (f.chain i) (f.chain (i + 1))) ∧
      NaturalConstituentDecomposition
        (sectionRepresentation ρ (f.chain i) (f.chain (i + 1))) (generalizedFitting G) := by
  have he := f.estimates ρ hfaith inferInstance hcore A hA
  let q := fun i => quadraticRatio
    (imageRepresentation (sectionRepresentation ρ (f.chain i) (f.chain (i + 1))))
  have hq (i : ℕ) (hi : i ∈ f.noncentral) : q i < 1 := (he.2.2.1 i hi).2
  have hlower (i : ℕ) (hi : i ∈ f.noncentral) : 1 / 2 ≤ q i :=
    linearThree_flag_ratio_lower ρ hK hsemisimple h36 earlier hsq hcore hp F mark f hi
  intro i hi
  obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp f.multiple
  obtain ⟨j, hj, hij⟩ : ∃ j ∈ f.noncentral, i ≠ j := by
    by_cases hia : i = a
    · exact ⟨b, hb, hia ▸ hab⟩
    · exact ⟨a, ha, hia⟩
  have hhalf : q i ≤ 1 / 2 :=
    half_budget_le_half (hq i hi) (hq j hj) (hlower j hj) (he.2.2.2.1 i hi j hj hij)
  have hf := (half_flag_factor_reconstruction ρ hK hsemisimple h36 earlier
    hsq hcore hp f hi hhalf).1
  refine ⟨hf, ?_⟩
  let τ := sectionRepresentation ρ (f.chain i) (f.chain (i + 1))
  have hactual : quadraticRatio τ ≤ 1 / 2 := (image_ratio_of_faithful τ hf) ▸ hhalf
  obtain ⟨B, hB, hn⟩ := all_constituents_natural_of_half τ hK earlier
    (generalizedFitting G) hsq rfl hcore hf hactual
  obtain ⟨n, W, hsum, hW⟩ := faithful_flag_constituents_on_original ρ h36 hsq hcore f hi hf
  exact ⟨B, hB, n, W, hsum, fun i => ⟨(hW i).1, (hW i).2, hn (W i) (hW i).1 (hW i).2⟩⟩

/-- All three natural actor alternatives yield faithful natural constituents
throughout the same original source chief flag. -/
theorem natural_flag_all_constituents [Finite G] [FiniteDimensional (ZMod 2) V]
    {K : GroupClass.{u}} (hK : IrreducibleBranch.ContainsSimpleTwoGroups K)
    (hsemisimple : SourceInduction.HighThreeRank.CoverCentralizer.SourceConstruction.SemisimpleInput K)
    (h36 : Chapter1.Section02.A36Input K)
    (earlier : SourceInduction.ProjectiveLine.IrreducibleClassificationInput.{u,v} K)
    [IsQuasisimple (generalizedFitting G)] (hsq : IsSQTK K (generalizedFitting G))
    (hfaith : Function.Injective ρ) (hcore : pCore 2 G = ⊥)
    (hp : IsPGroup 2 (G ⧸ generalizedFitting G))
    (mark : NaturalActor (generalizedFitting G))
    (f : ReducibleChiefFlag ρ (generalizedFitting G))
    (A : Subgroup G) (hA : IsMinimalBestOffender ρ A) :
    ∀ i ∈ f.noncentral,
      Function.Injective (sectionRepresentation ρ (f.chain i) (f.chain (i + 1))) ∧
      NaturalConstituentDecomposition
        (sectionRepresentation ρ (f.chain i) (f.chain (i + 1))) (generalizedFitting G) := by
  rcases mark with ⟨F, ⟨e⟩⟩ | ⟨d, hd, ⟨e⟩⟩
  · exact linearThree_flag_all_natural ρ hK hsemisimple h36 earlier hsq hfaith hcore hp F e f A hA
  · intro i hi
    exact ⟨binary_flag_factor_faithful ρ hd e f hi,
      binary_flag_all_natural ρ hK earlier hsq hfaith hcore hd e f A hA i hi⟩

/-- The original reducible B.5.1 hypothesis now supplies a single LA-chief
flag all of whose noncentral factors are faithful and have actual natural
component constituents. Its source hypotheses, quotient carriers, and the
three possible original natural groups are retained. -/
theorem reducible_all_natural_constituents [Finite G]
    {K : GroupClass.{u}} (hK : IrreducibleBranch.ContainsSimpleTwoGroups K)
    (hsemisimple : SourceInduction.HighThreeRank.CoverCentralizer.SourceConstruction.SemisimpleInput K)
    (h36 : Chapter1.Section02.A36Input K)
    (earlier : SourceInduction.ProjectiveLine.IrreducibleClassificationInput.{u,v} K)
    {L : Subgroup G} (h : QuasisimpleSourceHypothesis ρ K L)
    (hnot : ¬ IsIrrPlus ρ L (moved ρ L)) :
    NaturalActor L ∧ ∃ A : Subgroup G, IsMinimalBestOffender ρ A ∧
      ∃ f : ReducibleChiefFlag (ρ.comp (L ⊔ A).subtype) (generalizedFitting ↥(L ⊔ A)),
        ∀ i ∈ f.noncentral,
          Function.Injective (sectionRepresentation (ρ.comp (L ⊔ A).subtype)
            (f.chain i) (f.chain (i + 1))) ∧
          NaturalConstituentDecomposition
            (sectionRepresentation (ρ.comp (L ⊔ A).subtype) (f.chain i) (f.chain (i + 1)))
            (generalizedFitting ↥(L ⊔ A)) := by
  let := h.finite_module
  let : IsQuasisimple L := h.quasisimple
  let : L.Normal := component_normal_of_fitting_eq_sup_center L h.fitting
  obtain ⟨hn, A, hA, f, _⟩ := reducible_naturalActor ρ hK hsemisimple h36 earlier h hnot
  refine ⟨hn, A, hA, f, ?_⟩
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
  have hq : IsPGroup 2 (H ⧸ generalizedFitting H) :=
    (IrreducibleBranch.local_quotient_isTwoGroup L A hp).of_equiv
      (QuotientGroup.quotientMulEquivOfEq hfit.symm)
  have hcore : pCore 2 H = ⊥ :=
    IrreducibleBranch.local_twoCore_eq_bot L H h.fitting h.twoCore le_sup_left
  have hmark : NaturalActor (generalizedFitting H) := NaturalActor.of_equiv
    ((MulEquiv.subgroupCongr hfit).trans
      (subgroupOfEquivOfLe (show L ≤ H from le_sup_left))) hn
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
  exact natural_flag_all_constituents σ hK hsemisimple h36 earlier hsq
    (h.faithful.comp H.subtype_injective) hcore hq hmark f (A.subgroupOf H) hmin

end CFSG.Quasithin.ChapterB.QuasisimpleSource.SourceCompletion
