module
public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceCompletion.CaseComparison
public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceCompletion.RatioPreservation

/-!
# Natural constituents throughout the binary chief flag

The earlier B.4.2 catalogue gives a one-third lower bound in the binary
SL4 branch and a one-quarter lower bound in SL5. The source pairwise ratio
budget then excludes the S8 alternative in SL4. Every noncentral flag factor
has faithful natural constituents on its original actor. All central kernels
have already been removed by the centerfree F* argument.

Source: Aschbacher--Smith B.5.1, pp.100–101, (++) through the natural
constituent assertion preceding (I). Component irreducibility is subsequent.
-/

@[expose] public noncomputable section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open scoped MatrixGroups ENNReal IsMulCommutative
namespace CFSG.Quasithin.ChapterB.QuasisimpleSource.SourceCompletion
universe u v
variable {G : Type u} [Group G] {V : Type v} [AddCommGroup V] [Module (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V)

theorem binary_four_third_le_ratio {L H : Subgroup G}
    (h : SourceInduction.ProjectiveLine.IrreducibleActionCase ρ L H)
    (mark : L ≃* SL(4,ZMod 2)) : 1 / 3 ≤ quadraticRatio ρ := by
  cases h with
  | binaryLinear d hd _ e he =>
    have heq := binary_degree_eq hd (Or.inl rfl) (e.groupEquiv.symm.trans mark)
    subst d
    rw [he]
    norm_num
  | linearThree _ _ _ he => rw [he]; norm_num
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

/-- The local component in CB is the same marked original group. -/
def local_component_equiv [Finite G] (C : Subgroup G) [IsQuasisimple C]
    (hfit : generalizedFitting G = C) (hcore : pCore 2 G = ⊥)
    {B : Subgroup G} (hB : IsBestOffender ρ B) : generalizedFitting ↥(C ⊔ B) ≃* C := by
  let : C.Normal := hfit ▸ generalizedFitting_normal (G := G)
  have hcenter : center G ≤ C := by
    rw [← hfit]
    exact le_trans (show center G ≤ fittingSubgroup G from
      le_sSup ⟨inferInstance, inferInstance⟩) le_sup_left
  have hfit' : generalizedFitting G = C ⊔ center G := by rw [hfit, sup_of_le_left hcenter]
  have hlocal : generalizedFitting ↥(C ⊔ B) = C.subgroupOf (C ⊔ B) :=
    IrreducibleBranch.local_generalizedFitting C B hfit' hcore (hB.1.2.isPGroup 2 B)
  exact (MulEquiv.subgroupCongr hlocal).trans
    (subgroupOfEquivOfLe (show C ≤ C ⊔ B from le_sup_left))

/-- A faithful binary SL4 chief actor has ratio at least one third, even
when its restriction to the component was initially reducible. -/
theorem binary_four_third_le_of_constituents [Finite G] [FiniteDimensional (ZMod 2) V]
    [Nontrivial V] {K : GroupClass.{u}} (hK : IrreducibleBranch.ContainsSimpleTwoGroups K)
    (earlier : SourceInduction.ProjectiveLine.IrreducibleClassificationInput.{u,v} K)
    (C : Subgroup G) [IsQuasisimple C] (hC : IsSQTK K C)
    (hfit : generalizedFitting G = C) (hcore : pCore 2 G = ⊥)
    (hfaith : Function.Injective ρ) (hdec : FaithfulConstituentDecomposition ρ C)
    (mark : C ≃* SL(4,ZMod 2)) (hq : quadraticRatio ρ ≤ 1) :
    1 / 3 ≤ quadraticRatio ρ := by
  obtain ⟨B, hB, hb⟩ := bounded_constituent_classification ρ hK earlier C hC
    hfit hcore hfaith hq le_rfl
  obtain ⟨W, hi, hf⟩ := hdec.exists_constituent ρ
  obtain ⟨hs, hc, hr⟩ := hb W hi hf
  exact (binary_four_third_le_ratio _ hc
    ((local_component_equiv ρ C hfit hcore hB.1).trans mark)).trans hr

/-- All constituents in a binary chief actor are natural for the same original
group and the same degree, under the chief-flag ratio bounds. -/
theorem binary_natural_constituents [Finite G] [FiniteDimensional (ZMod 2) V]
    {K : GroupClass.{u}} (hK : IrreducibleBranch.ContainsSimpleTwoGroups K)
    (earlier : SourceInduction.ProjectiveLine.IrreducibleClassificationInput.{u,v} K)
    (C : Subgroup G) [IsQuasisimple C] (hC : IsSQTK K C)
    (hfit : generalizedFitting G = C) (hcore : pCore 2 G = ⊥)
    (hfaith : Function.Injective ρ) (hdec : FaithfulConstituentDecomposition ρ C)
    {d : ℕ} (hd : d = 4 ∨ d = 5) (mark : C ≃* SL(d,ZMod 2))
    (hq : quadraticRatio ρ < 1) (hfour : d = 4 → quadraticRatio ρ < 3 / 4) :
    NaturalConstituentDecomposition ρ C := by
  obtain ⟨B, hB, hb⟩ := bounded_constituent_classification ρ hK earlier C hC
    hfit hcore hfaith hq.le le_rfl
  obtain ⟨n, W, hsum, hW⟩ := hdec
  refine ⟨B, hB, n, W, hsum, fun i => ⟨(hW i).1, (hW i).2, ?_⟩⟩
  obtain ⟨hs, hc, hr⟩ := hb (W i) (hW i).1 (hW i).2
  refine ⟨hs, Or.inr ⟨d, hd, ?_⟩⟩
  exact binary_natural_of_ratio _ hc hd
    ((local_component_equiv ρ C hfit hcore hB.1).trans mark)
    (hr.trans_lt hq) (fun he => hr.trans_lt (hfour he))

/-- Passing to the actual action image preserves ratios when the original
action has already been proved faithful. -/
theorem image_ratio_of_faithful (hf : Function.Injective ρ) :
    quadraticRatio (imageRepresentation ρ) = quadraticRatio ρ := by
  have hi : Function.Injective (actionHom ρ) := by
    intro x y hxy
    apply hf
    exact congrArg (imageRepresentation ρ) hxy
  let e := MulEquiv.ofBijective (actionHom ρ) ⟨hi, ρ.asGroupHom.rangeRestrict_surjective⟩
  exact (NaturalExtensions.FourSpaceOffenders.reindex_ratio (imageRepresentation ρ) e).symm

/-- Every binary source flag factor has faithful component constituents on
its original actor, whose central kernel has already been eliminated. -/
theorem binary_flag_constituents [Finite G] [FiniteDimensional (ZMod 2) V]
    [IsQuasisimple (generalizedFitting G)]
    {d : ℕ} (hd : d = 4 ∨ d = 5) (mark : generalizedFitting G ≃* SL(d,ZMod 2))
    (f : ReducibleChiefFlag ρ (generalizedFitting G)) {i : ℕ} (hi : i ∈ f.noncentral) :
    FaithfulConstituentDecomposition
      (sectionRepresentation ρ (f.chain i) (f.chain (i + 1))) (generalizedFitting G) := by
  apply faithful_constituent_decomposition _ (binary_flag_factor_faithful ρ hd mark f hi)
    (f.irreducible ρ ((f.mem_noncentral i).mp hi).1)
  left
  rw [Nat.card_congr (centerCongr mark).toEquiv,
    BinaryLinear.OuterCyclic.binary_center_eq_bot (by rcases hd with rfl | rfl <;> decide)]
  exact Subgroup.card_bot

/-- Same-degree lower bounds on every actual binary source chief factor. -/
theorem binary_flag_ratio_lower [Finite G] [FiniteDimensional (ZMod 2) V]
    {K : GroupClass.{u}} (hK : IrreducibleBranch.ContainsSimpleTwoGroups K)
    (earlier : SourceInduction.ProjectiveLine.IrreducibleClassificationInput.{u,v} K)
    [IsQuasisimple (generalizedFitting G)] (hsq : IsSQTK K (generalizedFitting G))
    (hcore : pCore 2 G = ⊥)
    {d : ℕ} (hd : d = 4 ∨ d = 5) (mark : generalizedFitting G ≃* SL(d,ZMod 2))
    (f : ReducibleChiefFlag ρ (generalizedFitting G)) {i : ℕ} (hi : i ∈ f.noncentral)
    (hr : quadraticRatio (imageRepresentation
      (sectionRepresentation ρ (f.chain i) (f.chain (i + 1)))) ≤ 1) :
    1 / (d - 1 : ℕ) ≤ quadraticRatio (imageRepresentation
      (sectionRepresentation ρ (f.chain i) (f.chain (i + 1)))) := by
  let τ := sectionRepresentation ρ (f.chain i) (f.chain (i + 1))
  have hf := binary_flag_factor_faithful ρ hd mark f hi
  have hc := binary_flag_constituents ρ hd mark f hi
  have hirr := f.irreducible ρ ((f.mem_noncentral i).mp hi).1
  let := hirr
  let : Nontrivial (↥(f.chain (i + 1)).toSubmodule ⧸
    (sectionLower ρ (f.chain i) (f.chain (i + 1))).toSubmodule) :=
      Subrepresentation.irreducible_module_nontrivial τ
  rw [image_ratio_of_faithful _ hf] at hr ⊢
  rcases hd with rfl | rfl
  · simpa using binary_four_third_le_of_constituents τ hK earlier
      (generalizedFitting G) hsq rfl hcore hf hc mark hr
  · simpa using quarter_le_ratio_of_constituents τ hK earlier
      (generalizedFitting G) hsq rfl hcore hf hc hr

private theorem third_budget_lt_three_quarters {x y : ℝ≥0∞}
    (hy : 1 / 3 ≤ y) (hxy : x + y ≤ 1) : x < 3 / 4 := by
  by_contra! hx
  have hbad : (3 / 4 : ℝ≥0∞) + 1 / 3 ≤ 1 := (add_le_add hx hy).trans hxy
  have hh := ENNReal.toReal_mono (by norm_num : (1 : ℝ≥0∞) ≠ ⊤) hbad
  rw [ENNReal.toReal_add (ENNReal.div_ne_top (by norm_num) (by norm_num))
    (ENNReal.div_ne_top (by norm_num) (by norm_num))] at hh
  norm_num [ENNReal.toReal_div] at hh

/-- The original chief flag now has natural constituents at every noncentral
factor in both binary branches. Its actual pairwise ratio budget discharges
the S8 exclusion; no shape of the other factors is assumed. -/
theorem binary_flag_all_natural [Finite G] [FiniteDimensional (ZMod 2) V]
    {K : GroupClass.{u}} (hK : IrreducibleBranch.ContainsSimpleTwoGroups K)
    (earlier : SourceInduction.ProjectiveLine.IrreducibleClassificationInput.{u,v} K)
    [IsQuasisimple (generalizedFitting G)] (hsq : IsSQTK K (generalizedFitting G))
    (hfaith : Function.Injective ρ) (hcore : pCore 2 G = ⊥)
    {d : ℕ} (hd : d = 4 ∨ d = 5) (mark : generalizedFitting G ≃* SL(d,ZMod 2))
    (f : ReducibleChiefFlag ρ (generalizedFitting G))
    (A : Subgroup G) (hA : IsMinimalBestOffender ρ A) :
    ∀ i ∈ f.noncentral,
      NaturalConstituentDecomposition
        (sectionRepresentation ρ (f.chain i) (f.chain (i + 1))) (generalizedFitting G) := by
  have he := f.estimates ρ hfaith inferInstance hcore A hA
  let q := fun i => quadraticRatio
    (imageRepresentation (sectionRepresentation ρ (f.chain i) (f.chain (i + 1))))
  have hq (i : ℕ) (hi : i ∈ f.noncentral) : q i < 1 := (he.2.2.1 i hi).2
  have hlower (i : ℕ) (hi : i ∈ f.noncentral) : 1 / (d - 1 : ℕ) ≤ q i :=
    binary_flag_ratio_lower ρ hK earlier hsq hcore hd mark f hi (hq i hi).le
  intro i hi
  have hfour : d = 4 → q i < 3 / 4 := by
    intro hd4
    obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp f.multiple
    obtain ⟨j, hj, hij⟩ : ∃ j ∈ f.noncentral, i ≠ j := by
      by_cases hia : i = a
      · exact ⟨b, hb, hia ▸ hab⟩
      · exact ⟨a, ha, hia⟩
    apply third_budget_lt_three_quarters (y := q j)
    · simpa [hd4] using hlower j hj
    · exact he.2.2.2.1 i hi j hj hij
  let τ := sectionRepresentation ρ (f.chain i) (f.chain (i + 1))
  have hf := binary_flag_factor_faithful ρ hd mark f hi
  have hratio : q i = quadraticRatio τ := image_ratio_of_faithful τ hf
  exact binary_natural_constituents τ hK earlier (generalizedFitting G) hsq rfl hcore hf
    (binary_flag_constituents ρ hd mark f hi) hd mark
    (hratio ▸ hq i hi) (fun heq => hratio ▸ hfour heq)

end CFSG.Quasithin.ChapterB.QuasisimpleSource.SourceCompletion
