module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalLinearFieldEscapeModulesOpposite
public import Theory.Representation.BinaryConjugationSection.ImageDimensions
public import Theory.Representation.BinaryOffender.CubicRatio

/-!
# The opposite action filtration and its exact index budget

For the literal G.2.3 opposite subgroup A, successive commutators of U
lie in W, S₂, and V, and A centralizes V. On the faithful action on U/V₁,
the image of S₂ has codimension rank(A*)+1. These are actual coordinate
images and the original projection, not independently chosen modules.

If the remaining source geometry proves [A,S₂]≤V₁ and rank(A*)>1,
the filtration is cubic and its ratio is strictly below two. Those two
premises are explicit here; the generic G.2.3 layer bound [A,S₂]≤V alone
does not supply them. The Chapter 12 application feeds this concrete
bound into D.2.13 on the original three-prime kernel image.

Source: Aschbacher--Smith G.2.3 and 5.1.23, printed pp.333--334,645.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative commutatorElement ENNReal
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.CubicEscape.SpanAction
open ChapterG.Section02 ChapterG.Section02.Setup
variable {G : Type*} [Group G] [Finite G] {D : Setup G}

theorem binary_opposite_commutator_filtration (h : D.Hypothesis) (b : D.BinaryNaturalData)
    (g : G) (hgL : g ∈ D.L) (hgN : g ∉ D.G₁) :
    let A := conjugate (D.W g) g
    ⁅A,D.U⁆ ≤ D.W g ∧ ⁅A,D.W g⁆ ≤ D.S₂ g ∧
      ⁅A,D.S₂ g⁆ ≤ D.V ∧ ⁅A,D.V⁆ = ⊥ ∧ D.V ≤ D.S₂ g := by
  have hUT := h.U_normal_in_T.1
  obtain ⟨hI, he, hnorm, hindex, hgI⟩ := binary_source_inputs h b hUT g hgL hgN
  obtain ⟨hN, hE, σ, d, hS, hprod, hVE, hES, hVC, hVN, hEN, hEC, _⟩ :=
    D.binary_source_clauses_three_to_seven h b hUT h.frattini_U_le_point
      g hgL hgN hI (binarySourceCoreEquiv h b hUT g hgL hgN) hnorm hindex
  let A := conjugate (D.W g) g
  have hAS : A ≤ D.S g := le_sup_right.trans hS.ge
  have hAI : A ≤ D.I g := hAS.trans (pCoreIn_le 2 _)
  have hUS : D.U ≤ normalizer (D.S g : Set G) :=
    le_sup_left.trans (D.binary_core_normalized g)
  have hAU : ⁅A,D.U⁆ ≤ D.W g :=
    le_inf (le_normalizer_iff_commutator_le_right.mp (hAS.trans hnorm))
      ((commutator_mono hAS le_rfl).trans (le_normalizer_iff_commutator_le_left.mp hUS))
  have hSW : D.S g ≤ normalizer (D.W g : Set G) :=
    (le_inf hnorm (D.S g).le_normalizer).trans inf_normalizer_le_normalizer_inf
  have hSg : conjugate (D.S g) g = D.S g :=
    mem_normalizer_iff_map_conj_eq.mp
      ((normalizer (D.S g : Set G)).inv_mem (D.binary_core_normalized g hgI))
  have hSA : D.S g ≤ normalizer (A : Set G) := by
    have hh := (map_mono (f := (MulAut.conj g⁻¹).toMonoidHom) hSW).trans
      ((D.W g).le_normalizer_map (MulAut.conj g⁻¹).toMonoidHom)
    change conjugate (D.S g) g ≤ normalizer (A : Set G) at hh
    rwa [hSg] at hh
  have hAW : ⁅A,D.W g⁆ ≤ D.S₂ g := by
    rw [D.binary_marked_intersection g hgI hES]
    exact le_inf (le_normalizer_iff_commutator_le_right.mp (hAS.trans hSW))
      (le_normalizer_iff_commutator_le_left.mp (inf_le_right.trans hSA))
  have hAE : ⁅A,D.S₂ g⁆ ≤ D.V := by
    rw [commutator_comm]
    exact (commutator_mono le_rfl hAI).trans hEC
  have hAV : ⁅A,D.V⁆ = ⊥ := commutator_eq_bot_iff_le_centralizer.mpr
    (hAS.trans (le_centralizer_iff.mp (hVC.trans inf_le_right)))
  exact ⟨hAU,hAW,hAE,hAV,hVE⟩

-- The original image of the middle layer has codimension one more than the actor rank.
theorem binary_opposite_middle_codimension (h : D.Hypothesis) (b : D.BinaryNaturalData)
    (g : G) (hgL : g ∈ D.L) (hgN : g ∉ D.G₁) :
    let E := ((conjugate (D.W g) g).subgroupOf D.H).map (projection h)
    Module.finrank (ZMod 2) ((conjugationSection h).imageSpace (D.S₂ g)) +
      (rank E + 1) = Module.finrank (ZMod 2) (Additive (moduleSubgroup h)) := by
  obtain ⟨he,hi⟩ := binary_opposite_image h b g hgL hgN
  let E := ((conjugate (D.W g) g).subgroupOf D.H).map (projection h)
  let : IsElementaryAbelian 2 E := he
  have hcard : Nat.card E = 2 ^ rank E := by
    unfold rank
    obtain ⟨m,hm⟩ := (IsElementaryAbelian.isPGroup 2 E).exists_card_eq
    rw [hm, Nat.log_pow (by decide : 1 < 2)]
  have hVE := (binary_opposite_commutator_filtration h b g hgL hgN).2.2.2.2
  apply (conjugationSection h).imageSpace_codimension_of_index (D.S₂ g)
    inf_le_left (h.point_le.trans hVE) (rank E + 1)
  change (D.S₂ g).relIndex D.U = 2 * Nat.card E at hi
  rw [hi,hcard,pow_succ,Nat.mul_comm]


private theorem displacement_mem_imageSpace
    (h : D.Hypothesis) (A B C : Subgroup G) (hc : ⁅A,B⁆ ≤ C)
    (a : D.H) (ha : (a : G) ∈ A)
    (v : Additive (moduleSubgroup h)) (hv : v ∈ (conjugationSection h).imageSpace B) :
    displacement (representation h) (projection h a) v ∈
      (conjugationSection h).imageSpace C := by
  let c := conjugationSection h
  obtain ⟨u,hu,rfl⟩ := (c.mem_imageSpace_iff B v).mp hv
  let w : D.U := (⟨(a:G)*u*(a:G)⁻¹,
    (mem_normalizer_iff.mp (c.normalized a.property) u).mp u.property⟩ : D.U)*u⁻¹
  apply (c.mem_imageSpace_iff C _).mpr
  refine ⟨w,hc (commutator_mem_commutator ha hu),?_⟩
  change (c.coordinates (_ * u⁻¹)).toAdd = _
  rw [map_mul,map_inv]
  change (c.coordinates ⟨(a:G)*u*(a:G)⁻¹,_⟩).toAdd + -(c.coordinates u).toAdd = _
  rw [c.equivariant]
  exact (sub_eq_add_neg _ _).symm

theorem binary_opposite_third_displacement (h : D.Hypothesis) (b : D.BinaryNaturalData)
    (g : G) (hgL : g ∈ D.L) (hgN : g ∉ D.G₁) :
    let E := ((conjugate (D.W g) g).subgroupOf D.H).map (projection h)
    ∀ a ∈ E, ∀ b ∈ E, ∀ c ∈ E, ∀ v : Additive (moduleSubgroup h),
      displacement (representation h) a (displacement (representation h) b
        (displacement (representation h) c v)) ∈
          (conjugationSection h).imageSpace D.V := by
  intro E a ha a' ha' a'' ha'' v
  obtain ⟨a,ha,rfl⟩ := ha
  obtain ⟨a',ha',rfl⟩ := ha'
  obtain ⟨a'',ha'',rfl⟩ := ha''
  obtain ⟨hAU,hAW,hAE,_,_⟩ := binary_opposite_commutator_filtration h b g hgL hgN
  apply displacement_mem_imageSpace h _ _ _ hAE a ha
  apply displacement_mem_imageSpace h _ _ _ hAW a' ha'
  exact (conjugationSection h).displacement_range_le_imageSpace_of_commutator_le
    _ _ hAU a'' ha'' ⟨v,rfl⟩

theorem binary_opposite_fourth_displacement (h : D.Hypothesis) (b : D.BinaryNaturalData)
    (g : G) (hgL : g ∈ D.L) (hgN : g ∉ D.G₁) :
    let E := ((conjugate (D.W g) g).subgroupOf D.H).map (projection h)
    ∀ a ∈ E, ∀ b ∈ E, ∀ c ∈ E, ∀ e ∈ E,
      ∀ v : Additive (moduleSubgroup h),
      displacement (representation h) a (displacement (representation h) b
        (displacement (representation h) c (displacement (representation h) e v))) = 0 := by
  intro E a ha a' ha' a'' ha'' a''' ha''' v
  obtain ⟨a,ha,rfl⟩ := ha
  have hAV := (binary_opposite_commutator_filtration h b g hgL hgN).2.2.2.1
  exact sub_eq_zero.mpr ((conjugationSection h).fixed_on_imageSpace_of_commutator_le
    _ _ (hAV.le.trans bot_le) a ha _
    (binary_opposite_third_displacement h b g hgL hgN a' ha' a'' ha'' a''' ha''' v))


theorem binary_opposite_strict_cubic_of_middle_fixed
    (h : D.Hypothesis) (b : D.BinaryNaturalData)
    (g : G) (hgL : g ∈ D.L) (hgN : g ∉ D.G₁)
    (hfix : ⁅conjugate (D.W g) g,D.S₂ g⁆ ≤ D.V₁)
    (hm : 1 < rank (((conjugate (D.W g) g).subgroupOf D.H).map (projection h))) :
    cubicRatio (representation h) < 2 := by
  let E := ((conjugate (D.W g) g).subgroupOf D.H).map (projection h)
  let σ := representation h
  let c := conjugationSection h
  obtain ⟨he,_⟩ := binary_opposite_image h b g hgL hgN
  have hn : E ≠ ⊥ := by
    intro hh
    have hh' : rank E = 0 := by simp [rank,hh]
    change 1 < rank E at hm
    omega
  have hE : IsElementaryTwo E := ⟨hn,he⟩
  have hfixed : c.imageSpace (D.S₂ g) ≤ fixedSpace σ E := by
    intro v hv a₀
    obtain ⟨a,ha,heq⟩ := a₀.property
    change σ (a₀ : Actor h) v = v
    rw [←heq]
    exact c.fixed_on_imageSpace_of_commutator_le _ _ hfix a ha v hv
  have hdim := binary_opposite_middle_codimension h b g hgL hgN
  have hcodim := fixedCodim_add_finrank σ E
  have hle := Submodule.finrank_mono hfixed
  have hsmall : fixedCodim σ E < 2 * rank E := by
    change Module.finrank (ZMod 2) (c.imageSpace (D.S₂ g)) + (rank E + 1) = _ at hdim
    change 1 < rank E at hm
    omega
  have hAU := (binary_opposite_commutator_filtration h b g hgL hgN).1
  have hAW := (binary_opposite_commutator_filtration h b g hgL hgN).2.1
  have hcubic : IsCubic σ E := by
    intro a ha a' ha' a'' ha'' v
    obtain ⟨a,ha,rfl⟩ := ha
    obtain ⟨a',ha',rfl⟩ := ha'
    obtain ⟨a'',ha'',rfl⟩ := ha''
    apply sub_eq_zero.mpr
    apply c.fixed_on_imageSpace_of_commutator_le _ _ hfix a ha
    apply displacement_mem_imageSpace h _ _ _ hAW a' ha'
    exact c.displacement_range_le_imageSpace_of_commutator_le _ _ hAU a'' ha'' ⟨v,rfl⟩
  have hr : actionRatio σ E < 2 := by
    have h0 : (rank E : ℝ≥0∞) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hE.rank_pos)
    rw [actionRatio, ENNReal.div_lt_iff (Or.inl h0) (Or.inl (by simp))]
    exact_mod_cast hsmall
  exact (iInf_le_of_le E (iInf_le_of_le ⟨hE,hcubic⟩ le_rfl)).trans_lt hr

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.CubicEscape.SpanAction
