module

public import Theory.GroupTheory.GeneralizedFitting.CentralizerViaCComponents
public import Theory.GroupTheory.GeneralizedFitting.SimpleTwoQuotient
public import Theory.GroupTheory.PResidual.NormalSubgroup


/-!
# Simple generalized Fitting subgroups and two-group extensions

A nonabelian simple generalized Fitting subgroup has trivial centralizer:
self-centralization places its centralizer in its trivial center. Consequently
the solvable radical and all prime cores vanish. If a Sylow two-subgroup
supplements it, the quotient is a two-group, and the layer, two-residual and
solvable residual are all the simple subgroup. Every nontrivial subgroup then
has full commutator with it, by the simple-component commutator dichotomy.

The normal-subgroup versions are also used after changing the ambient carrier
to an intrinsic subgroup or a radical quotient. All quotient normality here is
in the explicitly indicated ambient group.

Source: the standard generalized Fitting and component calculus, as recorded
in Aschbacher--Smith, *The Classification of Quasithin Groups*, A.3.3;
the application is the whole-group E.1.2(E2) case under the hypotheses on
F*(G) and G = LT in E.1.14, printed pp.210, 214 (1 March 2004 manuscript).
-/

public section

open Subgroup
namespace Theory.GroupTheory.SimpleSocle
variable {G : Type*} [Group G] [Finite G]

private theorem perfect_of_nonabelian {H : Type*} [Group H] [IsSimpleGroup H]
    (ha : ¬ IsMulCommutative H) : Group.IsPerfect H := by
  exact ⟨(IsSimpleGroup.eq_bot_or_eq_top_of_normal (_root_.commutator H)
    inferInstance).resolve_left (fun h => ha ((commutator_eq_bot_iff H).mp h))⟩

private theorem center_eq_bot {H : Type*} [Group H] [IsSimpleGroup H]
    (ha : ¬ IsMulCommutative H) : center H = ⊥ := by
  exact (IsSimpleGroup.eq_bot_or_eq_top_of_normal (center H) inferInstance).resolve_right
    (fun h => ha (center_eq_top_iff.mp h))

/-- A nonabelian simple generalized Fitting subgroup is an actual component. -/
theorem isComponent [IsSimpleGroup (generalizedFitting G)]
    (ha : ¬ IsMulCommutative (generalizedFitting G)) :
    IsComponent G (generalizedFitting G) := by
  let := perfect_of_nonabelian ha
  exact ⟨(inferInstance : (generalizedFitting G).Normal).isSubnormal,
    ⟨((QuotientGroup.quotientMulEquivOfEq (center_eq_bot ha)).trans
      QuotientGroup.quotientBot).isSimpleGroup⟩⟩

/-- The action on a nonabelian simple generalized Fitting subgroup is faithful. -/
theorem centralizer_eq_bot [IsSimpleGroup (generalizedFitting G)]
    (ha : ¬ IsMulCommutative (generalizedFitting G)) :
    centralizer (generalizedFitting G : Set G) = ⊥ := by
  apply le_bot_iff.mp
  intro x hx
  have hxL := centralizer_generalizedFitting_le G hx
  have hz : (⟨x, hxL⟩ : generalizedFitting G) ∈ center (generalizedFitting G) := by
    rw [mem_center_iff]
    intro y
    exact Subtype.ext (mem_centralizer_iff.mp hx y y.property)
  rw [center_eq_bot ha, mem_bot] at hz
  exact congrArg (fun y : generalizedFitting G => (y : G)) hz

/-- A faithful nonabelian simple normal subgroup forces the solvable radical to vanish. -/
theorem radical_eq_bot (L : Subgroup G) [L.Normal] [IsSimpleGroup L]
    [Group.IsPerfect L] (hC : centralizer (L : Set G) = ⊥) :
    solvableRadical G = ⊥ := by
  by_contra hR
  have hle := simple_normal_le_of_normal_ne_bot_of_centralizer_eq_bot L
    (Group.IsPerfect.not_isMulCommutative L) hC (solvableRadical G) hR
  have : Group.IsSolvable L :=
    Group.isSolvable_of_isSolvable_injective (inclusion_injective hle)
  exact Group.IsPerfect.not_isSolvable L this

/-- Every prime core of a finite radical-free group is trivial. -/
theorem pCore_eq_bot (hR : solvableRadical G = ⊥) (p : ℕ) [Fact p.Prime] :
    pCore p G = ⊥ := by
  let : Group.IsNilpotent (pCore p G) := pCore_isPGroup.isNilpotent
  exact le_bot_iff.mp ((le_solvableRadical (pCore p G) inferInstance inferInstance).trans hR.le)

/-- A normal quasisimple subgroup with two-group quotient is the layer and both residuals. -/
theorem layer_residuals (L : Subgroup G) [L.Normal] [IsQuasisimple L]
    (hq : IsPGroup 2 (G ⧸ L)) :
    componentLayer G = L ∧ pResidual 2 G = L ∧ solvableResidual G = L := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let : Group.IsNilpotent (G ⧸ L) := hq.isNilpotent
  have hL : IsComponent G L := ⟨(inferInstance : L.Normal).isSubnormal, inferInstance⟩
  refine ⟨le_antisymm ?_ (le_sSup hL), ?_,
    le_antisymm (solvableResidual_le_of_solvable_quotient L)
      (le_solvableResidual_of_isPerfect L)⟩
  · apply sSup_le
    intro K hK
    let := hK.2
    exact le_of_isPerfect_of_solvable_quotient K L
  · refine le_antisymm (show pResidual 2 G ≤ L from sInf_le ⟨inferInstance, hq⟩) ?_
    apply le_sInf
    rintro N ⟨hn, hN⟩
    let := hn
    let : Group.IsNilpotent (G ⧸ N) := hN.isNilpotent
    exact le_of_isPerfect_of_solvable_quotient L N

omit [Finite G] in
/-- Every nontrivial subgroup acts with full commutator on a faithful simple normal subgroup. -/
theorem commutator_eq (L : Subgroup G) [L.Normal] [IsSimpleGroup L]
    [Group.IsPerfect L] (hC : centralizer (L : Set G) = ⊥)
    (A : Subgroup G) (hA : A ≠ ⊥) : L = ⁅L, A⁆ := by
  rcases simple_subnormal_commutator_dichotomy L A
      (inferInstance : L.Normal).isSubnormal with hb | he
  · rw [commutator_comm] at hb
    exact (hA (le_bot_iff.mp ((commutator_eq_bot_iff_le_centralizer.mp hb).trans hC.le))).elim
  · simpa [Normal.map_conj_eq] using he.symm

/-- All structural identities for a simple generalized Fitting subgroup supplemented by a Sylow two-subgroup. -/
theorem structure_of_sylow_supplement [IsSimpleGroup (generalizedFitting G)]
    (ha : ¬ IsMulCommutative (generalizedFitting G))
    (T : Sylow 2 G) (hgen : generalizedFitting G ⊔ (T : Subgroup G) = ⊤) :
    centralizer (generalizedFitting G : Set G) = ⊥ ∧
      solvableRadical G = ⊥ ∧ pCore 2 G = ⊥ ∧
      componentLayer G = generalizedFitting G ∧
      pResidual 2 G = generalizedFitting G ∧
      solvableResidual G = generalizedFitting G ∧
      IsPGroup 2 (G ⧸ generalizedFitting G) := by
  let := (isComponent ha).2
  have hC := centralizer_eq_bot ha
  have hR := radical_eq_bot (generalizedFitting G) hC
  have hq := isPGroup_quotient_of_sup_eq_top (generalizedFitting G) T T.isPGroup' hgen
  obtain ⟨hE, hp, hs⟩ := layer_residuals (generalizedFitting G) hq
  exact ⟨hC, hR, pCore_eq_bot hR 2, hE, hp, hs, hq⟩

end Theory.GroupTheory.SimpleSocle
