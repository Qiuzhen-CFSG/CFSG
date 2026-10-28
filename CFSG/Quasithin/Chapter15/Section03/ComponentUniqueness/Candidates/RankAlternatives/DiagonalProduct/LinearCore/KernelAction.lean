module

public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.Candidates.RankAlternatives.DiagonalProduct.LinearCore.ActionLift
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.Candidates.RankAlternatives.DiagonalProduct.LinearCore.KernelAction.Setup
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.Candidates.RankAlternatives.DiagonalProduct.LinearCore.KernelAction.ModuloCenter
public import Mathlib.GroupTheory.Transfer

/-!
# Central errors in the linear centralizer-kernel action

Put X = θ(M ∩ L) and A = O²(Y₊ ∩ L). The source theta identity puts
X in Y₊ ∩ L, and two-perfectness puts X in A. Suppose XZ(L) has odd
index in L. Transfer from the perfect group L to XZ(L)/X is trivial.
On Z(L) it is the index-power map; since Z(L) is a two-group, that map
is injective. Thus Z(L) lies in X, and hence in A.

Consequently an action bound [C_{Y₊}(L), y] ≤ Z(L) gives the requested
bound into A. The centerless case needs no Sylow coverage calculation.
This does not require y to fix Z(L), and retains nontrivial central
two-covers. The original transfer and conditional action APIs remain available.

For the actual marked source branch, the earlier Borel construction proves
O₂(A) = S ∩ L. The component theorem gives Z(L) = O₂(L), and relative
normality in I places this core in the actual Sylow subgroup S. Thus Z(L)
lies in A directly. `commutator_mem_of_linear_source` combines this deduction
with the proved modulo-centre action, retaining the same y, field and quotient
equivalence in both linear branches. Its explicit earlier local conclusions
are exactly those of `ModuloCenter.actionModuloCenter_of_source`; their source
assembly remains with the parent. No central containment or Sylow-coverage
certificate is an input to this source bound.

Source: Aschbacher--Smith, combined manuscript (1 March 2004), final
paragraph of 15.3.37, printed p.1135, with 15.3.11(6),(8). The earlier-input
Borel and centre argument follows the strategy on printed p.1136 without
assuming a conclusion of 15.3.38--40. The transfer argument uses the ordinary
group-theoretic transfer map.
-/

public section

open Subgroup Theory.GroupTheory
open scoped IsMulCommutative commutatorElement MatrixGroups

namespace CFSG.Quasithin.Chapter15.Section03.Candidates.LinearCore.KernelAction

private theorem center_le_of_odd_index_sup {K : Type*} [Group K] [Finite K]
    [Group.IsPerfect K] (D : Subgroup K)
    (hZ : IsPGroup 2 (center K)) (hindex : Nat.Coprime 2 (D ⊔ center K).index) :
    center K ≤ D := by
  let B := D ⊔ center K
  have hn : B ≤ normalizer (D : Set K) :=
    sup_le D.le_normalizer (center_le_normalizer _)
  let N := D.subgroupOf B
  let : N.Normal := normal_subgroupOf_of_le_normalizer hn
  let q := QuotientGroup.mk' N
  let f : center K →* B ⧸ N := q.comp (inclusion (show center K ≤ B from le_sup_right))
  have hf : Function.Surjective f := by
    intro x
    obtain ⟨b, rfl⟩ := QuotientGroup.mk'_surjective N x
    obtain ⟨d, hd, z, hz, he⟩ := mem_sup_of_normal_right.mp b.property
    refine ⟨⟨z, hz⟩, ?_⟩
    have hde : q ⟨d, mem_sup_left hd⟩ = 1 := (QuotientGroup.eq_one_iff _).mpr hd
    have hb : b = (⟨d, mem_sup_left hd⟩ : B) * ⟨z, mem_sup_right hz⟩ :=
      Subtype.ext he.symm
    rw [hb, map_mul, hde, one_mul]
    rfl
  let : IsMulCommutative (B ⧸ N) := ⟨⟨by
    intro x y
    obtain ⟨a, rfl⟩ := hf x
    obtain ⟨b, rfl⟩ := hf y
    rw [← map_mul, ← map_mul, mul_comm a b]⟩⟩
  have hQ : IsPGroup 2 (B ⧸ N) := hZ.of_surjective f hf
  intro z hz
  let zB : B := ⟨z, mem_sup_right hz⟩
  have ht : MonoidHom.transfer q z = q zB ^ B.index := by
    rw [MonoidHom.transfer_eq_pow]
    · rw [← map_pow]
      rfl
    · intro k g _
      rw [mul_assoc, ← (mem_center_iff.mp ((center K).pow_mem hz k) g),
        inv_mul_cancel_left]
  have ht1 : MonoidHom.transfer q z = 1 :=
    Abelianization.commutator_subset_ker (MonoidHom.transfer q)
      (Group.IsPerfect.mem_commutator)
  have hd : orderOf (q zB) ∣ B.index := orderOf_dvd_of_pow_eq_one (ht.symm.trans ht1)
  have he : q zB = 1 := orderOf_eq_one_iff.mp
    (Nat.eq_one_of_dvd_coprimes (hQ.orderOf_coprime hindex (q zB)) dvd_rfl hd)
  exact (show zB ∈ N from (QuotientGroup.eq_one_iff zB).mp he)

variable {G : Type*} [Group G] [Finite G]

private theorem center_isTwoGroup {I L : Subgroup G} (hLI : L ≤ I)
    (hL : IsComponent I (L.subgroupOf I)) (hodd : pPrimeCore 2 I = ⊥) :
    IsPGroup 2 (center L) := by
  have h : IsPGroup 2 (center (L.subgroupOf I)) := by
    rw [component_center_eq_twoCore hL hodd]
    exact pCore_isPGroup
  exact h.of_equiv (centerCongr (subgroupOfEquivOfLe hLI))

/-- Cubic Sylow coverage absorbs the full central two-cover into A.
Centerless models need no such calculation. This disjunction is a remaining
model/root calculation, not a field of `SourceSetup`. -/
theorem center_le_componentPart {d : CharacteristicTwo.LocalData G}
    {I L : Subgroup G} (h : SourceSetup d I L)
    (hcenter : center L = ⊥ ∨ CentralSylowCoverage d.M L) :
    (center L).map L.subtype ≤ componentPart d.Yplus L := by
  rcases hcenter with htrivial | hcover
  · rw [htrivial, Subgroup.map_bot]
    exact bot_le
  let eL := subgroupOfEquivOfLe h.component_le
  let := h.component.2
  let : Group.IsPerfect L := Group.IsPerfect.ofSurjective
    (f := eL.toMonoidHom) eL.surjective
  have hcentral := center_le_of_odd_index_sup ((theta (d.M ⊓ L)).subgroupOf L)
    (center_isTwoGroup h.component_le h.component h.odd_core) hcover
  have hXL : theta (d.M ⊓ L) ≤ L := (theta_le _).trans inf_le_right
  have hXY : theta (d.M ⊓ L) ≤ d.Yplus := by
    rw [← h.theta_eq]
    exact theta_mono (inf_le_inf_left d.M h.component_le)
  have hXA : theta (d.M ⊓ L) ≤ componentPart d.Yplus L := by
    rw [componentPart, ComponentIntersection.twoResidualAmbient_eq_map_pResidual]
    have hmono := embedded_pResidual_mono 2 (le_inf hXY hXL)
    rwa [(pResidual_eq_top_iff _ _).mpr (ComponentIntersection.theta_isPPerfect _),
      ← MonoidHom.range_eq_map, range_subtype] at hmono
  rintro z ⟨x, hx, rfl⟩
  exact hXA (hcentral hx)

/-- The final kernel bound conditional on its two independent local outputs.
The element y is unchanged; in particular its action on Z(L) need not be trivial. -/
theorem commutator_mem_of_source {d : CharacteristicTwo.LocalData G}
    {I L : Subgroup G} (h : SourceSetup d I L)
    (hcenter : center L = ⊥ ∨ CentralSylowCoverage d.M L) (y : G)
    (hmod : ActionModuloCenter d.Yplus L y) :
    ∀ c ∈ d.Yplus, c ∈ centralizer (L : Set G) →
      ⁅c, y⁆ ∈ componentPart d.Yplus L := by
  intro c hc hcl
  exact center_le_componentPart h hcenter (hmod c hc hcl)

open DiagonalOuter.CoverReduction

/-- The constructed Borel core absorbs the entire component centre. Relative
normality puts O₂(L) in the actual S, so Z(L) ≤ S ∩ L = O₂(A) ≤ A.
No centre or Sylow-coverage conclusion is assumed. -/
theorem center_le_componentPart_of_marked_source
    {d : CharacteristicTwo.LocalData G} {I L : Subgroup G}
    (h : SourceSetup d I L) (earlier : LocalCover.SourceBorel.Earlier d)
    {n : ℕ} (hnpos : 0 < n) (heven : Even n)
    (c : ProjectiveMarking L (2 ^ n)) (y : d.Yplus) (hy : c.Diagonal (y : G)) :
    (center L).map L.subtype ≤ componentPart d.Yplus L := by
  obtain ⟨b⟩ := LocalCover.SourceBorel.orientedBorelData_of_marked_source
    h.outside h.component_le h.component h.rank_component h.rank_yplus
    earlier hnpos heven c y.property hy
  have hnormal := LocalCover.rank_two_component_normal_in h.component_le h.component
    h.odd_core h.rank_overgroup h.rank_component
  have hIL := (normal_subgroupOf_iff_le_normalizer h.component_le).mp hnormal
  have hZ := LocalCover.center_eq_twoCore_in h.component_le h.component h.odd_core
  obtain ⟨P, hP⟩ := h.sylow
  have hZS : (center L).map L.subtype ≤ d.S := by
    rw [hZ]
    exact (pCoreIn_mono_of_normalizes h.component_le hIL).trans
      (hP ▸ pCoreIn_le_sylow I P)
  have hZSL : (center L).map L.subtype ≤ d.S ⊓ L :=
    le_inf hZS (map_subtype_le _)
  exact (hZSL.trans b.component_core.ge).trans (pCoreIn_le 2 _)

/-- The requested centralizer-kernel bound for both original linear branches,
with the same actor, coefficient field, quotient equivalence and diagonal
matrix. This discharges the kernel premise of `cover_of_action_image`.

The retained earlier inputs are the uniform local conclusions in
`SourceBorel.Earlier`, 15.3.11(3), the full 15.3.7 alternatives and residual
image, 15.3.8, and C_V(Y)=1 from the natural residual action. Centre containment
and the modulo-centre bound are both deductions from these inputs. -/
theorem commutator_mem_of_linear_source
    {d : CharacteristicTwo.LocalData G} {I L : Subgroup G}
    (h : SourceSetup d I L) (earlier : LocalCover.SourceBorel.Earlier d)
    (hn : d.Yplus ≤ normalizer (L : Set G)) (y : d.Yplus) (hy : orderOf y = 3)
    {F : Type} [Field F] [Finite F]
    (hcase : (∃ n : ℕ, 0 < n ∧ Even n ∧ ClassicalGroup.IsPSL L 3 (2 ^ n) ∧
      Nat.card F = 2 ^ n) ∨ Nat.card F = 4)
    (e : (L ⧸ pCore 2 L) ≃* PSL(3,F))
    (α : MulAut L) (δ : Matrix.GeneralLinearGroup (Fin 3) F)
    (hconj : ConjugationOn L (y : G) α)
    (houter : Matrix.PSL3.OuterSolvable.linearConj F δ ∉ MulAut.innerSubgroup PSL(3,F))
    (hcompat : ∀ x : L, e (QuotientGroup.mk' (pCore 2 L) (α x)) =
      Matrix.PSL3.OuterSolvable.linearConj F δ (e (QuotientGroup.mk' (pCore 2 L) x)))
    (hchoice : Chapter4.UniqueMaximalOvergroup (d.Y ⊔ d.S) d.M →
      d.Yplus = Stellmacher.twoResidualAmbient (d.Y ⊓ centralizer (d.V₁ : Set G)) →
      normalizer (d.V₁ : Set G) ≤ d.M ∧ normalizer (d.V₂ : Set G) ≤ d.M)
    (h7 : ThreeAlternatives.ElementaryAlternative d.M d.Mc d.V ∨
      ThreeAlternatives.ExtraspecialAlternative d.M d.Mc d.V d.action)
    (himage7 : d.action.image d.Y =
      Stellmacher.twoResidualAmbient (⊤ : Subgroup OrthogonalActor))
    (hΩ : centralOmegaIn d.S ≤ d.V)
    (hVY : d.V ⊓ centralizer (d.Y : Set G) = ⊥) :
    ∀ z ∈ d.Yplus, z ∈ centralizer (L : Set G) →
      ⁅z, (y : G)⁆ ∈ componentPart d.Yplus L := by
  have hmod := ModuloCenter.actionModuloCenter_of_source h earlier hn y hy hcase
    e α δ hconj houter hcompat hchoice h7 himage7 hΩ hVY
  have hyG : orderOf (y : G) = 3 := (Subgroup.orderOf_coe y).trans hy
  have hZ : (center L).map L.subtype ≤ componentPart d.Yplus L := by
    rcases hcase with ⟨n, hnpos, heven, _, hF⟩ | hF
    · let c : ProjectiveMarking L (2 ^ n) := ⟨F, hF, e⟩
      exact center_le_componentPart_of_marked_source h earlier hnpos heven c y
        ⟨hyG, δ, houter, α, hconj, hcompat⟩
    · let c : ProjectiveMarking L (2 ^ 2) := ⟨F, hF, e⟩
      exact center_le_componentPart_of_marked_source h earlier (by decide) (by decide) c y
        ⟨hyG, δ, houter, α, hconj, hcompat⟩
  intro z hz hzL
  exact hZ (hmod z hz hzL)

end CFSG.Quasithin.Chapter15.Section03.Candidates.LinearCore.KernelAction
