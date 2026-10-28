module

public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.Candidates.RankAlternatives.DiagonalProduct.CoreRemoval
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.Candidates.RankAlternatives.DiagonalProduct.LinearCore.MatrixImage.SourceAssembly
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.Candidates.RankAlternatives.DiagonalProduct.LinearCore.KernelAction
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.Candidates.RankAlternatives.DiagonalProduct.LinearCore.ActionLift
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.Candidates.RankAlternatives.OuterActor
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.LocalData

/-!
# The linear diagonal core-cover assembly

The standing constructions are anchored by `CharacteristicTwo.LocalData`:
Y is the actual residual of the normal closure of O₂(M ∩ M_c), and Y₊
is one of the two choices in Hypothesis 15.3.10. Both choices lie in Y.
The selected ordinary component and O(I) = 1 supply its central two-core.
The rank-two bound makes its relative centralizer three-free.

`cover_of_local_action_image` combines these deductions with the lifting
argument in `ActionLift`. It retains the chosen actor and quotient
equivalence, including the nontrivial central two-cover of PSL₃(4).

`cover_of_source_coordinates` now discharges image generation using the
matrix-image source assembly and discharges the centralizer-kernel bound
using the earlier Borel and centre geometry. Both calculations use the
same field, quotient equivalence, conjugation and matrix.
`cover_of_linear_source` unpacks either original linear alternative once;
`product_of_linear_source` applies core cancellation to obtain the exact
product with the original actor.

The explicit inputs are the earlier local conclusions in
`MatrixImage.SourceSetup` and `LocalCover.SourceBorel.Earlier`, the
plane-normalizer clause of 15.3.11(3), the full alternatives and residual
image of 15.3.7, and the natural-module conclusions Ω₁(Z(S)) ≤ V and
C_V(Y) = 1. Their discharge belongs to the source-theorem parent. There
are no remaining Borel, root-action, image-generation or kernel-action
premises. No conclusion from 15.3.38--40 is used.

Source: Aschbacher--Smith, combined manuscript (1 March 2004), final
paragraph of 15.3.37, printed p.1135; 15.3.7, 15.3.10--12, pp.1122--1125.
-/

public section

open Subgroup Theory.GroupTheory
open scoped Pointwise commutatorElement

namespace CFSG.Quasithin.Chapter15.Section03.Candidates.LinearCore
variable {G H : Type*} [Group G] [Group H] [Finite G]

/-- The actual source constructions discharge the kernel/core and center hypotheses.
Image generation and kernel action remain the two independent local obligations. -/
theorem cover_of_local_action_image (d : CharacteristicTwo.LocalData G)
    {I L : Subgroup G} (hI : I ∈ d.Hplus)
    (hLI : L ≤ I) (hcomp : IsComponent I (L.subgroupOf I))
    (hodd : pPrimeCore 2 I = ⊥) (hLrank : 2 ≤ primeRank 3 L)
    (hIrank : primeRank 3 I ≤ 2)
    (hY : IsPGroup 3 (d.Y ⧸ pCore 2 d.Y))
    (hn : d.Yplus ≤ normalizer (L : Set G))
    (e : (L ⧸ pCore 2 L) ≃* H) (y : d.Yplus) (hy : orderOf y = 3)
    (himage : (quotientAction hn e).range ≤
      ((componentPart d.Yplus L).subgroupOf d.Yplus).map (quotientAction hn e) ⊔
        zpowers (quotientAction hn e y))
    (hkernel : ∀ c ∈ d.Yplus, c ∈ centralizer (L : Set G) →
      ⁅c, (y : G)⁆ ∈ componentPart d.Yplus L) :
    DiagonalCoreCover d.Y d.Yplus L y := by
  let eL := subgroupOfEquivOfLe hLI
  let := hcomp.2
  let : IsQuasisimple L := IsQuasisimple.of_mulEquiv eL
  have hcore : pCore 2 L ≤ center L := by
    intro x hx
    obtain ⟨z, hz, rfl⟩ := (pCore_map_iso 2 eL).symm ▸ hx
    apply mem_center_iff.mpr
    intro l
    have he := congrArg eL
      (mem_center_iff.mp ((component_center_eq_twoCore hcomp hodd).ge hz) (eL.symm l))
    change l * eL z = eL z * l
    simpa only [map_mul, eL.apply_symm_apply] using he
  have hYplus : d.Yplus ≤ d.Y := by
    rcases d.choice with h | ⟨_, h⟩
    · exact h.le
    · rw [h]
      exact (map_subtype_le _).trans inf_le_left
  exact cover_of_action_image hYplus hY (le_sup_left.trans hI.1.2) hn e hcore
    (local_centralizer_three_coprime hLI hcomp hodd hLrank hIrank)
    y hy himage hkernel

open DiagonalOuter.CoverReduction

omit [Finite G] in
private theorem kernelSetup {d : CharacteristicTwo.LocalData G}
    {I L : Subgroup G} (h : MatrixImage.SourceSetup d I L) :
    KernelAction.SourceSetup d I L :=
  { outside := h.outside
    sylow := h.sylow
    component_le := h.component_le
    component := h.component
    odd_core := h.odd_core
    component_outside := h.component_outside
    orbit_eq := h.orbit_eq
    rank_component := h.rank_component
    rank_yplus := h.rank_yplus
    rank_overgroup := h.rank_overgroup
    theta_eq := h.theta_eq
    normalizer_eq := h.normalizer_eq
    quotient_three := h.quotient_three
    yplus_quotient_three := h.yplus_quotient_three
    intersection_characteristic_two := h.intersection_characteristic_two
    residual_ne := h.residual_ne
    core_normalizes := h.core_normalizes
    component_cores_le := h.component_cores_le
    shadow := h.shadow
    characteristic_two_containment := h.characteristic_two_containment }

private theorem normalizes_of_source_setup {d : CharacteristicTwo.LocalData G}
    {I L : Subgroup G} (h : MatrixImage.SourceSetup d I L) :
    d.Yplus ≤ normalizer (L : Set G) := by
  have hnormal := LocalCover.rank_two_component_normal_in h.component_le h.component
    h.odd_core h.rank_overgroup h.rank_component
  exact (le_sup_left.trans h.outside.1.2).trans
    ((normal_subgroupOf_iff_le_normalizer h.component_le).mp hnormal)

/-- The two core-cover clauses in the original matrix coordinates. Both the
quotient-action image and the centralizer-kernel action are proved from the
earlier source conclusions, including the actual Sylow and O_{2,Φ} quotient. -/
theorem cover_of_source_coordinates {d : CharacteristicTwo.LocalData G}
    {I L : Subgroup G} (h : MatrixImage.SourceSetup d I L)
    (earlier : LocalCover.SourceBorel.Earlier d)
    (y : d.Yplus) (hy : orderOf y = 3)
    {F : Type} [Field F] [Finite F]
    (hcase : MatrixImage.LinearCase L (Nat.card F))
    (w : MatrixImage.DiagonalCoordinates L (y : G) F)
    (hchoice : Chapter4.UniqueMaximalOvergroup (d.Y ⊔ d.S) d.M →
      d.Yplus = Stellmacher.twoResidualAmbient (d.Y ⊓ centralizer (d.V₁ : Set G)) →
      normalizer (d.V₁ : Set G) ≤ d.M ∧ normalizer (d.V₂ : Set G) ≤ d.M)
    (h7 : ThreeAlternatives.ElementaryAlternative d.M d.Mc d.V ∨
      ThreeAlternatives.ExtraspecialAlternative d.M d.Mc d.V d.action)
    (himage7 : d.action.image d.Y =
      Stellmacher.twoResidualAmbient (⊤ : Subgroup OrthogonalActor))
    (hΩ : centralOmegaIn d.S ≤ d.V)
    (hVY : d.V ⊓ centralizer (d.Y : Set G) = ⊥) :
    DiagonalCoreCover d.Y d.Yplus L (y : G) := by
  have hn := normalizes_of_source_setup h
  have himage := MatrixImage.image_le_of_source_setup h hn y hy hcase w
  have hkernel := KernelAction.commutator_mem_of_linear_source (kernelSetup h) earlier
    hn y hy hcase w.e w.conjugation w.matrix w.conjugation_eq w.outer w.compatible
    hchoice h7 himage7 hΩ hVY
  exact cover_of_local_action_image d h.outside h.component_le h.component h.odd_core
    h.rank_component.ge h.rank_overgroup h.quotient_three hn w.e y hy himage hkernel

/-- The cover and core-action bound for precisely the two original linear
branches. The field-four case permits a nontrivial central two-cover, and
unpacking the diagonal witness preserves its actor and compatible equivalence. -/
theorem cover_of_linear_source {d : CharacteristicTwo.LocalData G}
    {I L : Subgroup G} (h : MatrixImage.SourceSetup d I L)
    (earlier : LocalCover.SourceBorel.Earlier d)
    {y : G} (hy : y ∈ d.Yplus) (hy3 : orderOf y = 3)
    (hlinear : (∃ n : ℕ, 0 < n ∧ Even n ∧ ClassicalGroup.IsPSL L 3 (2 ^ n) ∧
      LinearDiagonalOnTwoQuotient L y (2 ^ n)) ∨ LinearDiagonalOnTwoQuotient L y 4)
    (hchoice : Chapter4.UniqueMaximalOvergroup (d.Y ⊔ d.S) d.M →
      d.Yplus = Stellmacher.twoResidualAmbient (d.Y ⊓ centralizer (d.V₁ : Set G)) →
      normalizer (d.V₁ : Set G) ≤ d.M ∧ normalizer (d.V₂ : Set G) ≤ d.M)
    (h7 : ThreeAlternatives.ElementaryAlternative d.M d.Mc d.V ∨
      ThreeAlternatives.ExtraspecialAlternative d.M d.Mc d.V d.action)
    (himage7 : d.action.image d.Y =
      Stellmacher.twoResidualAmbient (⊤ : Subgroup OrthogonalActor))
    (hΩ : centralOmegaIn d.S ≤ d.V)
    (hVY : d.V ⊓ centralizer (d.Y : Set G) = ⊥) :
    DiagonalCoreCover d.Y d.Yplus L y := by
  have hmodel : ∃ q, MatrixImage.LinearCase L q ∧ LinearDiagonalOnTwoQuotient L y q := by
    rcases hlinear with ⟨n, hn, heven, hL, hdiag⟩ | hdiag
    · exact ⟨2 ^ n, Or.inl ⟨n, hn, heven, hL, rfl⟩, hdiag⟩
    · exact ⟨4, Or.inr rfl, hdiag⟩
  obtain ⟨q, hcase, hdiag⟩ := hmodel
  obtain ⟨F, hF, hfin, hcard, ⟨w⟩⟩ := MatrixImage.diagonalCoordinates_iff.mp hdiag
  have hfield : MatrixImage.LinearCase L (Nat.card F) := hcard.symm ▸ hcase
  have hy' : orderOf (⟨y, hy⟩ : d.Yplus) = 3 := by
    simpa only [Subgroup.orderOf_mk] using hy3
  exact cover_of_source_coordinates h earlier ⟨y, hy⟩ hy' hfield w
    hchoice h7 himage7 hΩ hVY

/-- The actual core-removal consumer: the earlier source inputs and either
linear branch give the exact product with the original order-three actor.
Two-perfectness follows from θ(M ∩ I) = Y₊; no core containment is assumed. -/
theorem product_of_linear_source {d : CharacteristicTwo.LocalData G}
    {I L : Subgroup G} (h : MatrixImage.SourceSetup d I L)
    (earlier : LocalCover.SourceBorel.Earlier d)
    {y : G} (hy : y ∈ d.Yplus) (hy3 : orderOf y = 3)
    (hlinear : (∃ n : ℕ, 0 < n ∧ Even n ∧ ClassicalGroup.IsPSL L 3 (2 ^ n) ∧
      LinearDiagonalOnTwoQuotient L y (2 ^ n)) ∨ LinearDiagonalOnTwoQuotient L y 4)
    (hchoice : Chapter4.UniqueMaximalOvergroup (d.Y ⊔ d.S) d.M →
      d.Yplus = Stellmacher.twoResidualAmbient (d.Y ⊓ centralizer (d.V₁ : Set G)) →
      normalizer (d.V₁ : Set G) ≤ d.M ∧ normalizer (d.V₂ : Set G) ≤ d.M)
    (h7 : ThreeAlternatives.ElementaryAlternative d.M d.Mc d.V ∨
      ThreeAlternatives.ExtraspecialAlternative d.M d.Mc d.V d.action)
    (himage7 : d.action.image d.Y =
      Stellmacher.twoResidualAmbient (⊤ : Subgroup OrthogonalActor))
    (hΩ : centralOmegaIn d.S ≤ d.V)
    (hVY : d.V ⊓ centralizer (d.Y : Set G) = ⊥) :
    (d.Yplus : Set G) = (componentPart d.Yplus L : Set G) * (zpowers y : Set G) := by
  have hcover := cover_of_linear_source h earlier hy hy3 hlinear
    hchoice h7 himage7 hΩ hVY
  have hperfect : IsPPerfect 2 d.Yplus :=
    h.theta_eq ▸ ComponentIntersection.theta_isPPerfect (d.M ⊓ I)
  exact hcover.product hperfect hy (normalizes_of_source_setup h)

end CFSG.Quasithin.Chapter15.Section03.Candidates.LinearCore
