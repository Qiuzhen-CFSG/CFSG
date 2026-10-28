module
public import CFSG.Quasithin.Chapter13.Section03.SourceCompletion.ParabolicControl.Source

/-!
# Strict rank for the original binary unitary module

The compatible full-automizer chart identifies the original three-space with
its standard model. The preceding nondegenerate-plane centralizer theorem and
maximal-escape action theorem force this three-space to have an escaping
centralizer if the rank is three. The proved parabolic control contradicts
that escape, giving r(G,V)>3. E.6.1 applicability is constructed on the same
module and quotient kernels. The two earlier geometric arguments remain
explicit named source obligations.

Source: Aschbacher--Smith, 13.3.12(2--3) and 13.3.17(2), pp.889--890,893;
E.6.11(2), pp.249--250, in the combined manuscript of 1 March 2004.
-/

public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section03.SourceCompletion
open ChapterE Atlas.G2.Natural.BinaryPointFlag
variable {G : Type*} [Group G] [Finite G] {V : Subgroup G}
  [IsElementaryAbelian 2 V]

omit [Finite G] in
/-- The full automizer chart is faithful because it intertwines the faithful
conjugation representation. -/
theorem unitary_chart_injective
    (rho : Automizer V →* Atlas.G2.Model F) (E : Additive V ≃ₗ[F] W)
    (he : ∀ a v, E (automizerRepresentation V a v) =
      Atlas.G2.Restricted.NaturalCoordinates.action F (rho a) (E v)) :
    Function.Injective rho := by
  intro a b hab
  apply automizerRepresentation_injective V
  apply LinearMap.ext
  intro v
  apply E.injective
  rw [he, he, hab]

omit [Finite G] in
/-- The original chosen three-space, not a newly selected flag, is the
standard three-space in its compatible coordinate chart. -/
theorem unitary_standard_three_eq
    (E : Additive V ≃ₗ[F] W) (R : Subgroup G) (hRV : R ≤ V)
    (hR : pointCoordinateSubspace E R = seed) :
    UnitaryGeometry.standardThree E = R := by
  have hseed : Atlas.G2.Natural.BinaryIsotropicThree.target false = seed := by
    ext x
    rw [mem_seed]
    rfl
  ext x
  constructor
  · intro hx
    let v : Additive V := Additive.ofMul ⟨x, UnitaryGeometry.standardThree_le E hx⟩
    have hw : E v ∈ seed := hseed ▸ (UnitaryGeometry.standardThree_space E).le
      (show E v ∈ (UnitaryGeometry.ambientSpace (UnitaryGeometry.standardThree E)).map
        E.toLinearMap from ⟨v,hx,rfl⟩)
    exact (mem_pointCoordinateSubspace E R v).mp (hR.symm ▸ hw)
  · intro hx
    let v : Additive V := Additive.ofMul ⟨x,hRV hx⟩
    have hw : E v ∈ Atlas.G2.Natural.BinaryIsotropicThree.target false :=
      hseed.symm ▸ hR ▸ (mem_pointCoordinateSubspace E R v).mpr hx
    obtain ⟨w,hw,hwe⟩ := (UnitaryGeometry.standardThree_space E).symm.le hw
    have hwv : w = v := E.injective hwe
    subst w
    exact hw

/-- Nondegenerate-plane control and the earlier maximal-escape action theorem
make the original three-space centralizer bound strict: r(G,V)>3. -/
theorem unitary_rank_gt_three_of_three_centralizer
    {Kc : GroupClass} {T : Sylow 2 G} {M : Subgroup G}
    (h : ChapterE.Section06.HypothesisE61 Kc T M V)
    (rho : Automizer V →* Atlas.G2.Model F) (E : Additive V ≃ₗ[F] W)
    (he : ∀ a v, E (automizerRepresentation V a v) =
      Atlas.G2.Restricted.NaturalCoordinates.action F (rho a) (E v))
    (hd : commutator (Atlas.G2.Model F) ≤ rho.range)
    (hFour : ∀ A : Subgroup G, A ≤ V → Nat.card A = 4 →
      ((UnitaryGeometry.markedForm E).restrict
        (UnitaryGeometry.ambientSpace (V := V) A)).Nondegenerate →
      centralizer (A : Set G) ≤ M)
    (hact : ∀ U ∈ ChapterE.Section06.obstructionFamily M V,
      (∀ X : Subgroup G, U < X → X ≤ V → centralizer (X : Set G) ≤ M) →
      1 < subgroupCorank V U →
      ∃ x ∈ M ⊓ centralizer (U : Set G), x ∉ centralizer (V : Set G))
    (R : Subgroup G) (hRV : R ≤ V)
    (hR : pointCoordinateSubspace E R = seed)
    (hC : centralizer (R : Set G) ≤ M) :
    (3 : ℕ∞) < globalR V := by
  have hlow : (3 : ℕ∞) ≤ globalR V :=
    UnitaryGeometry.natural_source_rank_reduction h E hFour
  apply lt_of_le_of_ne hlow
  intro heq
  have hescape := UnitaryGeometry.natural_source_standard_three_escape h E rho
    (unitary_chart_injective rho E he) he
    (fun g => hd g.property) hFour hact heq.symm
  exact hescape ((unitary_standard_three_eq E R hRV hR).symm ▸ hC)


/-- The nondegenerate-plane conclusion of original 13.3.12(2), expressed in
any chart of the actual natural module. It is a source obligation. -/
@[expose] def UnitaryPlaneCentralizers (V M : Subgroup G)
    [IsElementaryAbelian 2 V] : Prop :=
  ∀ (rho : Automizer V →* Atlas.G2.Model F) (E : Additive V ≃ₗ[F] W),
    (∀ a v, E (automizerRepresentation V a v) =
      Atlas.G2.Restricted.NaturalCoordinates.action F (rho a) (E v)) →
    commutator (Atlas.G2.Model F) ≤ rho.range →
    ∀ A : Subgroup G, A ≤ V → Nat.card A = 4 →
      ((UnitaryGeometry.markedForm E).restrict
        (UnitaryGeometry.ambientSpace (V := V) A)).Nondegenerate →
      centralizer (A : Set G) ≤ M

/-- The part of E.6.11(2) used to exclude the second isotropic three-space
orbit. This is an earlier-source obligation, not an assumed rank bound. -/
@[expose] def MaximalEscapeAction (V M : Subgroup G) : Prop :=
  ∀ U ∈ ChapterE.Section06.obstructionFamily M V,
    (∀ X : Subgroup G, U < X → X ≤ V → centralizer (X : Set G) ≤ M) →
    1 < subgroupCorank V U →
    ∃ x ∈ M ⊓ centralizer (U : Set G), x ∉ centralizer (V : Set G)

omit [IsElementaryAbelian 2 V] in
/-- Original 13.3.17(2), conditional on precisely the preceding plane and
maximal-escape source arguments. The marked three-space, E.6.1 applicability,
and parabolic control are all constructed on the original subgroups. -/
theorem unitary_rank_gt_three_of_earlier_geometry
    (D : ChapterF.Section09.Setup G) [IsElementaryAbelian 2 D.V]
    (e : inducedAutomizer D.V D.L ≃* Atlas.G2.Natural.BinaryNormalizer.Derived)
    (E0 : Additive D.V ≃ₗ[F] Atlas.G2.Natural.Space F)
    (he0 : ∀ (l : inducedAutomizer D.V D.L) v,
      E0 (automizerRepresentation D.V l v) =
        Atlas.G2.Natural.derivedAction F (e l) (E0 v))
    (hUV : D.Vplus ≤ D.V) (hZV : D.V₁ ≤ D.V)
    (hTZ : (D.T : Subgroup G) ≤ normalizer (D.V₁ : Set G))
    (hTU : (D.T : Subgroup G) ≤ normalizer (D.Vplus : Set G))
    (hZ : Nat.card D.V₁ = 2) (hU : Nat.card D.Vplus = 8)
    (hres : pResidual 2 D.L = ⊤)
    (hTL : (D.T : Subgroup G) ≤ normalizer (D.L : Set G))
    (hVLT : D.V ≤ D.LT) (hred : IsPReduced 2 (D.V.subgroupOf D.LT))
    (hsyl : (D.T : Subgroup G) ⊓ centralizer (D.V : Set G) = D.LT.pCoreIn 2)
    (hNL : normalizer (D.V : Set G) ≤ normalizer (D.L : Set G))
    (hfaith : D.L ⊓ centralizer (D.V : Set G) ≤ D.L.pCoreIn 2)
    (hu : ∀ N : Subgroup G, IsMaximalTwoLocal N → D.LT ≤ N →
      N = normalizer (D.L : Set G))
    (B : Subgroup G) (hBV : B ≤ D.V)
    (hTB : (D.T : Subgroup G) ≤ normalizer (B : Set G)) (hB : Nat.card B = 4)
    (hHfull : D.H = normalizer (D.V₁ : Set G)) (hm : ⁅D.QH,B⁆ ≠ ⊥)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hTI : ∀ g ∈ normalizer (D.L : Set G),
      D.V ⊓ D.V.map (MulAut.conj g).toMonoidHom = ⊥ ∨
      D.V.map (MulAut.conj g).toMonoidHom = D.V)
    (hplanes : UnitaryPlaneCentralizers D.V (normalizer (D.L : Set G)))
    (hact : MaximalEscapeAction D.V (normalizer (D.L : Set G))) :
    (3 : ℕ∞) < globalR D.V := by
  have hLTN : D.LT ≤ normalizer (D.V : Set G) :=
    (normal_subgroupOf_iff_le_normalizer hVLT).mp hred.normal
  have hVn : D.V ≠ ⊥ := by
    intro hv
    have hz : D.V₁ = ⊥ := le_bot_iff.mp (hv ▸ hZV)
    rw [hz, Subgroup.card_bot] at hZ
    omega
  have hE := unitary_source_E61 hG D.T D.L (normalizer (D.L : Set G)) hVn
    hVLT hLTN (sup_le D.L.le_normalizer hTL) hsyl hu hTI
  obtain ⟨rho,E,he,_,hd,_,_,hs⟩ := exists_unitary_flag_marking
    D.T D.L D.V₁ B D.Vplus (le_sup_left.trans hLTN) hNL e E0 he0
    (le_sup_right.trans hLTN) hZV hBV hUV hTZ hTB hTU hZ hB hU
  have hC := (unitary_original_parabolic_control D e E0 he0 hUV hZV hTZ hTU
    hZ hU hres hTL hVLT hred hNL hfaith B hBV hTB hB hHfull hm hTI).1
  have hd' : commutator (Atlas.G2.Model F) ≤ rho.range := hd.trans (map_le_range _ _)
  exact unitary_rank_gt_three_of_three_centralizer hE rho E he hd'
    (hplanes rho E he hd') hact D.Vplus hUV hs (hC.trans hNL)

end CFSG.Quasithin.Chapter13.Section03.SourceCompletion
