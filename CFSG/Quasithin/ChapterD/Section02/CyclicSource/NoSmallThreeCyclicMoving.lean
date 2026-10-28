module
public import CFSG.Quasithin.ChapterD.Section02.CyclicSource.NoSmallThreeFamily
public import CFSG.Quasithin.ChapterD.Section02.CyclicSource.NoSmallThreeCyclicStructure
public import CFSG.Quasithin.ChapterD.Section02.CyclicSource.NoSmallThreeNineGeometry
public import Theory.Representation.BinaryPlaneCubicCentralizer

/-!
# A normal cubic factor in the moving-nine cyclic branch

When every minimum involution has a cubic commutator with the three-core,
a normal cubic factor of support different from four is central: each
involution centralizes it because its commutator cannot coincide with the
involution's four-space factor.

For the order-nine global commutator with three four-space factors, the
fixed-plane geometry supplies just such a central cubic with zero fixed
space. The kernel of the action on the three factors preserves their
spanning binary fixed planes, so the central cubic makes this kernel a
three-group. The three-point action theorem then supplies a normal
four-space factor, ready for the normal-cubic source endpoint.

Source: Aschbacher–Smith D.2.26 and D.2.28–29, pp.191–192. The final
interface retains the original source SQTK cover and local cyclic input.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender
namespace CFSG.Quasithin.ChapterD.CyclicSource
variable {G V : Type*} [Group G] [Finite G]
  [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  {ρ : Representation (ZMod 2) G V}

theorem CoreHypotheses.smallSupport_commutator_mem_fourSpaceThreeFactors
    (h : CoreHypotheses ρ) (hq : cubicRatio ρ = 2)
    (hfive : ∀ A ∈ QhatStar ρ, ⁅pCore 5 G,A⁆ = ⊥)
    (hNo : ∀ X : Subgroup G, X ≤ pCore 3 G → Nat.card X = 3 →
      Module.finrank (ZMod 2) (subspaceCommutator ρ ⊤ X) ≠ 2)
    {t : G} (ht : t ∈ smallSupportInvolutions ρ)
    (hcyc : Nat.card (⁅pCore 3 G,zpowers t⁆ : Subgroup G) = 3) :
    ⁅pCore 3 G,zpowers t⁆ ∈ fourSpaceThreeFactors ρ := by
  refine ⟨commutator_le_left _ _,hcyc,?_⟩
  rcases h.local_threeCore_alternatives hq hfive hNo ht with hc | hc
  · exact hc.2
  · have he := hc.2.1
    omega

theorem CoreHypotheses.normal_cubic_central_of_support_ne_four
    (h : CoreHypotheses ρ) (hq : cubicRatio ρ = 2)
    (hfive : ∀ A ∈ QhatStar ρ, ⁅pCore 5 G,A⁆ = ⊥)
    (hNo : ∀ X : Subgroup G, X ≤ pCore 3 G → Nat.card X = 3 →
      Module.finrank (ZMod 2) (subspaceCommutator ρ ⊤ X) ≠ 2)
    (hcyc : ∀ t ∈ smallSupportInvolutions ρ,
      Nat.card (⁅pCore 3 G,zpowers t⁆ : Subgroup G) = 3)
    (Z : Subgroup G) [Z.Normal] (hZR : Z ≤ pCore 3 G) (hZ : Nat.card Z = 3)
    (hW : Module.finrank (ZMod 2) (subspaceCommutator ρ ⊤ Z) ≠ 4) :
    Z ≤ center G := by
  have hcent : (⊤ : Subgroup G) ≤ centralizer (Z : Set G) := by
    rw [←h.smallSupport_generated]
    apply (closure_le _).mpr
    intro t ht
    have hcomm : ⁅Z,zpowers t⁆ = ⊥ := by
      by_contra hne
      have hCZ : ⁅Z,zpowers t⁆ ≤ Z := commutator_le_left _ _
      have hCF : ⁅Z,zpowers t⁆ ≤ ⁅pCore 3 G,zpowers t⁆ := commutator_mono hZR le_rfl
      have hcard : Nat.card (⁅Z,zpowers t⁆ : Subgroup G) = 3 := by
        have hd : Nat.card (⁅Z,zpowers t⁆ : Subgroup G) ∣ 3 := hZ ▸ card_dvd_of_le hCZ
        exact (Nat.prime_three.eq_one_or_self_of_dvd _ hd).resolve_left
          (fun hh => hne (card_eq_one.mp hh))
      have heZ : ⁅Z,zpowers t⁆ = Z := eq_of_le_of_card_ge hCZ (by rw [hcard,hZ])
      have heF : ⁅Z,zpowers t⁆ = ⁅pCore 3 G,zpowers t⁆ :=
        eq_of_le_of_card_ge hCF (by rw [hcard,hcyc t ht])
      have hdim := (h.smallSupport_commutator_mem_fourSpaceThreeFactors hq hfive hNo ht
        (hcyc t ht)).2.2
      exact hW ((congrArg (fun D => Module.finrank (ZMod 2) (subspaceCommutator ρ ⊤ D))
        (heZ.symm.trans heF)).trans hdim)
    have hc := le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hcomm)
    exact hc (mem_zpowers t)
  exact centralizer_eq_top_iff_subset.mp (top_unique hcent)

/-- The original source family has a normal member once its three fixed
planes and the omitted cubic factor have been identified. -/
theorem CoreHypotheses.normal_fourSpace_factor_of_three_planes
    (h : CoreHypotheses ρ) (hq : cubicRatio ρ = 2)
    (hfive : ∀ A ∈ QhatStar ρ, ⁅pCore 5 G,A⁆ = ⊥)
    (hNo : ∀ X : Subgroup G, X ≤ pCore 3 G → Nat.card X = 3 →
      Module.finrank (ZMod 2) (subspaceCommutator ρ ⊤ X) ≠ 2)
    (hcyc : ∀ t ∈ smallSupportInvolutions ρ,
      Nat.card (⁅pCore 3 G,zpowers t⁆ : Subgroup G) = 3)
    (hR : IsMulCommutative (pCore 3 G))
    (hcard : Nat.card (fourSpaceThreeFactorsIn ρ ⁅pCore 3 G,⊤⁆) = 3)
    (hspan : ⨆ D : fourSpaceThreeFactorsIn ρ ⁅pCore 3 G,⊤⁆,
      fixedSpace ρ D.val = ⊤)
    (hd : ∀ D ∈ fourSpaceThreeFactorsIn ρ ⁅pCore 3 G,⊤⁆,
      Module.finrank (ZMod 2) (fixedSpace ρ D) = 2)
    (Z : Subgroup G) [Z.Normal] (hZE : Z ≤ ⁅pCore 3 G,⊤⁆) (hZ : Nat.card Z = 3)
    (hW : Module.finrank (ZMod 2) (subspaceCommutator ρ ⊤ Z) ≠ 4)
    (hfix : fixedSpace ρ Z = ⊥) :
    ∃ D : Subgroup G, D ≤ ⁅pCore 3 G,⊤⁆ ∧ Nat.card D = 3 ∧
      Module.finrank (ZMod 2) (subspaceCommutator ρ ⊤ D) = 4 ∧ D.Normal := by
  have hZR := hZE.trans (commutator_le_left (pCore 3 G) ⊤)
  have hcentral := h.normal_cubic_central_of_support_ne_four hq hfive hNo hcyc
    Z hZR hZ hW
  obtain ⟨D,hD,hN⟩ := Representation.exists_normal_of_three_fixed_planes
    ρ h.faithful (fourSpaceThreeFactorsIn ρ ⁅pCore 3 G,⊤⁆) (by
      intro D hD g
      have hY : D ∈ fourSpaceThreeFactors ρ :=
        ⟨hD.1.trans (commutator_le_left _ _),hD.2⟩
      exact ⟨(map_mono hD.1).trans_eq (Normal.map_conj_eq _ g),
        (fourSpaceThreeFactors_conjugate ρ hY g).2⟩)
    hcard hspan hd (by
      intro D hD
      exact ((le_centralizer_iff_isMulCommutative.mpr hR).trans
        (centralizer_le (hD.1.trans (commutator_le_left _ _)))).trans
          (Subgroup.centralizer_le_normalizer _)) Z hZR hZ hcentral hfix
  exact ⟨D,hD.1,hD.2.1,hD.2.2,hN⟩

/-- In the order-nine branch, a three-member family of four-space cubic
actors contains a normal member. All action and geometry inputs come from
the original source hypotheses. -/
theorem Hypotheses.nine_three_factor_normal
    (h : Hypotheses ρ)
    {H : Type*} [Group H] [Finite H] {K : GroupClass} (hH : IsSQTK K H)
    (f : H →* G) (honto : Function.Surjective f)
    (hq : cubicRatio ρ = 2)
    (hfive : ∀ A ∈ QhatStar ρ, ⁅pCore 5 G,A⁆ = ⊥)
    (hNo : ∀ X : Subgroup G, X ≤ pCore 3 G → Nat.card X = 3 →
      Module.finrank (ZMod 2) (subspaceCommutator ρ ⊤ X) ≠ 2)
    (hcyc : ∀ t ∈ smallSupportInvolutions ρ,
      Nat.card (⁅pCore 3 G,zpowers t⁆ : Subgroup G) = 3)
    (hE9 : Nat.card (⁅pCore 3 G,⊤⁆ : Subgroup G) = 9)
    (hS3 : Nat.card (fourSpaceThreeFactorsIn ρ ⁅pCore 3 G,⊤⁆) = 3) :
    ∃ D : Subgroup G, D ≤ ⁅pCore 3 G,⊤⁆ ∧ Nat.card D = 3 ∧
      Module.finrank (ZMod 2) (subspaceCommutator ρ ⊤ D) = 4 ∧ D.Normal := by
  have hs := h.toCoreHypotheses.threeCore_structure_of_cyclic_commutators
    hH f honto hfive hcyc
  let : IsElementaryAbelian 3 (⁅pCore 3 G,⊤⁆ : Subgroup G) := hs.2.2
  obtain ⟨_,hd,hspan,Z,hZE,hZN,hZ,hW,hfix,_⟩ :=
    CoreHypotheses.nine_support_geometry ρ h.toCoreHypotheses
      (⁅pCore 3 G,⊤⁆ : Subgroup G) hE9
      (h.threeCore_commutator_fixed_eq_bot hq hfive hNo) hS3
  let : Z.Normal := hZN
  exact h.toCoreHypotheses.normal_fourSpace_factor_of_three_planes hq hfive hNo hcyc
    hs.1 hS3 hspan hd Z hZE hZ (by omega) hfix

end CFSG.Quasithin.ChapterD.CyclicSource
