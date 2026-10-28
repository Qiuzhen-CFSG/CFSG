module

public import Stellmacher.Recognition.GTwoSixtyFourIndexTwo
public import Stellmacher.Recognition.GTwoSixtyFourCoreActions
public import Stellmacher.Recognition.GTwoSixtyFourSmallActions
public import Stellmacher.Recognition.GTwoSixtyFourPairNormalizerRigidity
public import ABG.ChapterII.Section1.ExtremalNormalizerControl
public import FeitThompson.BGsection6.Defs

/-!
# Normalizers preserve the order-64 G₂ involution partition

The canonical subgroup U is normal in the distinguished Sylow subgroup S.
Consequently an extremal normalizer whose conjugation image is a two-group
preserves U: its element fusion is already conjugacy in S. A subgroup X
contained in U also contributes no crossing of the partition.

For the remaining centric subgroups, the N₂ and trivial odd-core hypotheses
make the actual ambient normalizer solvable of characteristic two. These
reductions do not assert that a local vertex is a full ambient centralizer.
The centric classification and the small-subgroup two-core alternatives
reduce all remaining actions to the two vertex cores. The initial core is
controlled intrinsically. Pair normalizer rigidity identifies the second
core's full normalizer with its vertex, completing the ambient control.
Thus every extremal centric normalizer preserves membership in U on
involutions.

Source: Stellmacher (8.6)(a), `refs/latex/stellmacher-n-group.tex`, and the
extremal normalizer reduction in ABG, Chapter II §1, article p.11.
-/

namespace Stellmacher.Recognition

open BenderSuzuki.External BenderSuzuki.PFchapter1section1

private theorem normal_mem_iff_of_isConj
    {H : Type*} [Group H] (U : Subgroup H) [hU : U.Normal]
    {x y : H} (hxy : IsConj x y) : x ∈ U ↔ y ∈ U := by
  obtain ⟨g, rfl⟩ := isConj_iff.mp hxy
  constructor
  · exact fun hx => hU.conj_mem x hx g
  · intro hy
    simpa only [inv_mul_cancel_left, mul_assoc, inv_mul_cancel, mul_one] using
      hU.conj_mem' (g * x * g⁻¹) hy g

/-- Two-group automizers preserve the canonical subgroup on every element,
not just on involutions. -/
public theorem gTwo_card64_normalizer_preserves_transfer_of_range_isPGroup
    {G : Type*} [Group G] [Finite G] (data : GTwoTwoDerivedTypeData G)
    (hcard : Nat.card data.sylowIntersection = 64)
    (X : Subgroup G) (hX : HuppertExtremal data.sylowIntersection X)
    (hRange : IsPGroup 2 (Subgroup.normalizerMonoidHom (H := X)).range)
    (g : G) (hg : g ∈ Subgroup.normalizer (X : Set G))
    (x y : data.sylowIntersection) (hx : (x : G) ∈ X)
    (hxy : g⁻¹ * (x : G) * g = (y : G)) :
    x ∈ gTwoCard64TransferSubgroup data ↔ y ∈ gTwoCard64TransferSubgroup data := by
  let := (gTwo_card64_transfer_structure data hcard).1
  exact normal_mem_iff_of_isConj (gTwoCard64TransferSubgroup data)
    (ABG.extremal_normalizer_fusion_control_of_range_isPGroup
      data.sylowIntersection X hX hRange g hg x y hx hxy)

/-- A centric subgroup contained in the transfer subgroup cannot move an
element across its boundary. Centricity and extremality are not needed here. -/
public theorem gTwo_card64_normalizer_preserves_transfer_of_le
    {G : Type*} [Group G] [Finite G] (data : GTwoTwoDerivedTypeData G)
    (X : Subgroup G)
    (hle : X.subgroupOf (data.sylowIntersection : Subgroup G) ≤
      gTwoCard64TransferSubgroup data)
    (g : G) (hg : g ∈ Subgroup.normalizer (X : Set G))
    (x y : data.sylowIntersection) (hx : (x : G) ∈ X)
    (hxy : g⁻¹ * (x : G) * g = (y : G)) :
    x ∈ gTwoCard64TransferSubgroup data ↔ y ∈ gTwoCard64TransferSubgroup data := by
  have hy : (y : G) ∈ X := hxy ▸ ((Subgroup.mem_normalizer_iff''.mp hg) _).mp hx
  exact iff_of_true (hle hx) (hle hy)

/-- The ambient normalizer of a nontrivial subgroup of the supplied Sylow
has the full local structure furnished by the terminal hypotheses. -/
public theorem gTwo_card64_normalizer_local_structure
    {G : Type*} [Group G] [Finite G] (data : GTwoTwoDerivedTypeData G)
    (hN : IsNTwoGroup G)
    (hcore : ∀ V : Subgroup G, IsTwoLocal V → pPrimeCore 2 V = ⊥)
    (X : Subgroup G) (hXS : X ≤ (data.sylowIntersection : Subgroup G))
    (hXne : X ≠ ⊥) :
    Group.IsSolvable (Subgroup.normalizer (X : Set G)) ∧
      pPrimeCore 2 (Subgroup.normalizer (X : Set G)) = ⊥ ∧
      IsCharacteristicTwoType (Subgroup.normalizer (X : Set G)) := by
  have hXp : IsPGroup 2 X := data.sylowIntersection.isPGroup'.of_injective
    (Subgroup.inclusion hXS) (Subgroup.inclusion_injective hXS)
  have hlocal : IsTwoLocal (Subgroup.normalizer (X : Set G)) := ⟨X, hXne, hXp, rfl⟩
  exact ⟨hN _ hlocal, hcore _ hlocal,
    centralizer_pCore_le_pCore_of_pPrimeCore_eq_bot (hN _ hlocal) (hcore _ hlocal)⟩

/-- The small exceptions are controlled as soon as the two vertex cores are.
Their actual normalizer two-cores either supply the step immediately or have
order at least 32, where the centric classification applies again. -/
public theorem gTwo_card64_small_step_of_core_control
    {G : Type*} [Group G] [Finite G] (hN : IsNTwoGroup G)
    (hcore : ∀ V : Subgroup G, IsTwoLocal V → pPrimeCore 2 V = ⊥)
    (data : GTwoTwoDerivedTypeData G)
    (hcard : Nat.card data.sylowIntersection = 64)
    (hCore : GTwoCard64CoreControl data)
    (X : Subgroup G) (hX : HuppertExtremal data.sylowIntersection X)
    (hc : subgroupCentralizerIn (data.sylowIntersection : Subgroup G) X ≤ X)
    (hsmall : GTwoCard64SmallException X) :
    GTwoCard64NormalizerStep data X := by
  rcases gTwo_card64_small_core_alternative hN hcore data hcard X hX hc hsmall with
    hstep | hlarge
  · exact hstep
  · exact gTwo_card64_step_of_large_normalizerPCore data hcard hCore X hX hc hlarge

/-- All extremal centric actions reduce to the two vertex-core actions. -/
public theorem gTwo_card64_normalizer_step_of_core_control
    {G : Type*} [Group G] [Finite G] (hN : IsNTwoGroup G)
    (hcore : ∀ V : Subgroup G, IsTwoLocal V → pPrimeCore 2 V = ⊥)
    (data : GTwoTwoDerivedTypeData G)
    (hcard : Nat.card data.sylowIntersection = 64)
    (hCore : GTwoCard64CoreControl data)
    (X : Subgroup G) (hX : HuppertExtremal data.sylowIntersection X)
    (hc : subgroupCentralizerIn (data.sylowIntersection : Subgroup G) X ≤ X) :
    GTwoCard64NormalizerStep data X := by
  let := data.groupK
  let := data.finiteK
  by_cases hU : X.subgroupOf (data.sylowIntersection : Subgroup G) ≤
      gTwoCard64TransferSubgroup data
  · exact gTwo_card64_step_of_le_transfer data X hU
  by_cases haut : IsPGroup 2 (MulAut X)
  · exact gTwo_card64_step_of_range_isPGroup data hcard X hX (haut.to_subgroup _)
  rcases gTwo_card64_centric_classification data hcard X hX.1 hc haut hU with
    hEA | hCP | hQa | hQb
  · exact gTwo_card64_small_step_of_core_control hN hcore data hcard hCore
      X hX hc (Or.inl hEA)
  · exact gTwo_card64_small_step_of_core_control hN hcore data hcard hCore
      X hX hc (Or.inr hCP)
  · exact hCore X (Or.inl hQa) hX hc
  · exact hCore X (Or.inr hQb) hX hc

/-- The exact involution interface needed by centric fusion, conditional only
on the remaining second-core normalizer containment. The order of the image
involution follows from conjugacy and is not a separate assumption. -/
public theorem gTwo_card64_normalizer_preserves_transfer_of_next_normalizer_le
    {G : Type*} [Group G] [Finite G] (hN : IsNTwoGroup G)
    (hcore : ∀ V : Subgroup G, IsTwoLocal V → pPrimeCore 2 V = ⊥)
    (data : GTwoTwoDerivedTypeData G)
    (hcard : Nat.card data.sylowIntersection = 64) :
    letI := data.groupK
    letI := data.finiteK
    let Qb := (Later.QAt data.Γ data.criticalPath.firstStep).map data.embedding
    Subgroup.normalizer (Qb : Set G) ≤
      (Later.GAt data.Γ data.criticalPath.firstStep).map data.embedding ⊔
        Subgroup.centralizer (Qb : Set G) →
    ∀ X : Subgroup G, HuppertExtremal data.sylowIntersection X →
      subgroupCentralizerIn (data.sylowIntersection : Subgroup G) X ≤ X →
      ∀ g ∈ Subgroup.normalizer (X : Set G), ∀ x y : data.sylowIntersection,
        (x : G) ∈ X → g⁻¹ * (x : G) * g = (y : G) → orderOf x = 2 →
        (x ∈ gTwoCard64TransferSubgroup data ↔ y ∈ gTwoCard64TransferSubgroup data) := by
  let := data.groupK
  let := data.finiteK
  dsimp only
  intro hnext X hX hc g hg x y hx hxy hx2
  have hCore : GTwoCard64CoreControl data := by
    intro Y hY _ _ k hk u v _ _ hu huv
    exact gTwo_card64_core_normalizer_preserves_transfer_of_next_normalizer_le
      data hcard hnext Y hY k hk u v hu huv
  have hconj : IsConj (x : G) (y : G) :=
    isConj_iff.mpr ⟨g⁻¹, by simpa only [inv_inv] using hxy⟩
  have horder : orderOf x = orderOf y := by
    obtain ⟨c, hc⟩ := hconj
    simpa only [Subgroup.orderOf_coe] using hc.orderOf_eq (c : G)
  exact gTwo_card64_normalizer_step_of_core_control hN hcore data hcard hCore
    X hX hc g hg x y hx2 (horder.symm.trans hx2) hx hxy

/-- Every extremal centric normalizer preserves the canonical involution
partition. The full local pair supplies the second-core normalizer containment
needed by the centric classification and normalizer two-core reductions. -/
public theorem gTwo_card64_normalizer_preserves_transfer
    {G : Type*} [Group G] [Finite G] (hN : IsNTwoGroup G)
    (hcore : ∀ V : Subgroup G, IsTwoLocal V → pPrimeCore 2 V = ⊥)
    (data : GTwoTwoDerivedTypeData G)
    (hcard : Nat.card data.sylowIntersection = 64)
    (X : Subgroup G) (hX : HuppertExtremal data.sylowIntersection X)
    (hc : subgroupCentralizerIn (data.sylowIntersection : Subgroup G) X ≤ X)
    (g : G) (hg : g ∈ Subgroup.normalizer (X : Set G))
    (x y : data.sylowIntersection) (hx : (x : G) ∈ X)
    (hxy : g⁻¹ * (x : G) * g = (y : G)) (hx2 : orderOf x = 2) :
    x ∈ gTwoCard64TransferSubgroup data ↔ y ∈ gTwoCard64TransferSubgroup data := by
  exact gTwo_card64_normalizer_preserves_transfer_of_next_normalizer_le
    hN hcore data hcard (gTwo_card64_next_normalizer_le hN hcore data hcard)
    X hX hc g hg x y hx hxy hx2

end Stellmacher.Recognition
