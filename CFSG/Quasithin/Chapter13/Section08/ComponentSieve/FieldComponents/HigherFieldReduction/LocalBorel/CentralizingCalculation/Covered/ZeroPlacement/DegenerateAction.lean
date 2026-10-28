module

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.LocalBorel.CentralizingCalculation.Covered.ZeroPlacement.Reduction
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.Components.Swapped.LinearTwo.BorelDiagonal.SourceBorel

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.LocalBorel.CentralizingCalculation.Covered.ZeroPlacement.DegenerateAction.NaturalKernel

/-!
# Two-core reductions for the degenerate covered intersection

Write D = L₁, X = L₁,+ and Z = L₀. The actual marked direct product
in D/O₂(D) puts X ∩ Z in O₂(D). If O²(D ∩ BX) = X, monotonicity
and two-perfectness then show that Z ∩ BX is a two-group. Consequently
[B,Z] lies in both O₂(B) and O₂(Z). The branch also makes X normal
relative to BD; Z is already normal there by the central-preimage
construction. No ambient normality is asserted.

The branch is exactly equivalent to failure of Z ≤ BX. The overlap theta
identity puts every order-three element of BX in X, giving m₃(BX) = 1
and m₃(B) ≤ 1. Conversely, the genuine elementary order-nine quotient
of D shows that Z ≤ BX is equivalent to m₃(BX) ≥ 2. Thus the remaining
branch has rank one; a rank-two Borel suffices only when that rank has
actually been proved for the model. These deductions retain the possible surviving two-cores and do not prove that K* normalizes
Z* in H/O₂(H). That additional higher-field action calculation remains
open; in particular, two-core containment of [B,Z] is not centralization
of its star image. The re-exported `NaturalKernel` calculation identifies
the full covered action kernel with C_{BL₁}(V) and proves
[BL₁,L₀] ≤ O₂(L), retaining the distinction between O₂(L) and O₂(H).

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
Notation 13.2.1 and 13.2.2(3), printed p.877; 13.7.3(9), p.936;
the local Borel calculation in 13.8.20, p.954/PDF p.971.
-/

@[expose] public section
open Subgroup
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.LocalBorel.CentralizingCalculation.Covered.ZeroPlacement.DegenerateAction
open CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.LinearThree.Geometry.CoveredProduct.ResidualPlacement
open LocalAction
universe u v
variable {G : Type u} [Group G] [Finite G]

omit [Finite G] in
private theorem residual_eq_bot_of_isTwoGroup (A : Subgroup G) (hp : IsPGroup 2 A) :
    residual A = ⊥ := by
  have hr : pResidual 2 A = ⊥ := le_antisymm
    (sInf_le ⟨inferInstance, hp.to_quotient ⊥⟩) bot_le
  simp only [LinearThree.Geometry.CoveredProduct.ResidualPlacement.residual, hr,
    Subgroup.map_bot]

private theorem isTwoGroup_of_residual_eq_bot (A : Subgroup G)
    (hr : residual A = ⊥) : IsPGroup 2 A := by
  have hp : pResidual 2 A = ⊥ := by
    apply (map_injective A.subtype_injective)
    rw [Subgroup.map_bot]
    exact hr
  exact (isPGroup_quotient_pResidual (G := A) 2).of_equiv
    ((QuotientGroup.quotientMulEquivOfEq hp).trans QuotientGroup.quotientBot)

/-- The two source factors meet only in the intrinsic two-core of L₁. -/
theorem plus_inf_zero_le_twoCore (L T V V₁ V₃ : Subgroup G)
    (a : NaturalSetup L T V V₁ V₃)
    (hfactor : one L T V₁ = plus L T V₁ ⊔ zero L) :
    plus L T V₁ ⊓ zero L ≤ (one L T V₁).pCoreIn 2 := by
  let D := one L T V₁
  have hd : Disjoint (Source.starImage D (zero L))
      (Source.starImage D (plus L T V₁)) := by
    simpa only [zeroCoreMap, plusCoreMap, localCoreMap_range] using
      a.marks_disjoint hfactor
  intro x hx
  let xD : D := ⟨x, plus_le_one L T V₁ a.line_stable hx.1⟩
  have hq : QuotientGroup.mk' (pCore 2 D) xD = 1 := by
    exact (disjoint_iff_inf_le.mp hd) ⟨⟨xD, hx.2, rfl⟩, ⟨xD, hx.1, rfl⟩⟩
  exact ⟨xD, (QuotientGroup.eq_one_iff _).mp hq, rfl⟩

/-- The degenerate branch removes the odd part of the central intersection.
It does not remove its possible two-core. -/
theorem zero_intersection_isTwoGroup (L T V V₁ V₃ J : Subgroup G)
    (a : NaturalSetup L T V V₁ V₃)
    (hfactor : one L T V₁ = plus L T V₁ ⊔ zero L)
    (hdegenerate : residual (one L T V₁ ⊓ J) = plus L T V₁) :
    IsPGroup 2 (zero L ⊓ J : Subgroup G) := by
  let I := zero L ⊓ J
  have hrX : residual I ≤ plus L T V₁ := by
    rw [← hdegenerate]
    exact embedded_pResidual_mono 2
      (inf_le_inf (zero_le_one_of_factorization L T V₁ hfactor) le_rfl)
  have hrQ : residual I ≤ (one L T V₁).pCoreIn 2 :=
    (le_inf hrX ((residual_le I).trans inf_le_left)).trans
      (plus_inf_zero_le_twoCore L T V V₁ V₃ a hfactor)
  have hp : IsPGroup 2 (residual I) := (isPGroup_pCoreIn 2 _).to_le hrQ
  have hr : residual (residual I) = residual I := by
    change (pResidual 2 (residual I)).map (residual I).subtype = residual I
    rw [(pResidual_eq_top_iff 2 _).mpr (residual_isPPerfect I),
      ← MonoidHom.range_eq_map, range_subtype]
  exact isTwoGroup_of_residual_eq_bot I
    (hr.symm.trans (residual_eq_bot_of_isTwoGroup _ hp))

variable {T : Sylow 2 G} {H K L V V₁ V₂ V₃ M G₁ : Subgroup G}
  [(Source.starImage H K).Normal] {n : ℕ} {unitary four : Bool}
  (d : SourceContext.{u,v} T H K L V V₁ V₂ V₃ M G₁ n unitary four)
  (a : NaturalSetup L (T : Subgroup G) V V₁ V₃)
  (hfactor : one L (T : Subgroup G) V₁ = plus L (T : Subgroup G) V₁ ⊔ zero L)

/-- The degenerate intersection is characteristic under the Borel product,
so the whole product normalizes X. -/
theorem product_normalizes_plus
    (hdegenerate : residual (one L (T : Subgroup G) V₁ ⊓
      (d.B ⊔ plus L (T : Subgroup G) V₁)) = plus L (T : Subgroup G) V₁) :
    d.B ⊔ one L (T : Subgroup G) V₁ ≤
      normalizer (plus L (T : Subgroup G) V₁ : Set G) := by
  apply sup_le
  · rw [← hdegenerate]
    exact ((le_inf (le_sup_left.trans (Covered.product_normalizes_one d))
      (le_sup_left.trans (d.B ⊔ plus L (T : Subgroup G) V₁).le_normalizer)).trans
        inf_normalizer_le_normalizer_inf).trans (normalizer_le_residual_normalizer _)
  · exact one_normalizes_plus L (T : Subgroup G) V₁

/-- The actual Borel product already normalizes the central mark, before
the higher-field calculation under K*. -/
theorem product_normalizes_zero : d.B ⊔ one L (T : Subgroup G) V₁ ≤
    normalizer (zero L : Set G) :=
  d.product_normalizes_L.trans (normalizer_le_zero_normalizer L)

include a hfactor in
/-- Specialization to the literal source Borel. -/
theorem source_zero_intersection_isTwoGroup
    (hdegenerate : residual (one L (T : Subgroup G) V₁ ⊓
      (d.B ⊔ plus L (T : Subgroup G) V₁)) = plus L (T : Subgroup G) V₁) :
    IsPGroup 2 (zero L ⊓ (d.B ⊔ plus L (T : Subgroup G) V₁) : Subgroup G) :=
  zero_intersection_isTwoGroup L (T : Subgroup G) V V₁ V₃ _ a hfactor hdegenerate

include a hfactor in
/-- In the branch, the Borel commutator with the central residual is a
two-group normal in each factor. Neither intrinsic two-core is discarded. -/
theorem borel_zero_commutator_le_twoCores
    (hdegenerate : residual (one L (T : Subgroup G) V₁ ⊓
      (d.B ⊔ plus L (T : Subgroup G) V₁)) = plus L (T : Subgroup G) V₁) :
    ⁅d.B, zero L⁆ ≤ d.B.pCoreIn 2 ⊓ (zero L).pCoreIn 2 := by
  have hZB : zero L ≤ normalizer (d.B : Set G) :=
    (zero_le_one_of_factorization L (T : Subgroup G) V₁ hfactor).trans
      (le_sup_left.trans d.borel_normalized)
  have hBZ : d.B ≤ normalizer (zero L : Set G) :=
    le_sup_left.trans (product_normalizes_zero d)
  have hCB : ⁅d.B, zero L⁆ ≤ d.B :=
    le_normalizer_iff_commutator_le_left.mp hZB
  have hCZ : ⁅d.B, zero L⁆ ≤ zero L := by
    rw [commutator_comm]
    exact le_normalizer_iff_commutator_le_left.mp hBZ
  have hp : IsPGroup 2 (⁅d.B, zero L⁆ : Subgroup G) :=
    (source_zero_intersection_isTwoGroup d a hfactor hdegenerate).to_le
      (le_inf hCZ (hCB.trans le_sup_left))
  exact le_inf
    (le_pCoreIn_of_normalizes hp hCB (normalizer_commutator_ge_left _ _))
    (le_pCoreIn_of_normalizes hp hCZ (normalizer_commutator_ge_right _ _))

include a hfactor in
/-- The residual branch is exactly the failure of central placement, not a
stronger replacement for that failure. -/
theorem degenerate_iff_not_zero_le_product :
    residual (one L (T : Subgroup G) V₁ ⊓
      (d.B ⊔ plus L (T : Subgroup G) V₁)) = plus L (T : Subgroup G) V₁ ↔
      ¬ zero L ≤ d.B ⊔ plus L (T : Subgroup G) V₁ := by
  constructor
  · intro hdegenerate hz
    have hp := source_zero_intersection_isTwoGroup d a hfactor hdegenerate
    rw [inf_eq_left.mpr hz] at hp
    have hq := hp.to_quotient (pCore 2 (zero L))
    obtain ⟨k, hk⟩ := hq.exists_card_eq
    rw [a.zero_core_card] at hk
    have hd : 3 ∣ 2 ^ k := hk ▸ dvd_rfl
    exact (by decide : ¬ 3 ∣ 2) (Nat.prime_three.dvd_of_dvd_pow hd)
  · exact source_intersection_residual_of_not_zero d a hfactor

/-- Every cubic element of BX belongs to the plus residual in the degenerate branch.
The membership in L₁ is obtained from the literal overlap theta identity. -/
theorem threes_mem_plus
    (hdegenerate : residual (one L (T : Subgroup G) V₁ ⊓
      (d.B ⊔ plus L (T : Subgroup G) V₁)) = plus L (T : Subgroup G) V₁)
    {g : G} (hg : g ∈ d.B ⊔ plus L (T : Subgroup G) V₁)
    (ho : orderOf g = 3) : g ∈ plus L (T : Subgroup G) V₁ := by
  have hXD := plus_le_one L (T : Subgroup G) V₁ d.standing.line_stable
  have hgJ : g ∈ d.B ⊔ one L (T : Subgroup G) V₁ :=
    (sup_le_sup le_rfl hXD) hg
  have hgD : g ∈ one L (T : Subgroup G) V₁ := by
    rw [d.theta_product]
    exact subset_closure ⟨hgJ, ho⟩
  let I := one L (T : Subgroup G) V₁ ⊓ (d.B ⊔ plus L (T : Subgroup G) V₁)
  let gI : I := ⟨g, hgD, hg⟩
  have hr : gI ∈ pResidual 2 I := mem_pResidual_of_orderOf_coprime (by
    rw [← Subgroup.orderOf_coe gI]
    change Nat.Coprime 2 (orderOf g)
    rw [ho]
    decide)
  rw [← hdegenerate]
  exact ⟨gI, hr, rfl⟩

include a hfactor in
/-- The degenerate product has exactly three-rank one. Its upper bound comes
from all cubic elements, and positivity from the genuine cubic X quotient. -/
theorem product_threeRank_eq_one
    (hdegenerate : residual (one L (T : Subgroup G) V₁ ⊓
      (d.B ⊔ plus L (T : Subgroup G) V₁)) = plus L (T : Subgroup G) V₁) :
    primeRank 3 (d.B ⊔ plus L (T : Subgroup G) V₁ : Subgroup G) = 1 := by
  let X := plus L (T : Subgroup G) V₁
  have hup : primeRank 3 (d.B ⊔ X : Subgroup G) ≤ 1 :=
    (Components.Swapped.LinearTwo.threeRank_le_of_contains_threes _ _
      (fun g hg ho => threes_mem_plus d hdegenerate hg ho)).trans
      (Components.Swapped.LinearTwo.rank_le_one_of_cubic_core_quotient X
        (a.plus_core_card hfactor))
  have hpos : primeRank 3 X ≠ 0 := by
    intro he
    have hd : 3 ∣ Nat.card X := by
      have hxcard : Nat.card (X ⧸ pCore 2 X) = 3 := a.plus_core_card hfactor
      rw [← hxcard]
      exact (pCore 2 X).card_quotient_dvd_card
    exact PrimeRank.eq_zero_iff_not_dvd_card.mp he hd
  have hlo : primeRank 3 X ≤ primeRank 3 (d.B ⊔ X : Subgroup G) :=
    Theory.GroupTheory.primeRank_le_of_injective 3
      (inclusion (le_sup_right : X ≤ d.B ⊔ X)) (inclusion_injective _)
  change primeRank 3 (d.B ⊔ X : Subgroup G) = 1
  omega

include a hfactor in
/-- Any actual Borel with three-rank at least two excludes the branch. -/
theorem borel_threeRank_le_one
    (hdegenerate : residual (one L (T : Subgroup G) V₁ ⊓
      (d.B ⊔ plus L (T : Subgroup G) V₁)) = plus L (T : Subgroup G) V₁) :
    primeRank 3 d.B ≤ 1 := by
  rw [← product_threeRank_eq_one d a hfactor hdegenerate]
  exact Theory.GroupTheory.primeRank_le_of_injective 3
    (inclusion (le_sup_left : d.B ≤ d.B ⊔ plus L (T : Subgroup G) V₁))
    (inclusion_injective _)

include a hfactor in
private theorem two_le_one_threeRank :
    2 ≤ primeRank 3 (one L (T : Subgroup G) V₁) := by
  let D := one L (T : Subgroup G) V₁
  let Q := D ⧸ pCore 2 D
  let : IsMulCommutative Q := a.one_quotient_commutative hfactor
  let : CommGroup Q := IsMulCommutative.instCommGroup
  have hq : 2 ≤ primeRank 3 Q := primeRank_ge_of_elementary_embedding
    (a.one_quotient_cube hfactor)
    (show Nat.card Q = 3 ^ 2 from a.one_quotient_card hfactor)
    (MonoidHom.id Q) Function.injective_id
  exact hq.trans (primeRank_quotient_le_of_isTwoGroup 3 (by decide)
    (pCore 2 D) pCore_isPGroup)

include a hfactor in
/-- Placement is precisely the rank-two case of BX. The order-nine quotient
is used only after proving its actual exponent and retaining its two-core.
This equivalence does not assert that every higher-field Borel has rank two. -/
theorem zero_le_product_iff_two_le_threeRank :
    zero L ≤ d.B ⊔ plus L (T : Subgroup G) V₁ ↔
      2 ≤ primeRank 3 (d.B ⊔ plus L (T : Subgroup G) V₁ : Subgroup G) := by
  constructor
  · intro hz
    have hle : one L (T : Subgroup G) V₁ ≤ d.B ⊔ plus L (T : Subgroup G) V₁ := by
      rw [hfactor]
      exact sup_le le_sup_right hz
    exact (two_le_one_threeRank a hfactor).trans
      (Theory.GroupTheory.primeRank_le_of_injective 3 (inclusion hle) (inclusion_injective _))
  · intro hr
    by_contra hz
    have he := product_threeRank_eq_one d a hfactor
      (source_intersection_residual_of_not_zero d a hfactor hz)
    omega


end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.LocalBorel.CentralizingCalculation.Covered.ZeroPlacement.DegenerateAction
