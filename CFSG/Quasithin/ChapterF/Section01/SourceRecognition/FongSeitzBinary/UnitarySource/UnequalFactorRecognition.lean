module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.QuadrangleStructure.UnequalLinearRadicals
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.UnitarySource.QuadraticFactorOrderRecognition

/-!
# Unequal original linear factors and the binary U₄ row

The original PSL₂ quotient marks construct the full larger SL₂ actor,
both faithful local groups and both remainder-to-kernel containments.
For rotation four and strictly unequal field orders, the Frattini and
fixed-space estimates make the larger original two-core elementary,
force the smaller core to be nonabelian, and give both crossed-root
equations. The smaller core's derived subgroup has exactly the smaller
field order. Every transport uses the supplied full amalgam marking.

The larger field has order at most the square of the smaller. When the
smaller field is binary, this forces the larger field to have four
elements. The completed quadratic recognition therefore supplies the full
U₄(2) comparison without an assumed quadratic ratio or core structure.
Both endpoint squares, the whole Borel, both orientations and the literal
original quotient representatives are retained. Neither original factor
is assumed perfect.

The nonbinary unequal ratio, remaining rows and exhaustive seven-row
selection stay open. The earlier source producers still supply F.1.1,
the marked split quotient, rotation four and the actual linear factors.
UnequalFactorApplications uses the literal Chapter 12 preparation to
discharge F.1.1; this module does not assert unconditional Theorem D.

Source: DGS, Groups and Graphs (1985), (5.7), (11.6)--(11.7),
pp.173--175 and Theorem D, p.224; Fong--Seitz I (6A)(b), II (8B).
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
open Theory.SpecificGroups.ClassicalUnitary.RankTwoPresentation
namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.QuadrangleStructure
variable {G X : Type*} [Group G] [Group X]
  {L : Fin 2 → Subgroup G} {S : Subgroup G} {P : Fin 2 → Subgroup X}
  (Q : MarkedQuotient P)
  (mark : RankTwoAmalgam.Iso
    (RankTwoAmalgam.ofSubgroups (parabolic L S 0)
      (parabolic L S 0 ⊓ parabolic L S 1) (parabolic L S 1) inf_le_left inf_le_right)
    Q.standardAmalgam)
  (h : HypothesisF11 L S) (split : SplitData Q.tits)

include mark h split in
private theorem linear_models {F : Type*} [Field F] [Finite F] [CharP F 2]
    (i : Fin 2) (μ : ((L i) ⧸ pCore 2 (L i)) ≃* PSL(2,F)) :
    simpleRemainder Q split i ≤ localKernel Q i ∧
      Nonempty (rankOne Q split i ≃* SL(2,F)) ∧
      Nonempty (localGroup Q split i ≃* PSL(2,F)) := by
  let := h.finite_local i
  obtain ⟨T,hT⟩ := h.sylow i
  have hV := MarkedLocal.linear_remainder_le_kernel Q mark h split i T hT μ
  obtain ⟨f,hf,hk,_⟩ := MarkedLocal.linear_actor_quotient_of_factor Q mark h split i μ
  let : ((S ⊔ L i).subgroupOf (parabolic L S i)).Normal :=
    marked_sylow_factor_normal Q mark h split i
  obtain ⟨a,b,_,_⟩ := marked_linear_localGroup Q mark h split i
    (UnitarySource.actorReflection Q split i) hV _ (subgroupOf_mono _ le_sup_left) f hf hk
  exact ⟨hV,⟨a⟩,⟨b⟩⟩

include mark h split in
/-- The original unequal linear factors force an elementary larger core,
a nonabelian smaller core, both crossed-root equations and the quadratic
upper bound. No exact field ratio or source-core structure is assumed. -/
theorem marked_unequal_linear_structure
    {F k : Type*} [Field F] [Finite F] [CharP F 2]
    [Field k] [Finite k] [CharP k 2]
    (hm : rotationOrder Q = 4) (i j : Fin 2) (hij : i ≠ j)
    (μi : ((L i) ⧸ pCore 2 (L i)) ≃* PSL(2,F))
    (μj : ((L j) ⧸ pCore 2 (L j)) ≃* PSL(2,k))
    (hlt : Nat.card k < Nat.card F) :
    IsElementaryAbelian 2 ((parabolic L S i).pCoreIn 2) ∧
      ⁅(parabolic L S j).pCoreIn 2,(parabolic L S j).pCoreIn 2⁆ ≠ ⊥ ∧
      ⁅simpleRoot Q split j,rootAt Q split j (Q.simple i)⁆ = ⊥ ∧
      ⁅simpleRoot Q split i,rootAt Q split i (Q.simple j)⁆ = rootAt Q split j (Q.simple i) ∧
      Nat.card F ≤ Nat.card k ^ 2 ∧
      Nat.card (⁅(parabolic L S j).pCoreIn 2,(parabolic L S j).pCoreIn 2⁆ : Subgroup G) = Nat.card k := by
  obtain ⟨hVi,⟨μ⟩,⟨ξ⟩⟩ := linear_models Q mark h split i μi
  obtain ⟨hVj,_,⟨ν⟩⟩ := linear_models Q mark h split j μj
  let := Theory.AlgebraicGroup.TitsSystem.SourceBinary.QuadrangleStructure.unequal_linear_larger_remainder_elementary
    Q split hm i j hij hVi hVj μ ν hlt
  obtain ⟨hcomm,hcross,hbound⟩ :=
    Theory.AlgebraicGroup.TitsSystem.SourceBinary.QuadrangleStructure.unequal_linear_cross_roots
      Q split hm i j hij hVi hVj μ ν hlt
  have helem : IsElementaryAbelian 2 ((parabolic L S i).pCoreIn 2) := by
    have hinj : Function.Injective (MarkedLocal.endpointMap Q mark i) :=
      (Q.tits.standardParabolic {Q.simple i}).subtype_injective.comp
        (MarkedLocal.endpoint Q mark i).injective
    have he := IsElementaryAbelian.comap_of_injective (p := 2)
      (MarkedLocal.endpointMap Q mark i) hinj (simpleRemainder Q split i)
    rw [MarkedLocal.remainder_comap_of_containment Q mark split i hVi] at he
    let := he
    exact IsElementaryAbelian.map (parabolic L S i).subtype
  have hderived : Nat.card (⁅(parabolic L S j).pCoreIn 2,
      (parabolic L S j).pCoreIn 2⁆ : Subgroup G) = Nat.card k := by
    rw [←marked_remainder_derived_card Q mark h split j hVj,
      (Theory.AlgebraicGroup.TitsSystem.SourceBinary.QuadrangleStructure.remainder_derived_frattini
        Q split hm j i hij.symm hVj hVi
        (simpleRoot_elementary_of_linear Q split j ν)
        (simpleRoot_elementary_of_linear Q split i ξ)).1,hcross]
    exact (card_rightConjugate _ _).trans (GTwoSource.simpleRoot_card Q split j hVj ν)
  refine ⟨helem,?_,hcomm,hcross,hbound,hderived⟩
  intro hzero
  rw [hzero,Subgroup.card_bot] at hderived
  have := Finite.one_lt_card (α := k)
  omega

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.QuadrangleStructure

namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.UnitarySource
variable {G X F k : Type*} [Group G] [Group X]
  [Field F] [Finite F] [CharP F 2] [Field k] [Finite k] [CharP k 2]
  {L : Fin 2 → Subgroup G} {S : Subgroup G} {P : Fin 2 → Subgroup X}
  (Q : MarkedQuotient P)
  (mark : RankTwoAmalgam.Iso
    (RankTwoAmalgam.ofSubgroups (parabolic L S 0)
      (parabolic L S 0 ⊓ parabolic L S 1) (parabolic L S 1) inf_le_left inf_le_right)
    Q.standardAmalgam)
  (h : HypothesisF11 L S) (split : SplitData Q.tits)
  (hm : rotationOrder Q = 4) (i j : Fin 2) (hij : i ≠ j)
  (μi : ((L i) ⧸ pCore 2 (L i)) ≃* PSL(2,F))
  (μj : ((L j) ⧸ pCore 2 (L j)) ≃* PSL(2,k))
  (hlt : Nat.card k < Nat.card F) (hk : Nat.card k = 2)

include mark h split hm hij μi μj hlt hk in
/-- A binary smaller factor forces the exact quadratic field ratio; the
larger field order is derived from the actual split quadrangle. -/
theorem binary_unequal_factor_orders :
    Nat.card F = 4 ∧ Nat.card F = Nat.card k ^ 2 := by
  have hb := (QuadrangleStructure.marked_unequal_linear_structure
    Q mark h split hm i j hij μi μj hlt).2.2.2.2.1
  rw [hk] at hb hlt
  let := Fintype.ofFinite F
  obtain ⟨n,_,hn⟩ := FiniteField.card F 2
  have hF : Nat.card F = 2^(n : ℕ) := by simpa only [Nat.card_eq_fintype_card] using hn
  have hn' : 2 ≤ (n : ℕ) := by
    by_contra! hh
    have he := Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ))
      (show (n : ℕ) ≤ 1 by omega)
    rw [←hF] at he
    norm_num at he
    omega
  have hlow : 4 ≤ Nat.card F := by
    rw [hF]
    exact Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) hn'
  have he : Nat.card F = 4 := by norm_num at hb; omega
  exact ⟨he,by rw [he,hk]; norm_num⟩

include mark h split hm hij μi μj hlt hk in
/-- The binary unequal linear quadrangle has the full U₄(2) comparison,
without an assumed field ratio or original-core structure. -/
theorem marked_binary_unequal_unitaryFour_catalogue :
    Chapter6.Source.RankOneGeneric.Global.ConcreteAmalgamComparison
      (RankTwoAmalgam.ofSubgroups (parabolic L S 0)
        (parabolic L S 0 ⊓ parabolic L S 1) (parabolic L S 1) inf_le_left inf_le_right) :=
  marked_quadratic_factor_order_unitaryFour_catalogue Q mark h split hm i j hij μi μj
    (binary_unequal_factor_orders Q mark h split hm i j hij μi μj hlt hk).2

open BenderSuzuki.MatrixGroups
open Theory.SpecificGroups.ClassicalUnitary.UnitaryFourFlag
open Representation.OrthogonalFourMinus.FiniteModel
open UnitaryPresentation

include mark h split hm hij μi μj hlt hk in
/-- The U₄(2) equivalence induces both endpoint maps and the entire overlap
on the same quotient; no quadratic field-order premise remains. -/
theorem marked_binary_unequal_unitaryFour_comparison :
    ∃ (e : PSU (Field 1) (form (Field 1) (conjugation 1) (conjugation_involutive 1)) ≃* (X ⧸ Q.D))
      (c : RankTwoAmalgam.Iso
        (RankTwoAmalgam.ofSubgroups (parabolic L S 0)
          (parabolic L S 0 ⊓ parabolic L S 1) (parabolic L S 1) inf_le_left inf_le_right)
        (MarkedAmalgam.flag
          ((pointParabolicSU (Field 1) (form (Field 1) (conjugation 1) (conjugation_involutive 1))).map
            (project (Field 1) (form (Field 1) (conjugation 1) (conjugation_involutive 1))))
          ((planeParabolicSU (Field 1) (form (Field 1) (conjugation 1) (conjugation_involutive 1))).map
            (project (Field 1) (form (Field 1) (conjugation 1) (conjugation_involutive 1)))) j)),
      (∀ a : parabolic L S 0, (c.left a : PSU (Field 1) (form (Field 1) (conjugation 1) (conjugation_involutive 1))) =
        e.symm (mark.left a : X ⧸ Q.D)) ∧
      (∀ a : (parabolic L S 0 ⊓ parabolic L S 1 : Subgroup G),
        (c.middle a : PSU (Field 1) (form (Field 1) (conjugation 1) (conjugation_involutive 1))) =
          e.symm (mark.middle a : X ⧸ Q.D)) ∧
      (∀ a : parabolic L S 1, (c.right a : PSU (Field 1) (form (Field 1) (conjugation 1) (conjugation_involutive 1))) =
        e.symm (mark.right a : X ⧸ Q.D)) :=
  marked_quadratic_factor_order_unitaryFour_comparison Q mark h split hm i j hij μi μj
    (binary_unequal_factor_orders Q mark h split hm i j hij μi μj hlt hk).2 1 (by simpa using hk)

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.UnitarySource

namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.UnitarySource
open BenderSuzuki.MatrixGroups
open Theory.SpecificGroups.ClassicalUnitary.UnitaryFourFlag
open Representation.OrthogonalFourMinus.FiniteModel
open UnitaryPresentation
variable {G F k : Type*} [Group G]
  [Field F] [Finite F] [CharP F 2] [Field k] [Finite k] [CharP k 2]
  {L : Fin 2 → Subgroup G} {S : Subgroup G}
  (Q : SourceQuotient L S) (h : HypothesisF11 L S) (split : SplitData Q.tits)
  (hm : rotationOrder Q = 4) (i j : Fin 2) (hij : i ≠ j)
  (μi : ((L i) ⧸ pCore 2 (L i)) ≃* PSL(2,F))
  (μj : ((L j) ⧸ pCore 2 (L j)) ≃* PSL(2,k))
  (hlt : Nat.card k < Nat.card F) (hk : Nat.card k = 2)

include h split hm hij μi μj hlt hk in
/-- The complete comparison evaluates on the literal original quotient map
at both endpoints and at every element of the whole overlap. -/
theorem original_binary_unequal_unitaryFour_comparison :
    ∃ (e : PSU (Field 1) (form (Field 1) (conjugation 1) (conjugation_involutive 1)) ≃* ((generated L S) ⧸ Q.D))
      (c : RankTwoAmalgam.Iso
        (RankTwoAmalgam.ofSubgroups (parabolic L S 0)
          (parabolic L S 0 ⊓ parabolic L S 1) (parabolic L S 1) inf_le_left inf_le_right)
        (MarkedAmalgam.flag
          ((pointParabolicSU (Field 1) (form (Field 1) (conjugation 1) (conjugation_involutive 1))).map
            (project (Field 1) (form (Field 1) (conjugation 1) (conjugation_involutive 1))))
          ((planeParabolicSU (Field 1) (form (Field 1) (conjugation 1) (conjugation_involutive 1))).map
            (project (Field 1) (form (Field 1) (conjugation 1) (conjugation_involutive 1)))) j)),
      (∀ a : parabolic L S 0, (c.left a : PSU (Field 1) (form (Field 1) (conjugation 1) (conjugation_involutive 1))) =
        e.symm (Q.q ⟨a,parabolic_le_generated 0 a.property⟩)) ∧
      (∀ a : (parabolic L S 0 ⊓ parabolic L S 1 : Subgroup G),
        (c.middle a : PSU (Field 1) (form (Field 1) (conjugation 1) (conjugation_involutive 1))) =
          e.symm (Q.q ⟨a,parabolic_le_generated 0 a.property.1⟩)) ∧
      (∀ a : parabolic L S 1, (c.right a : PSU (Field 1) (form (Field 1) (conjugation 1) (conjugation_involutive 1))) =
        e.symm (Q.q ⟨a,parabolic_le_generated 1 a.property⟩)) :=
  original_quadratic_factor_order_unitaryFour_comparison Q h split hm i j hij μi μj
    (binary_unequal_factor_orders Q (originalMarkedIso Q) h split hm i j hij μi μj hlt hk).2
    1 (by simpa using hk)

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.UnitarySource
