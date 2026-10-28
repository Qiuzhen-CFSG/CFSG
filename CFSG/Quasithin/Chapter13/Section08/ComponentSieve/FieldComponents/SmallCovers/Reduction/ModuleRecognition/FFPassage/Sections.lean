module

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.SmallCovers.Reduction.ModuleRecognition.Inputs
public import Theory.Representation.CubicComponentFaithfulness
public import Theory.Representation.BinaryOffender.SectionOffender
public import Theory.Representation.BinaryOffender.EquivariantOffender
public import Theory.Representation.BinaryOffender.IrreducibleExistence
public import Theory.Representation.Quotient
public import Theory.Representation.RepEquiv

/-!
# Cubic faithful sections and the ratio-one equality case

The central generator has no fixed vectors, so an actual Irr⁺ member is an
irreducible submodule. If an offender stabilizes this member, the universal
irreducible input applies inside the generated overgroup. Ratio one forces
zero fixed codimension on the complementary quotient. Cubic faithfulness of
every proper quotient then forces the member to be the whole module.

This is the section argument for Aschbacher–Smith 13.8.21(2), printed p.956,
using B.4.2(8) (p.86) and the fixed-codimension comparison in F.9.18(6)
(pp.325–326). Stabilization of the chosen Irr⁺ member is explicit here; it
must be supplied by the genuine B.7.2(1), not by irreducible classification.
-/

@[expose] public noncomputable section

open Subgroup Representation Representation.BinaryOffender Atlas.Codes
open Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.SmallCovers.Reduction.ModuleRecognition.FFPassage
universe u v
variable {D : Type u} [Group D]
variable {V : Type v} [AddCommGroup V] [Module (ZMod 2) V]

/-- The assumed self-centralizing component and its actual central generator
identify the ambient centralizer with a subgroup of the cubic group. -/
theorem centralizer_le_zpowers (L : Subgroup D) (z : D)
    (hcent : centralizer (L : Set D) ≤ L)
    (hzcenter : zpowers z = (center L).map L.subtype) :
    centralizer (L : Set D) ≤ zpowers z := by
  rw [hzcenter]
  intro g hg
  refine ⟨⟨g, hcent hg⟩, ?_, rfl⟩
  exact mem_center_iff.mpr fun l => Subtype.ext (hg l l.property)

/-- Centralizer control and the cubic polynomial survive restriction to any
intermediate overgroup. Normality is relative to that overgroup. -/
theorem restricted_cubic_data (ρ : Representation (ZMod 2) D V)
    (L J : Subgroup D) (hLJ : L ≤ J) (z : D) (hzL : z ∈ L)
    (hzorder : orderOf z = 3)
    (hcent : centralizer (L : Set D) ≤ zpowers z) (hpoly : CubicPolynomial ρ z) :
    let zJ : J := ⟨z, hLJ hzL⟩
    orderOf zJ = 3 ∧
      centralizer (L.subgroupOf J : Set J) ≤ zpowers zJ ∧
      CubicPolynomial (ρ.comp J.subtype) zJ := by
  dsimp only
  refine ⟨(orderOf_injective J.subtype J.subtype_injective ⟨z, hLJ hzL⟩).symm.trans hzorder, ?_, hpoly⟩
  intro g hg
  have hc : (g : D) ∈ centralizer (L : Set D) := by
    intro l hl
    exact congrArg Subtype.val (hg ⟨l, hLJ hl⟩ hl)
  obtain ⟨n, hn⟩ := mem_zpowers_iff.mp (hcent hc)
  exact mem_zpowers_iff.mpr ⟨n, Subtype.ext hn⟩

/-- Every nonzero section carrying the cubic polynomial is faithful after
restriction to an intermediate overgroup. -/
theorem faithful_restriction [Nontrivial V]
    (ρ : Representation (ZMod 2) D V) (L : Subgroup D) [L.Normal]
    (eL : L ≃* HexEvenAutomorphisms) (J : Subgroup D) (hLJ : L ≤ J)
    (z : D) (hzL : z ∈ L) (hzorder : orderOf z = 3)
    (hcent : centralizer (L : Set D) ≤ zpowers z) (hpoly : CubicPolynomial ρ z) :
    Function.Injective (ρ.comp J.subtype) := by
  let : IsQuasisimple HexEvenAutomorphisms := Hexacode.even_isQuasisimple
  let : IsQuasisimple (L.subgroupOf J) :=
    IsQuasisimple.of_mulEquiv ((subgroupOfEquivOfLe hLJ).trans eL).symm
  obtain ⟨horder, hc, hp⟩ := restricted_cubic_data ρ L J hLJ z hzL hzorder hcent hpoly
  exact faithful_of_cubicPolynomial (ρ.comp J.subtype) (L.subgroupOf J)
    ⟨z, hLJ hzL⟩ hzL horder hc hp

/-- The component has no fixed vectors on a cubic module. -/
theorem component_fixedSpace_eq_bot (ρ : Representation (ZMod 2) D V)
    (L : Subgroup D) (z : D) (hzL : z ∈ L) (hpoly : CubicPolynomial ρ z) :
    fixedSpace ρ L = ⊥ := by
  apply bot_unique
  intro v hv
  exact hpoly.fixed_eq_zero (hv ⟨z, hzL⟩)

/-- With no component-fixed vectors the literal Irr⁺ quotient is its numerator,
so the numerator itself is irreducible. -/
theorem irrPlus_irreducible (ρ : Representation (ZMod 2) D V)
    (L : Subgroup D) (z : D) (hzL : z ∈ L) (hpoly : CubicPolynomial ρ z)
    (I : Submodule (ZMod 2) V) (hI : IsIrrPlus ρ L I) :
    IsIrreducible (invariantSubspace ρ L I hI.choose).toRepresentation := by
  let C := (fixedSpace ρ L).comap I.subtype
  have hC : C = ⊥ := by
    dsimp [C]
    rw [component_fixedSpace_eq_bot ρ L z hzL hpoly,
      Submodule.comap_bot, Submodule.ker_subtype]
  let q := C.mkQ
  have hq : Function.Bijective q :=
    ⟨(LinearMap.ker_eq_bot).mp (C.ker_mkQ.trans hC), C.mkQ_surjective⟩
  let e : (invariantSubspace ρ L I hI.choose).toRepresentation ≃ₗ
      centralQuotientRepresentation ρ L I hI.choose :=
    { LinearEquiv.ofBijective q hq with
      isIntertwining' := fun _ => LinearMap.ext fun _ => rfl }
  exact e.irreducible_of_euqiv hI.choose_spec.2

variable [Finite D] [FiniteDimensional (ZMod 2) V]

/-- A stabilized Irr⁺ member of an FF-module exhausts the module. This uses
faithfulness on its nonzero numerator and on every proper quotient, not an
assumption excluding reducible or strong FF-modules. -/
theorem irrPlus_eq_top_of_offender
    (ρ : Representation (ZMod 2) D V) (L : Subgroup D) [L.Normal]
    (eL : L ≃* HexEvenAutomorphisms) (inputs : IrreducibleInputs.{u,v} L)
    (z : D) (hzL : z ∈ L) (hzorder : orderOf z = 3)
    (hcent : centralizer (L : Set D) ≤ zpowers z) (hpoly : CubicPolynomial ρ z)
    (A : Subgroup D) (hA : IsOffender ρ A)
    (I : Submodule (ZMod 2) V) (hI : IsIrrPlus ρ L I)
    (hAI : A ≤ subspaceStabilizer ρ I) : I = ⊤ := by
  let J := L ⊔ A
  let τ := ρ.comp J.subtype
  let L₀ := L.subgroupOf J
  let A₀ := A.subgroupOf J
  have hJI : J ≤ subspaceStabilizer ρ I := sup_le hI.choose hAI
  let W : Subrepresentation τ := ⟨I, fun g _ hv => (hJI g.property _).2 hv⟩
  let : IsQuasisimple HexEvenAutomorphisms := Hexacode.even_isQuasisimple
  let : IsQuasisimple L₀ :=
    IsQuasisimple.of_mulEquiv ((subgroupOfEquivOfLe (show L ≤ J from le_sup_left)).trans eL).symm
  obtain ⟨horder, hc, hp⟩ := restricted_cubic_data ρ L J le_sup_left z hzL hzorder hcent hpoly
  have hW : W ≠ ⊥ := fun he => hI.ne_bot ρ (congrArg Subrepresentation.toSubmodule he)
  have hfaith := faithful_subrepresentation_of_cubicPolynomial τ L₀
    ⟨z, (show L ≤ J from le_sup_left) hzL⟩ hzL horder hc hp W hW
  have hi : IsIrreducible (W.toRepresentation.comp L₀.subtype) := by
    have hirr := irrPlus_irreducible ρ L z hzL hpoly I hI
    exact (irreducible_comp_surjective_iff
      (subgroupOfEquivOfLe (show L ≤ J from le_sup_left)).toMonoidHom
      (subgroupOfEquivOfLe (show L ≤ J from le_sup_left)).surjective
      (invariantSubspace ρ L I hI.choose).toRepresentation).mpr hirr
  have hmap : A₀.map J.subtype = A := map_subgroupOf_eq_of_le le_sup_right
  have helem : IsElementaryTwo A₀ := by
    let : IsElementaryAbelian 2 A := hA.1.2
    refine ⟨?_, IsElementaryAbelian.subgroupOf (show A ≤ J from le_sup_right)⟩
    intro hb
    apply hA.1.1
    rw [← hmap, hb, Subgroup.map_bot]
  have hcodim : fixedCodim τ A₀ = fixedCodim ρ A := by
    change Module.finrank (ZMod 2) (V ⧸ fixedSpace τ A₀) = _
    rw [fixedSpace_comp_map, hmap]
    rfl
  have hrank : rank A₀ = rank A := by
    rw [← rank_map_injective J.subtype J.subtype_injective, hmap]
  have hAw : IsOffender W.toRepresentation A₀ :=
    ⟨helem, (fixedCodim_subrepresentation_le τ W A₀).trans
      (by rw [hcodim, hrank]; exact hA.2)⟩
  have hratio := inputs.ff_ratio J le_sup_left W.toSubmodule _ hfaith hi ⟨A₀, hAw⟩
  have heq := (hAw.best_and_codim_eq_of_quadraticRatio_eq_one W.toRepresentation hratio).2
  have hsum := fixedCodim_quotient_add_subrepresentation_le τ W A₀
  have hzero : fixedCodim W.quotientRepresentation A₀ = 0 := by
    rw [heq, hcodim, hrank] at hsum
    have := hA.2
    omega
  by_contra hItop
  have hWtop : W ≠ ⊤ := fun he => hItop (congrArg Subrepresentation.toSubmodule he)
  have hfq := faithful_quotient_of_cubicPolynomial τ L₀
    ⟨z, (show L ≤ J from le_sup_left) hzL⟩ hzL horder hc hp W hWtop
  have hfix := (fixedCodim_eq_zero_iff W.quotientRepresentation A₀).mp hzero
  apply helem.1
  apply bot_unique
  intro a ha
  change a = 1
  apply hfq
  apply LinearMap.ext
  intro v
  rw [map_one]
  change W.quotientRepresentation a v = v
  have hv : v ∈ fixedSpace W.quotientRepresentation A₀ := hfix ▸ Submodule.mem_top
  exact hv ⟨a, ha⟩

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.SmallCovers.Reduction.ModuleRecognition.FFPassage
