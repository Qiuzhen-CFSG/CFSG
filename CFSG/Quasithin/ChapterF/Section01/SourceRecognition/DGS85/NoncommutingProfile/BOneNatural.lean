module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.NoncommutingProfile.BOneGeometry
public import Theory.Representation.RankOne.QuadraticRecognition.NaturalConsequences
public import Theory.SpecificGroups.SL2.FieldAutomorphismCore

/-!
# Natural cores and full local centers in the b=1 branch

The paired geometry calculation gives Q=Z. The center of the local actor
maps trivially to its binary SL₂ quotient, so it lies in the now elementary
core. Consequently its full center equals its omega-center. This converts
the earlier natural section into the literal Q/Z(L) section. The retained
conjugator also identifies the source neighbor-core intersection D with
Z(L), without replacing D by a subgroup defined through this conclusion.

Quadratic Sylow action and fixed-space generation give natural copies;
the earlier natural dimension makes the multiplicity one. The exported
coordinates are surjective, have kernel exactly the full local center,
and intertwine original conjugation with the same matrix actors. Sylow
orders and the sharp fixed index give equality of the two field orders.

Source: DGS, *Groups and Graphs* (1985), 10.4--10.5(b), pp.155--156,
using the marked 7.1 action and its natural dimension. The path-parameter
and center-order dichotomies of 10.5(c,d) are not asserted here.
-/

@[expose] public noncomputable section
open Subgroup Representation Representation.BinaryOffender
open Representation.RankOne.QuadraticRecognition
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterF.Source.DGS85.NoncommutingProfile
open Subgroup.CosetGeometry.RankTwo
open Theory.GroupTheory.AmalgamGraph
variable {G : Type*} [Group G] {P : Fin 2 → Subgroup G} {B : Subgroup G}
variable {k W : Type*} [Field k] [Finite k] [CharP k 2]
  [AddCommGroup W] [Module (ZMod 2) W]
variable {v w : Vertex (family P)} (c : BOneActionData (family P) v w k W)

private theorem actor_center_le_core : centerIn c.actor ≤ Q (family P) v := by
  intro x hx
  let xL : c.actor := ⟨x,hx.1⟩
  have hc : c.quotient xL ∈ center SL(2,k) := by
    apply mem_center_iff.mpr
    intro y
    obtain ⟨z,rfl⟩ := c.onto y
    have he : z*xL = xL*z := Subtype.ext (hx.2 z z.property)
    simpa only [map_mul] using congrArg c.quotient he
  rw [Atlas.RankOneFieldAutomorphisms.sl_center_eq_bot,mem_bot] at hc
  have hm : xL ∈ c.quotient.ker := hc
  exact (show xL ∈ (Q (family P) v).subgroupOf c.actor from c.kernel ▸ hm)

/-- The full actor center has exponent two after the core calculation. -/
theorem actor_omegaCenter_eq_center (h : LocallyRankOneTriple P B)
    (hcore : Q (family P) v = Z (family P) v) :
    omegaCenterIn c.actor = centerIn c.actor := by
  apply le_antisymm
  · intro x hx
    have hh := (mem_omegaCenterIn_iff _ _).mp hx
    exact ⟨hh.1,hh.2.1⟩
  · intro x hx
    have hxQ := actor_center_le_core c hx
    have hxZ : x ∈ Z (family P) v := hcore ▸ hxQ
    have hxom := (mem_omegaCenterIn_iff _ _).mp ((source_Z_Q_U h v).1 hxZ)
    exact (mem_omegaCenterIn_iff _ _).mpr ⟨hx.1,hx.2,hxom.2.2⟩

/-- The identified source core is elementary abelian. -/
theorem core_elementary (h : LocallyRankOneTriple P B)
    (hcore : Q (family P) v = Z (family P) v) :
    IsElementaryAbelian 2 (Q (family P) v) := by
  rw [hcore]
  exact IsElementaryAbelian.of_injective (inclusion (source_Z_Q_U h v).1)
    (inclusion_injective _)

/-- The source intersection for the actual chosen conjugator equals the full local center. -/
theorem literal_D_eq_actor_center (h : LocallyRankOneTriple P B)
    (hcore : Q (family P) v = Z (family P) v) (g : c.actor)
    (d : OppositeCenterGeometry (family P) v w ((g : G) • w)) (hd : d.actor = c.actor) :
    D (family P) w ((g : G) • w) = centerIn c.actor := by
  apply le_antisymm
  · let : IsElementaryAbelian 2 (Q (family P) v) := core_elementary h hcore
    have he : IsElementaryAbelian 2 (D (family P) w ((g : G) • w)) :=
      IsElementaryAbelian.of_injective (inclusion d.separated) (inclusion_injective _)
    exact (D_le_actor_center h d he).trans (congrArg centerIn hd).le
  · intro x hx
    have hxZ : x ∈ Z (family P) v := hcore ▸ actor_center_le_core c hx
    have hZw : Z (family P) w ≤ c.actor := by
      intro z hz
      have hzQ := (mem_omegaCenterIn_iff _ _).mp ((source_Z_Q_U h w).1 hz)
      exact c.neighbor_core_le hzQ.1
    have hxc : x ∈ centralizer (Z (family P) w : Set G) :=
      (centralizer_le hZw) hx.2
    have hxQw : x ∈ Q (family P) w :=
      (show x ∈ Z (family P) v ⊓ Q (family P) w from
        c.centralizer_intersection ▸ (show x ∈ Z (family P) v ⊓ centralizer (Z (family P) w : Set G)
          from ⟨hxZ,hxc⟩)).2
    refine ⟨hxQw,?_⟩
    rw [Q_translate]
    refine ⟨x,hxQw,?_⟩
    change (g : G)*x*(g : G)⁻¹ = x
    rw [hx.2 g g.property,mul_inv_cancel_right]

/-- The earlier section rewritten on the actual core, with the full local center retained. -/
def naturalCoreSection (h : LocallyRankOneTriple P B)
    (hcore : Q (family P) v = Z (family P) v) :
    BinaryConjugationSection c.actor (Q (family P) v) (centerIn c.actor)
      (c.representation.comp c.quotient) := by
  rw [hcore,←actor_omegaCenter_eq_center c h hcore]
  exact c.coordinates

/-- The marked quotient kernel proves normality relative to its local actor. -/
theorem coreNormal : ((Q (family P) v).subgroupOf c.actor).Normal :=
  c.kernel ▸ (inferInstance : c.quotient.ker.Normal)

local instance : ((Q (family P) v).subgroupOf c.actor).Normal := coreNormal c

/-- The actual local actor modulo the embedded vertex core, via its marked quotient map. -/
def localQuotientEquiv :
    c.actor ⧸ (Q (family P) v).subgroupOf c.actor ≃* SL(2,k) :=
  (QuotientGroup.quotientMulEquivOfEq c.kernel.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective c.quotient c.onto)

/-- The local quotient equivalence uses the original quotient map on representatives. -/
theorem localQuotientEquiv_mk (x : c.actor) :
    localQuotientEquiv c (QuotientGroup.mk' ((Q (family P) v).subgroupOf c.actor) x) = c.quotient x := rfl

include c in
/-- The neighbor center has the same core index as its actual SL₂ Sylow image. -/
theorem neighbor_center_index (h : LocallyRankOneTriple P B) :
    (Q (family P) v).relIndex (Z (family P) w) = Nat.card k := by
  have hZQ : Z (family P) w ≤ Q (family P) w := by
    intro z hz
    exact ((mem_omegaCenterIn_iff _ _).mp ((source_Z_Q_U h w).1 hz)).1
  have he := BinaryConjugationSection.actor_image_card_eq_relIndex
    c.actor (Q (family P) v) (Z (family P) w) c.quotient c.kernel
    (hZQ.trans c.neighbor_core_le)
  rw [c.neighbor_image] at he
  exact he.symm.trans
    (Nat.card_congr (Matrix.SpecialLinearGroup.sylowEquivAdditive k 2 c.imageSylow).symm.toEquiv)

local instance bOneNaturalAlgebra : Algebra (ZMod 2) k := ZMod.algebra k 2

include c in
/-- Natural dimension and sharpness compute the reverse center/core index. -/
theorem opposite_core_index_of_natural
    (E : W ≃ₗ[ZMod 2] (Fin 2 → k)) :
    (Q (family P) w).relIndex (Z (family P) v) = Nat.card k := by
  let : Finite W := Finite.of_equiv (Fin 2 → k) E.toEquiv.symm
  have hc := (sl2_natural_fixed_spaces c.representation c.imageSylow
    c.quadratic c.generated c.fixed_bot E).1
  have hquot := Submodule.card_eq_card_quotient_mul_card
    (fixedSpace c.representation c.imageSylow)
  rw [card_of_natural_coordinates E,hc,c.sharp_index,pow_two] at hquot
  exact (Nat.mul_left_cancel (Nat.card_pos : 0 < Nat.card k) hquot).symm

/-- The earlier natural dimension makes the original representation a single natural module. -/
theorem exists_natural_coordinates (E : W ≃ₗ[ZMod 2] (Fin 2 → k)) :
    ∃ E' : W ≃ₗ[ZMod 2] (Fin 2 → k),
      ∀ a x, E' (c.representation a x) = Matrix.mulVec a.val (E' x) := by
  let : Finite W := Finite.of_equiv (Fin 2 → k) E.toEquiv.symm
  obtain ⟨m,e,he⟩ := sl2_natural_copies c.representation c.imageSylow
    c.quadratic c.generated c.fixed_bot
  have hd := e.finrank_eq
  have hE := E.finrank_eq
  simp only [Module.finrank_pi_fintype,Finset.sum_const,Finset.card_univ,
    Fintype.card_fin,smul_eq_mul] at hd hE
  have hk := Module.finrank_pos (R := ZMod 2) (M := k)
  have hm : m = 1 := by nlinarith
  subst m
  refine ⟨e.trans (LinearEquiv.funUnique (Fin 1) (ZMod 2) (Fin 2 → k)),?_⟩
  intro a x
  exact he a x 0

/-- A literal natural quotient: exact full-center kernel and actual conjugation equations. -/
theorem natural_core_coordinates (h : LocallyRankOneTriple P B)
    (hcore : Q (family P) v = Z (family P) v)
    (E : W ≃ₗ[ZMod 2] (Fin 2 → k)) :
    ∃ φ : Q (family P) v →* Multiplicative (Fin 2 → k),
      Function.Surjective φ ∧ φ.ker = (centerIn c.actor).subgroupOf (Q (family P) v) ∧
      ∀ (a : c.actor) (x : Q (family P) v), ∃ y : Q (family P) v,
        (y : G) = (a : G) * (x : G) * (a : G)⁻¹ ∧
        (φ y).toAdd = Matrix.mulVec (c.quotient a).val (φ x).toAdd := by
  obtain ⟨E',he⟩ := exists_natural_coordinates c E
  let d := naturalCoreSection c h hcore
  let e := E'.toAddEquiv.toMultiplicative
  let φ := e.toMonoidHom.comp d.coordinates
  refine ⟨φ,e.surjective.comp d.onto,?_,?_⟩
  · ext x
    change e (d.coordinates x) = 1 ↔ (x : G) ∈ centerIn c.actor
    constructor
    · intro hx
      apply (d.coordinates_eq_one_iff x).mp
      exact e.injective (hx.trans e.map_one.symm)
    · intro hx
      rw [(d.coordinates_eq_one_iff x).mpr hx,map_one]
  · intro a x
    let y : Q (family P) v := ⟨(a : G) * (x : G) * (a : G)⁻¹,
      (mem_normalizer_iff.mp (d.normalized a.property) x).mp x.property⟩
    refine ⟨y,rfl,?_⟩
    change E' (d.coordinates y).toAdd =
      Matrix.mulVec (c.quotient a).val (E' (d.coordinates x).toAdd)
    rw [d.equivariant a x]
    exact he (c.quotient a) (d.coordinates x).toAdd

/-- The original core order retains its full central factor. -/
theorem core_card_of_natural (h : LocallyRankOneTriple P B)
    (hcore : Q (family P) v = Z (family P) v)
    (E : W ≃ₗ[ZMod 2] (Fin 2 → k)) :
    Nat.card (Q (family P) v) = Nat.card k ^ 2 * Nat.card (centerIn c.actor) := by
  have he := (naturalCoreSection c h hcore).card_section
  rw [card_of_natural_coordinates E] at he
  exact he

theorem paired_field_orders_eq
    {k₀ k₁ W₀ W₁ : Type*} [Field k₀] [Finite k₀] [CharP k₀ 2]
    [Field k₁] [Finite k₁] [CharP k₁ 2]
    [AddCommGroup W₀] [Module (ZMod 2) W₀] [AddCommGroup W₁] [Module (ZMod 2) W₁]
    (h : LocallyRankOneTriple P B)
    (c₀ : BOneActionData (family P) (base (family P) false) (base (family P) true) k₀ W₀)
    (c₁ : BOneActionData (family P) (base (family P) true) (base (family P) false) k₁ W₁)
    (E₀ : W₀ ≃ₗ[ZMod 2] (Fin 2 → k₀)) : Nat.card k₀ = Nat.card k₁ := by
  exact (opposite_core_index_of_natural c₀ E₀).symm.trans (neighbor_center_index c₁ h)

end CFSG.Quasithin.ChapterF.Source.DGS85.NoncommutingProfile
