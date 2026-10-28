module
public import CFSG.Quasithin.ChapterB.Section04.NaturalExtensions.FFConsequences.HigherRank.Transport
public import CFSG.Quasithin.ChapterB.Section04.NaturalExtensions.QuadraticSplitting.Source
public import Theory.GroupTheory.SpecificGroups.KleinFourGenerators
import Mathlib.Tactic.NoncommRing

/-!
# Quadratic four-groups with a common quotient axis

Two distinct common-axis elementary roots generate a four-group. Their three
nonidentity elements fix exactly the kernel of the same coordinate functional,
so the axis has codimension one. The four root-product identities propagate
quadraticity from the generators to every pair of elements in this subgroup.
All actors are pulled back through the original marking and the axis is a
submodule of the literal quotient by the original natural submodule.

In the dual quotient orientation, inverse transpose turns common-center roots
into common-axis roots, and the imported extension calculation proves their
products vanish. The natural orientation retains its root-product calculation
as an explicit premise. The final application supplies the complete hypotheses
of B.4.9(1); it does not assert splitting or discharge that remaining premise.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, B.4.9(1) and
its application in B.4.9(2)(i), printed pp.92–95. This construction covers the
higher binary dimensions, beyond the cases treated explicitly in the printed
proof, using the sparse-root extension identities.
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
open Representation Representation.BinaryOffender Matrix
namespace CFSG.Quasithin.ChapterB.NaturalExtensions.HigherRank
open QuasisimpleSource

private theorem quadratic_pair {G V : Type*} [Group G] [AddCommGroup V]
    [Module (ZMod 2) V] (ρ : Representation (ZMod 2) G V) (x y : G)
    (hxx : x * x = 1) (hyy : y * y = 1) (hc : Commute x y)
    (h₁ : (ρ x - 1) * (ρ x - 1) = 0)
    (h₂ : (ρ x - 1) * (ρ y - 1) = 0)
    (h₃ : (ρ y - 1) * (ρ x - 1) = 0)
    (h₄ : (ρ y - 1) * (ρ y - 1) = 0) :
    IsQuadratic ρ (Subgroup.closure ({x, y} : Set G)) := by
  have hxy : ρ (x*y) - 1 = (ρ x - 1) + (ρ y - 1) := by
    calc
      _ = (ρ x - 1) * (ρ y - 1) + (ρ x - 1) + (ρ y - 1) := by
        rw [map_mul]
        noncomm_ring
      _ = _ := by rw [h₂, zero_add]
  intro a ha b hb v
  have hp : (ρ a - 1) * (ρ b - 1) = 0 := by
    rcases (Subgroup.mem_closure_pair_iff x y hxx hyy hc a).mp ha with
      ha | ha | ha | ha <;>
    rcases (Subgroup.mem_closure_pair_iff x y hxx hyy hc b).mp hb with
      hb | hb | hb | hb <;>
    simp only [ha, hb, map_one, sub_self, zero_mul, mul_zero, hxy, add_mul, mul_add,
      h₁, h₂, h₃, h₄, add_zero]
  have hv := LinearMap.congr_fun hp v
  exact sub_eq_zero.mp hv

private theorem roots_axis_four {G V W : Type*} [Group G]
    [AddCommGroup V] [Module (ZMod 2) V] [AddCommGroup W] [Module (ZMod 2) W]
    (ρ : Representation (ZMod 2) G V) (σ : Representation (ZMod 2) G W)
    {n : ℕ} (e : ActionEquiv σ (linearNatural BinaryField.two n))
    {i j k : Fin n} (hij : i ≠ j) (hkj : k ≠ j) (hik : i ≠ k)
    (hp : ∀ a b : Fin n, ∀ haj : a ≠ j, ∀ hbj : b ≠ j,
      (ρ (e.groupEquiv.symm (SpecialLinearGroup.transvection haj 1)) - 1) *
      (ρ (e.groupEquiv.symm (SpecialLinearGroup.transvection hbj 1)) - 1) = 0) :
    ∃ E : Subgroup G, IsElementaryAbelian 2 E ∧ Nat.card E = 4 ∧ IsQuadratic ρ E ∧
      ∃ I : Submodule (ZMod 2) W, Module.finrank (ZMod 2) (W ⧸ I) = 1 ∧
        ∀ g ∈ E, g ≠ 1 → fixedSpace σ (Subgroup.zpowers g) = I := by
  classical
  let x := e.groupEquiv.symm (SpecialLinearGroup.transvection hij 1)
  let y := e.groupEquiv.symm (SpecialLinearGroup.transvection hkj 1)
  have root_sq {a b : Fin n} (hab : a ≠ b) :
      (SpecialLinearGroup.transvection hab (1 : ZMod 2)) *
        SpecialLinearGroup.transvection hab 1 = 1 := by
    simpa only [CharTwo.neg_eq] using SpecialLinearGroup.transvection_mul_neg hab (1 : ZMod 2)
  have hx : x*x=1 := by simp only [x, ← map_mul, root_sq, map_one]
  have hy : y*y=1 := by simp only [y, ← map_mul, root_sq, map_one]
  have hc : Commute x y := by
    change x*y=y*x
    simp only [x, y, ← map_mul]
    rw [OneCohomology.SLHigherNatural.transvection_commute hij hkj hkj.symm hij.symm]
  have hrne {a b : Fin n} (hab : a ≠ b) :
      SpecialLinearGroup.transvection hab (1 : ZMod 2) ≠ 1 := by
    intro h
    have h' := congrArg (fun g : SpecialLinearGroup (Fin n) (ZMod 2) => g.val a b) h
    simp [SpecialLinearGroup.transvection_coe, hab] at h'
  have hx1 : x ≠ 1 := by
    intro h
    apply hrne hij
    simpa only [x, e.groupEquiv.apply_symm_apply, map_one] using congrArg e.groupEquiv h
  have hy1 : y ≠ 1 := by
    intro h
    apply hrne hkj
    simpa only [y, e.groupEquiv.apply_symm_apply, map_one] using congrArg e.groupEquiv h
  have hxy : x ≠ y := by
    intro h
    have h' := congrArg (fun g => (e.groupEquiv g).val i j) h
    simp [x, y, SpecialLinearGroup.transvection_coe, hij, hik.symm] at h'
  let E := Subgroup.closure ({x,y} : Set G)
  let : IsKleinFour E := Subgroup.isKleinFour_closure_pair x y hx hy hx1 hy1 hxy hc
  have hel : IsElementaryAbelian 2 E :=
    { toIsMulCommutative := IsKleinFour.isMulCommutative
      exponent_dvd_p := by rw [IsKleinFour.exponent_two] }
  have hquad : IsQuadratic ρ E := quadratic_pair ρ x y hx hy hc
    (hp i i hij hij) (hp i k hij hkj) (hp k i hkj hij) (hp k k hkj hkj)
  let l : W →ₗ[ZMod 2] ZMod 2 := (LinearMap.proj j).comp e.linearEquiv.toLinearMap
  have hl : Function.Surjective l := by
    intro c
    refine ⟨e.linearEquiv.symm (Pi.single j c), ?_⟩
    change (e.linearEquiv (e.linearEquiv.symm (Pi.single j c))) j = c
    simp
  refine ⟨E, hel, IsKleinFour.card_four, hquad, l.ker, ?_, ?_⟩
  · rw [(l.quotKerEquivOfSurjective hl).finrank_eq, Module.finrank_self]
  have hact {a : Fin n} (haj : a ≠ j) (v : W) :
      e.linearEquiv (σ (e.groupEquiv.symm (SpecialLinearGroup.transvection haj 1)) v) =
        e.linearEquiv v + Pi.single a (e.linearEquiv v j) := by
    rw [e.intertwines, e.groupEquiv.apply_symm_apply]
    exact (OneCohomology.SLHigherNatural.action_transvection haj (1 : ZMod 2) _).trans
      (by simp)
  have hax (v : W) : e.linearEquiv (σ x v) = e.linearEquiv v + Pi.single i (e.linearEquiv v j) :=
    hact hij v
  have hay (v : W) : e.linearEquiv (σ y v) = e.linearEquiv v + Pi.single k (e.linearEquiv v j) :=
    hact hkj v
  have haxy (v : W) : e.linearEquiv (σ (x*y) v) =
      e.linearEquiv v + Pi.single k (e.linearEquiv v j) + Pi.single i (e.linearEquiv v j) := by
    rw [map_mul]
    change e.linearEquiv (σ x (σ y v)) = _
    rw [hax, hay]
    simp [hkj.symm]
  intro g hg hg1
  ext v
  rw [mem_fixedSpace_zpowers_iff, LinearMap.mem_ker]
  change σ g v = v ↔ e.linearEquiv v j = 0
  rw [← e.linearEquiv.injective.eq_iff]
  rcases (Subgroup.mem_closure_pair_iff x y hx hy hc g).mp hg with rfl | rfl | rfl | rfl
  · exact (hg1 rfl).elim
  · rw [hax]
    simp
  · rw [hay]
    simp
  · rw [haxy]
    constructor
    · intro h
      have h' := congrFun h i
      simpa [Pi.single_apply, hik] using h'
    · intro h
      simp [h]

private noncomputable def axisDualAction {G H V W : Type*} [Group G] [Group H]
    [AddCommGroup V] [Module (ZMod 2) V] [AddCommGroup W] [Module (ZMod 2) W]
    {ρ : Representation (ZMod 2) G V} {σ : Representation (ZMod 2) H W}
    (e : ActionEquiv ρ σ) : ActionEquiv ρ.dual σ.dual where
  groupEquiv := e.groupEquiv
  linearEquiv := e.linearEquiv.symm.dualMap
  intertwines g f := by
    ext w
    change f (ρ g⁻¹ (e.linearEquiv.symm w)) = f (e.linearEquiv.symm (σ (e.groupEquiv g)⁻¹ w))
    congr 1
    apply e.linearEquiv.injective
    rw [e.intertwines, e.linearEquiv.apply_symm_apply, e.linearEquiv.apply_symm_apply,
      e.groupEquiv.map_inv]

private theorem graph_symm_root {n : ℕ} {i j : Fin n} (hij : i ≠ j) :
    (BinaryLinear.OuterCyclic.graphSL n).symm (SpecialLinearGroup.transvection hij 1) =
      SpecialLinearGroup.transvection hij.symm 1 := by
  change (SpecialLinearGroup.transpose (SpecialLinearGroup.transvection hij (1 : ZMod 2)))⁻¹ = _
  have ht : SpecialLinearGroup.transpose (SpecialLinearGroup.transvection hij (1 : ZMod 2)) =
      SpecialLinearGroup.transvection hij.symm 1 := by
    apply Subtype.ext
    simp [SpecialLinearGroup.coe_transpose, SpecialLinearGroup.transvection_coe]
  rw [ht, SpecialLinearGroup.transvection_inv, CharTwo.neg_eq]

variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  {F : BinaryField} {n : ℕ} {ρ : Representation (ZMod 2) G V}

/-- The natural-orientation root calculation is the only premise retained by
this witness construction. Its independent producer is the natural extension
calculation, and the splitting assembly must discharge it. -/
def NaturalAxisRootProducts (d : DoubleNatural F n ρ) (hF : F.degree = 1) : Prop :=
  ∀ (_ : d.space.quotientRepresentation.Equiv d.space.toRepresentation),
    ∀ {i j k : Fin n} (hij : i ≠ j) (hkj : k ≠ j),
      (ρ ((binaryForm d hF).natural.groupEquiv.symm
        (SpecialLinearGroup.transvection hij 1)) - 1) *
      (ρ ((binaryForm d hF).natural.groupEquiv.symm
        (SpecialLinearGroup.transvection hkj 1)) - 1) = 0

private theorem natural_axis_four (d : DoubleNatural F n ρ)
    (hF : F.degree = 1) (hn : 6 ≤ n) (hp : NaturalAxisRootProducts d hF)
    (eQ : d.space.quotientRepresentation.Equiv d.space.toRepresentation) :
    ∃ E : Subgroup G, IsElementaryAbelian 2 E ∧ Nat.card E = 4 ∧ IsQuadratic ρ E ∧
      ∃ I : Submodule (ZMod 2) (V ⧸ d.space.toSubmodule),
        Module.finrank (ZMod 2) ((V ⧸ d.space.toSubmodule) ⧸ I) = 1 ∧
        ∀ g ∈ E, g ≠ 1 → fixedSpace d.space.quotientRepresentation (Subgroup.zpowers g) = I := by
  let b := binaryForm d hF
  let e : ActionEquiv d.space.quotientRepresentation (linearNatural BinaryField.two n) :=
    { groupEquiv := b.natural.groupEquiv
      linearEquiv := eQ.toLinearEquiv.trans b.natural.linearEquiv
      intertwines := by
        intro g v
        have h := LinearMap.congr_fun (eQ.isIntertwining' g) v
        change eQ (d.space.quotientRepresentation g v) = d.space.toRepresentation g (eQ v) at h
        exact (congrArg b.natural.linearEquiv h).trans (b.natural.intertwines g (eQ v)) }
  let i : Fin n := ⟨0, by omega⟩
  let j : Fin n := ⟨2, by omega⟩
  let k : Fin n := ⟨1, by omega⟩
  exact roots_axis_four ρ d.space.quotientRepresentation e
    (i := i) (j := j) (k := k) (by simp [i, j]) (by simp [k, j]) (by simp [i, k])
    (fun a b haj hbj => hp eQ haj hbj)

/-- In the dual quotient orientation the ambient quadratic four-group is
unconditional. Inverse transpose exchanges the common center upstairs in the
natural coordinates with the common axis on the actual quotient. -/
theorem degree_one_dual_axis_four (d : DoubleNatural F n ρ)
    (hF : F.degree = 1) (hn : 6 ≤ n)
    (eQ : d.space.quotientRepresentation.Equiv d.space.toRepresentation.dual) :
    ∃ E : Subgroup G, IsElementaryAbelian 2 E ∧ Nat.card E = 4 ∧ IsQuadratic ρ E ∧
      ∃ I : Submodule (ZMod 2) (V ⧸ d.space.toSubmodule),
        Module.finrank (ZMod 2) ((V ⧸ d.space.toSubmodule) ⧸ I) = 1 ∧
        ∀ g ∈ E, g ≠ 1 → fixedSpace d.space.quotientRepresentation (Subgroup.zpowers g) = I := by
  let b := binaryForm d hF
  let eN := axisDualAction b.natural
  let eD := dualNaturalEquiv n
  let e : ActionEquiv d.space.quotientRepresentation (linearNatural BinaryField.two n) :=
    { groupEquiv := eN.groupEquiv.trans eD.groupEquiv
      linearEquiv := eQ.toLinearEquiv.trans (eN.linearEquiv.trans eD.linearEquiv)
      intertwines := by
        intro g v
        have h := LinearMap.congr_fun (eQ.isIntertwining' g) v
        change eQ (d.space.quotientRepresentation g v) = d.space.toRepresentation.dual g (eQ v) at h
        exact (congrArg (fun w => eD.linearEquiv (eN.linearEquiv w)) h).trans
          ((congrArg eD.linearEquiv (eN.intertwines g (eQ v))).trans
            (eD.intertwines (eN.groupEquiv g) (eN.linearEquiv (eQ v)))) }
  let i : Fin n := ⟨0, by omega⟩
  let j : Fin n := ⟨2, by omega⟩
  let k : Fin n := ⟨1, by omega⟩
  apply roots_axis_four ρ d.space.quotientRepresentation e
    (i := i) (j := j) (k := k) (by simp [i, j]) (by simp [k, j]) (by simp [i, k])
  intro a b haj hbj
  change (ρ ((binaryForm d hF).natural.groupEquiv.symm
      ((BinaryLinear.OuterCyclic.graphSL n).symm (SpecialLinearGroup.transvection haj 1))) - 1) *
    (ρ ((binaryForm d hF).natural.groupEquiv.symm
      ((BinaryLinear.OuterCyclic.graphSL n).symm (SpecialLinearGroup.transvection hbj 1))) - 1) = 0
  rw [graph_symm_root, graph_symm_root]
  exact degree_one_dual_root_product d hF hn eQ haj.symm hbj.symm

/-- The literal quotient-axis four-group required in B.4.9(1), in every higher
binary dimension and both quotient orientations. Only the natural-orientation
root identity remains explicit; no containment in an offender is required. -/
theorem degree_one_axis_four (d : DoubleNatural F n ρ)
    (hF : F.degree = 1) (hn : 6 ≤ n) (hp : NaturalAxisRootProducts d hF) :
    ∃ E : Subgroup G, IsElementaryAbelian 2 E ∧ Nat.card E = 4 ∧ IsQuadratic ρ E ∧
      ∃ I : Submodule (ZMod 2) (V ⧸ d.space.toSubmodule),
        Module.finrank (ZMod 2) ((V ⧸ d.space.toSubmodule) ⧸ I) = 1 ∧
        ∀ g ∈ E, g ≠ 1 → fixedSpace d.space.quotientRepresentation (Subgroup.zpowers g) = I := by
  rcases d.quotient with h | h
  · obtain ⟨eQ⟩ := h
    exact natural_axis_four d hF hn hp eQ
  · obtain ⟨eQ⟩ := h
    exact degree_one_dual_axis_four d hF hn eQ

/-- Actual `DoubleNatural` application to the complete B.4.9(1) source
interface. The rank-three root-group clause and the F₄ clause are vacuous
here. Splitting itself remains the responsibility of the source assembly. -/
theorem degree_one_quadraticSplitting_source (d : DoubleNatural F n ρ)
    (hF : F.degree = 1) (hn : 6 ≤ n) (hp : NaturalAxisRootProducts d hF) :
    QuadraticSplitting.SourceHypotheses d := by
  obtain ⟨E, he, hc, hq, I, hI, hfix⟩ := degree_one_axis_four d hF hn hp
  refine { family := Or.inr ⟨hF, by omega⟩
           four := ⟨E, ⟨he, hc, I, ?_, hfix⟩, hq, ?_⟩
           fourField := ?_ }
  · simpa only [hF] using hI
  · intro hn3
    omega
  · intro hF2
    omega

end CFSG.Quasithin.ChapterB.NaturalExtensions.HigherRank
