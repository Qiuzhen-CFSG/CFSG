module
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.Recognition.NormalCubic
public import Theory.ElementaryAbelian.Injective
public import Theory.LinearAlgebra.AlternatingFinrank

/-!
# The original square form when the center is the marked point

If Z(U) is V₁, the actual nonabelian closure is extraspecial. The literal
quotients U/Z(U) and the image of U in G₁/V₁ are identified by their
canonical quotient maps, and the dotted H quotient is H/O₂(H).

The square map on U/Z(U) is H invariant and nondegenerate. The original
intersection E is elementary, so its image is singular. If that image has
half the ambient dimension, the isotropic dimension bound proves its
maximality. These are the quadratic conclusions used in original 14.3.12.

Source: Aschbacher--Smith, 12.8.8, 12.8.11 and 14.3.12(3--4),
printed pp.851--854,993.
-/

@[expose] public noncomputable section
namespace CFSG.Quasithin.Chapter14.Section03.NonabelianSource.Recognition
open Subgroup Theory.GroupTheory Module
open scoped IsMulCommutative
open Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter12.Section08.InvariantFlag.Symplectic
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {V : Subgroup G} {n : ℕ}

omit [Finite G] in
theorem center_eq_point_subgroup (F : InvariantFlag T V n)
    (hZ : F.ZU = F.Vi 1) : center F.U = (F.Vi 1).subgroupOf F.U := by
  rw [← hZ]
  ext u
  change u ∈ center F.U ↔ (u : G) ∈ (center F.U).map F.U.subtype
  exact ⟨fun hu => mem_map_of_mem _ hu, fun ⟨w,hw,he⟩ =>
    (show w = u from Subtype.ext he) ▸ hw⟩

/-- When the actual center is the marked point, the whole closure is extraspecial. -/
theorem extraspecial_of_center_point (F : InvariantFlag T V n) [IsElementaryAbelian 2 V]
    (d : ClosureGeometry F) (hn : 1 ≤ n) (hZ : F.ZU = F.Vi 1)
    (hne : ¬ IsMulCommutative F.U) : IsExtraspecial 2 F.U where
  center_order_p := by
    rw [center_eq_point_subgroup F hZ]
    exact (Nat.card_congr (subgroupOfEquivOfLe
      (show F.Vi 1 ≤ F.U from (F.le_seed 1).trans (le_conjugateSpanBy V F.H))).toEquiv).trans
      (by simpa using F.card 1 hn)
  quotient_elementary_abelian := F.uhat_elementary_of_point hn d.two d.frattini_point
  quotient_nontrivial := QuotientGroup.nontrivial_iff.mpr (fun ht => hne (center_eq_top_iff.mp ht))

/-- The center-point equality kills the center's Frattini subgroup. -/
theorem center_frattini_bot_of_center_point (F : InvariantFlag T V n)
    [IsElementaryAbelian 2 V] (d : ClosureGeometry F) (hZ : F.ZU = F.Vi 1) :
    frattini (center F.U) = ⊥ := by
  let j : center F.U →* V := {
    toFun z := ⟨z, F.le_seed 1 (by rw [← hZ]; exact mem_map_of_mem F.U.subtype z.property)⟩
    map_one' := rfl
    map_mul' := fun _ _ => rfl }
  let : IsElementaryAbelian 2 (center F.U) := IsElementaryAbelian.of_injective j
    (fun x y he => Subtype.ext (Subtype.ext (congrArg (fun z : V => (z : G)) he)))
  let : Fact (IsPGroup 2 (center F.U)) := ⟨d.two.of_injective _ (center F.U).subtype_injective⟩
  exact (frattini_eq_bot_iff_isElementaryAbelian (p := 2)).mpr inferInstance

/-- The center-point square form vanishes on the actual elementary intersection. -/
theorem quadratic_intersection_of_center_point (F : InvariantFlag T V n)
    [IsElementaryAbelian 2 V] [IsElementaryAbelian 2 F.Uhat]
    (d : ClosureGeometry F) (hn : 1 ≤ n) (hZ : F.ZU = F.Vi 1)
    (g : G) (hdis : Disjoint (conjugate (F.Vi 1) g) F.ZU) :
    let q := F.uhatQuadraticForm hn d.two d.frattini_point
      (center_frattini_bot_of_center_point F d hZ)
    (∀ x ∈ hatSpace F (F.E g), q x = 0) ∧
    (∀ (h : F.H) (x : F.Uhat), q (Additive.ofMul (F.uhatAction h x)) = q (Additive.ofMul x)) ∧
    q.polarBilin.Nondegenerate := by
  let hphi := center_frattini_bot_of_center_point F d hZ
  let q := F.uhatQuadraticForm hn d.two d.frattini_point hphi
  have hPhi : (frattini F.U).map F.U.subtype = F.Vi 1 := by
    rw [d.frattini_point]
    exact map_subgroupOf_eq_of_le
      (show F.Vi 1 ≤ F.U from (F.le_seed 1).trans (le_conjugateSpanBy V F.H))
  let : IsElementaryAbelian 2 (F.E g) := F.E_elementary hn g d.two hPhi hdis
  refine ⟨?_,?_,?_⟩
  · intro x hx
    obtain ⟨u,hu,he⟩ := (show x.toMul ∈ hatImage F (F.E g) from hx)
    have hs : u ^ 2 = 1 := Subtype.ext (elemPow_eq_one_of_isElementaryAbelian (A := F.E g) (u : G) hu)
    have hs' : F.uhatSquare d.two hphi (QuotientGroup.mk' (center F.U) u) = 1 := by
      apply Subtype.ext
      rw [F.uhatSquare_apply_mk,hs]
      rfl
    change q x = 0
    change q (Additive.ofMul x.toMul) = 0
    rw [← he]
    rw [F.uhatQuadraticForm_apply,hs']
    simp only [map_one]
    rfl
  · intro h x
    change (SmallFrattini.binaryMark _ (F.uhatSquare d.two hphi (F.uhatAction h x))).toAdd = _
    rw [F.uhatSquare_invariant hn d.two d.frattini_point]
    rfl
  · change (F.uhatQuadraticForm hn d.two d.frattini_point hphi).polarBilin.Nondegenerate
    rw [F.uhatQuadraticForm_polar]
    exact F.uhatBilinearForm_nondegenerate hn d.two d.frattini_point

/-- A singular half-dimensional intersection is maximal among singular subspaces. -/
theorem maximal_singular_of_half_dimension (F : InvariantFlag T V n)
    [IsElementaryAbelian 2 V] [IsElementaryAbelian 2 F.Uhat]
    (d : ClosureGeometry F) (hn : 1 ≤ n) (hZ : F.ZU = F.Vi 1)
    (g : G) (hdis : Disjoint (conjugate (F.Vi 1) g) F.ZU)
    (hd : Module.finrank (ZMod 2) (hatSpace F (F.E g)) =
      Module.finrank (ZMod 2) (Additive F.Uhat) / 2) :
    let q := F.uhatQuadraticForm hn d.two d.frattini_point
      (center_frattini_bot_of_center_point F d hZ)
    ∀ S : Submodule (ZMod 2) (Additive F.Uhat), hatSpace F (F.E g) ≤ S →
      (∀ x ∈ S, q x = 0) → S = hatSpace F (F.E g) := by
  let q := F.uhatQuadraticForm hn d.two d.frattini_point
    (center_frattini_bot_of_center_point F d hZ)
  have hnd := (quadratic_intersection_of_center_point F d hn hZ g hdis).2.2
  change ∀ S : Submodule (ZMod 2) (Additive F.Uhat), hatSpace F (F.E g) ≤ S →
    (∀ x ∈ S, q x = 0) → S = hatSpace F (F.E g)
  intro S hle hs
  have hi : ∀ x ∈ S, ∀ y ∈ S, q.polarBilin x y = 0 := by
    intro x hx y hy
    rw [QuadraticMap.polarBilin_apply_apply,QuadraticMap.polar,hs (x+y) (S.add_mem hx hy),
      hs x hx,hs y hy]
    simp
  have hb := LinearMap.BilinForm.twice_finrank_le_of_isotropic q.polarBilin hnd S hi
  obtain ⟨a,ha⟩ := AlternatingForm.even_finrank
    (F.uhatBilinearForm hn d.two d.frattini_point)
    (F.uhatBilinearForm_isAlt hn d.two d.frattini_point)
    (F.uhatBilinearForm_nondegenerate hn d.two d.frattini_point)
  exact (Submodule.eq_of_le_of_finrank_le hle (by omega)).symm

omit [Finite G] in
noncomputable def hatTildeEquiv_of_center_point (F : InvariantFlag T V n)
    [IsElementaryAbelian 2 V] (hZ : F.ZU = F.Vi 1) : F.Uhat ≃* F.tilde F.U :=
  (QuotientGroup.quotientMulEquivOfEq (center_eq_point_subgroup F hZ)).trans F.utildeEquiv

omit [Finite G] in
@[simp] theorem hatTildeEquiv_of_center_point_apply_mk (F : InvariantFlag T V n)
    [IsElementaryAbelian 2 V] (hZ : F.ZU = F.Vi 1) (u : F.U) :
    hatTildeEquiv_of_center_point F hZ (QuotientGroup.mk' (center F.U) u) =
      F.tildeMap F.U F.U_le_H u := by
  change F.utildeEquiv (QuotientGroup.mk' ((F.Vi 1).subgroupOf F.U) u) = _
  exact F.utildeEquiv_apply_mk u

omit [Finite G] in
theorem hatTildeEquiv_of_center_point_inverse (F : InvariantFlag T V n)
    [IsElementaryAbelian 2 V] (hn : 1 ≤ n) (hZ : F.ZU = F.Vi 1) :
    (hatTildeEquiv_of_center_point F hZ).symm.toMonoidHom = F.tildeToUhat hn := by
  ext x
  obtain ⟨u,rfl⟩ := F.tildeMap_surjective F.U F.U_le_H x
  change (hatTildeEquiv_of_center_point F hZ).symm (F.tildeMap F.U F.U_le_H u) = _
  calc
    _ = QuotientGroup.mk' (center F.U) u := by
      rw [← hatTildeEquiv_of_center_point_apply_mk F hZ u, MulEquiv.symm_apply_apply]
    _ = _ := (F.tildeToUhat_apply_map hn u).symm

omit [Finite G] in
theorem tildeToUhat_bijective_of_center_point (F : InvariantFlag T V n)
    [IsElementaryAbelian 2 V] (hn : 1 ≤ n) (hZ : F.ZU = F.Vi 1) :
    Function.Bijective (F.tildeToUhat hn) := by
  rw [← hatTildeEquiv_of_center_point_inverse F hn hZ]
  exact (hatTildeEquiv_of_center_point F hZ).symm.bijective

omit [Finite G] in
noncomputable def terminalStarEquiv_of_center_point (F : InvariantFlag T V n)
    [IsElementaryAbelian 2 V] (d : ClosureGeometry F) (hZ : F.ZU = F.Vi 1) :
    F.TerminalHdot ≃* HStar F.H :=
  QuotientGroup.quotientMulEquivOfEq (terminal_kernel_of_center_point F d hZ)

omit [Finite G] in
@[simp] theorem terminalStarEquiv_of_center_point_apply_mk (F : InvariantFlag T V n)
    [IsElementaryAbelian 2 V] (d : ClosureGeometry F) (hZ : F.ZU = F.Vi 1) (h : F.H) :
    terminalStarEquiv_of_center_point F d hZ (QuotientGroup.mk' F.terminalHatAction.ker h) =
      QuotientGroup.mk' (pCore 2 F.H) h := rfl

/-- The original square quadratic form on the literal central quotient. -/
noncomputable def centerPointQuadraticForm (F : InvariantFlag T V n)
    [IsElementaryAbelian 2 V] [IsElementaryAbelian 2 F.Uhat]
    (d : ClosureGeometry F) (hn : 1 ≤ n) (hZ : F.ZU = F.Vi 1) :
    QuadraticForm (ZMod 2) (Additive F.Uhat) :=
  F.uhatQuadraticForm hn d.two d.frattini_point
    (center_frattini_bot_of_center_point F d hZ)

end CFSG.Quasithin.Chapter14.Section03.NonabelianSource.Recognition
