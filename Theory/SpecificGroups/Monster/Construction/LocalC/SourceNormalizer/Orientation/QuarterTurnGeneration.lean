module

public import Theory.SpecificGroups.Monster.Construction.LocalC.SourceNormalizer.Orientation.QuarterTurnGeneration.CentralAction
public import Theory.SpecificGroups.Monster.Construction.LocalC.SourceNormalizer.Orientation.QuarterTurnGeneration.HyperbolicModel
public import Theory.SpecificGroups.ClassicalOrthogonal.SplitOdd.ReflectionGeneration

/-!
# Quarter turns generate the actual extraspecial automorphism group

Nonsingular spanning puts every inner automorphism in the subgroup generated
by quarter turns. Factor a central isometry into nonsingular symmetries and
lift each factor to the explicit quarter turn. The discrepancy acts trivially
on the central quotient and is inner, completing the group-theoretic reduction.

The actual central square form is isometric to the split binary form in
dimension 24. Transporting its symmetry factorization through that isometry,
and using the proved nonsingular spanning theorem, discharges both geometric
premises of the reduction and gives unconditional generation on `Q1Image`.

Source: Aschbacher, *Sporadic Groups*, Exercise 4.4, p. 64, as used in the spin
normalizer calculation on pp. 147–148.
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false

open scoped commutatorElement IsMulCommutative
open Atlas.Codes
noncomputable section
namespace Sporadic.Monster.Construction.LocalC.SourceNormalizer
open TrialitySpin

theorem conj_eq_of_centralVector_eq {x y : Q1Image}
    (h : centralVector x = centralVector y) : MulAut.conj x = MulAut.conj y := by
  have hz : x * y⁻¹ ∈ Subgroup.center Q1Image := by
    apply (QuotientGroup.eq_one_iff _).mp
    change (QuotientGroup.mk' (Subgroup.center Q1Image)) (x*y⁻¹) = 1
    rw [map_mul,map_inv]
    have hh := congrArg Additive.toMul h
    change QuotientGroup.mk' (Subgroup.center Q1Image) x =
      QuotientGroup.mk' (Subgroup.center Q1Image) y at hh
    rw [hh,mul_inv_cancel]
  have he : MulAut.conj (x*y⁻¹) = 1 := by
    apply MulEquiv.ext
    intro z
    exact (show Commute (x*y⁻¹) z from
      (Subgroup.mem_center_iff.mp hz z).symm).mul_inv_cancel
  rw [map_mul,map_inv] at he
  exact mul_inv_eq_one.mp he

theorem inner_mem_of_nonsingular_span
    (hspan : Submodule.span Bit {v : CentralSpace | q1CentralQuadraticForm v = 1} = ⊤)
    (q : Q1Image) : MulAut.conj q ∈ Subgroup.closure quarterTurnAutomorphisms := by
  let H := Subgroup.closure quarterTurnAutomorphisms
  let K := H.comap (MulAut.conj : Q1Image →* MulAut Q1Image)
  let P := K.map (QuotientGroup.mk' (Subgroup.center Q1Image))
  let S : Submodule Bit CentralSpace := P.toAddSubgroup.toZModSubmodule 2
  have hle : Submodule.span Bit {v : CentralSpace | q1CentralQuadraticForm v = 1} ≤ S := by
    apply Submodule.span_le.mpr
    intro v hv
    obtain ⟨x,rfl⟩ := centralVector_surjective v
    exact ⟨x,nonsingular_conj_mem x ((centralVector_square_iff x).mp hv),rfl⟩
  have hv : centralVector q ∈ S := hle (by rw [hspan]; trivial)
  obtain ⟨x,hx,hxq⟩ := hv
  have he : MulAut.conj x = MulAut.conj q := conj_eq_of_centralVector_eq hxq
  exact he ▸ hx

theorem quarterTurnAutomorphisms_generate_of_lifts
    (hinner : ∀ q : Q1Image, MulAut.conj q ∈ Subgroup.closure quarterTurnAutomorphisms)
    (hlift : ∀ α : MulAut Q1Image, ∃ β : MulAut Q1Image,
      β ∈ Subgroup.closure quarterTurnAutomorphisms ∧
      ∀ x, centralVector (β x) = centralVector (α x)) :
    Subgroup.closure quarterTurnAutomorphisms = ⊤ := by
  apply top_unique
  intro α _
  obtain ⟨β,hβ,hagree⟩ := hlift α
  obtain ⟨q,hq⟩ := exists_inner_of_trivial_quotient (β⁻¹ * α) (by
    intro x
    change centralVector ((β⁻¹ * α) x) = centralVector x
    apply (centralAutomorphism β).injective
    rw [centralAutomorphism_vector,centralAutomorphism_vector]
    change centralVector (β (β.symm (α x))) = centralVector (β x)
    rw [β.apply_symm_apply,hagree])
  have hγ := hinner q
  rw [← hq] at hγ
  simpa using (Subgroup.closure quarterTurnAutomorphisms).mul_mem hβ hγ


private theorem symmetry_list_lift
    (as : List {v : CentralSpace // q1CentralQuadraticForm v = 1}) :
    ∃ β : MulAut Q1Image, β ∈ Subgroup.closure quarterTurnAutomorphisms ∧
      ∀ x : Q1Image, centralVector (β x) = as.foldr
        (fun a w => w + q1CentralQuadraticForm.polarBilin a.val w • a.val) (centralVector x) := by
  induction as with
  | nil => exact ⟨1,(Subgroup.closure _).one_mem,fun _ => rfl⟩
  | cons a as ih =>
    obtain ⟨β,hβ,hact⟩ := ih
    obtain ⟨q,hq⟩ := centralVector_surjective a.val
    have hq2 : q^2 = q1ImageCenterGenerator :=
      (centralVector_square_iff q).mp (hq ▸ a.property)
    refine ⟨quarterTurn q hq2 * β,
      (Subgroup.closure _).mul_mem (Subgroup.subset_closure (quarterTurn_mem q hq2)) hβ,?_⟩
    intro x
    change centralVector (quarterTurn q hq2 (β x)) = _
    rw [quarterTurn_centralVector,hact,hq]
    rfl

/-- Generation reduces to nonsingular spanning and symmetry factorization for the
actual central square form. These are separate geometric obligations. -/
theorem quarterTurnAutomorphisms_generate_of_quadratic_geometry
    (hspan : Submodule.span Bit {v : CentralSpace | q1CentralQuadraticForm v = 1} = ⊤)
    (hfactor : ∀ f : CentralSpace ≃ₗ[Bit] CentralSpace,
      (∀ v, q1CentralQuadraticForm (f v) = q1CentralQuadraticForm v) →
      ∃ as : List {v : CentralSpace // q1CentralQuadraticForm v = 1},
        ∀ v, f v = as.foldr
          (fun a w => w + q1CentralQuadraticForm.polarBilin a.val w • a.val) v) :
    Subgroup.closure quarterTurnAutomorphisms = ⊤ := by
  apply quarterTurnAutomorphisms_generate_of_lifts (inner_mem_of_nonsingular_span hspan)
  intro α
  obtain ⟨as,has⟩ := hfactor (centralAutomorphism α) (centralAutomorphism_preserves α)
  obtain ⟨β,hβ,hact⟩ := symmetry_list_lift as
  refine ⟨β,hβ,?_⟩
  intro x
  rw [hact, ← has, centralAutomorphism_vector]

/-- Isometries of the actual central square form factor into nonsingular symmetries,
transported through its constructed hyperbolic isometry. -/
theorem q1CentralQuadraticForm_symmetry_factorization
    (f : CentralSpace ≃ₗ[Bit] CentralSpace)
    (hf : ∀ v, q1CentralQuadraticForm (f v) = q1CentralQuadraticForm v) :
    ∃ as : List {v : CentralSpace // q1CentralQuadraticForm v = 1},
      ∀ v, f v = as.foldr
        (fun a w => w + q1CentralQuadraticForm.polarBilin a.val w • a.val) v := by
  let e := q1CentralHyperbolicIsometry
  let g := e.symm.toLinearEquiv.trans (f.trans e.toLinearEquiv)
  have hg (w) : ClassicalOrthogonal.formD 12 (ZMod 2) (g w) =
      ClassicalOrthogonal.formD 12 (ZMod 2) w := by
    change ClassicalOrthogonal.formD 12 (ZMod 2) (e (f (e.symm w))) = _
    rw [e.map_app, hf, e.symm.map_app]
  obtain ⟨as,has⟩ :=
    ClassicalOrthogonal.ReflectionGeneration.binary_split_24_symmetry_factorization g hg
  let pull : {a // ClassicalOrthogonal.formD 12 (ZMod 2) a = 1} →
      {v : CentralSpace // q1CentralQuadraticForm v = 1} :=
    fun a => ⟨e.symm a.val, (e.symm.map_app a.val).trans a.property⟩
  have hpolar (a w) :
      q1CentralQuadraticForm.polarBilin (e.symm a) (e.symm w) =
        (ClassicalOrthogonal.formD 12 (ZMod 2)).polarBilin a w :=
    ClassicalOrthogonal.Quadratic.isometry_between_polar _ _ e.symm a w
  have htransport (bs : List {a // ClassicalOrthogonal.formD 12 (ZMod 2) a = 1}) (w) :
      e.symm (bs.foldr
        (fun a u => u + (ClassicalOrthogonal.formD 12 (ZMod 2)).polarBilin a.val u • a.val) w) =
      (bs.map pull).foldr
        (fun a u => u + q1CentralQuadraticForm.polarBilin a.val u • a.val) (e.symm w) := by
    induction bs with
    | nil => rfl
    | cons a bs ih =>
      simp only [List.map_cons, List.foldr_cons, map_add, map_smul]
      dsimp only [pull]
      rw [← ih, hpolar]
  refine ⟨as.map pull, fun v => ?_⟩
  have h := congrArg e.symm (has (e v))
  change e.symm (e (f (e.symm (e v)))) = _ at h
  simpa only [e.symm_apply_apply, htransport] using h

/-- Quarter turns generate the full automorphism group of the actual extraspecial
group `Q1Image`. Their quotient symmetries generate every isometry, and their
squares generate the inner kernel. -/
theorem quarterTurnAutomorphisms_generate :
    Subgroup.closure quarterTurnAutomorphisms = ⊤ :=
  quarterTurnAutomorphisms_generate_of_quadratic_geometry
    q1CentralQuadraticForm_nonsingular_span q1CentralQuadraticForm_symmetry_factorization

end Sporadic.Monster.Construction.LocalC.SourceNormalizer
