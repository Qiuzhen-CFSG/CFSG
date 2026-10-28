module
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.SylowGeometry.SourceWitnesses.MarkedProduct.QuotientCoordinates
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.SylowGeometry.SourceWitnesses.MarkedProduct.Concrete.NoStrong
public import CFSG.Quasithin.ChapterB.Section02.Baumann

/-!
# Source hypotheses for Baumann’s argument

The literal orthogonal action identifies both the faithful action quotient and its fixed spaces. The checked elementary-image bound therefore proves the quantitative no-strong-offender hypothesis of B.2.18, including elementary images without elementary lifts.

Source: Aschbacher–Smith, B.2.18 and15.4.12(4–6), pp.81 and1160–1161.
-/

@[expose] public section
open Subgroup Stellmacher
open OrthogonalFourBinary OrthogonalFourBinary.TerminalLines OrthogonalFourBinary.SylowGeometry
namespace CFSG.Quasithin.Chapter15.Section04.LocalSetup.SourceWitnesses.MarkedProduct
open FamilySource FamilySource.ModuleStructure
open FamilySource.ModuleStructure.BinaryNormalizer FamilySource.ModuleStructure.BaumannPair
open ChapterB.BaumannArgument
variable {G : Type*} [Group G] [Finite G]
omit [Finite G] in
theorem Action.kernel {W : Subgroup G} (d : Action W) :
    d.actor.ker = centralizer (W : Set G) := by
  ext g
  constructor
  · intro hg w hw
    have hh := d.intertwines g ⟨w,hw⟩
    rw [show d.actor g = 1 from hg, map_one] at hh
    change (d.coordinates.symm (d.coordinates ⟨w,hw⟩) : G) = g*w*g⁻¹ at hh
    rw [d.coordinates.symm_apply_apply] at hh
    exact (mul_inv_eq_iff_eq_mul.mp hh.symm).symm
  · intro hg
    apply vectorAction_injective
    apply MulEquiv.ext
    intro v
    let w := d.coordinates.symm v
    have hh := d.intertwines g w
    rw [d.coordinates.apply_symm_apply] at hh
    have he : g * (w : G) * g⁻¹ = w := mul_inv_eq_iff_eq_mul.mpr (hg w w.property).symm
    have hcv : d.coordinates.symm (vectorAction (d.actor g) v) = d.coordinates.symm v :=
      Subtype.ext (hh.trans he)
    exact d.coordinates.symm.injective hcv


omit [Finite G] in
noncomputable def Action.fixedEquiv {W : Subgroup G} (d : Action W) (A : Subgroup G) :
    (W ⊓ centralizer (A : Set G) : Subgroup G) ≃ FixedVectors (A.map d.actor) where
  toFun w := ⟨(d.coordinates ⟨w,w.property.1⟩).toAdd, by
    rintro _ ⟨a,ha,rfl⟩
    change vectorAction (d.actor a) (d.coordinates ⟨w,w.property.1⟩) =
      d.coordinates ⟨w,w.property.1⟩
    apply d.coordinates.symm.injective
    apply Subtype.ext
    rw [d.coordinates.symm_apply_apply]
    exact (d.intertwines a ⟨w,w.property.1⟩).trans
      (mul_inv_eq_iff_eq_mul.mpr (w.property.2 a ha))⟩
  invFun v := ⟨d.coordinates.symm (Multiplicative.ofAdd v.val),
    (d.coordinates.symm (Multiplicative.ofAdd v.val)).property, by
      intro a ha
      have he := d.intertwines a (d.coordinates.symm (Multiplicative.ofAdd v.val))
      rw [d.coordinates.apply_symm_apply] at he
      have hf := v.property (d.actor a) (mem_map.mpr ⟨a,ha,rfl⟩)
      change vectorAction (d.actor a) (Multiplicative.ofAdd v.val) = Multiplicative.ofAdd v.val at hf
      rw [hf] at he
      exact mul_inv_eq_iff_eq_mul.mp he.symm⟩
  left_inv w := by
    apply Subtype.ext
    exact congrArg (fun x : W => (x : G)) (d.coordinates.symm_apply_apply ⟨w,w.property.1⟩)
  right_inv v := by
    apply Subtype.ext
    exact d.coordinates.apply_symm_apply (Multiplicative.ofAdd v.val)

noncomputable def Action.faithfulQuotient {W : Subgroup G} [W.Normal] (d : Action W) :
    (G ⧸ centralizer (W : Set G)) ≃* d.actor.range :=
  (QuotientGroup.quotientMulEquivOfEq (Action.kernel d).symm).trans
    (QuotientGroup.quotientKerEquivRange d.actor)

omit [Finite G] in
theorem Action.noStrong {W : Subgroup G} [W.Normal] (d : Action W) (R : Subgroup G) :
    NoStrongOffenders W R := by
  intro A _ hAe _
  let e := Action.faithfulQuotient d
  let f := d.actor.range.subtype.comp e.toMonoidHom
  have hf : Function.Injective f := d.actor.range.subtype_injective.comp e.injective
  have he : f.comp (actionMap W) = d.actor := by
    apply MonoidHom.ext
    intro g
    rfl
  have hmap : (A.map (actionMap W)).map f = A.map d.actor := by rw [map_map,he]
  have hcard : Nat.card (A.map d.actor) = Nat.card (A.map (actionMap W)) := by
    rw [←hmap,card_map_of_injective hf]
  let : IsElementaryAbelian 2 (A.map d.actor) := hmap ▸ hAe.map f
  have hc := Concrete.elementary_rank_le_fixed_codim (A.map d.actor)
  have hw : Nat.card W = 16 := by
    rw [Nat.card_congr d.coordinates.toEquiv,Nat.card_eq_fintype_card]
    decide +kernel
  rw [hcard,←Nat.card_congr (Action.fixedEquiv d A)] at hc
  change _ ≤ Nat.log 2 (Nat.card W) - _
  rw [hw]
  exact hc

end CFSG.Quasithin.Chapter15.Section04.LocalSetup.SourceWitnesses.MarkedProduct
