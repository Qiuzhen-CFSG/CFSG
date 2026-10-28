module
public import Theory.Representation.BinaryDoubledNaturalNormalizer
public import Theory.Representation.NormalPSubgroupKernel
public import Theory.SpecificGroups.SL2.BinaryDihedral
public import Theory.SpecificGroups.DihedralSolvable

/-!
# Multiplicity obstruction in the binary doubled-natural normalizer

The literal normalizer of two copies of the natural SL₃(2)-module is
SL₃(2) × SL₂(2). Projecting to the second factor records its action on
multiplicities. A two-group image fixes a nonzero multiplicity vector,
hence preserves a proper natural copy. Thus its full action is reducible.
Since SL₂(2) is solvable of order six, an image prime to three is a two-group.

The Chapter 10 selected-module consumer obtains the prime-to-three condition
from the actual cubic residual and contradicts irreducibility from minimality.
Source: Aschbacher--Smith, B.5.6 and D.3.21, printed pp.105 and204--207.
-/

public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Subgroup Matrix
namespace Representation.SL3DoubledNaturalOffenders

/-- The literal multiplicity projection of the binary doubled-natural normalizer. -/
def binaryMultiplicity : normalizer (ZMod 2) →* MultiplicitySL (ZMod 2) :=
  (MonoidHom.snd _ _).comp binaryNormalizerEquiv.toMonoidHom

private def naturalCopy (u : Fin 2 → ZMod 2) :
    Natural (ZMod 2) →ₗ[ZMod 2] Space (ZMod 2) where
  toFun w i := u i • w
  map_add' _ _ := by ext i j; exact mul_add _ _ _
  map_smul' _ _ := by ext i j; exact mul_left_comm _ _ _

private theorem tensor_naturalCopy
    (g : SL (ZMod 2) × MultiplicitySL (ZMod 2)) (u : Fin 2 → ZMod 2) (w : Natural (ZMod 2)) :
    tensorRepresentation (ZMod 2) g (naturalCopy u w) =
      naturalCopy (g.2.val.mulVec u) (g.1.val.mulVec w) := by
  funext i
  change g.1.val.mulVec (g.2.val i 0 • (u 0 • w) + g.2.val i 1 • (u 1 • w)) = _
  rw [smul_smul,smul_smul,←add_smul,Matrix.mulVec_smul]
  change _ = (g.2.val.mulVec u) i • (g.1.val.mulVec w)
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two]

/-- A two-group multiplicity image fixes a nonzero multiplicity vector,
hence a proper natural copy. The whole doubled action is reducible. -/
theorem not_irreducible_of_binaryMultiplicity_twoGroup
    {H : Type*} [Group H] [Finite H] (f : H →* normalizer (ZMod 2))
    (hp : IsPGroup 2 (binaryMultiplicity.comp f).range) :
    ¬ IsIrreducible ((action (ZMod 2)).comp ((normalizer (ZMod 2)).subtype.comp f)) := by
  let μ := binaryMultiplicity.comp f
  let σ := (specialLinearNatural (k := ZMod 2) 2).comp μ.range.subtype
  have hc : ringChar (ZMod 2) = 2 := ringChar.eq (ZMod 2) 2
  obtain ⟨u,hu,hfix⟩ := pGroup_fix_nonzero_vector (by omega : ringChar (ZMod 2) ≠ 0)
    (by rw [hc]; exact hp) σ
  have hufix (h : H) : (μ h).val.mulVec u = u := hfix (μ.rangeRestrict h)
  let τ := (action (ZMod 2)).comp ((normalizer (ZMod 2)).subtype.comp f)
  let C : Subrepresentation τ := {
    toSubmodule := (naturalCopy u).range
    apply_mem_toSubmodule := by
      intro h v hv
      obtain ⟨w,rfl⟩ := hv
      refine ⟨(binaryNormalizerEquiv (f h)).1.val.mulVec w,?_⟩
      change naturalCopy u _ = (f h).val.val (naturalCopy u w)
      rw [binaryNormalizerEquiv_action,tensor_naturalCopy]
      change naturalCopy u _ = naturalCopy ((μ h).val.mulVec u) _
      rw [hufix] }
  have hi : Function.Injective (naturalCopy u) := by
    obtain ⟨i,hi⟩ := Function.ne_iff.mp hu
    have hi1 : u i = 1 := by
      have hh := (by decide : ∀ z : ZMod 2, z = 0 ∨ z = 1) (u i)
      exact hh.resolve_left hi
    intro w z he
    have hh := congrFun he i
    change u i • w = u i • z at hh
    simpa only [hi1,one_smul] using hh
  have hd : Module.finrank (ZMod 2) C.toSubmodule = 3 := by
    change Module.finrank (ZMod 2) (naturalCopy u).range = 3
    rw [LinearMap.finrank_range_of_inj hi]
    exact Module.finrank_fin_fun (ZMod 2)
  intro hirr
  let := hirr
  rcases eq_bot_or_eq_top C with hb | ht
  · have he : C.toSubmodule = ⊥ := congrArg Subrepresentation.toSubmodule hb
    rw [he,finrank_bot] at hd
    omega
  · have he : C.toSubmodule = ⊤ := congrArg Subrepresentation.toSubmodule ht
    have hdim : Module.finrank (ZMod 2) (Space (ZMod 2)) = 6 := by
      simp [Space,Natural,Module.finrank_pi_fintype]
    rw [he,finrank_top,hdim] at hd
    omega

/-- The multiplicity group is the concrete solvable group of order six. -/
theorem binary_multiplicity_solvable : Group.IsSolvable (MultiplicitySL (ZMod 2)) := by
  let e := Matrix.SpecialLinearGroup.sl2TwoEquivPSL2Two.trans
    Theory.SpecificGroups.BinaryDihedral.dihedralThreeEquivPSL2Two.symm
  let := GLS3.Chapter5.dihedralGroup_isSolvable 3
  exact Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective

/-- Excluding three from a multiplicity image makes it a two-group. -/
theorem binary_multiplicity_twoGroup_of_three_free
    (P : Subgroup (MultiplicitySL (ZMod 2))) (hP : Nat.Coprime 3 (Nat.card P)) :
    IsPGroup 2 P := by
  have hc : Nat.card (MultiplicitySL (ZMod 2)) = 6 := by
    let e := Matrix.SpecialLinearGroup.sl2TwoEquivPSL2Two.trans
      Theory.SpecificGroups.BinaryDihedral.dihedralThreeEquivPSL2Two.symm
    rw [Nat.card_congr e.toEquiv,DihedralGroup.nat_card]
  have hd := card_subgroup_dvd_card P
  rw [hc] at hd
  have h : Nat.card P ∣ 2 := hP.symm.dvd_of_dvd_mul_right hd
  exact IsPGroup.of_card_dvd_pow (n := 1) h

end Representation.SL3DoubledNaturalOffenders
