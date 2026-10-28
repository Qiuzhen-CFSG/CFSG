module
public import CFSG.Quasithin.ChapterC.Section01.BlockTypes.AutomorphismAction.FixedOrthogonalCoordinates
public import Theory.ElementaryAbelian.Injective
public import Theory.SpecificGroups.SL2.UpperUnipotent

/-!
# The structure of the original orthogonal fixed group

The marked full-cover action is faithful on its natural quotient. Consequently
the literal fixed two-core is self-centralizing. The radical supplies a
nontrivial central element, and the coherent center detection identifies the
fixed group's center with the fixed part of the original center.

An abelian Sylow two-subgroup would centralize the normal elementary fixed core
and hence equal it. Its image would be a trivial Sylow two-subgroup of SL₂ over
the coefficient fixed field, contradicting the nontrivial upper root. This
argument includes the two-element fixed field.

Source: Aschbacher–Smith, Lemmas 2.4.12(2) and 2.4.23(1), printed pp.532,537.
-/

public section
noncomputable section
open Subgroup Representation
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterC
variable {L : Type*} [Group L] {n : ℕ} {a : MulAut L}
namespace FixedOrthogonalCoordinates
variable (c : FixedOrthogonalCoordinates L n a)
include c

/-- The literal fixed core is self-centralizing, including the binary fixed field. -/
theorem centralizer_core_eq :
    centralizer ((pCore 2 L).subgroupOf a.fixedSubgroup : Set a.fixedSubgroup) =
      (pCore 2 L).subgroupOf a.fixedSubgroup := by
  apply le_antisymm
  · intro l hl
    rw [← c.actor_kernel, MonoidHom.mem_ker]
    apply Subtype.ext
    apply Matrix.ext_iff_mulVec.mpr
    intro v
    let w : SL2OrthogonalCover.Space (FixedBy.subfield c.F c.coefficient) := ![0, v 0, v 1]
    obtain ⟨u, hu⟩ := c.core.surjective (Multiplicative.ofAdd w)
    have hc : MulAut.conjNormal l u = u := by
      apply Subtype.ext
      change l * (u : a.fixedSubgroup) * l⁻¹ = u
      rw [← mem_centralizer_iff.mp hl u u.property, mul_inv_cancel_right]
    have hi := c.conjugation_equivariant l u
    rw [hc, hu] at hi
    have hp := congrArg SL2OrthogonalCover.projection hi
    rw [SL2OrthogonalCover.projection.isIntertwining] at hp
    change SL2OrthogonalCover.projection w =
      SL2OrthogonalCover.natural (c.actor l) (SL2OrthogonalCover.projection w) at hp
    have hw : SL2OrthogonalCover.projection w = v := by
      ext i
      fin_cases i <;> rfl
    rw [hw] at hp
    simpa only [SL2OrthogonalCover.natural, specialLinearNatural_apply,
      Matrix.SpecialLinearGroup.coe_one, Matrix.one_mulVec] using hp.symm
  · intro l hl
    rw [mem_centralizer_iff]
    intro u hu
    have he : (⟨u, hu⟩ : (pCore 2 L).subgroupOf a.fixedSubgroup) * ⟨l, hl⟩ =
        ⟨l, hl⟩ * ⟨u, hu⟩ := by
      apply c.core.injective
      rw [map_mul, map_mul, mul_comm]
    exact congrArg Subtype.val he

/-- The fixed group's center is the literal fixed part of the original center. -/
theorem center_eq : center a.fixedSubgroup = (center L).subgroupOf a.fixedSubgroup := by
  have hzQ : center a.fixedSubgroup ≤ (pCore 2 L).subgroupOf a.fixedSubgroup := by
    rw [← c.centralizer_core_eq]
    exact center_le_centralizer _
  ext z
  constructor
  · intro hz
    exact c.center_detection ⟨z, hzQ hz⟩ (fun l => by
      apply Subtype.ext
      exact mul_inv_eq_iff_eq_mul.mpr (mem_center_iff.mp hz l))
  · intro hz
    rw [mem_center_iff]
    intro l
    apply Subtype.ext
    exact mem_center_iff.mp hz l

/-- A nonzero radical vector gives a nontrivial original-center fixed element. -/
theorem center_ne_bot : center a.fixedSubgroup ≠ ⊥ := by
  let K := FixedBy.subfield c.F c.coefficient
  let Q := (pCore 2 L).subgroupOf a.fixedSubgroup
  let v : SL2OrthogonalCover.Space K := ![1, 0, 0]
  let u : Q := c.core.symm (Multiplicative.ofAdd v)
  have hu : (u : a.fixedSubgroup) ∈ center a.fixedSubgroup := by
    rw [mem_center_iff]
    intro l
    have hh : MulAut.conjNormal l u = u := by
      apply c.core.injective
      apply Multiplicative.toAdd.injective
      rw [c.conjugation_equivariant]
      change SL2OrthogonalCover.action (c.actor l) (c.core (c.core.symm _)).toAdd =
        (c.core (c.core.symm _)).toAdd
      rw [c.core.apply_symm_apply]
      exact (show v ∈ Representation.OneCohomology.fixed (SL2OrthogonalCover.action (F := K)) from by
        rw [SL2OrthogonalCover.fixed_radical, SL2OrthogonalCover.mem_polar_ker]
        exact ⟨rfl, rfl⟩) (c.actor l)
    exact mul_inv_eq_iff_eq_mul.mp (congrArg Subtype.val hh)
  intro hz
  have hue : u = 1 := Subtype.ext (show (u : a.fixedSubgroup) = 1 from mem_bot.mp (hz ▸ hu))
  have h := congrArg (fun w : Q => (c.core w).toAdd 0) hue
  simp [u, v] at h

/-- Every Sylow two-subgroup of the original fixed group is nonabelian. -/
theorem sylow_nonabelian [Finite L]
    (hQ : IsElementaryAbelian 2 ((pCore 2 L).subgroupOf a.fixedSubgroup))
    (P : Sylow 2 a.fixedSubgroup) : ¬ IsMulCommutative P := by
  intro hP
  let := hP
  let := hQ
  let K := FixedBy.subfield c.F c.coefficient
  let Q := (pCore 2 L).subgroupOf a.fixedSubgroup
  have hQP : Q ≤ P := (IsElementaryAbelian.isPGroup 2 Q).le_sylow_of_normal P
  have hPQ : (P : Subgroup a.fixedSubgroup) ≤ Q := by
    change (P : Subgroup a.fixedSubgroup) ≤
      (pCore 2 L).subgroupOf a.fixedSubgroup
    rw [← c.centralizer_core_eq]
    intro l hl
    rw [mem_centralizer_iff]
    intro u hu
    exact congrArg Subtype.val (mul_comm (⟨u, hQP hu⟩ : P) ⟨l, hl⟩)
  let S : Sylow 2 (SL2OrthogonalCover.SL K) := P.mapSurjective c.actor_surjective
  have hS : (S : Subgroup (SL2OrthogonalCover.SL K)) = ⊥ := by
    apply bot_unique
    intro g hg
    change g = 1
    obtain ⟨l, hl, rfl⟩ := hg
    rw [← MonoidHom.mem_ker, c.actor_kernel]
    exact hPQ hl
  let U := Matrix.SpecialLinearGroup.upperUnipotentSylow K 2
  have hU : (U : Subgroup (SL2OrthogonalCover.SL K)) = ⊥ := by
    have heq : (U : Subgroup (SL2OrthogonalCover.SL K)) = S :=
      S.is_maximal' U.isPGroup' (hS ▸ bot_le)
    rw [hS] at heq
    exact heq
  have ht : SL2OrthogonalCover.upper (1 : K) ∈ U :=
    (Matrix.SpecialLinearGroup.mem_upperUnipotent K _).mpr ⟨1, rfl⟩
  have he : SL2OrthogonalCover.upper (1 : K) = 1 := mem_bot.mp (hU ▸ ht)
  have hh := congrArg (fun g : SL2OrthogonalCover.SL K => g.val 0 1) he
  have h01 : (SL2OrthogonalCover.upper (1 : K)).val 0 1 = 1 := by
    simp [SL2OrthogonalCover.upper, Matrix.SpecialLinearGroup.transvection_coe]
  simp [h01] at hh
end FixedOrthogonalCoordinates

/-- The actual outer full-cover involution supplies all three fixed-group
structure conclusions without a lower bound on its coefficient fixed field. -/
theorem IsL2EvenBlock.fixed_orthogonal_structure (hL : IsL2EvenBlock L n)
    (hcore : pCore 2 L = blockU L) (hz : Nat.card (center L) = 2 ^ n)
    (a : MulAut L) (ha : a ^ 2 = 1)
    (houter : ¬ ∃ g, quotientAut (pCore 2 L) a = MulAut.conj g) :
    centralizer ((pCore 2 L).subgroupOf a.fixedSubgroup : Set a.fixedSubgroup) =
      (pCore 2 L).subgroupOf a.fixedSubgroup ∧
    center a.fixedSubgroup = (center L).subgroupOf a.fixedSubgroup ∧
    center a.fixedSubgroup ≠ ⊥ ∧
    ∀ P : Sylow 2 a.fixedSubgroup, ¬ IsMulCommutative P := by
  let := hL.2.1.finite
  let : IsElementaryAbelian 2 (pCore 2 L) := hcore ▸ hL.2.1.elementary
  let f : ((pCore 2 L).subgroupOf a.fixedSubgroup) →* pCore 2 L :=
    { toFun u := ⟨u.val.val, u.property⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  have hf : Function.Injective f := by
    intro u v huv
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun x : pCore 2 L => x.val) huv
  have hQ : IsElementaryAbelian 2 ((pCore 2 L).subgroupOf a.fixedSubgroup) :=
    IsElementaryAbelian.of_injective f hf
  obtain ⟨c⟩ := hL.fixed_orthogonal_coordinates hcore hz a ha houter
  exact ⟨c.centralizer_core_eq, c.center_eq, c.center_ne_bot, c.sylow_nonabelian hQ⟩
end CFSG.Quasithin.ChapterC
