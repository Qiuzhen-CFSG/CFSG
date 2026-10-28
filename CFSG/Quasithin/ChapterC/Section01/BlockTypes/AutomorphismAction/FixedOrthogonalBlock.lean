module
public import CFSG.Quasithin.ChapterC.Section01.BlockTypes.AutomorphismAction.FixedOrthogonalCoordinates
public import CFSG.Quasithin.ChapterC.Section01.BlockTypes.NaturalExtensionRecognition

/-!
# Recognizing the full-cover fixed block

The coherent fixed orthogonal coordinates give the literal natural central
quotient, commutator generation and short-block properties when the fixed
field has more than two elements. The same marking identifies its center
with the original center intersected with the fixed group. A nonzero radical
vector proves this center is nontrivial.

Source: Aschbacher--Smith 2.4.12(2) and 2.4.23(1), printed pp.532,537.
-/

public section
noncomputable section
open Subgroup Representation Theory.SpecificGroups.SymplecticFour
namespace CFSG.Quasithin.ChapterC
variable {L : Type*} [Group L] [Finite L]

/-- The marked fixed group is the full central-cover block at half the degree. -/
theorem FixedOrthogonalCoordinates.fixed_block {n : ℕ} {a : MulAut L}
    (c : FixedOrthogonalCoordinates L n a)
    (hQ : IsElementaryAbelian 2 ((pCore 2 L).subgroupOf a.fixedSubgroup))
    (hn : 4 ≤ n) :
    ∃m:ℕ,1<m ∧ n=2*m ∧ IsL2EvenBlock a.fixedSubgroup m ∧
      pCore 2 a.fixedSubgroup = (pCore 2 L).subgroupOf a.fixedSubgroup ∧
      center a.fixedSubgroup = (center L).subgroupOf a.fixedSubgroup ∧
      center a.fixedSubgroup ≠ ⊥ := by
  obtain ⟨m,hm,hnm,hcard⟩ := c.fixed_field_parameters
  have hm' : 1<m := by omega
  let K := FixedBy.subfield c.F c.coefficient
  let : Algebra (ZMod 2) K := ZMod.algebra K 2
  let Q := (pCore 2 L).subgroupOf a.fixedSubgroup
  have hc : 2<Nat.card K := by
    rw [hcard]
    exact lt_of_lt_of_le (by decide : 2<2^2) (Nat.pow_le_pow_right (by decide : 0<2) hm')
  let d : NaturalExtension (F:=K) Q := naturalExtensionOfOrthogonal hQ
    c.actor c.actor_surjective c.actor_kernel hc c.core c.conjugation_equivariant
  have hzQ : center a.fixedSubgroup ≤ Q := by
    rw [←d.centralizer_eq]
    intro z hz
    rw [mem_centralizer_iff]
    intro u hu
    exact mem_center_iff.mp hz u
  have hcenter : center a.fixedSubgroup = (center L).subgroupOf a.fixedSubgroup := by
    ext z
    constructor
    · intro hz
      exact c.center_detection ⟨z,hzQ hz⟩ (fun l => by
        apply Subtype.ext
        exact mul_inv_eq_iff_eq_mul.mpr (mem_center_iff.mp hz l))
    · intro hz
      rw [mem_center_iff]
      intro l
      apply Subtype.ext
      exact mem_center_iff.mp hz l
  let v : SL2OrthogonalCover.Space K := ![1,0,0]
  let u : Q := c.core.symm (Multiplicative.ofAdd v)
  have hu : (u:a.fixedSubgroup) ∈ center a.fixedSubgroup := by
    rw [mem_center_iff]
    intro l
    have hh : MulAut.conjNormal l u=u := by
      apply c.core.injective
      apply Multiplicative.toAdd.injective
      rw [c.conjugation_equivariant]
      change SL2OrthogonalCover.action (c.actor l) (c.core (c.core.symm _)).toAdd = (c.core (c.core.symm _)).toAdd
      rw [c.core.apply_symm_apply]
      exact (show v∈Representation.OneCohomology.fixed (SL2OrthogonalCover.action (F:=K)) from by
        rw [SL2OrthogonalCover.fixed_radical,SL2OrthogonalCover.mem_polar_ker]
        exact ⟨rfl,rfl⟩) (c.actor l)
    exact mul_inv_eq_iff_eq_mul.mp (congrArg Subtype.val hh)
  have hne : center a.fixedSubgroup ≠ ⊥ := by
    intro hz
    have hue : u=1 := Subtype.ext (show (u:a.fixedSubgroup)=1 from mem_bot.mp (hz ▸ hu))
    have h := congrArg (fun w:Q => (c.core w).toAdd 0) hue
    simp [u,v] at h
  exact ⟨m,hm',hnm,isL2EvenBlock_of_naturalExtension d hm' hcard,d.core_eq hc,hcenter,hne⟩
end CFSG.Quasithin.ChapterC
