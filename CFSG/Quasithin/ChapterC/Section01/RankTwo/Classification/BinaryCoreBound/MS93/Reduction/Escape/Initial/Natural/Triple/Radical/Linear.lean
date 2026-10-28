module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.Initial.Natural.Triple.Composition.Residual
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.Initial.Natural.Triple.Quotient
public import Theory.Representation.NormalInvariants

/-!
# Rank-one displacement and the radical-fixed space

Suppose an actor with nontrivial image in the local SL₃(2) quotient has
fixed codimension at most one. If the two-residual moves the kernel-fixed
space, that subspace consumes the full codimension bound. The actor fixes
the quotient by this subspace, so normal generation modulo the two-group
kernel makes the residual fix that quotient too. Thus the residual moving
space is fixed by the kernel.

Annihilator duality translates fixed-space containment on the literal dual
back into group commutator containment, retaining the quotient kernel.
This is the representation implication used in the binary dual-module step
of Meierfrankenfeld--Stellmacher (1993), (4.3.1)(iii), p.883. The geometric
nontriviality premise is proved separately, rather than assuming descent or
splitting an extension.
-/

public section

open Subgroup Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.Initial.Natural.Triple
variable {G E : Type*} [Group G] [AddCommGroup E] [Module (ZMod 2) E]
  [FiniteDimensional (ZMod 2) E]

theorem moving_le_fixed_of_fixedSpace_not_le
    (π : G →* BinaryLinearThree.Group) (hπ : Function.Surjective π)
    (hk : IsPGroup 2 π.ker) (A : Subgroup G) (hne : A.map π ≠ ⊥)
    (ρ : Representation (ZMod 2) G E) (hd : fixedCodim ρ A ≤ 1)
    (hn : ¬ fixedSpace ρ π.ker ≤ fixedSpace ρ (pResidual 2 G)) :
    Coinvariants.ker (ρ.comp (pResidual 2 G).subtype) ≤ fixedSpace ρ π.ker := by
  let W := fixedSubrepresentationOfNormal ρ π.ker
  have hpos : 0 < fixedCodim W.toRepresentation A := by
    by_contra! hz
    have hzero := (fixedCodim_eq_zero_iff W.toRepresentation A).mp
      (Nat.eq_zero_of_le_zero hz)
    have hfix := Composition.residual_fixed_of_actor_fixed π hπ hk A hne
      W.toRepresentation hzero
    apply hn
    intro v hv g
    have hh : (⟨v, hv⟩ : W.toSubmodule) ∈ fixedSpace W.toRepresentation
        (pResidual 2 G) := by rw [hfix]; trivial
    exact congrArg Subtype.val (hh g)
  have hb := fixedCodim_quotient_add_subrepresentation_le ρ W A
  have hz : fixedCodim W.quotientRepresentation A = 0 := by omega
  have hf := Composition.residual_fixed_of_actor_fixed π hπ hk A hne
    W.quotientRepresentation ((fixedCodim_eq_zero_iff _ _).mp hz)
  apply Submodule.span_le.mpr
  rintro _ ⟨⟨g, v⟩, rfl⟩
  have hh : W.toSubmodule.mkQ v ∈ fixedSpace W.quotientRepresentation
      (pResidual 2 G) := by rw [hf]; trivial
  have he := hh g
  change W.toSubmodule.mkQ (ρ g v) = W.toSubmodule.mkQ v at he
  exact (Submodule.Quotient.mk_eq_zero W.toSubmodule).mp (by
    change W.toSubmodule.mkQ (ρ g v - v) = 0
    rw [map_sub, he, sub_self])


variable {G : Type*} [Group G] (H N : Subgroup G) [H.Normal] [N.Normal]
  [IsElementaryAbelian 2 (H ⧸ N.subgroupOf H)]

omit [H.Normal] in
/-- An inclusion of literal quotient images lifts with precisely the original kernel. -/
theorem le_sup_of_quotientImage_le (D E : Subgroup G) (hD : D ≤ H)
    (hi : quotientImage H N D ≤ quotientImage H N E) : D ≤ N ⊔ E := by
  intro x hx
  let xH : H := ⟨x, hD hx⟩
  let q := QuotientGroup.mk' (N.subgroupOf H)
  have hm : Additive.ofMul (q xH) ∈ quotientImage H N D := ⟨xH, hx, rfl⟩
  obtain ⟨y, hy, he⟩ := hi hm
  have he' : q y = q xH := he
  have hxy : x * (y : G)⁻¹ ∈ N := by
    have hh : q (xH * y⁻¹) = 1 := by rw [map_mul, map_inv, he', mul_inv_cancel]
    have hk : xH * y⁻¹ ∈ N.subgroupOf H := (QuotientGroup.eq_one_iff _).mp hh
    exact hk
  rw [show x = (x * (y : G)⁻¹) * y by simp]
  exact (N ⊔ E).mul_mem ((show N ≤ N ⊔ E from le_sup_left) hxy)
    ((show E ≤ N ⊔ E from le_sup_right) hy)

/-- Dual fixed-space containment reverses to containment of group commutators,
with the exact quotient kernel retained. -/
theorem commutator_le_sup_of_dual_fixedSpace_le (A B : Subgroup G)
    (h : fixedSpace (sectionRepresentation H N).dual A ≤
      fixedSpace (sectionRepresentation H N).dual B) : ⁅H, B⁆ ≤ N ⊔ ⁅H, A⁆ := by
  let ρ := sectionRepresentation H N
  have hcomp (D : Subgroup G) : Representation.dual (ρ.comp D.subtype) = ρ.dual.comp D.subtype := by
    ext g f v
    rfl
  change invariants (ρ.dual.comp A.subtype) ≤ invariants (ρ.dual.comp B.subtype) at h
  rw [← hcomp A, ← hcomp B, invariants_dual_eq_commutator_annihilator,
    invariants_dual_eq_commutator_annihilator] at h
  have hm := Subspace.dualAnnihilator_le_dualAnnihilator_iff.mp h
  rw [commutatorSpace_eq_image, commutatorSpace_eq_image] at hm
  exact le_sup_of_quotientImage_le H N _ _ (commutator_le_left H B) hm

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.Initial.Natural.Triple
