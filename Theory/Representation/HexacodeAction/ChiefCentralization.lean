module

public import Theory.Representation.HexacodeAction.SmallInvolution
public import Theory.GroupTheory.NoncentralChiefRefinement.BinarySections
public import Theory.GroupTheory.NoncentralChiefRefinement.UniqueResidualLayer
public import Theory.Representation.BinaryConjugationSection.DisplacementBound

/-!
# Chief centralization from one-dimensional hexacode-cover displacement

A marked even involution costs at least two dimensions on every nontrivial
simple binary module above the hexacode group with a two-group kernel.
A literal commutator subgroup of relative order at most two therefore makes
all chief intervals of the specified normal two-group section central.
The two-residual centralizes the whole section, including its extensions.

Source: Aschbacher--Smith 12.7.16, printed p.844.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender NoncentralChiefRefinement Atlas.Codes
open scoped IsMulCommutative
namespace Representation.Hexacode
variable {H : Type*} [Group H] [Finite H]

/-- The actual residual centralizes a normal two-section when an actor
containing an even involution has at most one dimension of displacement. -/
theorem residual_commutator_le_of_displacement_index_two
    (π : H →* HexAutomorphisms) (hE : hexSign.ker≤π.range) (hp : IsPGroup 2 π.ker)
    (Q Z : Subgroup H) [Q.Normal] [Z.Normal] (hQ : IsPGroup 2 Q) (hZQ : Z≤Q)
    (A B : Subgroup H) (hAE : A.map π≤hexSign.ker)
    (t : HexEvenAutomorphisms) (ht : orderOf t=2) (htA : t.val∈A.map π)
    (hcomm : ⁅Q,A⁆≤B) (hindex : Z.relIndex B≤2) :
    ⁅Q,pResidual 2 H⁆≤Z := by
  let z : NormalNode H := ⟨Z,inferInstanceAs Z.Normal⟩
  let q : NormalNode H := ⟨Q,inferInstanceAs Q.Normal⟩
  obtain ⟨s,hsZ,hsQ⟩ := exists_chiefSeries z q hZQ
  have hall (i : Fin s.length) : IsCentral (s i.castSucc) (s i.succ) := by
    let L := s i.castSucc
    let U := s i.succ
    have hLU : L ⋖ U := (covBy_iff_isChief L U).mpr (s.isChief i)
    have hUQ : U.val≤Q := by
      have hh := CompositionSeries.le_last (s:=s) i.succ
      rw [hsQ] at hh
      exact hh
    have hZL : Z≤L.val := by
      have hh := CompositionSeries.head_le (s:=s) i.castSucc
      rw [hsZ] at hh
      exact hh
    let : IsElementaryAbelian 2 (Section L U) := chief_elementary L U hLU (hQ.to_le hUQ)
    let ρ : Representation (ZMod 2) H (Additive (Section L U)) := binarySectionRepresentation L U
    let : Representation.IsIrreducible ρ := binarySection_irreducible L U hLU
    apply (binarySection_trivial_iff L U).mp
    by_contra hn
    obtain ⟨a,ha,hat⟩ := htA
    have hcyc : (zpowers a).map π≤hexSign.ker := (map_mono (zpowers_le.mpr ha)).trans hAE
    have hta : t.val∈(zpowers a).map π := hat ▸ mem_map_of_mem π (mem_zpowers a)
    have hlower := SmallInvolution.projected_simple_fixedCodim_lower
      π hE hp ρ hn (zpowers a) hcyc t ht hta
    let d : BinaryConjugationSection (⊤ : Subgroup H) U.val L.val (ρ.comp (⊤ : Subgroup H).subtype) := {
      section_le := le_top
      kernel_le := hLU.le
      normalized := le_normalizer_of_normal
      coordinates := {
        toFun := fun u => Multiplicative.ofAdd (Additive.ofMul
          (QuotientGroup.mk' (L.val.subgroupOf U.val) u))
        map_one' := map_one (QuotientGroup.mk' (L.val.subgroupOf U.val))
        map_mul' := map_mul (QuotientGroup.mk' (L.val.subgroupOf U.val)) }
      onto := QuotientGroup.mk'_surjective _
      kernel_eq := QuotientGroup.ker_mk' _
      equivariant := fun _ _ => rfl }
    have hc : ⁅A,U.val⁆≤B := by
      rw [commutator_comm]
      exact (commutator_mono hUQ le_rfl).trans hcomm
    have hupper := d.displacement_rank_le_of_commutator_bound A B Z hZL hc 1
      (by simpa only [pow_one] using hindex) ⟨a,mem_top a⟩ ha
    change Module.finrank (ZMod 2) (LinearMap.range (ρ a-1))≤1 at hupper
    rw [fixedCodim_zpowers_eq_displacement_rank] at hlower
    change 2≤Module.finrank (ZMod 2) (LinearMap.range (ρ a-1)) at hlower
    exact (by decide : ¬ (2:ℕ)≤1) (hlower.trans hupper)
  have hpLast : IsPGroup 2 s.last.val := by rw [hsQ]; exact hQ
  have hc := s.residual_commutator_le_head_of_central_steps hpLast hall
  simpa only [hsZ,hsQ,z,q] using hc

end Representation.Hexacode
