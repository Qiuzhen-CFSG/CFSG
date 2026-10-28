module

public import Theory.AtlasPort.OtherSporadic.Codes.HexacodeAutomorphismPackage
public import Theory.GroupTheory.Commutator.PerfectQuotient
public import Theory.GroupTheory.Covering
public import Mathlib.GroupTheory.SpecificGroups.Alternating.Centralizer

/-!
# The quasisimple triple cover in the hexacode action

The commutator of two explicit lifts of disjoint three-cycles generates
the order-three coordinate kernel. Since the alternating quotient is
perfect, the even hexacode group is perfect as well. Its center is exactly
that kernel, and quotienting by the center gives the actual alternating
group on six letters. Thus this concrete carrier satisfies the convention
for `Â₆` in Aschbacher–Smith, *The Classification of Quasithin Groups*,
A.3.5, printed p.43 (combined manuscript, 1 March 2004).

The explicit lifts, their commutator, and coordinate map are from the
licensed ATLAS port `Theory.AtlasPort.OtherSporadic.Codes.HexacodeNonsplit`
and `HexacodeAutomorphismPackage`. The four-element field realization of
K.1.3 is a further action-identification problem.
-/

@[expose] public section

open Atlas.Codes Subgroup
open scoped commutatorElement

namespace Representation.Hexacode

theorem even_kernel_le_commutator :
    hexEvenCoordinate.ker ≤ commutator HexEvenAutomorphisms := by
  rw [hexEvenCoordinate_kernel]
  apply Subgroup.zpowers_le.mpr
  let x : HexEvenAutomorphisms := ⟨hexX, hexX_even⟩
  let y : HexEvenAutomorphisms := ⟨hexY, hexY_even⟩
  have hc : ⁅x, y⁆ = hexEvenZ ^ 2 := Subtype.ext hexXY_commutator
  have h2 : hexEvenZ ^ 2 ∈ commutator HexEvenAutomorphisms := by
    rw [← hc]
    exact Subgroup.commutator_mem_commutator (mem_top x) (mem_top y)
  have h4 := (commutator HexEvenAutomorphisms).pow_mem h2 2
  have h3 : hexEvenZ ^ 3 = 1 := by
    rw [← hexEvenZ_order]
    exact pow_orderOf_eq_one _
  have hpow : (hexEvenZ ^ 2) ^ 2 = hexEvenZ := by
    rw [← pow_mul]
    change hexEvenZ ^ (3 + 1) = hexEvenZ
    rw [pow_succ, h3, one_mul]
  rwa [hpow] at h4

theorem even_isPerfect : Group.IsPerfect HexEvenAutomorphisms := by
  let : Group.IsPerfect (alternatingGroup (Fin 6)) :=
    ⟨commutator_alternatingGroup_eq_top (by simp)⟩
  have h := CentralExtension.ker_sup_commutator_eq_top_of_surjective
    hexEvenCoordinate hexEvenCoordinate_surjective
  rw [sup_eq_right.mpr even_kernel_le_commutator] at h
  exact ⟨h⟩

theorem even_kernel_eq_center :
    hexEvenCoordinate.ker = center HexEvenAutomorphisms := by
  apply le_antisymm
  · intro x hx
    have hx' : hexCoordinateSixHom x.val = 1 := congrArg Subtype.val hx
    rw [mem_center_iff]
    intro y
    apply Subtype.ext
    exact (hex_even_kernel_central y ⟨x.val, hx'⟩).eq
  · intro x hx
    have hc : hexEvenCoordinate x ∈ center (alternatingGroup (Fin 6)) := by
      rw [mem_center_iff]
      intro y
      obtain ⟨z, rfl⟩ := hexEvenCoordinate_surjective y
      simpa only [map_mul] using congrArg hexEvenCoordinate (mem_center_iff.mp hx z)
    rwa [alternatingGroup.center_eq_bot (by simp), mem_bot] at hc

noncomputable def even_quotient_center_equiv :
    HexEvenAutomorphisms ⧸ center HexEvenAutomorphisms ≃* alternatingGroup (Fin 6) :=
  (QuotientGroup.quotientMulEquivOfEq even_kernel_eq_center.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective hexEvenCoordinate hexEvenCoordinate_surjective)

theorem even_center_card : Nat.card (center HexEvenAutomorphisms) = 3 := by
  rw [← even_kernel_eq_center]
  exact hexEven_kernel_card

theorem even_isQuasisimple : Theory.GroupTheory.IsQuasisimple HexEvenAutomorphisms where
  toIsPerfect := even_isPerfect
  simple := by
    let : IsSimpleGroup (alternatingGroup (Fin 6)) := alternatingGroup.isSimpleGroup (by simp)
    exact even_quotient_center_equiv.isSimpleGroup

end Representation.Hexacode
