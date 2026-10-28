module
public import Theory.SpecificGroups.BinaryLinear.ThreePointQuotient
public import Theory.GroupTheory.PCoreFrattiniTransport
public import Theory.GroupTheory.SymmetricThreeTwoCore

/-!
# Lifting the binary three-space point stabilizer quotient

A homomorphism whose full image is the stabilizer of a nonzero vector
and whose kernel is a two-group induces the literal S3 two-core quotient.
The point and the image equality are retained explicitly.

Source application: Aschbacher--Smith, final 14.6 endgame, printed p.1042.
-/

public section
open Subgroup
namespace BinaryLinear.PointStabilizerRank
variable {G : Type*} [Group G] [Finite G]

theorem three_point_quotient_of_action
    (f : G →* BinaryLinear.GL (Fin 3 → ZMod 2))
    (v : Fin 3 → ZMod 2) (hv : v ≠ 0)
    (hr : f.range = MulAction.stabilizer (BinaryLinear.GL (Fin 3 → ZMod 2)) v)
    (hk : IsPGroup 2 f.ker) :
    Nonempty ((G ⧸ pCore 2 G) ≃* Equiv.Perm (Fin 3)) := by
  let : Finite (BinaryLinear.GL (Fin 3 → ZMod 2)) :=
    Finite.of_injective (fun g : BinaryLinear.GL (Fin 3 → ZMod 2) =>
      (g : (Fin 3 → ZMod 2) → (Fin 3 → ZMod 2))) DFunLike.coe_injective
  let e := MulEquiv.subgroupCongr hr
  let g := e.toMonoidHom.comp f.rangeRestrict
  have hg : Function.Surjective g := e.surjective.comp f.rangeRestrict_surjective
  have hgker : g.ker = f.ker := by
    ext x
    change e (f.rangeRestrict x) = 1 ↔ f x = 1
    rw [map_eq_one_iff e e.injective]
    exact Subtype.ext_iff
  obtain ⟨ep⟩ := three_point_quotient (by simp) v hv
  exact ⟨(g.pCoreQuotientEquiv hg (hgker ▸ hk)).trans ep⟩

/-- The companion rank-two action used in the solvable source branch.
Here the full binary plane action already has image GL2(2) = S3. -/
theorem binary_plane_quotient_of_action
    (f : G →* BinaryLinear.GL (Fin 2 → ZMod 2))
    (hf : Function.Surjective f) (hk : IsPGroup 2 f.ker) :
    Nonempty ((G ⧸ pCore 2 G) ≃* Equiv.Perm (Fin 3)) := by
  let e := BinaryLinear.SmallParabolicLevi.linearTwoEquivSymmetricThree
  let g := e.toMonoidHom.comp f
  have hg : Function.Surjective g := e.surjective.comp hf
  have hgker : g.ker = f.ker := MonoidHom.ker_comp_of_injective f e.toMonoidHom e.injective
  have he := ker_eq_twoCore_of_surjective_perm_three g hg (hgker ▸ hk)
  exact ⟨(QuotientGroup.quotientMulEquivOfEq he.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective g hg)⟩

end BinaryLinear.PointStabilizerRank
