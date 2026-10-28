module
public import Theory.Representation.Mathieu.M22James.MovedStabilizer
public import Theory.Representation.Mathieu.M22James.NoFF.AmbientInvolutions
/-!
# The nonsolvable moved-point stabilizer in an ambient Mathieu action

A marked Mathieu component gives the actual ambient matrix action on its
invariant subspace. An involution of displacement four is inner: the checked
outer action has displacement six. The component's displacement has the same
dimension as the whole ambient displacement, hence their literal images
coincide. This transports the original vector to a moved model vector, and
then transports its nonsolvable stabilizer back through the group marking.
Ambient fixed layers and nonsplit extensions are retained throughout.

Source: Aschbacher–Smith, proof of 12.6.26, printed p.832, using H.12.1.
-/
public section
set_option backward.isDefEq.respectTransparency false

namespace Sporadic.Mathieu.M22TripleCover.MovedStabilizer
open Representation Representation.BinaryOffender Subgroup
open BinaryNaturalDual.VectorStabilizers
open Janko4.InvolutionCentralizers.First.QuotientExtension
variable {G W : Type*} [Group G] [AddCommGroup W] [Module (ZMod 2) W]
  [FiniteDimensional (ZMod 2) W]

/-- A point in a rank-four ambient displacement remains a moved point in the
marked Mathieu component, without discarding ambient fixed layers. -/
theorem marked_moved_stabilizer_not_solvable
    (ρ : Representation (ZMod 2) G W) (B : Subgroup G) [B.Normal]
    (C : Subrepresentation ρ) (ec : B ≃* M22TripleCover)
    (em : Representation.Equiv (C.toRepresentation.comp B.subtype) (representationOfEquiv ec))
    (t : G) (ht : t ^ 2 = 1)
    (hd : fixedCodim C.toRepresentation (zpowers t) = 4)
    (hfull : Module.finrank (ZMod 2) (ρ t - LinearMap.id).range ≤ 4)
    (u : C.toSubmodule) (hu : u.val ∈ (ρ t - LinearMap.id).range) (hne : em u ≠ 0) :
    ¬ Group.IsSolvable (representationStabilizer binaryRepresentation (em u)) := by
  classical
  let α := Ambient.markedTripleAmbientHom C.toRepresentation B ec em
  have ha (g : G) (v : C.toSubmodule) :
      em (C.toRepresentation g v) = Ambient.binaryAction (α g) (em v) :=
    Ambient.markedTripleAmbientHom_intertwining C.toRepresentation B ec em g v
  have hc : fixedCodim Ambient.binaryAction (zpowers (α t)) = 4 := by
    have he := fixedCodim_map_equivariant C.toRepresentation Ambient.binaryAction
      α em.toLinearEquiv ha (zpowers t)
    rw [MonoidHom.map_zpowers] at he
    exact he.symm.trans hd
  have htα : α t ^ 2 = 1 := by rw [←map_pow,ht,map_one]
  have hnα : α t ≠ 1 := by
    intro he
    rw [fixedCodim_zpowers_eq_displacement_rank,he,map_one,Module.End.one_eq_id,
      sub_self,LinearMap.range_zero,finrank_bot] at hc
    contradiction
  have hoα : orderOf (α t) = 2 := orderOf_eq_prime htα hnα
  have hin : α t ∈ coverSubgroup := by
    by_contra ho
    have hh := NoFF.outer_binaryCodim (α t) hoα ho
    omega
  rw [←coverInclusion_range] at hin
  obtain ⟨b,hb⟩ := hin
  have hi : Function.Injective coverInclusion := inclusion_injective _
  have hb2 : b ^ 2 = 1 := hi (by rw [map_pow,hb,htα,map_one])
  have hb1 : b ≠ 1 := by intro he; apply hnα; rw [←hb,he,map_one]
  have hop (v : C.toSubmodule) :
      em (C.toRepresentation t v) = binaryRepresentation b (em v) := by
    rw [ha,←hb]
    rfl
  let R := (C.toRepresentation t - LinearMap.id).range
  have hr : R.map C.toSubmodule.subtype ≤ (ρ t - LinearMap.id).range := by
    rintro _ ⟨v,⟨x,hx⟩,rfl⟩
    exact ⟨x.val,congrArg Subtype.val hx⟩
  have hdim : Module.finrank (ZMod 2) (R.map C.toSubmodule.subtype) = 4 := by
    rw [Submodule.finrank_map_subtype_eq]
    rw [fixedCodim_zpowers_eq_displacement_rank] at hd
    exact hd
  have heq : R.map C.toSubmodule.subtype = (ρ t - LinearMap.id).range :=
    Submodule.eq_of_le_of_finrank_le hr (by rw [hdim]; exact hfull)
  have huR : u ∈ R := by
    have hh : u.val ∈ R.map C.toSubmodule.subtype := heq.symm ▸ hu
    obtain ⟨v,hv,he⟩ := hh
    exact (Subtype.ext he : v = u) ▸ hv
  obtain ⟨x,hx⟩ := huR
  have hm : em u ∈ (binaryRepresentation b - LinearMap.id).range := by
    refine ⟨em x,?_⟩
    have he := congrArg em hx
    change em (C.toRepresentation t x - x) = em u at he
    rw [map_sub,hop] at he
    exact he
  exact moved_stabilizer_not_solvable b (orderOf_eq_prime hb2 hb1) (em u) hne hm
end Sporadic.Mathieu.M22TripleCover.MovedStabilizer

namespace Sporadic.Mathieu.M22TripleCover.MovedStabilizer
open Representation Representation.BinaryOffender Subgroup
open BinaryNaturalDual.VectorStabilizers
variable {G W : Type*} [Group G] [AddCommGroup W] [Module (ZMod 2) W]
  [FiniteDimensional (ZMod 2) W]
/-- The stabilizer in the original component is nonsolvable as well. -/
theorem original_moved_stabilizer_not_solvable
    (ρ : Representation (ZMod 2) G W) (B : Subgroup G) [B.Normal]
    (C : Subrepresentation ρ) (ec : B ≃* M22TripleCover)
    (em : Representation.Equiv (C.toRepresentation.comp B.subtype) (representationOfEquiv ec))
    (t : G) (ht : t ^ 2 = 1)
    (hd : fixedCodim C.toRepresentation (zpowers t) = 4)
    (hfull : Module.finrank (ZMod 2) (ρ t - LinearMap.id).range ≤ 4)
    (u : C.toSubmodule) (hu : u.val ∈ (ρ t - LinearMap.id).range) (hne : u.val ≠ 0) :
    ¬ Group.IsSolvable (representationStabilizer (ρ.comp B.subtype) u.val) := by
  have hmodel : em u ≠ 0 := by
    intro he
    exact hne (congrArg Subtype.val (em.toLinearEquiv.map_eq_zero_iff.mp he))
  intro hs
  let := hs
  let P := representationStabilizer (ρ.comp B.subtype) u.val
  let Q := representationStabilizer binaryRepresentation (em u)
  let f : Q →* P := {
    toFun g := ⟨ec.symm g.val,by
      have he := LinearMap.congr_fun (em.isIntertwining' (ec.symm g.val)) u
      change em ((C.toRepresentation.comp B.subtype) (ec.symm g.val) u) =
        binaryRepresentation (ec (ec.symm g.val)) (em u) at he
      rw [ec.apply_symm_apply] at he
      have hh : (C.toRepresentation.comp B.subtype) (ec.symm g.val) u = u :=
        em.toLinearEquiv.injective (he.trans g.property)
      exact congrArg Subtype.val hh⟩
    map_one' := Subtype.ext (map_one ec.symm)
    map_mul' _ _ := Subtype.ext (map_mul ec.symm _ _) }
  have hf : Function.Injective f := by
    intro g k he
    apply Subtype.ext
    apply ec.symm.injective
    exact congrArg (fun x : P => x.val) he
  exact marked_moved_stabilizer_not_solvable ρ B C ec em t ht hd hfull u hu hmodel
    (Group.isSolvable_of_isSolvable_injective hf)
end Sporadic.Mathieu.M22TripleCover.MovedStabilizer
