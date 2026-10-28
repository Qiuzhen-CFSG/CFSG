module
public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceImplication.MovedSection
public import Theory.Representation.BinaryOffender.CubicIrreducibleSection

/-!
# Central cubic elements on actual moved sections

On a faithful irreducible binary section a nontrivial central cubic has
zero norm. That norm has fixed image on the original moved space, so full
commutator generation makes it zero there as well. The actual central
projection is therefore injective. Moreover an ambient vector fixed by
the cubic is fixed by the whole component: its component displacements
are cubic-fixed vectors in the moved space and hence vanish.

The source application is the original triple-six branch of B.5.1 and
15.3.21, printed pp.99–103 and1127 in the combined Aschbacher–Smith
manuscript (1 March 2004). Every representation and projection stays literal;
no complement or block structure is assumed.
-/

public section
open Subgroup Representation Representation.BinaryOffender
namespace CFSG.Quasithin.ChapterB.QuasisimpleSource
variable {D W : Type*} [Group D] [AddCommGroup W] [Module (ZMod 2) W]
variable {ρ : Representation (ZMod 2) D W} {L : Subgroup D}

private theorem binary_add_self (v : W) : v + v = 0 := by
  have h := @two_smul (ZMod 2) W _ _ _ v
  rw [show (2 : ZMod 2) = 0 by decide,zero_smul] at h
  exact h.symm

/-- The cubic norm vanishes on the actual moved space. -/
theorem MovedSection.centralCubicNorm_eq_zero
    (s : MovedSection ρ L) (hi : IsIrrPlus ρ L s.space.toSubmodule)
    (hf : Function.Injective s.action) (hir : IsIrreducible (s.action.comp L.subtype))
    (z : L) (hz : z ∈ center L) (hne : z ≠ 1) (hz3 : z^3 = 1)
    (v : W) (hv : v ∈ s.space.toSubmodule) : centralCubicNorm ρ z v = 0 := by
  have hn := centralCubicNorm_eq_zero_of_irreducible (s.action.comp L.subtype)
    hir (hf.comp L.subtype_injective) z hz hne hz3
  apply centralCubicNorm_eq_zero_on_commutator ρ L s.space.toSubmodule hi.choose_spec.1
    (z : D) (fun l hl => congrArg Subtype.val (mem_center_iff.mp hz ⟨l,hl⟩).symm) ?_ v hv
  intro w hw
  let n : s.space.toSubmodule :=
    s.space.toRepresentation z (s.space.toRepresentation z ⟨w,hw⟩) +
      s.space.toRepresentation z ⟨w,hw⟩ + ⟨w,hw⟩
  have hp : s.central.toSubmodule.mkQ n = 0 := by
    have hh := LinearMap.congr_fun hn (s.central.toSubmodule.mkQ ⟨w,hw⟩)
    exact hh
  have hc := (Submodule.Quotient.mk_eq_zero s.central.toSubmodule).mp hp
  rw [s.central_eq] at hc
  intro g
  exact congrArg Subtype.val (hc g)

/-- The actual central projection is injective in the cubic irreducible case. -/
theorem MovedSection.centralProjection_injective_of_cubic
    (s : MovedSection ρ L) (hi : IsIrrPlus ρ L s.space.toSubmodule)
    (hf : Function.Injective s.action) (hir : IsIrreducible (s.action.comp L.subtype))
    (z : L) (hz : z ∈ center L) (hne : z ≠ 1) (hz3 : z^3 = 1) :
    Function.Injective s.central.toSubmodule.mkQ := by
  apply (injective_iff_map_eq_zero _).mpr
  intro v hv
  have hc := (Submodule.Quotient.mk_eq_zero s.central.toSubmodule).mp hv
  rw [s.central_eq] at hc
  have hzv : ρ z v = (v : W) := congrArg Subtype.val (hc z)
  have hn := s.centralCubicNorm_eq_zero hi hf hir z hz hne hz3 v v.property
  rw [centralCubicNorm_apply,hzv,hzv,binary_add_self,zero_add] at hn
  exact Subtype.ext hn

/-- Fixing the central cubic already means fixing the component on the ambient module. -/
theorem MovedSection.fixed_of_central_cubic
    (s : MovedSection ρ L) (hi : IsIrrPlus ρ L s.space.toSubmodule)
    (hf : Function.Injective s.action) (hir : IsIrreducible (s.action.comp L.subtype))
    (z : L) (hz : z ∈ center L) (hne : z ≠ 1) (hz3 : z^3 = 1)
    (v : W) (hv : ρ z v = v) : v ∈ fixedSpace ρ L := by
  intro g
  have hw : ρ g v - v ∈ s.space.toSubmodule := by
    rw [s.space_eq]
    exact Submodule.subset_span ⟨g,g.property,v,Submodule.mem_top,rfl⟩
  have hzw : ρ z (ρ g v - v) = ρ g v - v := by
    rw [map_sub,hv]
    have hc : ρ z (ρ g v) = ρ g (ρ z v) := by
      change (ρ z * ρ g) v = (ρ g * ρ z) v
      rw [←map_mul,←map_mul]
      exact congrArg (fun x : L => ρ (x : D) v) (mem_center_iff.mp hz g).symm
    rw [hc,hv]
  have hn := s.centralCubicNorm_eq_zero hi hf hir z hz hne hz3 _ hw
  rw [centralCubicNorm_apply,hzw,hzw,binary_add_self,zero_add] at hn
  exact sub_eq_zero.mp hn

end CFSG.Quasithin.ChapterB.QuasisimpleSource
