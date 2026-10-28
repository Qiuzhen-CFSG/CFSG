module
public import Theory.Representation.CubicFixedSpace
public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceImplication.Geometry

/-!
# Cubic fixed-space witnesses on actual moved sections

An actual moved section provides both central-extension maps required by the
cubic lifting argument: its denominator is fixed by the marked component,
and the quotient above its moved space is trivial. An equivariant model
marking therefore transports a cubic witness to every ambient Sylow subgroup.
The companion theorem works directly on the moved space, with zero kernel.
Source application: Aschbacher–Smith B.5.1 and15.4.20.
-/

public section
open Subgroup Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterB.QuasisimpleSource
variable {Q V M W : Type*} [Group Q] [Finite Q] [Group M]
    [AddCommGroup V] [Module (ZMod 2) V] [AddCommGroup W] [Module (ZMod 2) W]

theorem MovedSection.cubic_enlargement
    (ρ : Representation (ZMod 2) Q V) (J C : Subgroup Q)
    (s : MovedSection (ρ.comp J.subtype) (C.subgroupOf J))
    (σ : Representation (ZMod 2) M W)
    (e : ActionEquiv (s.action.comp (C.subgroupOf J).subtype) σ)
    (A : Subgroup M) (hA : IsPGroup 2 A) (a : M)
    (ha : a ^ 3 = 1) (hne : a ≠ 1) (hn : a ∈ normalizer (A : Set M))
    (hfix : ∀ w ∈ fixedSpace σ A, σ a w = w)
    (S : Sylow 2 Q) :
    ∃ c : Q, c ∉ S ∧ c ^ 3 = 1 ∧ ∀ v ∈ fixedSpace ρ (S : Subgroup Q), ρ c v = v := by
  let fJ : M →* J :=
    (C.subgroupOf J).subtype.comp e.groupEquiv.symm.toMonoidHom
  let f : M →* Q := J.subtype.comp fJ
  have hf : Function.Injective f :=
    J.subtype_injective.comp ((C.subgroupOf J).subtype_injective.comp e.groupEquiv.symm.injective)
  let U : Subrepresentation (ρ.comp f) :=
    ⟨s.space.toSubmodule,fun g v hv => s.space.apply_mem_toSubmodule (fJ g) hv⟩
  let b : U.toSubmodule →ₗ[ZMod 2] s.space.toSubmodule := LinearMap.id
  let π : U.toSubmodule →ₗ[ZMod 2] W :=
    e.linearEquiv.toLinearMap.comp (s.central.toSubmodule.mkQ.comp b)
  have hact (g : M) (w : U.toSubmodule) :
      b (U.toRepresentation g w) = s.space.toRepresentation (fJ g) (b w) := by
    apply Subtype.ext
    rfl
  have hequiv : ∀ g w, π (U.toRepresentation g w) =
      σ g (π w) := by
    intro g w
    change e.linearEquiv (s.central.toSubmodule.mkQ (b (U.toRepresentation g w))) = _
    rw [hact]
    have hh := e.intertwines (e.groupEquiv.symm g) (s.central.toSubmodule.mkQ (b w))
    simpa only [π, MovedSection.action, fJ,
      MonoidHom.comp_apply, LinearMap.comp_apply, LinearEquiv.coe_coe,
      Subrepresentation.quotientRepresentation_mk, Subgroup.subtype_apply, MulEquiv.coe_toMonoidHom, MulEquiv.apply_symm_apply] using hh
  have hcentral : ∀ g w, π w = 0 → U.toRepresentation g w = w := by
    intro g w hw
    have hz : s.central.toSubmodule.mkQ (b w) = 0 :=
      e.linearEquiv.injective (by simpa only [π, LinearMap.comp_apply, LinearEquiv.coe_coe, map_zero] using hw)
    have hm : b w ∈ s.central.toSubmodule := (Submodule.Quotient.mk_eq_zero _).mp hz
    rw [s.central_eq] at hm
    exact hm (e.groupEquiv.symm g)
  have hquot : ∀ g v, ρ (f g) v - v ∈ U := by
    intro g v
    change ρ (f g) v - v ∈ s.space.toSubmodule
    rw [s.space_eq]
    exact Submodule.subset_span ⟨fJ g,(e.groupEquiv.symm g).property,v,Submodule.mem_top,rfl⟩
  apply sylow_fixedSpace_enlargement_of_embedded_cubic ρ f hf A hA a ha hne _ S
  exact cubic_fixedSpace_of_central_section (ρ.comp f) σ A a ha hn U π
    hequiv hcentral hquot hfix

theorem MovedSection.space_cubic_enlargement
    (ρ : Representation (ZMod 2) Q V) (J C : Subgroup Q)
    (s : MovedSection (ρ.comp J.subtype) (C.subgroupOf J))
    (σ : Representation (ZMod 2) M W)
    (e : ActionEquiv (s.space.toRepresentation.comp (C.subgroupOf J).subtype) σ)
    (A : Subgroup M) (hA : IsPGroup 2 A) (a : M)
    (ha : a ^ 3 = 1) (hne : a ≠ 1) (hn : a ∈ normalizer (A : Set M))
    (hfix : ∀ w ∈ fixedSpace σ A, σ a w = w)
    (S : Sylow 2 Q) :
    ∃ c : Q, c ∉ S ∧ c ^ 3 = 1 ∧ ∀ v ∈ fixedSpace ρ (S : Subgroup Q), ρ c v = v := by
  let fJ : M →* J :=
    (C.subgroupOf J).subtype.comp e.groupEquiv.symm.toMonoidHom
  let f : M →* Q := J.subtype.comp fJ
  have hf : Function.Injective f :=
    J.subtype_injective.comp ((C.subgroupOf J).subtype_injective.comp e.groupEquiv.symm.injective)
  let U : Subrepresentation (ρ.comp f) :=
    ⟨s.space.toSubmodule,fun g v hv => s.space.apply_mem_toSubmodule (fJ g) hv⟩
  let b : U.toSubmodule →ₗ[ZMod 2] s.space.toSubmodule := LinearMap.id
  let π : U.toSubmodule →ₗ[ZMod 2] W :=
    e.linearEquiv.toLinearMap.comp b
  have hact (g : M) (w : U.toSubmodule) :
      b (U.toRepresentation g w) = s.space.toRepresentation (fJ g) (b w) := by
    apply Subtype.ext
    rfl
  have hequiv : ∀ g w, π (U.toRepresentation g w) = σ g (π w) := by
    intro g w
    change e.linearEquiv (b (U.toRepresentation g w)) = _
    rw [hact]
    have hh := e.intertwines (e.groupEquiv.symm g) (b w)
    simpa only [π, fJ, MonoidHom.comp_apply, LinearMap.comp_apply, LinearEquiv.coe_coe,
      Subgroup.subtype_apply, MulEquiv.coe_toMonoidHom, MulEquiv.apply_symm_apply] using hh
  have hcentral : ∀ g w, π w = 0 → U.toRepresentation g w = w := by
    intro g w hw
    have hw0 : b w = 0 := e.linearEquiv.injective (by
      simpa only [π, LinearMap.comp_apply, LinearEquiv.coe_coe, map_zero] using hw)
    have hw' : w = 0 := hw0
    rw [hw',map_zero]
  have hquot : ∀ g v, ρ (f g) v - v ∈ U := by
    intro g v
    change ρ (f g) v - v ∈ s.space.toSubmodule
    rw [s.space_eq]
    exact Submodule.subset_span ⟨fJ g,(e.groupEquiv.symm g).property,v,Submodule.mem_top,rfl⟩
  apply sylow_fixedSpace_enlargement_of_embedded_cubic ρ f hf A hA a ha hne _ S
  exact cubic_fixedSpace_of_central_section (ρ.comp f) σ A a ha hn U π
    hequiv hcentral hquot hfix

end CFSG.Quasithin.ChapterB.QuasisimpleSource
