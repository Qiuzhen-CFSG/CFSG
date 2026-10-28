module
public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceImplication.FullMovedProjection

/-!
# Coordinates for a fully moved module with trivial fixed space

The canonical projection to the source central quotient is surjective. Its
kernel is the component-fixed space, so a zero fixed space makes it an
actual linear equivalence. The whole actor and its component retain their
literal action under this equivalence. This supplies original-module
coordinates after the A7 cohomology splitting in source 10.2.9.
-/

@[expose] public noncomputable section
open Subgroup Representation Representation.BinaryOffender
namespace CFSG.Quasithin.ChapterB.QuasisimpleSource
variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  {ρ : Representation (ZMod 2) G V} {K : Subgroup G}

theorem MovedSection.fullProjection_surjective (s : MovedSection ρ K)
    (hm : moved ρ K = ⊤) : Function.Surjective (s.fullProjection hm) := by
  intro q
  obtain ⟨v, hv⟩ := s.central.toSubmodule.mkQ_surjective q
  refine ⟨v, ?_⟩
  exact hv

theorem MovedSection.fullProjection_injective (s : MovedSection ρ K)
    (hm : moved ρ K = ⊤) (hc : fixedSpace ρ K = ⊥) :
    Function.Injective (s.fullProjection hm) := by
  intro x y hxy
  apply sub_eq_zero.mp
  have hz : s.fullProjection hm (x - y) = 0 := by rw [map_sub, hxy, sub_self]
  have hz' := (s.fullProjection_eq_zero_iff hm (x-y)).mp hz
  rwa [hc, Submodule.mem_bot] at hz'

def MovedSection.fullProjectionEquiv (s : MovedSection ρ K)
    (hm : moved ρ K = ⊤) (hc : fixedSpace ρ K = ⊥) :
    V ≃ₗ[ZMod 2] (s.space.toSubmodule ⧸ s.central.toSubmodule) :=
  LinearEquiv.ofBijective (s.fullProjection hm)
    ⟨s.fullProjection_injective hm hc, s.fullProjection_surjective hm⟩

def MovedSection.fullActionEquiv (s : MovedSection ρ K)
    (hm : moved ρ K = ⊤) (hc : fixedSpace ρ K = ⊥) :
    ActionEquiv ρ s.central.quotientRepresentation where
  groupEquiv := MulEquiv.refl G
  linearEquiv := s.fullProjectionEquiv hm hc
  intertwines g v := s.fullProjection_intertwines hm g v

def MovedSection.fullComponentActionEquiv (s : MovedSection ρ K)
    (hm : moved ρ K = ⊤) (hc : fixedSpace ρ K = ⊥) :
    ActionEquiv (ρ.comp K.subtype) (s.central.quotientRepresentation.comp K.subtype) where
  groupEquiv := MulEquiv.refl K
  linearEquiv := s.fullProjectionEquiv hm hc
  intertwines k v := s.fullProjection_intertwines hm k v

end CFSG.Quasithin.ChapterB.QuasisimpleSource
