module
public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceImplication.Geometry

/-!
# The central quotient of a fully moved source module

When the source moved space is the whole module, its central quotient has a
canonical equivariant projection from the original module. Its kernel is
exactly the component-fixed space. This retains nonzero fixed seeds when
applying the B.5.1 natural-action models in source 10.2.9.
-/

@[expose] public noncomputable section
open Subgroup Representation Representation.BinaryOffender
namespace CFSG.Quasithin.ChapterB.QuasisimpleSource
variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  {ρ : Representation (ZMod 2) G V} {K : Subgroup G}

/-- Projection from the full moved module to its literal central quotient. -/
def MovedSection.fullProjection (s : MovedSection ρ K) (hm : moved ρ K = ⊤) :
    V →ₗ[ZMod 2] (s.space.toSubmodule ⧸ s.central.toSubmodule) :=
  s.central.toSubmodule.mkQ.comp ((LinearMap.id : V →ₗ[ZMod 2] V).codRestrict
    s.space.toSubmodule (fun _ => by rw [s.space_eq,hm]; trivial))

theorem MovedSection.fullProjection_intertwines (s : MovedSection ρ K)
    (hm : moved ρ K = ⊤) (g : G) (v : V) :
    s.fullProjection hm (ρ g v) = s.central.quotientRepresentation g (s.fullProjection hm v) := rfl

theorem MovedSection.fullProjection_eq_zero_iff (s : MovedSection ρ K)
    (hm : moved ρ K = ⊤) (v : V) :
    s.fullProjection hm v = 0 ↔ v ∈ fixedSpace ρ K := by
  change s.central.toSubmodule.mkQ _ = 0 ↔ _
  rw [Submodule.mkQ_apply,Submodule.Quotient.mk_eq_zero,s.central_eq]
  change (∀ k : K, s.space.toRepresentation k ⟨v,_⟩ = ⟨v,_⟩) ↔ ∀ k : K, ρ k v = v
  constructor
  · intro h k
    exact congrArg Subtype.val (h k)
  · intro h k
    exact Subtype.ext (h k)

end CFSG.Quasithin.ChapterB.QuasisimpleSource
