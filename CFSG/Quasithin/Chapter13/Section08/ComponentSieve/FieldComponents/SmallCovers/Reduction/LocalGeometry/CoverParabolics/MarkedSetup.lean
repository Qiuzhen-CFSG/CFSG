module

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.SmallCovers.Reduction.LocalGeometry
public import Theory.GroupTheory.Covering

/-!
# Inputs for the marked proper-residual branch

The source setup retains H = KT, the relatively normal C-component K,
the genuine Sylow arrangement, the solvable theta seed L₁, the cubic
quasisimple two-core quotient, and Y < L₁ for the literal cover residual.
The universal solvable-overgroup conclusion is precisely the earlier
13.8.13 input. Model equivalences and any trivial-diagram condition are
supplied separately when applying the two cover geometries.

The theta identity gives relative normality and survives restriction to
an overgroup of L₁. The actual component star equivalence is constructed
from C-component calculus. No K₁ containment, maximality, parabolic
identification or marked-image equality is a field of this setup.

Source: Aschbacher–Smith 13.8.21(2), printed p.956 (PDF p.973), after
Y = L₁ has been excluded. The marked geometric conclusions remain to
be proved from this boundary.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.SmallCovers.Reduction.LocalGeometry.CoverParabolics
variable {G : Type*} [Group G]

/-- The source inputs for the proper-residual branch, before constructing or identifying any parabolic. -/
structure MarkedSetup (H K L₁ T G₁ M : Subgroup G) where
  mem_Hz : H ∈ Source.Hz L₁ T G₁ M
  component_le : K ≤ H
  component : (K.subgroupOf H).IsCComponent
  component_normal : (K.subgroupOf H).Normal
  sylow : Chapter1.IsSylowIn 2 T H
  sylow_le_M : T ≤ M
  generated : H = K ⊔ T
  seed_le_component : L₁ ≤ K
  seed_solvable : Group.IsSolvable L₁
  theta : L₁ = closure {x : G | x ∈ H ⊓ M ∧ orderOf x = 3}
  proper_residual : coverResidualIn K < L₁
  quasisimple : IsQuasisimple (K ⧸ pCore 2 K)
  center_card : Nat.card (center (K ⧸ pCore 2 K)) = 3
  solvable_overgroups : ∀ X : Subgroup G, L₁ ⊔ T ≤ X → X ≤ G₁ →
    Group.IsSolvable X → X ≤ M

variable {H K L₁ T G₁ M : Subgroup G} (s : MarkedSetup H K L₁ T G₁ M)
include s

theorem MarkedSetup.seed_le_overlap : L₁ ≤ H ⊓ M := by
  rw [s.theta]
  exact (closure_le _).mpr fun _ hx => hx.1

theorem MarkedSetup.seed_normal : (L₁.subgroupOf (H ⊓ M)).Normal := by
  apply normal_subgroupOf_of_le_normalizer
  rw [s.theta]
  apply le_normalizer_closure_iff.mpr
  intro g hg x hx
  exact subset_closure ⟨(H ⊓ M).mul_mem ((H ⊓ M).mul_mem hg hx.1)
    ((H ⊓ M).inv_mem hg), (MulAut.conj g).orderOf_eq x |>.trans hx.2⟩

theorem MarkedSetup.overlap_proper : H ⊓ M < H :=
  lt_of_le_of_ne inf_le_left (fun he => s.mem_Hz.2.2 (he.ge.trans inf_le_right))

/-- The theta identity persists in every replacement containing its marked seed. -/
theorem MarkedSetup.theta_restrict (H' : Subgroup G) (hL : L₁ ≤ H') (hH' : H' ≤ H) :
    L₁ = closure {x : G | x ∈ H' ⊓ M ∧ orderOf x = 3} := by
  apply le_antisymm
  · conv_lhs => rw [s.theta]
    apply (closure_le _).mpr
    intro x hx
    have hxL : x ∈ L₁ := s.theta.symm ▸ subset_closure hx
    exact subset_closure ⟨⟨hL hxL, hx.1.2⟩, hx.2⟩
  · rw [s.theta]
    exact closure_mono fun x hx => ⟨⟨hH' hx.1.1, hx.1.2⟩, hx.2⟩

variable [Finite G]

/-- The component quotient is identified with its actual source star image. -/
noncomputable def MarkedSetup.componentStarEquiv :
    (K ⧸ pCore 2 K) ≃* Source.starImage H K :=
  Components.componentStarEquiv H K s.component_le s.component

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.SmallCovers.Reduction.LocalGeometry.CoverParabolics
