module

public import Theory.Representation.G2Natural
public import Theory.Representation.FirstCohomologyLinearTransport
public import Theory.Representation.BinaryOffender.EquivariantOffender
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2

/-!
# Marked J₂ restrictions of the natural G₂(4) module

The marking retains the actual degree-100 J₂ carrier, its embedding in the
split-octonion G₂ group, and an equivariant identification with the natural
trace-zero quotient. The permitted ambient group embeds in Aut(J₂), with
its inner action identified on the marked J₂ subgroup. Outer involutions
act semilinearly by the nonidentity field automorphism.

This is an input to the independent K.4.5 calculation, not a recognition
result. The source recognition is owned by the sporadic catalogue. No rank,
fixed-space, offender, or ratio conclusion is included in the marking.
Source: Aschbacher–Smith, K.4.5, printed p.460.
-/

@[expose] public section
namespace CFSG.Quasithin.ChapterK.JankoTwo
open Representation

variable {K G V : Type*} [Field K] [CharP K 2] [Algebra (ZMod 2) K]
  [FiniteDimensional (ZMod 2) K] [Group G] [AddCommGroup V] [Module (ZMod 2) V]

/-- The binary restriction of the actual natural octonion-quotient action. -/
abbrev naturalAction (K : Type*) [Field K] [CharP K 2] [Algebra (ZMod 2) K] :=
  Representation.restrictScalars (k := ZMod 2) (Atlas.G2.Natural.action K)

/-- Source module data, with a genuine embedding and compatible outer action. -/
structure MarkedModule (ρ : Representation (ZMod 2) G V) where
  fieldDegree : Module.finrank (ZMod 2) K = 2
  fieldGenerator : K
  generator_relation : fieldGenerator ^ 2 - fieldGenerator = 1
  inner : Subgroup G
  normal : inner.Normal
  carrierEquiv : inner ≃* Sporadic.LeechRelated.J2.Carrier
  ambientEmbedding : G →* MulAut Sporadic.LeechRelated.J2.Carrier
  ambient_injective : Function.Injective ambientEmbedding
  ambient_inner : ∀ l : inner, ambientEmbedding l = MulAut.conj (carrierEquiv l)
  embedding : inner →* Atlas.G2.Model K
  embedding_injective : Function.Injective embedding
  action : Representation (ZMod 2) G (Atlas.G2.Natural.Space K)
  equiv : ρ.Equiv action
  inner_action : ∀ (l : inner) v, action l v = naturalAction K (embedding l) v
  outer_semilinear : ∀ i : G, i ∉ inner → orderOf i = 2 →
    ∀ (c : K) (v : Atlas.G2.Natural.Space K), action i (c • v) = c ^ 2 • action i v

namespace MarkedModule
variable {ρ : Representation (ZMod 2) G V} (D : MarkedModule (K := K) ρ)
include D

/-- The dimension twelve follows from the marked scalar field and natural quotient. -/
theorem finrank_space : Module.finrank (ZMod 2) (Atlas.G2.Natural.Space K) = 12 := by
  rw [← Module.finrank_mul_finrank (ZMod 2) K (Atlas.G2.Natural.Space K),
    D.fieldDegree, Atlas.G2.Natural.finrank_space]

/-- The source module has dimension twelve by the actual equivariant equivalence. -/
theorem finrank : Module.finrank (ZMod 2) V = 12 :=
  D.equiv.toLinearEquiv.finrank_eq.trans D.finrank_space

end MarkedModule
end CFSG.Quasithin.ChapterK.JankoTwo
