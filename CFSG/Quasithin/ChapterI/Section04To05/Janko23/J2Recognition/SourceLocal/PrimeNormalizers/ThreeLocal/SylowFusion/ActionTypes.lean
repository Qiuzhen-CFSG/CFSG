module

public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.J2Recognition.SourceLocal.PrimeNormalizers.ThreeLocal.FusionTypes

/-!
# The remaining marked Sylow action

The projective quotient calculation must construct this internal complement
in the literal Sylow normalizer. Its action is the published conjugation
action on the intrinsic Frattini quotient. The source fusion and weak-closure
deductions are separate from this construction.

Source: Aschbacher, *Sporadic Groups* (1994), 47.3(3), printed p.262.
-/

@[expose] public section
open Subgroup
namespace CFSG.Quasithin.Janko23.J2Recognition.SourceLocal.PrimeNormalizers.ThreeLocal
variable {G : Type*} [Group G] [Finite G]

/-- Output of lifting the projective Sylow normalizer through the actual
central kernel. This structure makes no assertion of existence. -/
structure SylowNormalizerAction (P : Sylow 3 G) where
  complement : Subgroup (normalizer (P : Set G))
  cyclic : IsCyclic complement
  card : Nat.card complement = 8
  split : ((P : Subgroup G).subgroupOf (normalizer (P : Set G))).IsComplement' complement
  faithful : Function.Injective ((sylowFrattiniAction P).comp complement.subtype)
  transitive : ∀ u v : P ⧸ frattini P, u ≠ 1 → v ≠ 1 →
    ∃ b : complement, sylowFrattiniAction P b u = v

omit [Finite G] in
/-- Compatibility with the original quotient map, used to lift orbit fusion. -/
theorem sylowFrattiniAction_apply_mk (P : Sylow 3 G)
    (b : normalizer (P : Set G)) (x : P) :
    sylowFrattiniAction P b (QuotientGroup.mk' (frattini P) x) =
      QuotientGroup.mk' (frattini P) ((P : Subgroup G).normalizerMonoidHom b x) :=
  quotientAut_apply_mk (frattini P) ((P : Subgroup G).normalizerMonoidHom b) x

end CFSG.Quasithin.Janko23.J2Recognition.SourceLocal.PrimeNormalizers.ThreeLocal
