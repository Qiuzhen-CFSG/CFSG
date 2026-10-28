module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.Initial.Natural.Triple.Action
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.Initial.Natural.Triple.Composition.Filtration

/-!
# The actual dual radius-module filtration

The endpoint subgroup is elementary abelian, has order-two image in the
specified local SL₃(2) quotient, and has fixed codimension at most one on
the dual of the literal V_a/Z_a. Applying the independent representation
theorem gives either trivial residual action or invariant spaces F ≤ W
with residual-fixed margins and a literal natural section W/F. Its inherited
action is identified equivariantly, with the graph marking allowing duality.

This is the composition prerequisite for the dual-module argument in
Meierfrankenfeld–Stellmacher (1993), (4.3.1)(iii), p.883, using the
representation theory of (1.4)–(1.5), pp.842–843. Control of the two-core
on the dual moving space remains a separate extension argument; no triple
commutator conclusion is asserted here.
-/

public section

open Subgroup Representation Stellmacher.PushingUp.AmalgamGraph
open Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.Initial.Natural.Triple
variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}

/-- The actual dual radius quotient has at most one moving natural section,
with both margins fixed by the local two-residual. This does not assert that
the local two-core fixes the moving subspace. -/
theorem radius_dual_filtration (source : LocalSource L R)
    (geometry : Geometry R) (hb : 2 < geometry.b R) (modules : ModuleFacts source geometry)
    (p : Counterexample geometry)
    (hfour : Nat.card (radiusCommutator p.a p.a') = 4) :
    let S := stabilizer R p.a
    let H := (V R p.a).subgroupOf S
    let N := (Z R p.a).subgroupOf S
    letI := radius_normal p.a
    letI := geometry.Z_normal p.a
    letI : IsElementaryAbelian 2 (H ⧸ N.subgroupOf H) :=
      elementary_radius_quotient source geometry hb modules p.a p.color_a
    let ρ := (sectionRepresentation H N).dual
    ∃ π : S →* SL, Function.Surjective π ∧
      π.ker = (Q R p.a).subgroupOf S ∧
      (fixedSpace ρ (pResidual 2 S) = ⊤ ∨
        ∃ F W : Subrepresentation ρ, F ≤ W ∧
          F.toSubmodule ≤ fixedSpace ρ (pResidual 2 S) ∧
          fixedSpace W.quotientRepresentation (pResidual 2 S) = ⊤ ∧
          ∃ a : SL ≃* SL,
            Nonempty ((Representation.BinaryOffender.sectionRepresentation ρ F W).Equiv
              ((BinaryLinearThree.W.comp a.toMonoidHom).comp π))) := by
  let S := stabilizer R p.a
  let H := (V R p.a).subgroupOf S
  let N := (Z R p.a).subgroupOf S
  let := radius_normal (R := R) p.a
  let := geometry.Z_normal p.a
  let : IsElementaryAbelian 2 (H ⧸ N.subgroupOf H) :=
    elementary_radius_quotient source geometry hb modules p.a p.color_a
  let := finite_stabilizer R p.a
  obtain ⟨π, hπ, hker, hk, hA, hc⟩ :=
    exists_endpoint_projection source geometry hb modules p hfour
  exact ⟨π, hπ, hker, Composition.exists_residual_filtration π hπ hk
    ((Z R p.a').subgroupOf S) hA hc (sectionRepresentation H N).dual
    (radius_dual_displacement source geometry hb modules p)⟩
end CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.Initial.Natural.Triple
