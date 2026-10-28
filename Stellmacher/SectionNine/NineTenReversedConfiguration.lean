module
public import Stellmacher.SectionNine.NineTenPredecessorNoncommutation
public import Stellmacher.SectionNine.NineTenReversedCommutatorContainment
public import Stellmacher.SectionNine.NineTenReversedSuppliedPath

/-!
# The actual normalized reversed configuration through (9.10)(5)

At critical distance greater than three, retain both actual normalized
geometric extraction packets, including the original second actor and both
residual conjugator bounds. The same extracted predecessor has nontrivial
commutator with the penultimate center, and that commutator lies in both the
first and predecessor modules. The reversed endpoints form a commuting
critical pair with a full supplied path whose first vertex is the original
preterminal vertex and whose backward vertex is the original first step.

This is a thin assembly: actual (9.8) and (9.9) supply the two noncontainments
inside the normalized predecessor theorem; actual (9.4) and (9.7) prove its
noncommutation and the reversed commutator placement. The reversed-path
construction retains the original sequence rather than choosing another
geodesic. Every assertion uses the same data returned by one normalization.

Source: Stellmacher (9.10)(5), printed p.57, and the first sentence on p.58.
The further transvection choice and backward-containment reorientation for
(9.5), and the subsequent long-distance exclusions, remain separate results.
-/

namespace Stellmacher.SectionNine
open Later SectionsFiveToSeven CosetGraphContext SevenSix
universe u

public theorem nine_ten_normalized_reversed_configuration
    {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    {embedding : G →* H} {T A B : Subgroup G}
    (ctx : AmbientSectionNineContext H S0 S P1 P2 embedding T A B)
    (hb : 3 < ctx.criticalPath.length) :
    ∃ cp : CriticalPath ctx.Γ,
      cp.length = ctx.criticalPath.length ∧
      ⁅ZAt ctx.Γ cp.a, ZAt ctx.Γ cp.a'⁆ = ⊥ ∧
      (¬ ZAt ctx.Γ cp.a' ≤ VAt ctx.Γ cp.firstStep) ∧
      (¬ ZAt ctx.Γ cp.firstStep ≤ VAt ctx.Γ cp.a') ∧
      ∃ (neighbor second : ctx.Γ.Vertex) (actor : G) (E A0 : Subgroup G)
        (data : NineThreeGeometricData ctx.Γ cp.firstStep second
          (VAt ctx.Γ cp.a') E A0 actor),
        IsCriticalPathOffset ctx.Γ cp 2 second ∧
        ctx.Γ.act data.x⁻¹ second = cp.a ∧
        neighbor ∈ neighborhood ctx.Γ cp.a' ∧
        actor ∈ ZAt ctx.Γ neighbor ∧
        ⁅ZAt ctx.Γ cp.a, ZAt ctx.Γ neighbor⁆ ≠ ⊥ ∧
        twoResidualIn E ≤ ⁅twoResidualIn E, Subgroup.zpowers actor⁆ ∧
        ∃ (firstActor : G) (firstE firstA0 : Subgroup G)
          (firstData : NineThreeGeometricData ctx.Γ cp.a'
            (cp.path ⟨cp.length - 1, Nat.lt_succ_of_le (Nat.sub_le _ _)⟩)
            (VAt ctx.Γ cp.firstStep) firstE firstA0 firstActor),
          ctx.Γ.act firstData.x⁻¹
            (cp.path ⟨cp.length - 1, Nat.lt_succ_of_le (Nat.sub_le _ _)⟩) = neighbor ∧
          (∀ b : G, b ∈ VAt ctx.Γ cp.firstStep → b ∉ firstA0 →
            twoResidualIn firstE ≤ ⁅twoResidualIn firstE, Subgroup.zpowers b⁆) ∧
          ∀ third : ctx.Γ.Vertex, IsCriticalPathOffset ctx.Γ cp 3 third →
            let predecessor := ctx.Γ.act data.x⁻¹ third
            let penultimate := cp.path ⟨cp.length - 1, Nat.lt_succ_of_le (Nat.sub_le _ _)⟩
            ⁅VAt ctx.Γ predecessor, ZAt ctx.Γ penultimate⁆ ≠ ⊥ ∧
            ⁅VAt ctx.Γ predecessor, ZAt ctx.Γ penultimate⁆ ≤
              VAt ctx.Γ cp.firstStep ⊓ VAt ctx.Γ predecessor ∧
            IsCriticalPair ctx.Γ penultimate predecessor ∧
            ⁅ZAt ctx.Γ penultimate, ZAt ctx.Γ predecessor⁆ = ⊥ ∧
            ∃ path : Fin (cp.length + 1) → ctx.Γ.Vertex,
              path 0 = penultimate ∧
              path ⟨cp.length, Nat.lt_succ_self _⟩ = predecessor ∧
              path ⟨1, by have := cp.length_pos; omega⟩ =
                cp.path ⟨cp.length - 2, Nat.lt_succ_of_le (Nat.sub_le _ _)⟩ ∧
              path ⟨cp.length - 2, Nat.lt_succ_of_le (Nat.sub_le _ _)⟩ = cp.firstStep ∧
              ∀ index : Fin cp.length, ctx.Γ.adjacent (path index.castSucc) (path index.succ) := by
  obtain ⟨cp, hlen, hcomm, hterm, hfirst, neighbor, second, actor, E, A0, data,
    hsecond, hnew, hneighbor, hactor, hcenters, hactorComm,
    firstActor, firstE, firstA0, firstData, hfirstNew, hfirstActors, hnoncomm⟩ :=
    nine_ten_normalized_noncommuting_predecessor ctx hb
  let shifted : AmbientSectionNineContext H S0 S P1 P2 embedding T A B :=
    {ctx with criticalPath := cp, commutator_eq := hcomm}
  have hlength : 4 < cp.length := by
    have hfive := nine_ten_length_ge_five ctx.toLocalContext hb
    change 5 ≤ ctx.criticalPath.length at hfive
    omega
  let third0 := cp.path ⟨3, by omega⟩
  have hthird0 : IsCriticalPathOffset ctx.Γ cp 3 third0 := ⟨⟨3, by omega⟩, rfl, rfl⟩
  have hpath := nine_ten_reversed_supplied_path shifted hlength neighbor second actor E A0 data
    hsecond hnew hneighbor hcenters (hnoncomm third0 hthird0)
  have hcontain := nine_ten_reversed_commutator_containment shifted hlength hterm
    neighbor second actor E A0 data hsecond hactor hactorComm hnew hneighbor
      firstActor firstE firstA0 firstData hfirstNew
  refine ⟨cp, hlen, hcomm, hterm, hfirst, neighbor, second, actor, E, A0, data,
    hsecond, hnew, hneighbor, hactor, hcenters, hactorComm,
    firstActor, firstE, firstA0, firstData, hfirstNew, hfirstActors, ?_⟩
  intro third hthird
  have heq : third0 = third := by
    obtain ⟨index, hindex, hvertex⟩ := hthird
    have hindexEq : (⟨3, by omega⟩ : Fin (cp.length + 1)) = index := Fin.ext hindex.symm
    exact (congrArg cp.path hindexEq).trans hvertex
  subst third
  exact ⟨hnoncomm third0 hthird0, hcontain, hpath⟩

end Stellmacher.SectionNine
