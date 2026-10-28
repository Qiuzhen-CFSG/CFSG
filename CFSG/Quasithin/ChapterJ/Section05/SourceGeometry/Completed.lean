module
public import CFSG.Quasithin.ChapterJ.Section05.SourceGeometry.CommonSuzuki

/-!
# Original-source assembly with the exact Suzuki stabilizer

The genuine preceding marked J.4.7 equivalence selects the same original
q and g used to construct the rank-three action. Its second point stabilizer
has the two proved orbits on Delta and the unique975-point orbit on Sigma.
Its original common-neighbor stabilizer is identified with the literal Sz(2).
No graph-action, small-subgroup, or socle-avoidance certificate is assumed.
The preceding marked J.4.7 producer retains its source assembly owner.

Source: Aschbacher–Smith J.5.4(3) and J.5.5(4–5), printed pp.446–447.
-/

public noncomputable section
open Subgroup MulAction
namespace CFSG.Quasithin.ChapterJ.Section05
open RuSubgroup Centralizers.Choices Tits.ExceptionalParabolics.FullRee
variable {G:Type*} [Group G] [Finite G]

/-- The genuine preceding marked J.4.7 theorem supplies the original J.5.5 orbit geometry. -/
theorem SourceChoice.source_J_5_5_completed {d:LocalSetup G} (p:Plane d) (s:SourceChoice p)
    (B5:Sylow 5 d.toTypeRuSetup.H) (hi:∀a∈B5Image B5,s.v*a*s.v⁻¹=a⁻¹)
    (X:Sylow 3 p.parabolic) (e:p.F B5 X≃*ReeF4.Model 0)
    (hmark:((p.F₁ B5).subgroupOf (p.F B5 X)).map e.toMonoidHom=first)
    (P:Sylow 5 (p.F B5 X)) :
    ∃q g:G,q∈d.toTypeRuSetup.Q ∧
      g∈normalizer (((P:Subgroup (p.F B5 X)).map (p.F B5 X).subtype):Set G) ∧
      g∉p.F B5 X ∧ ∃(hq:q∉p.F B5 X)
      (hs:q•(q•basePoint (p.F B5 X))=basePoint (p.F B5 X))
      (_h:RudvalisAction (p.F B5 X) (q•basePoint (p.F B5 X)) (g•basePoint (p.F B5 X))),
      (∀x∈(sourceGraph (p.F B5 X) q hq hs).neighborSet (basePoint (p.F B5 X)),
        orbit (stabilizer (p.F B5 X) (g•basePoint (p.F B5 X))) x=
          (sourceGraph (p.F B5 X) q hq hs).commonNeighbors (basePoint (p.F B5 X)) (g•basePoint (p.F B5 X)) ∨
        orbit (stabilizer (p.F B5 X) (g•basePoint (p.F B5 X))) x=
          (sourceGraph (p.F B5 X) q hq hs).neighborSet (basePoint (p.F B5 X))∩
            sourceSigma (p.F B5 X) q hq hs (g•basePoint (p.F B5 X))) ∧
      (∀x∈sourceSigma (p.F B5 X) q hq hs (basePoint (p.F B5 X)),
        Nat.card (orbit (stabilizer (p.F B5 X) (g•basePoint (p.F B5 X))) x)=975→
          orbit (stabilizer (p.F B5 X) (g•basePoint (p.F B5 X))) x=
            (sourceGraph (p.F B5 X) q hq hs).neighborSet (g•basePoint (p.F B5 X))∩
              sourceSigma (p.F B5 X) q hq hs (basePoint (p.F B5 X))) ∧
      (∀x:(sourceGraph (p.F B5 X) q hq hs).commonNeighbors
          (basePoint (p.F B5 X)) (g•basePoint (p.F B5 X)),
        Nonempty (stabilizer (stabilizer (p.F B5 X) (g•basePoint (p.F B5 X))) x.val≃*
          BenderSuzuki.MatrixGroups.SuzukiMatrixGroup 0)) := by
  obtain ⟨q,g,hq,hg,hgF,hqF,hs,h,hO,hU⟩:=SourceChoice.source_J_5_5_orbits p s B5 hi X e hmark P
  exact ⟨q,g,hq,hg,hgF,hqF,hs,h,hO,hU,
    fun x=>h.common_neighbor_stabilizer_equiv_suzuki (p.F B5 X) q hqF hs x⟩

end CFSG.Quasithin.ChapterJ.Section05
