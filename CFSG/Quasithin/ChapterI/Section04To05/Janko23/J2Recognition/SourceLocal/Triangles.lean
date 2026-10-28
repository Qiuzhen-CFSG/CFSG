module

public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.J2Recognition.SourceLocal.System
public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.J2Recognition.SourceLocal.SourceOrbits.EdgeConfigurations.InternalTriangles
public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.J2Recognition.SourceLocal.SourceOrbits.EdgeConfigurations.SourceTriangles

/-!
# The two source triangle branches in the actual uniqueness system

The local A₅ supplies an internal third vertex in the endpoint A₄ and an
external third vertex generating A₅ with the endpoints. The internal common
neighbors form one orbit under the setwise edge stabilizer, by a transporter
inside the endpoint A₄. The external orbit is supplied by the source local
incidence and counting argument. Thus the two triangle types cover every
triangle of the source graph, without any additional orbit premise.

Source: Aschbacher, *Sporadic Groups* (1994), 47.6(5) and its application
in 47.10, pp.264, 267. The pointwise fixer is not used to merge the
internal triangles.
-/

public section

open Subgroup Theory.GroupTheory.GraphUniquenessSystem
namespace CFSG.Quasithin.Janko23.J2Recognition.SourceLocal.EdgeFrame
variable {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]
variable {D : Seed G} (F : EdgeFrame D)

/-- Both source types occur in the local orbit graph, with their literal
internal/external distinction relative to the endpoint A₄. -/
theorem triangle_representatives :
    ∃ T₁ T₂ : D.Vertex,
      (F.localData.simpleSystem.localEdge F.y T₁ ∧
        F.localData.simpleSystem.localEdge T₁ D.base) ∧
      (F.localData.simpleSystem.localEdge F.y T₂ ∧
        F.localData.simpleSystem.localEdge T₂ D.base) ∧
      T₁.val ≤ D.X ⊔ F.y.val ∧ ¬ T₂.val ≤ D.X ⊔ F.y.val ∧
      ¬ ∃ g : edgeStabilizer G D.base F.y, (g : G) • T₁ = T₂ := by
  obtain ⟨T₁, T₂, h₁, h₂, hs, hl, hn⟩ :=
    F.localData.two_triangle_types_of_alternatingFive F.localEquiv
      (le_sup_left.trans F.localData_endpoints)
      (le_sup_right.trans F.localData_endpoints) D.faithful
  refine ⟨T₁, T₂, h₁, h₂, (le_sup_right.trans_eq hs), ?_, hn⟩
  intro hle
  have he : D.X ⊔ F.y.val = F.K := (sup_eq_left.mpr hle).symm.trans hl
  have hc : Nat.card F.K = 60 := by
    rw [Nat.card_congr F.localEquiv.toEquiv, nat_card_alternatingGroup]
    norm_num
  have hj := card_join_of_adj D F.adjacent
  change Nat.card (D.X ⊔ F.y.val : Subgroup G) = 12 at hj
  rw [he, hc] at hj
  omega

/-- The already proved internal orbit discharges that branch of 47.6(5).
Only transitivity on external common neighbors remains explicit. -/
theorem trianglesInLocalOrbits_of_external_transitivity
    (hexternal : ∀ U V : D.Vertex,
      D.graph.Adj D.base U → D.graph.Adj F.y U →
      D.graph.Adj D.base V → D.graph.Adj F.y V →
      ¬ U.val ≤ D.X ⊔ F.y.val → ¬ V.val ≤ D.X ⊔ F.y.val →
      ∃ e : edgeStabilizer G D.base F.y, (e : G) • U = V) :
    F.localData.simpleSystem.TrianglesInLocalOrbits := by
  obtain ⟨T₁, T₂, h₁, h₂, hin, hout, _⟩ := F.triangle_representatives
  apply triangles_of_two_edgeStabilizer_orbits F.localData T₁ T₂ h₁ h₂
  intro V hVX hVY
  have h₁X := (F.localData.simpleSystem.localEdge_adj h₁.2).symm
  have h₁Y := F.localData.simpleSystem.localEdge_adj h₁.1
  have h₂X := (F.localData.simpleSystem.localEdge_adj h₂.2).symm
  have h₂Y := F.localData.simpleSystem.localEdge_adj h₂.1
  by_cases hV : V.val ≤ D.X ⊔ F.y.val
  · obtain ⟨g, _, hg⟩ := F.internal_third_transitive
      (InvolutionGeometry.Applications.edgeFixer_equiv D F.adjacent)
      F.localEquiv V T₁ hVX hVY h₁X h₁Y hV hin
    exact ⟨g, Or.inl hg⟩
  · obtain ⟨g, hg⟩ := hexternal V T₂ hVX hVY h₂X h₂Y hV hout
    exact ⟨g, Or.inr hg⟩

/-- Both triangle branches of 47.6(5) in the actual source uniqueness system.
All local incidence and transitivity premises are discharged from the seed. -/
theorem trianglesInLocalOrbits : F.localData.simpleSystem.TrianglesInLocalOrbits := by
  apply F.trianglesInLocalOrbits_of_external_transitivity
  intro U V hUX hUY hVX hVY houtU houtV
  obtain ⟨f, hf⟩ := EdgeConfigurations.external_common_transitive D F.y F.adjacent
    U V hUX hUY hVX hVY houtU houtV
  exact ⟨⟨f, Or.inl f.property⟩, hf⟩

end CFSG.Quasithin.Janko23.J2Recognition.SourceLocal.EdgeFrame
