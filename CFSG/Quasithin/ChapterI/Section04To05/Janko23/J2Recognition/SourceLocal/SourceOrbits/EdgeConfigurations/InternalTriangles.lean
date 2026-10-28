module

public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.J2Recognition.SourceLocal.SourceOrbits.EdgeConfigurations.Basic
public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.J2Recognition.SourceLocal.AlternatingFiveGeometry.Edges
public import Theory.SpecificGroups.Alternating.FiveLocalGeometry.InternalTriangles

/-!
# The internal setwise-edge orbit in the J₂ graph

The local A₅ geometry supplies a containing subgroup K. Inside K, the
finite marked-edge calculation exchanges the two remaining cubic subgroups
of the A₄ join. Restriction and inclusion give a conjugating element of
the literal ambient setwise edge stabilizer, inside X ⊔ Y itself.

This closes the internal transitivity branch of Aschbacher,
*Sporadic Groups* (1994), 47.6(5), p.264. The construction of K and
transitivity on external common neighbors are separate source steps.
-/

public section

open Subgroup Theory.GroupTheory.GraphUniquenessSystem
open scoped Pointwise
namespace CFSG.Quasithin.Janko23.J2Recognition.SourceLocal.EdgeConfigurations
variable {G : Type*} [Group G] [Finite G]

private theorem lift_conjugation (D : Seed G) (K : Subgroup G)
    (A B : D.Vertex) (hA : A.val ≤ K) (hB : B.val ≤ K) (g : K)
    (h : (A.val.subgroupOf K).map (MulAut.conj g).toMonoidHom = B.val.subgroupOf K) :
    (g : G) • A = B := by
  change MulAut.conj g • A.val.subgroupOf K = B.val.subgroupOf K at h
  rw [conj_smul_subgroupOf hA g] at h
  have hm := congrArg (fun P : Subgroup K => P.map K.subtype) h
  rw [map_subgroupOf_eq_of_le (conj_smul_le_of_le hA g),
    map_subgroupOf_eq_of_le hB] at hm
  exact Subtype.ext hm

/-- Any two internal common neighbors are conjugate under the actual setwise
edge stabilizer. The witness lies in the A₄ endpoint join. -/
theorem internal_third_transitive (D : Seed G) (K : Subgroup G)
    (eK : K ≃* alternatingGroup (Fin 5)) (Y : D.Vertex)
    (hXY : D.graph.Adj D.base Y) (hXK : D.X ≤ K) (hYK : Y.val ≤ K)
    (U V : D.Vertex)
    (hUX : D.graph.Adj D.base U) (hUY : D.graph.Adj Y U)
    (hVX : D.graph.Adj D.base V) (hVY : D.graph.Adj Y V)
    (hU : U.val ≤ D.X ⊔ Y.val) (hV : V.val ≤ D.X ⊔ Y.val) :
    ∃ g : edgeStabilizer G D.base Y,
      (g : G) ∈ D.X ⊔ Y.val ∧ (g : G) • U = V := by
  have hJK : D.X ⊔ Y.val ≤ K := sup_le hXK hYK
  have hUK := hU.trans hJK
  have hVK := hV.trans hJK
  have card (W : D.Vertex) (hW : W.val ≤ K) : Nat.card (W.val.subgroupOf K) = 3 := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hW).toEquiv, D.vertex_card]
  have neq (A B : D.Vertex) (hA : A.val ≤ K) (hB : B.val ≤ K) (hne : A ≠ B) :
      A.val.subgroupOf K ≠ B.val.subgroupOf K := by
    intro h
    apply hne
    apply Subtype.ext
    have hm := congrArg (fun P : Subgroup K => P.map K.subtype) h
    simpa only [map_subgroupOf_eq_of_le hA, map_subgroupOf_eq_of_le hB] using hm
  obtain ⟨eJ⟩ := (D.graph_adj_iff D.base Y).mp hXY
  obtain ⟨g, hg, hs, huv⟩ := alternatingGroup.FiveLocalGeometry.InternalTriangles.exists_transporter
    eK (D.X.subgroupOf K) (Y.val.subgroupOf K) (U.val.subgroupOf K) (V.val.subgroupOf K)
    (card D.base hXK) (card Y hYK) (card U hUK) (card V hVK)
    ((AlternatingFiveGeometry.joinSubgroupOfEquiv K D.X Y.val hXK hYK).trans eJ)
    (by rw [← subgroupOf_sup hXK hYK]; exact comap_mono hU)
    (by rw [← subgroupOf_sup hXK hYK]; exact comap_mono hV)
    (neq U D.base hUK hXK hUX.ne.symm) (neq U Y hUK hYK hUY.ne.symm)
    (neq V D.base hVK hXK hVX.ne.symm) (neq V Y hVK hYK hVY.ne.symm)
  have hstab : (g : G) ∈ edgeStabilizer G D.base Y := by
    rcases hs with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
    · exact Or.inl ⟨lift_conjugation D K D.base D.base hXK hXK g h₁,
        lift_conjugation D K Y Y hYK hYK g h₂⟩
    · exact Or.inr ⟨lift_conjugation D K D.base Y hXK hYK g h₁,
        lift_conjugation D K Y D.base hYK hXK g h₂⟩
  refine ⟨⟨g, hstab⟩, ?_, lift_conjugation D K U V hUK hVK g huv⟩
  have hm := mem_map_of_mem K.subtype hg
  simpa only [Subgroup.map_sup, map_subgroupOf_eq_of_le hXK,
    map_subgroupOf_eq_of_le hYK, Subgroup.subtype_apply] using hm

end CFSG.Quasithin.Janko23.J2Recognition.SourceLocal.EdgeConfigurations

namespace CFSG.Quasithin.Janko23.J2Recognition.SourceLocal.EdgeFrame
variable {G : Type*} [Group G] [Finite G] {D : Seed G} (F : EdgeFrame D)

/-- Application to the literal C_G(B), discharging the internal orbit needed
by the source triangle assembly from the earlier five-local model of K. -/
theorem internal_third_transitive
    (hF : Nonempty (edgeFixer G D.base F.y ≃* alternatingGroup (Fin 5)))
    (eK : F.K ≃* alternatingGroup (Fin 5)) (U V : D.Vertex)
    (hUX : D.graph.Adj D.base U) (hUY : D.graph.Adj F.y U)
    (hVX : D.graph.Adj D.base V) (hVY : D.graph.Adj F.y V)
    (hU : U.val ≤ D.X ⊔ F.y.val) (hV : V.val ≤ D.X ⊔ F.y.val) :
    ∃ g : edgeStabilizer G D.base F.y,
      (g : G) ∈ D.X ⊔ F.y.val ∧ (g : G) • U = V :=
  EdgeConfigurations.internal_third_transitive D F.K eK F.y F.adjacent
    (le_sup_left.trans (F.endpoints_le hF)) (le_sup_right.trans (F.endpoints_le hF))
    U V hUX hUY hVX hVY hU hV

end CFSG.Quasithin.Janko23.J2Recognition.SourceLocal.EdgeFrame
