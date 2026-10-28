module
public import Theory.GroupAction.EvenPolygonFixedConnected
public import Theory.GroupAction.RankTwoCosetGeometry.FixedFusion
public import CFSG.Quasithin.ChapterF.Section04.SourceCompletion.UnitaryNonbinary.FiveGeometry
public import CFSG.Quasithin.Chapter5.Section03UnitaryNativeLift.Models

/-!
# Fusion from the whole middle of a U₅(4) extension

Apply the proved quadrangle metric to the canonical completion of the same
extension, whose order bound is reflexive. An element of its whole middle
fixes the base edge. Unique short paths make its fixed graph connected,
even when outer involutions fix apartments. Compatible endpoint maps then
transport conjugacy along fixed paths.

This proves the middle-to-plane part of F.4.30 consumed by the original
ambient involution-coverage argument. It uses no ambient order bound and
no completion recognition. Source: Aschbacher–Smith F.4.30,35, pp.290–292.
-/

public noncomputable section

namespace CFSG.Quasithin.ChapterF.SourceCompletion.UnitaryNonbinary
open Subgroup Theory.GroupTheory
open Subgroup.CosetGeometry hiding Vertex base
open Subgroup.CosetGeometry.RankTwo SimpleGraph
open GroupAction.EvenPolygon
variable (U : GreenBook.UnitaryFive.Model 4) (E : FiveExtension U)

/-- Every element of the whole marked middle fixes a connected coset graph. -/
theorem FiveExtension.middle_fixed_connected (x : E.middle) :
    ((graph E.family).induce {v | inclusion (inf_le_left.trans E.left_le) x • v = v}).Connected := by
  let hgen := Chapter5.UnitaryNativeLift.Five.parabolics_generate U
  have hq := five_completion_quadrangle U E (E.completion hgen)
    (E.completion_overlap hgen) le_rfl
  rw [E.completion_family hgen] at hq
  have hg := (E.completion hgen).generated
  change (E.completion hgen).cosetFamily false ⊔ (E.completion hgen).cosetFamily true = ⊤ at hg
  rw [E.completion_family hgen] at hg
  have hconn := Subgroup.CosetGeometry.RankTwo.connected E.family hg
  have hm : Metric.MetricAction (G := E.carrier) 2 (graph E.family) (·.type) :=
    { adjacent_color := fun h => h.1
      smul_adj := fun g _ _ h => (translationGraphIso E.family g).toHom.map_adj h
      diameter_bound := fun v w => by
        obtain ⟨p,hp⟩ := hconn.exists_walk_length_eq_dist v w
        exact ⟨p,hp.le.trans (hq.2.1 v w)⟩
      cycle_bound := hq.1 }
  let t : E.carrier := inclusion (inf_le_left.trans E.left_le) x
  have hfix (i : Bool) : CosetGeometry.base E.family i ∈ fixedVertices (zpowers t) := by
    have ht : t ∈ MulAction.stabilizer E.carrier (CosetGeometry.base E.family i) := by
      rw [CosetGeometry.stabilizer_base]
      cases i
      · exact x.property.1
      · exact x.property.2
    exact fun g hg => (zpowers_le.mpr ht) hg
  have he : (graph E.family).Adj (CosetGeometry.base E.family false) (CosetGeometry.base E.family true) :=
    ⟨Bool.false_ne_true,1,rfl,rfl⟩
  have h := Metric.fixed_graph_connected hm (zpowers t)
    ⟨_,_,he,hfix false,hfix true⟩
  have hs : fixedVertices (zpowers t) = {v : CosetGeometry.Vertex E.family | t • v = v} := by
    ext v
    exact ⟨fun hv => hv t (mem_zpowers t),fun hv g hg => (show zpowers t ≤ MulAction.stabilizer E.carrier v from zpowers_le.mpr hv) hg⟩
  rw [hs] at h
  exact h

/-- Compatible endpoint maps preserve fusion from the whole middle into the
plane endpoint. No homomorphism from the entire extension is assumed. -/
theorem FiveExtension.right_fusion_of_middle {G : Type*} [Group G]
    (l : E.left →* G) (r : E.right →* G)
    (hc : ∀ z : E.middle, l (inclusion inf_le_left z) = r (inclusion inf_le_right z))
    (x : E.middle) (y : E.right)
    (hxy : IsConj (inclusion (inf_le_left.trans E.left_le) x) (inclusion E.right_le y)) :
    IsConj (r (inclusion inf_le_right x)) (r y) := by
  let f : ∀ i, E.family i →* G := fun i => match i with
    | false => l.comp (subgroupOfEquivOfLe E.left_le).toMonoidHom
    | true => r.comp (subgroupOfEquivOfLe E.right_le).toMonoidHom
  have hf (z : E.carrier) (h₀ : z ∈ E.family false) (h₁ : z ∈ E.family true) :
      f false ⟨z,h₀⟩ = f true ⟨z,h₁⟩ := hc ⟨z.val,h₀,h₁⟩
  let x' : E.family true := ⟨inclusion (inf_le_left.trans E.left_le) x,x.property.2⟩
  let y' : E.family true := (subgroupOfEquivOfLe E.right_le).symm y
  exact Subgroup.CosetGeometry.Fusion.of_fixed_connected E.family f hf x' y'
    (E.middle_fixed_connected U x).preconnected hxy
end CFSG.Quasithin.ChapterF.SourceCompletion.UnitaryNonbinary
