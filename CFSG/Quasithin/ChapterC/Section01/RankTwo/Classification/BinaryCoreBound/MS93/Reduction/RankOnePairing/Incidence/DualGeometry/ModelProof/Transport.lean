module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.RankOnePairing.Incidence.DualGeometry.ModelProof.Standard
/-!
# Simultaneous natural and contragredient coordinate transport

A common conjugator for the marked natural parabolics yields a different
conjugator for their duals, via inverse transpose and coordinate reversal.
Fixed spaces, actual orbit spans, and actors transport compatibly. The actor
automorphism preserves products, so opposite actors retain their required
neighboring-parabolic times seed-parabolic factorizations.

Source: Meierfrankenfeld--Stellmacher (1993), (1.7)(ii), printed p.848.
-/

@[expose] public section
open Matrix Subgroup
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.RankOnePairing.Incidence.DualGeometry.ModelProof
open FixedGeometry.ValueConstruction FixedGeometry.ValueConstruction.ModelProof
open Matrix.PSL3Two Matrix.PSL3Two.MarkedAutomorphisms
open BinaryLinearThree.AutomorphismAction

theorem graph_inverseTranspose (a : SL) : graph a = inverseTranspose a := by
  change a⁻¹.transpose = a.transpose⁻¹
  have hm (x y : SL) : (x*y).transpose = y.transpose*x.transpose := by
    apply Subtype.ext
    exact Matrix.transpose_mul _ _
  have ho : (1 : SL).transpose = 1 := by
    apply Subtype.ext
    exact Matrix.transpose_one
  apply eq_inv_of_mul_eq_one_left
  rw [← hm, mul_inv_cancel, ho]

def dualConjugator (k : SL) : SL := graph k * (Bruhat.perm 5)⁻¹

theorem graph_conj_diagram (k a : SL) :
    graph (MulAut.conj k a) = MulAut.conj (dualConjugator k) (diagram a) := by
  change graph (k*a*k⁻¹) = (graph k * (Bruhat.perm 5)⁻¹) *
    (Bruhat.perm 5 * inverseTranspose a * (Bruhat.perm 5)⁻¹) *
      (graph k * (Bruhat.perm 5)⁻¹)⁻¹
  rw [map_mul, map_mul, map_inv, graph_inverseTranspose a]
  group

theorem map_aut_mul (P : Subgroup SL) (α β : MulAut SL) :
    P.map (α * β).toMonoidHom = (P.map β.toMonoidHom).map α.toMonoidHom := by
  rw [Subgroup.map_map]
  rfl

theorem map_graph_conj (P : Subgroup SL) (k : SL) :
    (P.map (MulAut.conj k).toMonoidHom).map graph.toMonoidHom =
      (P.map diagram.toMonoidHom).map (MulAut.conj (dualConjugator k)).toMonoidHom := by
  rw [Subgroup.map_map, Subgroup.map_map]
  apply congrArg (fun f : SL →* SL => P.map f)
  apply MonoidHom.ext
  intro a
  exact graph_conj_diagram k a

theorem lineParabolic_map_diagram : lineParabolicSL.map diagram.toMonoidHom = pointParabolicSL := by
  ext a
  constructor
  · rintro ⟨x,hx,rfl⟩
    exact (diagram_line x).mpr hx
  · intro ha
    exact ⟨diagram a, (diagram_point_line a).mpr ha, diagram_apply_twice a⟩

theorem dual_marked (σ : MulAut SL) (g : SL) (i : Bool) :
    markedParabolic (dualMark σ) g i = (markedParabolic σ g i).map graph.toMonoidHom := by
  rw [markedParabolic, markedParabolic, Subgroup.map_map]
  rfl

theorem orbitSpan_map (σ τ : MulAut SL) (P : Subgroup SL) (A : Subgroup Space) :
    orbitSpan σ (P.map τ.toMonoidHom) A = orbitSpan (σ * τ) P A := by
  apply le_antisymm
  · apply iSup_le
    rintro ⟨a,ha⟩
    obtain ⟨b,hb,rfl⟩ := ha
    exact le_iSup_of_le (⟨b,hb⟩ : P) le_rfl
  · apply iSup_le
    intro a
    exact le_iSup_of_le (⟨τ a, mem_map_of_mem _ a.property⟩ : P.map τ.toMonoidHom) le_rfl

theorem orbitSpan_conj (σ : MulAut SL) (P : Subgroup SL) (A : Subgroup Space) (k : SL) :
    orbitSpan (MulAut.conj k * σ) P (A.map (vectorAction k).toMonoidHom) =
      (orbitSpan σ P A).map (vectorAction k).toMonoidHom := by
  unfold orbitSpan
  rw [Subgroup.map_iSup]
  apply iSup_congr
  intro a
  exact map_action_conj k (σ a) A

theorem seed_coordinates (σ : MulAut SL) (g : SL) (i : Bool) (k : SL)
    (hp : markedParabolic σ g i = lineParabolicSL.map (MulAut.conj k).toMonoidHom) :
    seedLine σ g i = L.map (vectorAction (dualConjugator k)).toMonoidHom := by
  rw [seedLine, dual_marked, hp, map_graph_conj, lineParabolic_map_diagram,
    fixedSpace_conj, fixed_point]

theorem plane_coordinates (σ : MulAut SL) (g : SL) (i : Bool) (k : SL)
    (hp : markedParabolic σ g i = lineParabolicSL.map (MulAut.conj k).toMonoidHom)
    (hq : markedParabolic σ g (!i) = pointParabolicSL.map (MulAut.conj k).toMonoidHom) :
    neighboringPlane σ g i = H.map (vectorAction (dualConjugator k)).toMonoidHom := by
  have ho : orbitSpan (dualMark σ) (modelParabolic g (!i)) (seedLine σ g i) =
      orbitSpan 1 (markedParabolic (dualMark σ) g (!i)) (seedLine σ g i) := by
    rw [markedParabolic, orbitSpan_map, one_mul]
  rw [neighboringPlane, ho, dual_marked, hq, map_graph_conj, seed_coordinates σ g i k hp,
    orbitSpan_map, one_mul, orbitSpan_map, orbitSpan_conj, orbit_plane]

def actor (σ : MulAut SL) (k : SL) : MulAut SL := (MulAut.conj k).trans σ.symm

theorem natural_actor (σ : MulAut SL) (k a : SL) : σ (actor σ k a) = MulAut.conj k a :=
  σ.apply_symm_apply _

theorem dual_actor (σ : MulAut SL) (k a : SL) :
    dualMark σ (actor σ k a) = MulAut.conj (dualConjugator k) (diagram a) := by
  change graph (σ (actor σ k a)) = _
  rw [natural_actor, graph_conj_diagram]

theorem actor_mem (σ : MulAut SL) (k : SL) (P A : Subgroup SL)
    (h : P.map σ.toMonoidHom = A.map (MulAut.conj k).toMonoidHom) (a : SL) :
    actor σ k a ∈ P ↔ a ∈ A := by
  constructor
  · intro ha
    have hh := mem_map_of_mem σ.toMonoidHom ha
    rw [h] at hh
    obtain ⟨b,hb,he⟩ := hh
    change MulAut.conj k b = σ (actor σ k a) at he
    rw [natural_actor] at he
    exact (MulAut.conj k).injective he ▸ hb
  · intro ha
    have hh : MulAut.conj k a ∈ P.map σ.toMonoidHom := by
      rw [h]
      exact mem_map_of_mem _ ha
    obtain ⟨b,hb,he⟩ := hh
    have he' : b = actor σ k a := σ.injective (he.trans (natural_actor σ k a).symm)
    exact he' ▸ hb

theorem natural_map_actor (σ : MulAut SL) (k a : SL) (A : Subgroup Space) :
    (A.map (vectorAction k).toMonoidHom).map (vectorAction (σ (actor σ k a))).toMonoidHom =
      (A.map (vectorAction a).toMonoidHom).map (vectorAction k).toMonoidHom := by
  rw [natural_actor, map_action_conj]

theorem dual_map_actor (σ : MulAut SL) (k a : SL) (A : Subgroup Space) :
    (A.map (vectorAction (dualConjugator k)).toMonoidHom).map
      (vectorAction (dualMark σ (actor σ k a))).toMonoidHom =
      (A.map (vectorAction (diagram a)).toMonoidHom).map
        (vectorAction (dualConjugator k)).toMonoidHom := by
  rw [dual_actor, map_action_conj]

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.RankOnePairing.Incidence.DualGeometry.ModelProof
