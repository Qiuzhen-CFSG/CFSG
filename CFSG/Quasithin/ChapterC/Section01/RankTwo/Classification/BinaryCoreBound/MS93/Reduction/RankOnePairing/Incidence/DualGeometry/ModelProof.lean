module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.RankOnePairing.Incidence.DualGeometry.ModelProof.Transport
/-!
# The marked dual matrix pencil

Zero natural fixed space selects the line member of the marked parabolic
pair. Its full two-core fixes a natural plane; the neighboring full two-core
fixes a line. In the contragredient action the seed is a line and its actual
neighboring orbit span is a plane. The standard coordinate calculation gives
all seven pencil conditions, transported through the common marking with
separate natural and dual conjugators.

The opposite actors retain the products of a neighboring-parabolic actor
and a seed-parabolic actor required for the literal ambient lifts. No local
residual-generation or ambient commutator assertion is assumed here.

Source: Meierfrankenfeld--Stellmacher, *Pushing up weak BN-pairs of rank two*
(1993), proof of (1.7)(ii), printed p.848.
-/

public section
open Matrix Subgroup
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.RankOnePairing.Incidence.DualGeometry
open FixedGeometry.ValueConstruction FixedGeometry.ValueConstruction.ModelProof
open Matrix.PSL3Two Matrix.PSL3Two.MarkedAutomorphisms ModelProof

private theorem standard_neighbors (p : SL) (hp : p ∈ lineParabolicSL) :
    ModelProof.H.map (vectorAction (diagram p)).toMonoidHom ≤
      L ⊔ L.map (vectorAction (diagram (p*d))).toMonoidHom ∧
    ModelProof.H.map (vectorAction (diagram p)).toMonoidHom ≤
      L ⊔ L.map (vectorAction (diagram (p*d^2))).toMonoidHom ∧
    ModelProof.H.map (vectorAction (p*d)).toMonoidHom ⊓
      ModelProof.H.map (vectorAction (p*d^2)).toMonoidHom ≤ L.map (vectorAction p).toMonoidHom ∧
    L.map (vectorAction p).toMonoidHom ≤ ModelProof.H := by
  have hpd := (diagram_line p).mpr hp
  refine ⟨?_, ?_, ?_, ?_⟩
  · have hh := congrArg (fun A : Subgroup Space => A.map (vectorAction (diagram p)).toMonoidHom) plane_span
    rw [Subgroup.map_sup, line_stable _ hpd, map_action_mul] at hh
    simpa only [map_mul, diagram_d] using hh.le
  · have hh := congrArg (fun A : Subgroup Space => A.map (vectorAction (diagram p)).toMonoidHom) plane_span_sq
    rw [Subgroup.map_sup, line_stable _ hpd, map_action_mul] at hh
    simpa only [map_mul, map_pow, diagram_d] using hh.le
  · rw [← map_action_mul, ← map_action_mul,
      ← Subgroup.map_inf _ _ (vectorAction p).toMonoidHom (vectorAction p).injective]
    exact map_mono plane_inter
  · rw [← plane_stable p hp]
    exact map_mono line_le_plane

private theorem geometry_of_line_point (σ : MulAut SL) (g : SL) (i : Bool) (k : SL)
    (hp : markedParabolic σ g i = lineParabolicSL.map (MulAut.conj k).toMonoidHom)
    (hq : markedParabolic σ g (!i) = pointParabolicSL.map (MulAut.conj k).toMonoidHom) :
    MatrixGeometry σ g i := by
  have hvp : modelValues σ g i = ModelProof.H.map (vectorAction k).toMonoidHom := by
    rw [values_eq_core, hp, core_fixed_conj, lineParabolicSL_pCoreIn_two_eq_R, fixed_lineCore]
  have hvq : modelValues σ g (!i) = L.map (vectorAction k).toMonoidHom := by
    rw [values_eq_core, hq, core_fixed_conj, MarkedProduct.pointParabolic_core, fixed_pointCore]
  have hs := seed_coordinates σ g i k hp
  have ht := plane_coordinates σ g i k hp hq
  have memp (a : SL) : actor σ k a ∈ modelParabolic g i ↔ a ∈ lineParabolicSL :=
    actor_mem σ k _ _ hp a
  have memq (a : SL) : actor σ k a ∈ modelParabolic g (!i) ↔ a ∈ pointParabolicSL :=
    actor_mem σ k _ _ hq a
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hs, Subgroup.card_map_of_injective (f := (vectorAction (dualConjugator k)).toMonoidHom)
      (vectorAction (dualConjugator k)).injective, line_card]
  · intro A hc hi
    have hc' : Nat.card (A.map (vectorAction k⁻¹).toMonoidHom) ≤ 4 := by
      rw [Subgroup.card_map_of_injective (f := (vectorAction k⁻¹).toMonoidHom)
        (vectorAction k⁻¹).injective]
      exact hc
    have hh := small_line _ hc' (invariant_pullback k lineParabolicSL A (hp ▸ hi))
    have hm := Subgroup.map_mono (f := (vectorAction k).toMonoidHom) hh
    rw [map_action_cancel] at hm
    rwa [hvp]
  · let p : modelParabolic g i := ⟨actor σ k c, (memp c).mpr lineCycle_mem⟩
    have h1 : ModelProof.H.map (vectorAction (dualConjugator k)).toMonoidHom ≤
        ⨆ p : modelParabolic g i,
          (neighboringPlane σ g i).map (vectorAction (dualMark σ p)).toMonoidHom := by
      apply le_iSup_of_le (1 : modelParabolic g i)
      change _ ≤ (neighboringPlane σ g i).map (vectorAction (dualMark σ 1)).toMonoidHom
      rw [map_one, map_action_one, ht]
    have h2 : (ModelProof.H.map (vectorAction d).toMonoidHom).map
        (vectorAction (dualConjugator k)).toMonoidHom ≤
        ⨆ p : modelParabolic g i,
          (neighboringPlane σ g i).map (vectorAction (dualMark σ p)).toMonoidHom := by
      apply le_iSup_of_le p
      change _ ≤ (neighboringPlane σ g i).map
        (vectorAction (dualMark σ (actor σ k c))).toMonoidHom
      rw [ht, dual_map_actor, diagram_c]
    apply top_unique
    have hh' := sup_le h1 h2
    rw [← Subgroup.map_sup, opposite_one,
      Subgroup.map_top_of_surjective (vectorAction (dualConjugator k)).toMonoidHom (vectorAction (dualConjugator k)).surjective] at hh'
    exact hh'
  · rintro ⟨p,hpm⟩
    obtain ⟨x,rfl⟩ := (actor σ k).surjective p
    have hx := (memp x).mp hpm
    obtain ⟨hr,hs',hi,hinc⟩ := standard_neighbors x hx
    let r : modelParabolic g (!i) := ⟨actor σ k d, (memq d).mpr d_mem⟩
    let s : modelParabolic g (!i) := ⟨actor σ k (d^2), (memq (d^2)).mpr (pow_mem d_mem 2)⟩
    refine ⟨r,s,?_,?_,?_,?_⟩
    · change (neighboringPlane σ g i).map (vectorAction (dualMark σ (actor σ k x))).toMonoidHom ≤
        seedLine σ g i ⊔ (seedLine σ g i).map
          (vectorAction (dualMark σ (actor σ k x * actor σ k d))).toMonoidHom
      rw [← map_mul (actor σ k), ht, hs, dual_map_actor, dual_map_actor, ← Subgroup.map_sup]
      exact map_mono hr
    · change (neighboringPlane σ g i).map (vectorAction (dualMark σ (actor σ k x))).toMonoidHom ≤
        seedLine σ g i ⊔ (seedLine σ g i).map
          (vectorAction (dualMark σ (actor σ k x * actor σ k (d^2)))).toMonoidHom
      rw [← map_mul (actor σ k), ht, hs, dual_map_actor, dual_map_actor, ← Subgroup.map_sup]
      exact map_mono hs'
    · change (modelValues σ g i).map
          (vectorAction (σ (actor σ k x * actor σ k d))).toMonoidHom ⊓
        (modelValues σ g i).map
          (vectorAction (σ (actor σ k x * actor σ k (d^2)))).toMonoidHom ≤
        (modelValues σ g (!i)).map (vectorAction (σ (actor σ k x))).toMonoidHom
      rw [← map_mul (actor σ k), ← map_mul (actor σ k), hvp, hvq,
        natural_map_actor, natural_map_actor, natural_map_actor,
        ← Subgroup.map_inf _ _ (vectorAction k).toMonoidHom (vectorAction k).injective]
      exact map_mono hi
    · change (modelValues σ g (!i)).map (vectorAction (σ (actor σ k x))).toMonoidHom ≤ _
      rw [hvp, hvq, natural_map_actor]
      exact map_mono hinc
  · let r : modelParabolic g (!i) := 1
    let s : modelParabolic g (!i) := ⟨actor σ k d, (memq d).mpr d_mem⟩
    let a : modelParabolic g i := ⟨actor σ k c, (memp c).mpr lineCycle_mem⟩
    refine ⟨r,s,a,a,?_,?_,?_⟩
    · change neighboringPlane σ g i ⊔ (neighboringPlane σ g i).map
        (vectorAction (dualMark σ (1 * actor σ k c))).toMonoidHom = ⊤
      rw [one_mul, ht, dual_map_actor, diagram_c, ← Subgroup.map_sup, opposite_one,
        Subgroup.map_top_of_surjective (vectorAction (dualConjugator k)).toMonoidHom (vectorAction (dualConjugator k)).surjective]
    · change neighboringPlane σ g i ⊔ (neighboringPlane σ g i).map
        (vectorAction (dualMark σ (actor σ k d * actor σ k c))).toMonoidHom = ⊤
      rw [← map_mul (actor σ k), ht, dual_map_actor, map_mul, diagram_d, diagram_c,
        ← Subgroup.map_sup, opposite_two,
        Subgroup.map_top_of_surjective (vectorAction (dualConjugator k)).toMonoidHom (vectorAction (dualConjugator k)).surjective]
    · change (modelValues σ g (!i)).map (vectorAction (σ (1 * actor σ k c))).toMonoidHom ⊓
        (modelValues σ g (!i)).map (vectorAction (σ (actor σ k d * actor σ k c))).toMonoidHom = ⊥
      rw [one_mul, ← map_mul (actor σ k), hvq, natural_map_actor, natural_map_actor,
        ← Subgroup.map_inf _ _ (vectorAction k).toMonoidHom (vectorAction k).injective,
        opposite_lines, Subgroup.map_bot]
  · change neighboringPlane σ g i ≤ modelValues (dualMark σ) g (!i)
    rw [values_eq_core, dual_marked, hq, map_graph_conj, pointParabolic_map_diagram,
      core_fixed_conj, lineParabolicSL_pCoreIn_two_eq_R, fixed_lineCore, ht]
  · intro D hD hi
    have hD' : D.map (vectorAction k⁻¹).toMonoidHom ≤ ModelProof.H := by
      have hh := Subgroup.map_mono (f := (vectorAction k⁻¹).toMonoidHom) hD
      rwa [hvp, map_action_cancel'] at hh
    obtain hh|hh := plane_irreducible _ hD' (invariant_pullback k lineParabolicSL D (hp ▸ hi))
    · left
      have hh' := congrArg (fun A : Subgroup Space => A.map (vectorAction k).toMonoidHom) hh
      simpa only [map_action_cancel, Subgroup.map_bot] using hh'
    · right
      have hh' := congrArg (fun A : Subgroup Space => A.map (vectorAction k).toMonoidHom) hh
      simpa only [map_action_cancel, hvp] using hh'

/-- Zero natural fixed space selects the line parabolic. The contragredient
seed, actual neighboring orbit span, and full-core value spaces satisfy the
seven dual pencil conditions, for every common automorphism marking. -/
theorem matrixGeometry_of_no_fixed (σ : MulAut SL) (g : SL) (i : Bool)
    (h : fixedSpace (markedParabolic σ g i) = ⊥) : MatrixGeometry σ g i := by
  obtain ⟨k,⟨hp,hq⟩|⟨hp,hq⟩⟩ := marked_pair σ g i
  · exfalso
    rw [hp, fixedSpace_conj, fixed_point] at h
    have hh : Nat.card (L.map (vectorAction k).toMonoidHom) = 2 := by
      rw [Subgroup.card_map_of_injective (f := (vectorAction k).toMonoidHom)
        (vectorAction k).injective, line_card]
    rw [h, card_bot] at hh
    omega
  · exact geometry_of_line_point σ g i k hp hq

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.RankOnePairing.Incidence.DualGeometry
