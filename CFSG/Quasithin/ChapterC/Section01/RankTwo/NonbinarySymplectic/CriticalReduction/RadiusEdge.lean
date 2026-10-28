module
public import CFSG.Quasithin.ChapterC.Section01.NaturalSixControl.SymplecticSetup.EdgeCentrality

/-!
# Radius centrality from the actual residual alternative

Each incident edge radius normally generates the original-vertex radius.
The literal residual and edge group generate the ambient group, so the
fixed branch of the residual alternative makes the kernel commutator
central. In the covering branch, nilpotent saturation puts the whole
radius in the abelian edge radius and again proves centrality.

This extracts only the graph and generation argument of the existing
symplectic setup; it uses no symmetric-six model assumption. `RadiusChief`
discharges its alternative on the nonbinary characteristic replacement.
Source: Meierfrankenfeld--Stellmacher (1993), (5.2)(ii), pp.914--915.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.NaturalStructure.Exclusion
open CFSG.Quasithin.ChapterC.NaturalSixControl
open CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup
open CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup.Source
namespace CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic.RadiusEdge
variable {M : Type*} [Group M] {R : Subgroup M}

private theorem adjacent_seed_le_radius {a t : Vertex R} (hat : Adjacent R a t) :
    Z R a ≤ V R t := by
  apply le_iSup_of_le a
  exact le_iSup_of_le
    (show (cosetGraph R).dist a t ≤ 2 from
      (SimpleGraph.dist_eq_one_iff_adj.mpr ((cosetGraph_adj R _ _).mpr hat)).le.trans (by decide)) le_rfl

private theorem map_comap_of_le_base (N : Subgroup (FreeAmalgam R))
    (hN : N ≤ stabilizer R (alpha R)) : (N.comap (embedM R)).map (embedM R) = N := by
  rw [map_comap_eq]
  apply inf_eq_right.mpr
  change N ≤ stabilizer R (mVertex R 1) at hN
  rwa [stabilizer_m_base] at hN

private theorem base_normalizes_image (N : Subgroup M) [N.Normal] :
    stabilizer R (alpha R) ≤ normalizer (N.map (embedM R) : Set (FreeAmalgam R)) := by
  rw [show alpha R = mVertex R 1 from rfl, stabilizer_m_base]
  change (embedM R).range ≤ _
  rw [MonoidHom.range_eq_map]
  simpa only [normalizer_eq_top] using N.le_normalizer_map (embedM R)

variable [Finite M] (geometry : Geometry R)
  (htwo : IsPGroup 2 R) (hcore : pCore 2 M ≤ R)
  (hgen : pResidual 2 M ⊔ R = ⊤)

omit [Finite M] in
private theorem radius_comap_map (hb : 2 < geometry.b R) :
    ((V R (alpha R)).comap (embedM R)).map (embedM R) = V R (alpha R) :=
  map_comap_of_le_base _ (geometry.V_local _ rfl hb)

omit [Finite M] in
private theorem edge_radius_comap_map (hb : 2 < geometry.b R) :
    ((V R (beta R)).comap (embedM R)).map (embedM R) = V R (beta R) :=
  map_comap_of_le_base _ ((edge_radius_le_radius rfl (base_adjacent R)).trans
    (geometry.V_local _ rfl hb))

/-- Normal generation in the literal original group M, through embedM. -/
private theorem radius_comap_eq_normalClosure_edge (hb : 2 < geometry.b R) :
    (V R (alpha R)).comap (embedM R) =
      normalClosure ((V R (beta R)).comap (embedM R) : Set M) := by
  let V₀ := (V R (alpha R)).comap (embedM R)
  let E := (V R (beta R)).comap (embedM R)
  let := radius_comap_normal (R := R)
  apply le_antisymm
  · have hV : V R (alpha R) ≤ (normalClosure (E : Set M)).map (embedM R) := by
      apply radius_le_of_normalized_edge rfl (base_adjacent R)
      · change V R (beta R) ≤ _
        rw [←edge_radius_comap_map geometry hb]
        exact map_mono le_normalClosure
      · exact base_normalizes_image _
    have h := comap_mono (f := embedM R) hV
    rwa [comap_map_eq_self_of_injective (embedM_injective R)] at h
  · apply normalClosure_le_normal
    exact comap_mono (f := embedM R) (edge_radius_le_radius rfl (base_adjacent R))

include hgen in
/-- The actual source generation M=L R supplies the edge-plus-moving cover. -/
private theorem radius_comap_le_edge_sup_commutator (hb : 2 < geometry.b R) :
    (V R (alpha R)).comap (embedM R) ≤
      (V R (beta R)).comap (embedM R) ⊔ ⁅(V R (alpha R)).comap (embedM R), (pResidual 2 M)⁆ := by
  let V₀ := (V R (alpha R)).comap (embedM R)
  let E := (V R (beta R)).comap (embedM R)
  let := radius_comap_normal (R := R)
  have hEV : E ≤ V₀ := comap_mono (f := embedM R)
    (edge_radius_le_radius rfl (base_adjacent R))
  let D := E ⊔ ⁅V₀,pResidual 2 M⁆
  let : D.Normal := by
    apply normalizer_eq_top_iff.mp
    apply top_unique
    rw [←hgen]
    apply sup_le
    · exact le_normalizer_sup_of_commutator_le V₀ (pResidual 2 M) E ⁅V₀,pResidual 2 M⁆ hEV le_rfl
    · exact (le_inf (radical_normalizes_edge_radius_comap (R := R)) le_normalizer_of_normal).trans
        (normalizer_inf_normalizer_le_normalizer_sup E ⁅V₀,pResidual 2 M⁆)
  calc
    V₀ = normalClosure (E : Set M) := radius_comap_eq_normalClosure_edge geometry hb
    _ ≤ D := normalClosure_le_normal (show E ≤ D from le_sup_left)


include htwo hcore hgen

/-- The source residual dichotomy forces centrality of the actual radius
commutator. All normality and edge-generation hypotheses are proved from the graph and the residual generation. -/
private theorem radius_commutator_central_of_residual_dichotomy (hb : 2 < geometry.b R)
    (hd : ⁅⁅V R (alpha R), Q R (alpha R)⁆, Ltilde R (alpha R)⁆ ≤ Z R (alpha R) ∨
      ⁅V R (alpha R), Ltilde R (alpha R)⁆ ≤ ⁅V R (alpha R), Q R (alpha R)⁆ ⊔ Z R (alpha R)) :
    ⁅V R (alpha R), Q R (alpha R)⁆ ≤ centralizer (V R (alpha R) : Set (FreeAmalgam R)) := by
  let f := embedM R
  let V₀ := (V R (alpha R)).comap f
  let E := (V R (beta R)).comap f
  let Z₀ := (Z R (alpha R)).comap f
  let P := pCore 2 M
  let := radius_comap_normal (R := R)
  let := SymplecticSeed.Z_comap_normal R
  have hVm : V₀.map f = V R (alpha R) := radius_comap_map geometry hb
  have hEm : E.map f = V R (beta R) := edge_radius_comap_map geometry hb
  have hZm : Z₀.map f = Z R (alpha R) := map_comap_of_le_base _
    ((Z_le_VBall R (alpha R) 2).trans (geometry.V_local _ rfl hb))
  have hPm : P.map f = Q R (alpha R) := (Q_alpha R htwo hcore).symm
  have hLm : (pResidual 2 M).map f = Ltilde R (alpha R) := by rw [Ltilde_alpha]
  have hVP : V₀ ≤ P := by
    have h := comap_mono (f := f) (geometry.V_le_Q hb (alpha R) rfl)
    rwa [Q_alpha_comap R htwo hcore] at h
  have hEV : E ≤ V₀ := comap_mono (f := f)
    (edge_radius_le_radius rfl (base_adjacent R))
  have hZE : Z₀ ≤ E := comap_mono (f := f) (adjacent_seed_le_radius (base_adjacent R))
  have hE : E ≤ centralizer (E : Set M) := by
    have hc := le_centralizer_iff_isMulCommutative.mpr
      (edge_radius_commutative geometry hb (alpha R) (beta R) rfl (base_adjacent R))
    intro x hx y hy
    apply embedM_injective R
    simpa only [map_mul] using hc hx (f y) hy
  have hcentral : ⁅V₀,P⁆ ≤ centralizer (V₀ : Set M) := by
    rcases hd with hd | hd
    · have hfixed : ⁅⁅V₀,P⁆,pResidual 2 M⁆ ≤ Z₀ := by
        apply (map_le_map_iff_of_injective (embedM_injective R)).mp
        rwa [map_commutator,map_commutator,hVm,hPm,hLm,hZm]
      exact edge_commutator_central_of_residual_fixed V₀ P E Z₀ (pResidual 2 M) R
        (radius_comap_eq_normalClosure_edge geometry hb) hEV hZE
        (radical_normalizes_edge_radius_comap (R := R)) hcore hgen hE hfixed
    · have hcover : ⁅V₀,pResidual 2 M⁆ ≤ E ⊔ ⁅V₀,P⁆ := by
        have hc : ⁅V₀,pResidual 2 M⁆ ≤ ⁅V₀,P⁆ ⊔ Z₀ := by
          apply (map_le_map_iff_of_injective (embedM_injective R)).mp
          rwa [map_commutator,Subgroup.map_sup,map_commutator,hVm,hPm,hLm,hZm]
        exact hc.trans (sup_le le_sup_right (hZE.trans le_sup_left))
      exact edge_commutator_central_of_residual_cover V₀ P E (pResidual 2 M) hVP (hEV.trans hVP)
        (pCore_isPGroup (p := 2) (G := M)).isNilpotent
        (hcore.trans (radical_normalizes_edge_radius_comap (R := R))) hE
        (radius_comap_le_edge_sup_commutator geometry hgen hb) hcover
  rw [←hVm,←hPm,←map_commutator]
  exact (map_mono hcentral).trans (map_centralizer_le_centralizer_image (V₀ : Set M) f)


/-- Direct input from the chief-budget theorem in M: the only preimages are
through the specified embedM, and both the residual and kernel are literal. -/
theorem radius_commutator_central_of_preimage_dichotomy (hb : 2 < geometry.b R)
    (hd : ⁅⁅(V R (alpha R)).comap (embedM R), pCore 2 M⁆, pResidual 2 M⁆ ≤
        (Z R (alpha R)).comap (embedM R) ∨
      ⁅(V R (alpha R)).comap (embedM R), pResidual 2 M⁆ ≤
        ⁅(V R (alpha R)).comap (embedM R), pCore 2 M⁆ ⊔
          (Z R (alpha R)).comap (embedM R)) :
    ⁅V R (alpha R), Q R (alpha R)⁆ ≤ centralizer (V R (alpha R) : Set (FreeAmalgam R)) := by
  apply radius_commutator_central_of_residual_dichotomy geometry htwo hcore hgen hb
  have hZ := map_comap_of_le_base (Z R (alpha R))
    ((Z_le_VBall R (alpha R) 2).trans (geometry.V_local _ rfl hb))
  rcases hd with hd | hd
  · left
    have hm := map_mono (f := embedM R) hd
    rwa [map_commutator,map_commutator,radius_comap_map geometry hb,
      ←Q_alpha R htwo hcore,←Ltilde_alpha,hZ] at hm
  · right
    have hm := map_mono (f := embedM R) hd
    rwa [map_commutator,Subgroup.map_sup,map_commutator,radius_comap_map geometry hb,
      ←Q_alpha R htwo hcore,←Ltilde_alpha,hZ] at hm


end CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic.RadiusEdge
