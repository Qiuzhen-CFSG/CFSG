module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Sp4Four.OuterReduction.SeedTransport
/-!
# Abelianness of the original star from its core radius

Every transported fixed seed lies in the central Z-layer of its own vertex.
If the entire star lies in every core in the two-edge neighborhood, all of
those generators commute with the star. The central omega attachment does
as well. The actual full-Sylow radius theorem supplies these core bounds
when the critical distance is at least four.

Source: MS93 (3.4), printed p.868. The distance-two boundary remains separate;
this module does not assert the full source star bound.
-/

@[expose] public noncomputable section
open Subgroup Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterC.RankTwo.Sp4Four
variable {M : Type*} [Group M] [Finite M] (R : Subgroup M)

theorem sourceStarAlpha_commutative_of_radius_core_bounds
    (geometry : Geometry R) (hb : 0 < geometry.b R)
    (Y : Subgroup R) (hY : Y.map (embedS R) ≤ U R (alpha R))
    (hradius : ∀ d : Vertex R, color R d = false →
      (cosetGraph R).dist (alpha R) d ≤ 2 → sourceStarAlpha R Y ≤ Q R d) :
    IsMulCommutative (sourceStarAlpha R Y) := by
  have hbeta : (starSpan R Y).map (embedS R) =
      (⨆ h : Hbar R, (Y.map (embedS R)).map (MulAut.conj (h : FreeAmalgam R)).toMonoidHom) ⊔
        Z R (beta R) := by
    simpa only [map_map,embedM_comp_subtype] using starSpan_map_graph R Y
  have hZ (d : Vertex R) (hd : color R d = false) :
      Z R d ≤ centralizer (Q R d : Set (FreeAmalgam R)) := by
    apply (geometry.omega_bound d hd (by rwa [geometry.distance_constant d hd])).trans
    exact le_centralizer_iff.mp (Q_le_centralizer_X R d)
  apply le_centralizer_iff_isMulCommutative.mp
  apply (sourceStarAlpha_le_iff R Y _).mpr
  intro g
  rw [hbeta,Subgroup.map_sup,Subgroup.map_iSup]
  apply sup_le
  · apply iSup_le
    intro h
    obtain ⟨hat,hdt⟩ := transported_seed_edges R g h
    let d := act R (g : FreeAmalgam R)⁻¹ (act R (h : FreeAmalgam R)⁻¹ (alpha R))
    let t := act R (g : FreeAmalgam R)⁻¹ (beta R)
    have hd : color R d=false := by simp only [d,action_preserves_color]; rfl
    have hdist : (cosetGraph R).dist (alpha R) d ≤ 2 := by
      have ha1 := SimpleGraph.dist_eq_one_iff_adj.mpr ((cosetGraph_adj R _ _).mpr hat)
      have hd1 := SimpleGraph.dist_eq_one_iff_adj.mpr ((cosetGraph_adj R _ _).mpr hdt)
      have htri := (cosetGraph_connected R).dist_triangle (u := alpha R) (v := t) (w := d)
      have htd : (cosetGraph R).dist t d=1 := by rwa [SimpleGraph.dist_comm]
      change (cosetGraph R).dist (alpha R) t=1 at ha1
      omega
    exact ((transported_seed_le_U R Y hY g h).trans (U_le_Z d)).trans
      ((hZ d hd).trans (centralizer_le (hradius d hd hdist)))
  · have hg : (g : FreeAmalgam R) ∈ stabilizer R (alpha R) := by
      simpa only [alpha,stabilizer_m_base] using g.property
    have hfix := mem_normalizer_iff_map_conj_eq.mp (Z_normalized R (alpha R) hg)
    have hba : Z R (beta R) ≤ Z R (alpha R) := by
      change edgeOmega R (beta R) ≤ ⨆ b, ⨆ (_ : Adjacent R (alpha R) b), edgeOmega R b
      exact le_iSup_of_le (beta R) (le_iSup_of_le (base_adjacent R) le_rfl)
    exact ((map_mono hba).trans_eq hfix).trans
      ((hZ (alpha R) rfl).trans (centralizer_le (hradius (alpha R) rfl (by simp))))

end CFSG.Quasithin.ChapterC.RankTwo.Sp4Four

open Theory.GroupTheory CFSG.Quasithin.ChapterC
namespace CFSG.Quasithin.ChapterC.RankTwo.Sp4Four
open MSCentralOrbit
variable {H J : Type*} [Group H] [Finite H] [Group J] [Finite J]

theorem original_sourceStarAlpha_commutative_of_four_le
    (R : Subgroup H) (hms : MSCharacteristicCondition R)
    (hp : IsPGroup 2 R) (hne : R ≠ ⊥) (hQR : pCore 2 H ≤ R)
    (hself : centralizer (pCore 2 H : Set H) ≤ pCore 2 H)
    (hfaith : centralizer (omegaOrbit R : Set H) = pCore 2 H)
    (q : H →* J) (hq : Function.Surjective q) (hcore : q.ker = pCore 2 H)
    [((pResidual 2 H).map q).Normal]
    [IsSimpleGroup ((pResidual 2 H).map q)] [IsQuasisimple ((pResidual 2 H).map q)]
    (hc : Nat.card ((pResidual 2 H).map q) = 979200)
    (hC : centralizer ((pResidual 2 H).map q : Set J) = ⊥)
    (hsq : IsSQTK KnownSimple.IsKnownSimple ((pResidual 2 H).map q))
    (geometry : Geometry R) (hfour : 4 ≤ geometry.b R)
    (Y : Subgroup R) (P : Sylow 2 (Ltilde R (alpha R)))
    (hY : Y.map (embedS R)=componentSylowSeed R (alpha R) P)
    (hn : Q R (beta R) ≤ normalizer (Y.map (embedS R) : Set (FreeAmalgam R))) :
    IsMulCommutative (sourceStarAlpha R Y) := by
  apply sourceStarAlpha_commutative_of_radius_core_bounds R geometry (by omega) Y
    (hY.le.trans inf_le_left)
  intro d hd hdist
  exact original_sourceStarAlpha_le_distant_core R hms hp hne hQR hself hfaith
    q hq hcore hc hC hsq geometry (by omega) Y P hY hn hd (by omega)

end CFSG.Quasithin.ChapterC.RankTwo.Sp4Four
