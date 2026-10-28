module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.PairedRadiusOriginalFixedPaths
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.TerminalIndices

/-!
# The actual paired source sequence excludes distance eight

Second-seed insertion applied to the reversed literal critical path places
its full critical commutator in the seed six edges from its start when b=8.
The same preceding-center contradiction as at distance six then applies:
full triple-seed centrality and the retained actual transporter force the
commutator into its own vertex center, contrary to its exact central index.
The shifted paired terminal alternative supplies that preceding centrality.

All endpoints remain the actual paired critical endpoints. The separate
fixed-endpoint notation printed on MS93 p.924 is not identified with them.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
open Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
open CFSG.Quasithin.ChapterC.Sp4Four.DistanceReduction
open CFSG.Quasithin.ChapterC.Sp4Four.DistanceReduction.LargeDistance
open CFSG.Quasithin.ChapterC.Sp4Four.SourceComparison
namespace CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic

private theorem fixed_seed_le_neighbor_seed
    {M : Type*} [Group M] [Finite M] {R : Subgroup M}
    (geometry : Geometry R) (hb : 0 < geometry.b R)
    {a t c : Vertex R} (ha : color R a=false) (hc : color R c=false)
    (hat : Adjacent R a t) (hct : Adjacent R c t)
    (D : Subgroup (FreeAmalgam R)) (hDZ : D ≤ Z R a)
    (hDC : D ≤ centralizer (stabilizer R a : Set (FreeAmalgam R))) :
    D ≤ Z R c := by
  have ht : color R t=true := by
    have hh := adjacent_color_ne R hat
    rw [ha] at hh
    cases ht : color R t <;> simp_all
  have hZX := geometry.omega_bound a ha (by rw [geometry.distance_constant a ha]; exact hb)
  apply le_trans _ (adjacent_Z_le R hc hct)
  intro x hx
  rw [Z,if_neg (by rw [ht]; decide)]
  obtain ⟨hxQ,hx2,_⟩ := mem_omegaCenter_iff.mp (hZX (hDZ hx))
  exact mem_omegaCenter_iff.mpr ⟨Q_le_adjacent_h R ht hat hxQ,hx2,
    fun y hy => hDC hx y (hy.2 a (adjacent_symm R hat))⟩

variable {H F : Type*} [Group H] [Finite H] [Field F] [Finite F] [CharP F 2]
variable {K R : Subgroup H} {n : ℕ} (h : Input K R n F)
variable (d : CharacteristicReduction K R)
include h

private theorem preceding_noncentral_of_eight
    {geometry : Geometry d.radical} (hb : geometry.b d.radical=8)
    (s : ℕ → CriticalSegment geometry)
    (hs : ∀ i, BackwardLink geometry (pairedRadiusChoice geometry (Nat.card F)) (s i) (s (i+1)))
    (hover : ∀ i k j, j+2*k ≤ geometry.b d.radical →
      (s (i+k)).path.walk.getVert (j+2*k)=(s i).path.walk.getVert j)
    (htriple : ∀ i, (Z d.radical (s i).first ⊓ Z d.radical (s (i+1)).first) ⊓
      Z d.radical (s (i+2)).first ≤ centralizer
        (stabilizer d.radical (s (i+1)).first : Set (FreeAmalgam d.radical))) (k : ℕ) :
    ¬ ⁅Z d.radical (s (k+3)).first,Z d.radical (s (k+3)).last⁆ ≤
      centralizer (stabilizer d.radical (s (k+2)).first : Set (FreeAmalgam d.radical)) := by
  intro hcent
  let D := ⁅Z d.radical (s (k+3)).first,Z d.radical (s (k+3)).last⁆
  have hb4 : 4 < geometry.b d.radical := by omega
  have hprev : (s (k+3)).path.walk.getVert 2=(s (k+2)).first := by
    have hh := (hs (k+2)).overlap 0 (by omega)
    simpa only [Nat.add_assoc,show 2+1=3 from rfl,Nat.zero_add,
      SimpleGraph.Walk.getVert_zero] using hh
  have hDprev : D ≤ Z d.radical (s (k+2)).first := by
    have hh := h.replacement_critical_commutator_le_second_seed_of_four_lt d (s (k+3)).path hb4
    rwa [hprev] at hh
  obtain ⟨t,hchoice,hat,hct,hfirst⟩ := (hs (k+1)).choice
  have hDnext : D ≤ Z d.radical (s (k+1)).first :=
    fixed_seed_le_neighbor_seed geometry (by omega) (s (k+2)).path.start_color
      (s (k+1)).path.start_color (by simpa only [Nat.add_assoc,show 1+1=2 from rfl] using hct)
      hat D hDprev hcent
  have hDfar : D ≤ Z d.radical (s k).first := by
    let path := (s (k+3)).path
    let rev : CriticalPath d.radical geometry (s (k+3)).last (s (k+3)).first :=
      { start_color := path.end_color
        walk := path.walk.reverse
        shortest := by rw [SimpleGraph.Walk.length_reverse,path.shortest,SimpleGraph.dist_comm]
        critical := critical_reverse d.radical geometry
          (MSCentralOrbit.edgeCentralizerCondition d.radical (h.replacement_two_group d)
            (h.replacement_core_le d) (h.replacement_omegaOrbit_centralizer d))
          (s (k+3)).first path.start_color (by
            rw [geometry.distance_constant _ path.start_color]
            exact (by omega : 0 < geometry.b d.radical))
          (s (k+3)).last path.end_color path.critical }
    have hh := h.replacement_critical_commutator_le_second_seed_of_four_lt d rev hb4
    change ⁅Z d.radical (s (k+3)).last,Z d.radical (s (k+3)).first⁆ ≤
      Z d.radical (path.walk.reverse.getVert 2) at hh
    rw [commutator_comm,SimpleGraph.Walk.getVert_reverse,path.length_eq_b,hb] at hh
    have hov := hover k 3 0 (by omega)
    simp only [Nat.zero_add,SimpleGraph.Walk.getVert_zero] at hov
    simpa only [path,show 8-2=2*3 from rfl,hov] using hh
  have hDnextC : D ≤ centralizer (stabilizer d.radical (s (k+1)).first : Set (FreeAmalgam d.radical)) :=
    (le_inf (le_inf hDfar hDnext) hDprev).trans (htriple k)
  obtain ⟨w,hpair,_,_,_⟩ := (hs (k+2)).choice
  obtain ⟨g,hg,hgu,hgw,hindex⟩ := hpair.1
  have hmiddle : (s (k+2)).path.walk.getVert 2=(s (k+1)).first := by
    have hh := (hs (k+1)).overlap 0 (by omega)
    simpa only [Nat.add_assoc,show 1+1=2 from rfl,Nat.zero_add,
      SimpleGraph.Walk.getVert_zero] using hh
  have hact : act d.radical g (s (k+1)).first=(s (k+3)).first := by
    simpa only [Nat.add_assoc,show 2+1=3 from rfl,hmiddle] using hgu.symm
  have hgS := Ltilde_le_stabilizer (s (k+2)).first hg
  have hDmap : D.map (MulAut.conj g⁻¹).toMonoidHom=D :=
    mem_normalizer_iff_map_conj_eq.mp (Subgroup.centralizer_le_normalizer _
      (le_centralizer_iff.mp hcent ((stabilizer d.radical (s (k+2)).first).inv_mem hgS)))
  have hDself : D ≤ centralizer (stabilizer d.radical (s (k+3)).first : Set (FreeAmalgam d.radical)) := by
    have hh := (map_mono (f := (MulAut.conj g⁻¹).toMonoidHom) hDnextC).trans
      (map_centralizer_le_centralizer_image _ _)
    change D.map (MulAut.conj g⁻¹).toMonoidHom ≤ centralizer
      ((stabilizer d.radical (s (k+1)).first).map (MulAut.conj g⁻¹).toMonoidHom : Set _) at hh
    rwa [hDmap,←stabilizer_act,hact] at hh
  have hDS : D ≤ stabilizer d.radical (s (k+3)).first :=
    (critical_commutator_le_start_seed (s (k+3)).path).trans (Z_le_stabilizer _ _)
  have hi := h.replacement_critical_commutator_central_index d (s (k+3)).path hb4.le
  rw [relIndex_eq_one.mpr (le_inf hDS hDself)] at hi
  have hlo := (h.replacement_critical_indices_ge_field d (s (k+3)).path (by omega)).1
  have hq : 1 < Nat.card F := Finite.one_lt_card
  omega

/-- The actual minimum replacement graph cannot have critical distance
eight. The paired paths and their complete fixed comparisons are constructed
from the original input; no path-selection premise is required. -/
theorem Input.replacement_distance_ne_eight (geometry : Geometry d.radical) :
    geometry.b d.radical ≠ 8 := by
  intro hb
  have hb4 : 4 < geometry.b d.radical := by omega
  obtain ⟨z,hz⟩ := criticalPair_exists d.radical (alpha d.radical)
    (geometry.exists_critical (alpha d.radical) rfl)
  let p : CriticalSegment geometry :=
    ⟨alpha d.radical,z,CriticalPath.ofPair rfl hz⟩
  obtain ⟨s,_,_,hs,hover,_,htriple⟩ :=
    h.replacement_paired_radius_original_fixed_paths d p hb4
  have htwo (i : ℕ) : (s (i+1)).path.walk.getVert 2=(s i).first := by
    simpa only [Nat.zero_add,SimpleGraph.Walk.getVert_zero] using
      (hs i).overlap 0 (by omega)
  have hprev (i : ℕ) :
      ⁅Z d.radical (s (i+1)).first,Z d.radical (s (i+1)).last⁆ ≤
        Z d.radical (s i).first := by
    have hh := h.replacement_critical_commutator_le_second_seed_of_four_lt d
      (s (i+1)).path hb4
    rwa [htwo i] at hh
  have halt := h.replacement_paired_radius_terminal_seed_alternative d hb4
    (fun i => s (i+1)) (fun i => hs (i+1))
  rcases halt with hleft | hright
  · exact preceding_noncentral_of_eight h d hb s hs hover htriple 0
      ((le_inf (le_inf hleft (hprev 2))
        (critical_commutator_le_start_seed (s 3).path)).trans (htriple 1))
  · exact preceding_noncentral_of_eight h d hb s hs hover htriple 1
      ((le_inf (le_inf hright (hprev 3))
        (critical_commutator_le_start_seed (s 4).path)).trans (htriple 2))

end CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
