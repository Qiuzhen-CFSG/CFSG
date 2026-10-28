module
public import CFSG.Quasithin.ChapterC.Section01.NaturalSixControl.SymplecticSetup.ForwardSpanDerived
/-!
# The core commutator lies in the forward hyperplane kernel

The forward hyperplane kernel T is normal in the starting stabilizer. It
contains Q_alpha intersect Q_c, and the neighboring point-core image has
order at most eight. Hence |Q_alpha:T| is at most eight. The native symmetric-six
small-section theorem makes the component centralize this quotient, giving
[Q_alpha,L_alpha] inside T.

At critical distance four the established span bound then places
[P,[Q_alpha,L_alpha]] in P', the specified central line. These are the
core-action inputs for the terminal central-extension argument. The final
consumer retains the literal SourceData characteristic replacement.

Source: Meierfrankenfeld--Stellmacher (1993), (3.10)(i), printed p.880,
with the native small-section argument applied to the terminal (5.12) span.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped commutatorElement
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
namespace CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup.Source
variable {M : Type*} [Group M] [Finite M] {L R W : Subgroup M} [L.Normal] [W.Normal]
  (s : Source L R W)

omit [Finite M] in
private theorem normalized_comap_normal (J : Subgroup (FreeAmalgam R))
    (hJ : stabilizer R (alpha R)≤normalizer (J:Set (FreeAmalgam R))) :
    (J.comap (embedM R)).Normal := by
  constructor
  intro n hn g
  change embedM R (g*n*g⁻¹)∈J
  rw [map_mul,map_mul,map_inv]
  exact (le_normalizer_iff.mp hJ (embedM R g)
    (by change embedM R g∈stabilizer R (mVertex R 1); rw [stabilizer_m_base]; exact ⟨g,rfl⟩)) _ hn

/-- The component commutator of the starting kernel fixes the forward Baumann slice. -/
theorem core_commutator_le_forward_hyperplane_kernel
    (u : Model.S)
    (hfull : R.map s.projection=Model.E.map (MulAut.conj u).toMonoidHom)
    (hb : 2<s.geometry.b R) {e : Vertex R}
    (p : CriticalPath R s.geometry (alpha R) e) :
    ⁅Q R (alpha R),Ltilde R (alpha R)⁆≤Q R (alpha R)⊓centralizer
      (U R (p.walk.getVert 2)⊓B R (alpha R) (s.geometry.Z_normal _):Set (FreeAmalgam R)) := by
  let T₀ := Q R (alpha R)⊓centralizer
    (U R (p.walk.getVert 2)⊓B R (alpha R) (s.geometry.Z_normal _):Set (FreeAmalgam R))
  have hl := p.length_eq_b
  have hc : color R (p.walk.getVert 2)=false := (p.vertex_color (by omega)).mpr (by decide)
  have hat : Adjacent R (alpha R) (p.walk.getVert 1) := by
    apply (cosetGraph_adj R _ _).mp
    simpa only [SimpleGraph.Walk.getVert_zero] using p.walk.adj_getVert_succ (i:=0) (by omega)
  have hct : Adjacent R (p.walk.getVert 2) (p.walk.getVert 1) :=
    adjacent_symm R ((cosetGraph_adj R _ _).mp (p.walk.adj_getVert_succ (i:=1) (by omega)))
  have ht : color R (p.walk.getVert 1)=true := by
    have hn := adjacent_color_ne R hat
    change false≠color R (p.walk.getVert 1) at hn
    cases hh:color R (p.walk.getVert 1) <;> simp_all
  have hQtG : Q R (p.walk.getVert 1)≤stabilizer R (alpha R) :=
    fun _ hx => hx.2 _ (adjacent_symm R hat)
  let := finite_stabilizer R (alpha R)
  let : Finite (Q R (p.walk.getVert 1)) :=
    Finite.of_injective (inclusion hQtG) (inclusion_injective _)
  let : Finite (Q R (alpha R)) := Finite.of_injective
    (inclusion (Q_le_adjacent_h R ht hat)) (inclusion_injective _)
  have hQT : Q R (alpha R)⊓Q R (p.walk.getVert 2)≤T₀ := by
    apply le_inf inf_le_left
    exact (inf_le_right.trans (le_centralizer_iff.mp
      (commutator_eq_bot_iff_le_centralizer.mp (Z_centralizes_Q R _ hc)))).trans
      (centralizer_le (inf_le_left.trans (DistanceEight.U_le_Z R _)))
  have hpnt : R.map s.projection≤Theory.SpecificGroups.SymmetricSix.BinaryFlags.pointCore.map
      (MulAut.conj u).toMonoidHom := by
    simpa only [Model.pointCore_eq_exceptional] using hfull.le
  have hi : T₀.relIndex (Q R (alpha R))≤8 := by
    calc
      _≤(Q R (alpha R)⊓Q R (p.walk.getVert 2)).relIndex (Q R (alpha R)) :=
        relIndex_le_of_le_left hQT index_ne_zero_of_finite
      _=(Q R (p.walk.getVert 2)).relIndex (Q R (alpha R)) := inf_relIndex_left _ _
      _≤(Q R (p.walk.getVert 2)).relIndex (Q R (p.walk.getVert 1)) :=
        relIndex_le_of_le_right (Q_le_adjacent_h R ht hat) index_ne_zero_of_finite
      _≤8 := s.edge_kernel_index_le_eight u hpnt _ _ hc hct
  let f := embedM R
  let D := (Q R (alpha R)).comap f
  let T := T₀.comap f
  let : D.Normal := normalized_comap_normal _ (Q_normalized R _)
  let : T.Normal := normalized_comap_normal _ (s.moving_hyperplane_kernel_normalized hb rfl hat hct)
  have hDm : D.map f=Q R (alpha R) := map_comap_eq_self
    ((show Q R (alpha R)≤stabilizer R (alpha R) from fun _ hx => hx.1).trans_eq (stabilizer_m_base R))
  have hTm : T.map f=T₀ := map_comap_eq_self
    ((show T₀≤Q R (alpha R) from inf_le_left).trans
      ((show Q R (alpha R)≤stabilizer R (alpha R) from fun _ hx => hx.1).trans_eq (stabilizer_m_base R)))
  have hD : D≤s.projection.ker := by
    rw [s.projection_kernel]
    apply (map_le_map_iff_of_injective (embedM_injective R)).mp
    rw [hDm,←Q_alpha R s.two_group s.core_le]
  have hp : IsPGroup 2 s.projection.ker := by
    rw [s.projection_kernel]
    exact pCore_isPGroup
  have hi₀ : T.relIndex D≤8 := by
    rw [relIndex_comap,hDm]
    exact hi
  have hh := map_mono (f:=f) (commutator_pResidual_le_of_symmetricSix_small_section s.projection
    (s.projection_surjective_of_radical_image_le_conjugate u hfull.le) hp D T hD hi₀)
  rw [map_commutator,hDm,hTm,←Ltilde_alpha] at hh
  exact hh
/-- On the terminal span, the core commutator acts only through the derived line. -/
theorem forward_span_core_commutator_le_derived
    (h : NativeCentralLayer s) (u : Model.S)
    (hfull : R.map s.projection=Model.E.map (MulAut.conj u).toMonoidHom)
    (hb : s.geometry.b R=4) {e : Vertex R}
    (p : CriticalPath R s.geometry (alpha R) e) :
    let P := localZSpan R (p.walk.getVert 2) (alpha R)
    ⁅P,⁅Q R (alpha R),Ltilde R (alpha R)⁆⁆≤⁅P,P⁆ := by
  have hi := s.forward_moving_index_eq_two_of_distance_four h u hfull hb p
  have hs := s.critical_forward_span_commutator_le_line_of_two_lt h u hfull (by omega) p hi.le
  exact ((commutator_mono le_rfl (s.core_commutator_le_forward_hyperplane_kernel u hfull
    (by omega) p)).trans hs.2).trans_eq (s.forward_span_derived_eq_line h u hfull hb p).1.symm
end CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup.Source

namespace CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup.SourceData
variable {K : Type*} [Group K] [Finite K] {L W : Subgroup K} [L.Normal] [W.Normal]
  {T : Sylow 2 K} (d : NaturalSixControl.SourceData L W T) (hm : IntrinsicMSPair d)
local notation "J" => (L⊔d.B : Subgroup K)
local notation "R" => d.B.subgroupOf J

/-- The actual replacement supplies the terminal core-action bound. -/
theorem reducedSource_block_or_forward_span_core_commutator_le_derived
    (r : CharacteristicReduction (L.subgroupOf J) R) {e : Vertex r.radical}
    (p : CriticalPath r.radical ((originalSource d hm).reduce r).geometry (alpha r.radical) e)
    (hb : ((originalSource d hm).reduce r).geometry.b r.radical=4) :
    IsAlternatingBlock L 6 ∨
      (let P := localZSpan r.radical (p.walk.getVert 2) (alpha r.radical)
       ⁅P,⁅Q r.radical (alpha r.radical),Ltilde r.radical (alpha r.radical)⁆⁆≤⁅P,P⁆) := by
  rcases reducedSource_block_or_full_point_image d hm r with hblock|hfull
  · exact Or.inl hblock
  · right
    let s := (originalSource d hm).reduce r
    have hf : r.radical.map s.projection=Model.E.map (MulAut.conj d.relabeler.val⁻¹).toMonoidHom := by
      simpa only [Model.pointCore_eq_exceptional] using hfull
    exact s.forward_span_core_commutator_le_derived (reduced_nativeCentralLayer d hm r) _ hf hb p
end CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup.SourceData
