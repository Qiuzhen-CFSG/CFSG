module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.DistanceFourRootSpanImage
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.DistanceFourSpanAction
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.DistanceFourFixedIndices
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.DistanceFourRootLayers
public import Theory.Representation.BinaryConjugationSection.FiniteOffenderIndex
import all CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.TrappedTransport
import all CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.DistanceFourNormalSpans

/-!
# The literal endpoint offender on its midpoint span quotient

Keep a distance-four critical path a--e--z whose endpoints are related by
the specified element g of G_e. Such a mark is retained by the actual
second backward selector; arbitrary critical paths need not have it.
The two literal B-moving budgets concern U_e at a and U_z at e.

For W = <Z_e^{G_a}> and C = W intersect Q_e, the terminal budget identifies
U_z intersect Q_a with U_z intersect B_e. Its commutator with C lies in
Z_e intersect D_a intersect D_e. It is therefore fixed at e and a, and
the same g transports fixedness to z. The full natural-cover theorem
kills this commutator. The root intersection theorem retains the entire
fixed attachment and gives [C,Z_z] <= Z_a.

The first budget bounds |W:C| by q. The actual endpoint image Z_z Q_a/Q_a
has order q, hence is an offender on the faithfully constructed literal
quotient W/(W intersect B_a). Its field, full kernel and coordinates are
all retained. No offender, fixed-space or image-bound callback is assumed.
Source: the final FF argument of MS93 (5.12), printed p.927, with the
coherent endpoint orbit supplied by the transition on printed p.925.
The internal imports reuse only the terminal twist intersection algebra
and transport of the literal fixed-radius premise.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open Theory.SpecificGroups.SymplecticFour
open scoped IsMulCommutative commutatorElement
open Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
open CFSG.Quasithin.ChapterC.Sp4Four.SourceComparison
open CFSG.Quasithin.ChapterC.RankTwo.Sp4Four
open CFSG.Quasithin.ChapterC.RankTwo.Sp4Four.SourceComparison
namespace CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
open ChapterB.QuasisimpleSource
variable {H F : Type*} [Group H] [Finite H] [Field F] [Finite F] [CharP F 2]
variable {K R : Subgroup H} {n : ℕ} (h : Input K R n F)
variable (d : CharacteristicReduction K R)
include h

private theorem terminal_moving_kernel_eq_B
    {geometry : Geometry d.radical} {a z : Vertex d.radical}
    (path : CriticalPath d.radical geometry a z) (hb : geometry.b d.radical=4)
    (hi : (B d.radical (path.walk.getVert 2) (geometry.Z_normal _)).relIndex
      (U d.radical z) ≤ Nat.card F) :
    U d.radical z ⊓ Q d.radical a =
      U d.radical z ⊓ B d.radical (path.walk.getVert 2) (geometry.Z_normal _) := by
  obtain ⟨x,hx,ht,_⟩ := h.replacement_terminal_edge_residual_twist d path (by omega)
  have hsub := terminal_B_intersection_le_kernel path (by omega) x hx ht
  rw [path.length_eq_b,hb] at hsub
  change U d.radical z ⊓ B d.radical (path.walk.getVert 2) (geometry.Z_normal _) ≤
    Q d.radical a at hsub
  let := finite_Z d.radical z
  let : Finite (U d.radical z) :=
    Finite.of_injective (inclusion (U_le_Z z)) (inclusion_injective _)
  have hupper := relIndex_le_of_le_left hsub (L := U d.radical z) index_ne_zero_of_finite
  rw [inf_relIndex_left] at hupper
  have hAS : Z d.radical a ≤ stabilizer d.radical z :=
    Z_le_stabilizer_of_dist_le a (geometry.exists_critical a path.start_color) path.critical.1.le
  have hlo := h.replacement_natural_fixed_index_lower d geometry (by omega) path.end_color
    (Z d.radical a) hAS path.critical.2
  have hUS : U d.radical z ≤ stabilizer d.radical a :=
    (U_le_Z z).trans (path.endpoint_Z_le_start_stabilizer (by omega))
  have hCa := MSCentralOrbit.C_eq_Q d.radical (h.replacement_two_group d)
    (h.replacement_core_le d) (h.replacement_omegaOrbit_centralizer d) a path.start_color
  have hfix : U d.radical z ⊓ centralizer (Z d.radical a : Set (FreeAmalgam d.radical)) =
      U d.radical z ⊓ Q d.radical a := by
    rw [←hCa]
    ext r
    exact ⟨fun hr => ⟨hr.1,hUS hr.1,hr.2⟩,fun hr => ⟨hr.1,hr.2.2⟩⟩
  have hindex : (centralizer (Z d.radical a : Set (FreeAmalgam d.radical))).relIndex
      (U d.radical z)=(Q d.radical a).relIndex (U d.radical z) := by
    rw [←inf_relIndex_left,hfix,inf_relIndex_left]
  rw [hindex] at hlo
  have hq : (Q d.radical a).relIndex (U d.radical z)=Nat.card F :=
    le_antisymm (hupper.trans hi) hlo
  exact inf_eq_of_relIndex_bounds (U d.radical z)
    (B d.radical (path.walk.getVert 2) (geometry.Z_normal _))
    (Q d.radical a) hsub (Nat.card F) hq hi

private theorem inner_stabilizer_eq
    (geometry : Geometry d.radical) (hb : 4 ≤ geometry.b d.radical)
    {a : Vertex d.radical} (ha : color d.radical a=false) :
    Ltilde d.radical a ⊔ Q d.radical a=stabilizer d.radical a := by
  obtain ⟨i,hi,hir,hiL,hiU,hiQ⟩ := vertex_coordinates_with_kernel d.radical
    (h.replacement_two_group d) (h.replacement_core_le d) ha
  rw [←hiL,←hiQ,←Subgroup.map_sup,h.replacement_residual d,
    h.replacement_inner_of_four_le d geometry hb,←MonoidHom.range_eq_map,hir]

private theorem span_kernel_fixes_full_root_intersection
    {geometry : Geometry d.radical} {a z : Vertex d.radical}
    (path : CriticalPath d.radical geometry a z) (hb : geometry.b d.radical=4)
    (g : FreeAmalgam d.radical) (hg : g ∈ stabilizer d.radical (path.walk.getVert 2))
    (hga : act d.radical g a=z)
    (hfixed : ⁅V d.radical a,Q d.radical a⁆ ≤ fixedCore d.radical a)
    (hi : (B d.radical (path.walk.getVert 2) (geometry.Z_normal _)).relIndex
      (U d.radical z) ≤ Nat.card F) :
    ⁅localZSpan d.radical (path.walk.getVert 2) a ⊓ Q d.radical (path.walk.getVert 2),
      Z d.radical z ⊓ Q d.radical a⁆=⊥ := by
  let e := path.walk.getVert 2
  let W := localZSpan d.radical e a
  let C := W ⊓ Q d.radical e
  let A := U d.radical z ⊓ Q d.radical a
  let R₀ := ⁅C,A⁆
  have hl := path.length_eq_b
  have he : color d.radical e=false := (path.vertex_color (by omega)).mpr (by decide)
  have hd : (cosetGraph d.radical).dist a e=2 := path.dist_start (by omega)
  have hWV : W ≤ V d.radical a := localZSpan_le_V d.radical (by
    rw [SimpleGraph.dist_comm,hd])
  have hCz : C ≤ stabilizer d.radical z := by
    have hh := (le_inf (inf_le_left.trans hWV) inf_le_right).trans
      (truncated_radius_le_endpoint_stabilizer path (by omega))
    simpa only [path.length_eq_b,hb,show 4-2=2 from rfl] using hh
  have hA : A=U d.radical z ⊓ B d.radical e (geometry.Z_normal e) :=
    terminal_moving_kernel_eq_B h d path hb hi
  have hRZa : R₀ ≤ fixedCore d.radical a :=
    (commutator_mono (inf_le_left.trans hWV) inf_le_right).trans hfixed
  obtain ⟨hWQ,hZQ,_,_,_,_⟩ :=
    h.replacement_distance_four_normal_spans_of_radius_fixed d path hb hfixed
  have hRZ : R₀ ≤ Z d.radical e :=
    (commutator_mono inf_le_left inf_le_right).trans (hWQ.le.trans hZQ)
  have hAB : A ≤ B d.radical e (geometry.Z_normal e) := hA.le.trans inf_le_right
  have hRDe : R₀ ≤ fixedCore d.radical e := by
    rw [show R₀=⁅C,A⁆ from rfl,commutator_comm]
    exact (commutator_mono
      (hAB.trans (Escape.EdgeTransfer.B_le_radius (by omega) e he)) inf_le_right).trans
      (radius_fixed_at d path.start_color he hfixed)
  have hRQ : R₀ ≤ centralizer (Q d.radical e : Set (FreeAmalgam d.radical)) :=
    hRZ.trans (commutator_eq_bot_iff_le_centralizer.mp (Z_centralizes_Q d.radical e he))
  have hRe : R₀ ≤ centralizer (stabilizer d.radical e : Set (FreeAmalgam d.radical)) := by
    apply le_centralizer_iff.mpr
    rw [←inner_stabilizer_eq h d geometry (by omega) he]
    exact sup_le (le_centralizer_iff.mp (hRDe.trans inf_le_right))
      (le_centralizer_iff.mp hRQ)
  have hRa : R₀ ≤ centralizer (stabilizer d.radical a : Set (FreeAmalgam d.radical)) := by
    apply le_centralizer_iff.mpr
    rw [←inner_stabilizer_eq h d geometry (by omega) path.start_color]
    exact sup_le (le_centralizer_iff.mp (hRZa.trans inf_le_right))
      (le_centralizer_iff.mp (hRe.trans
        (centralizer_le (Q_le_stabilizer_of_dist_two d.radical a e path.start_color hd))))
  have hRg : R₀.map (MulAut.conj g⁻¹).toMonoidHom=R₀ :=
    mem_normalizer_iff_map_conj_eq.mp (Subgroup.centralizer_le_normalizer _
      (le_centralizer_iff.mp hRe ((stabilizer d.radical e).inv_mem hg)))
  have hRz : R₀ ≤ centralizer (stabilizer d.radical z : Set (FreeAmalgam d.radical)) := by
    have hh := (map_mono (f := (MulAut.conj g⁻¹).toMonoidHom) hRa).trans
      (map_centralizer_le_centralizer_image _ _)
    change R₀.map (MulAut.conj g⁻¹).toMonoidHom ≤ centralizer
      ((stabilizer d.radical a).map (MulAut.conj g⁻¹).toMonoidHom : Set _) at hh
    rwa [hRg,←stabilizer_act,hga] at hh
  have hzero : ⁅C,A⁆=⊥ :=
    (h.replacement_natural_commutator_fixed_iff d geometry (by omega) path.end_color C A
      hCz inf_le_left).mp (hRz.trans (centralizer_le (Ltilde_le_stabilizer z)))
  have hcrit := h.replacement_distance_four_fixed_critical_indices d hb path.start_color hfixed path
  have hsmall : (Q d.radical z).relIndex (Z d.radical a)<Nat.card F^2 := by
    rw [hcrit.1]
    have hq : 1 < Nat.card F := Finite.one_lt_card
    nlinarith
  have hfull := (h.replacement_root_intersection_fixed_and_commutator d path (by omega)
    hsmall C hCz).1
  rw [h.replacement_distance_four_X_eq_Z d geometry hb path.end_color] at hfull
  exact hfull.trans hzero

/-- Paired literal seed budgets and the retained endpoint conjugator
produce an actual endpoint offender on the faithfully marked full span quotient. -/
theorem Input.replacement_distance_four_root_span_offender
    {geometry : Geometry d.radical} {a z : Vertex d.radical}
    (path : CriticalPath d.radical geometry a z) (hb : geometry.b d.radical=4)
    (g : FreeAmalgam d.radical) (hg : g ∈ stabilizer d.radical (path.walk.getVert 2))
    (hga : act d.radical g a=z)
    (hfixed : ⁅V d.radical a,Q d.radical a⁆ ≤ fixedCore d.radical a)
    (hfirst : (B d.radical a (geometry.Z_normal a)).relIndex
      (U d.radical (path.walk.getVert 2)) ≤ Nat.card F)
    (hlast : (B d.radical (path.walk.getVert 2) (geometry.Z_normal _)).relIndex
      (U d.radical z) ≤ Nat.card F) :
    let W := localZSpan d.radical (path.walk.getVert 2) a
    let D := W ⊓ B d.radical a (geometry.Z_normal a)
    ∃ E : BinaryField, E.degree=n ∧
      ∃ f : stabilizer d.radical a →* Sp E.Carrier,
        Function.Surjective f ∧ f.ker.map (stabilizer d.radical a).subtype=Q d.radical a ∧
        ∃ hD : (D.subgroupOf W).Normal,
          letI := hD
          ∃ hEA : IsElementaryAbelian 2 (W ⧸ D.subgroupOf W),
            letI := hEA
            ∃ σ : Representation (ZMod 2) (Sp E.Carrier) (Additive (W ⧸ D.subgroupOf W)),
              Function.Injective σ ∧
              ∃ c : BinaryConjugationSection (stabilizer d.radical a) W D (σ.comp f),
                (∀ w : W, (c.coordinates w).toAdd=
                  Additive.ofMul (QuotientGroup.mk' (D.subgroupOf W) w)) ∧
                IsOffender σ (((Z d.radical z).subgroupOf (stabilizer d.radical a)).map f) := by
  let e := path.walk.getVert 2
  let W := localZSpan d.radical e a
  let C := W ⊓ Q d.radical e
  let D := W ⊓ B d.radical a (geometry.Z_normal a)
  let S := stabilizer d.radical a
  have hl := path.length_eq_b
  have hd : (cosetGraph d.radical).dist a e=2 := path.dist_start (by omega)
  have hWV : W ≤ V d.radical a := localZSpan_le_V d.radical (by
    rw [SimpleGraph.dist_comm,hd])
  have hWQ : W ≤ Q d.radical a :=
    hWV.trans (geometry.V_le_Q (by omega) a path.start_color)
  have hCz : C ≤ stabilizer d.radical z := by
    have hh := (le_inf (inf_le_left.trans hWV) inf_le_right).trans
      (truncated_radius_le_endpoint_stabilizer path (by omega))
    simpa only [path.length_eq_b,hb,show 4-2=2 from rfl] using hh
  have hfix : C ≤ centralizer ((Z d.radical z ⊓ Q d.radical a :
      Subgroup (FreeAmalgam d.radical)) : Set _) :=
    commutator_eq_bot_iff_le_centralizer.mp
      (span_kernel_fixes_full_root_intersection h d path hb g hg hga hfixed hlast)
  have hZzS : Z d.radical z ≤ S := path.endpoint_Z_le_start_stabilizer (by omega)
  have hcomm : ⁅Z d.radical z,C⁆ ≤ D := by
    apply le_inf
    · exact (commutator_mono le_rfl inf_le_left).trans
        (le_normalizer_iff_commutator_le_right.mp
          (hZzS.trans (localZSpan_normalized d.radical e a)))
    · exact (h.replacement_critical_fixed_intersection_displacement d path (by omega)
        C hCz (inf_le_left.trans hWQ) hfix).trans
        ((critical_commutator_le_start_seed path).trans
          (Escape.EdgeTransfer.Z_le_B (by omega) a path.start_color))
  obtain ⟨E,hE,f,hf,hfQ,hD,hEA,σ,hfaith,c,hcoord,_⟩ :=
    h.replacement_distance_four_span_action_of_radius_fixed d path hb hfixed
  let := hD
  let := hEA
  refine ⟨E,hE,f,hf,hfQ,hD,hEA,σ,hfaith,c,hcoord,?_⟩
  let A := ((Z d.radical z).subgroupOf S).map f
  let := geometry.Z_elementary (by omega) z path.end_color
  let : IsElementaryAbelian 2 ((Z d.radical z).subgroupOf S) :=
    IsElementaryAbelian.subgroupOf hZzS
  have hA : IsElementaryAbelian 2 A := IsElementaryAbelian.map f
  have hk : f.ker=(Q d.radical a).subgroupOf S := by
    rw [←hfQ]
    exact (comap_map_eq_self_of_injective S.subtype_injective f.ker).symm
  have hcard : Nat.card A=Nat.card F := by
    change Nat.card (((Z d.radical z).subgroupOf S).map f)=Nat.card F
    rw [←relIndex_ker,hk,relIndex_subgroupOf hZzS]
    exact (h.replacement_distance_four_fixed_critical_indices d hb path.start_color hfixed path).2
  have hne : A≠⊥ := by
    intro heq
    have hone : Nat.card A=1 := card_eq_one.mpr heq
    have hq : 1 < Nat.card F := Finite.one_lt_card
    omega
  let := finite_stabilizer d.radical a
  let : Finite W := Finite.of_injective (inclusion c.section_le) (inclusion_injective _)
  apply BinaryConjugationSection.offender_of_section_index_of_finite σ f c
    (Z d.radical z) C hcomm ⟨hne,hA⟩
  rw [show C=W ⊓ Q d.radical e from rfl,inf_relIndex_left,hcard]
  exact h.replacement_distance_four_root_span_image d path hb hfixed hfirst

end CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
