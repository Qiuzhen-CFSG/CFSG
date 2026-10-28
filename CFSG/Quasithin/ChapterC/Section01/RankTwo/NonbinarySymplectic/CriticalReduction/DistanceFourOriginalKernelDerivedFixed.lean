module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.DistanceFourGeneralB4Endgame
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.DistanceFourSameOrbitSpanNoncentrality
public import Theory.ThreeSubgroups
public import Theory.GroupTheory.PResidual.SubnormalCoreAction
import all CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.SectionThree.NormalizationTransfer

/-!
# The original kernel derived subgroup is fixed

Once the literal original residual [Q_a,L_a] is the moving radius, the
fixed-radius hypothesis controls [[Q_a,L_a],Q_a]. Relative three-subgroups
places [Q_a',L_a] in the original fixed core. Two-perfect commutator
idempotence then removes this fixed displacement, so Q_a' lies in D_a.

Transport to the original midpoint, followed by the proved equality
(Q0 intersect Q_e)' = Q0' = W', contradicts the same-orbit span obstruction.
Every group is the original embedded group. No containment in a reciprocal
span, normalization of a residual intersection, seed budget, or replacement
selector is assumed.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
namespace CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
variable {H F : Type*} [Group H] [Finite H] [Field F] [Finite F] [CharP F 2]
variable {K R : Subgroup H} {n : ℕ} (h : Input K R n F)
variable (d : CharacteristicReduction K R)
include h

omit [Finite F] [CharP F 2] in
/-- With the proved original residual identity, the full original kernel's
own derived subgroup belongs to its fixed core. -/
theorem Input.replacement_original_kernel_derived_le_fixedCore
    {a : Vertex d.radical} (ha : color d.radical a=false)
    (hfixed : ⁅V d.radical a,Q d.radical a⁆ ≤ fixedCore d.radical a)
    (hQ₀ : ⁅Q d.radical a,Ltilde d.radical a⁆=Vcirc d.radical a) :
    ⁅Q d.radical a,Q d.radical a⁆ ≤ fixedCore d.radical a := by
  let S := stabilizer d.radical a
  let C := ⁅Q d.radical a,Q d.radical a⁆
  have hQS : Q d.radical a ≤ S := fun _ hx => hx.1
  have hCS : C ≤ S := (commutator_le_self _).trans hQS
  have hSD := SectionThree.fixedCore_normalized d.radical a
  have hmove : ⁅⁅Q d.radical a,Ltilde d.radical a⁆,Q d.radical a⁆ ≤
      fixedCore d.radical a := by
    rw [hQ₀]
    exact (commutator_mono (DistanceEight.Vcirc_le_V d.radical a) le_rfl).trans hfixed
  have hCL : ⁅C,Ltilde d.radical a⁆ ≤ fixedCore d.radical a :=
    commutator_commutator_le_of_rotate_of_le_normalizer
      (hQS.trans hSD) (hQS.trans hSD) ((Ltilde_le_stabilizer a).trans hSD)
      hmove (by simpa only [commutator_comm (Ltilde d.radical a)] using hmove)
  have hSC : S ≤ normalizer (C : Set (FreeAmalgam d.radical)) := by
    intro x hx
    rw [mem_normalizer_iff_map_conj_eq,map_commutator,
      mem_normalizer_iff_map_conj_eq.mp (Q_normalized d.radical a hx)]
  let A := C.subgroupOf S
  let := finite_stabilizer d.radical a
  let : A.Normal := normal_subgroupOf_of_le_normalizer hSC
  have hAp : IsPGroup 2 A :=
    ((Q_isPGroup d.radical (h.replacement_two_group d) (h.replacement_core_le d)
      a ha).to_le (commutator_le_self _)).comap_subtype
  have hid := congrArg (Subgroup.map S.subtype)
    (commutator_isPPerfect_idempotent (pResidual 2 S) A (isPPerfect_pResidual 2)
      hAp le_normalizer_of_normal)
  have hAm : A.map S.subtype=C := map_subgroupOf_eq_of_le hCS
  have hid' : ⁅⁅C,Ltilde d.radical a⁆,Ltilde d.radical a⁆ =
      ⁅C,Ltilde d.radical a⁆ := by
    simpa only [map_commutator,hAm,Ltilde] using hid
  have hzero : ⁅C,Ltilde d.radical a⁆=⊥ := by
    apply le_bot_iff.mp
    rw [←hid']
    exact (commutator_mono hCL le_rfl).trans
      (commutator_eq_bot_iff_le_centralizer.mpr
        (show fixedCore d.radical a ≤ centralizer
          (Ltilde d.radical a : Set (FreeAmalgam d.radical)) from inf_le_right)).le
  exact le_inf (commutator_le_self _) (commutator_eq_bot_iff_le_centralizer.mp hzero)

/-- The actual same-midpoint-orbit, fixed-radius b=4 branch is impossible.
The exact original-Q0 identity and derived retention supply the contradiction;
there is no additional numerical or normality premise. -/
theorem Input.replacement_distance_four_fixed_same_orbit_false
    {geometry : Geometry d.radical} {a z : Vertex d.radical}
    (path : CriticalPath d.radical geometry a z) (hb : geometry.b d.radical=4)
    (g : FreeAmalgam d.radical) (hg : g ∈ stabilizer d.radical (path.walk.getVert 2))
    (hga : act d.radical g a=z)
    (hfixed : ⁅V d.radical a,Q d.radical a⁆ ≤ fixedCore d.radical a) : False := by
  let e := path.walk.getVert 2
  let Q₀ := ⁅Q d.radical a,Ltilde d.radical a⁆
  let W := localZSpan d.radical e a
  obtain ⟨_,_,_,hQcirc,_,_,hder,_,hretain,_⟩ :=
    h.replacement_distance_four_general_b4_endgame d path hb g hg hga hfixed
  have hQa := h.replacement_original_kernel_derived_le_fixedCore d path.start_color hfixed hQcirc
  have hl := path.length_eq_b
  have he : color d.radical e=false := (path.vertex_color (by omega)).mpr (by decide)
  obtain ⟨u,hu⟩ := exists_mVertex_of_color d.radical path.start_color
  obtain ⟨v,hv⟩ := exists_mVertex_of_color d.radical he
  have hact : act d.radical (u⁻¹*v) a=e := by
    rw [hu,act_mVertex,mul_inv_cancel_left,←hv]
  have hQe : ⁅Q d.radical e,Q d.radical e⁆ ≤ fixedCore d.radical e := by
    have hh := map_mono (f := (MulAut.conj (u⁻¹*v)⁻¹).toMonoidHom) hQa
    rwa [map_commutator,←Q_act,←Escape.EdgeTransfer.fixedCore_act,hact] at hh
  have hQ₀e : ⁅Q₀,Q₀⁆ ≤ fixedCore d.radical e := by
    rw [←hretain]
    exact (commutator_mono inf_le_right inf_le_right).trans hQe
  have hWe : ⁅W,W⁆ ≤ fixedCore d.radical e := hder ▸ hQ₀e
  exact (h.replacement_distance_four_same_orbit_span_noncentrality d path hb
    g hg hga hfixed).2.2.1 hWe

end CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
