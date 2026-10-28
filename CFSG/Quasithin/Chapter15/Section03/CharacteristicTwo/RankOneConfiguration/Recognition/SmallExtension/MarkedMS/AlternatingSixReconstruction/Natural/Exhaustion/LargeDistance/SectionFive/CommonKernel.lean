module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.CompatibleKernel

/-!
# A central line from the shifted common-kernel seed span

Let D be a radius-two span normalized by a generating edge kernel and
contained in the critical predecessor kernel. If D escapes the Baumann
slice, the large critical-image estimate forces the critical image to
have order two. The full-cover fixed-hyperplane bound then makes
[D, Z_z ∩ Q_a] a nonzero line, retaining the central attachment.

For a family of seeds incident to one common edge kernel, that kernel
fixes each small commutator. The opposite seed fixes their span, so local
generation fixes the line throughout the starting stabilizer. It is
therefore disjoint from the noncentral critical line. In a centralizer
orbit of seeds, one conjugate seed generates the line, and centrality
transports its containment back to the original seed.

The application uses CompatibleKernel's actual characteristic replacement,
forward path and component conjugator. It preserves every shared vertex,
constructs the line in the shifted start's fixed core and shifted seed,
and proves it differs from the forward line. Both cover orders remain.

Source: Meierfrankenfeld--Stellmacher (1993), (3.3) and (5.9), printed
pp.866--867 and 920--922. The line here uses the full reverse seed kernel
Z_z ∩ Q_a. The source's A_0 on p.921 uses X_z ∩ Q_a; extending this
calculation to that larger kernel, the span comparison and strict slice
estimate remain to be proved. No source R_3 identity or distance exclusion
is asserted by this module.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender BinaryPermutation
open scoped commutatorElement IsMulCommutative Pointwise
open CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup
open Theory.SpecificGroups.SymmetricSix.BinaryFlags
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive
universe u

variable {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
  {h : SmallMSPair KnownSimple.IsKnownSimple L R} {e : CentralMarking L}
  {hz : center (L ⧸ pCore 2 L) = ⊥} {hn : InitialNatural h e hz}
  {d : Replacement L R} (s : FullSymmetricAction h e hz hn d)

private theorem last_edge_data (hb : 2 < replacementDistance h d)
    {a z : Vertex d.radical} (p : CriticalPath d.radical (replacementGeometry h d) a z) :
    let k := p.walk.getVert (p.walk.length-1)
    Adjacent d.radical z k ∧
    Q d.radical (p.walk.getVert (p.walk.length-2)) ≤ Q d.radical k ∧
    Z d.radical a ≤ Q d.radical k := by
  have hl : p.walk.length = replacementDistance h d := p.length_eq_b
  have hzk : Adjacent d.radical z (p.walk.getVert (p.walk.length-1)) := by
    have hh := p.walk.adj_getVert_succ (i := p.walk.length-1) (by omega)
    rw [show p.walk.length-1+1=p.walk.length by omega,p.walk.getVert_length] at hh
    exact adjacent_symm d.radical ((cosetGraph_adj d.radical _ _).mp hh)
  have hk : color d.radical (p.walk.getVert (p.walk.length-1)) = true := by
    have hh := adjacent_color_ne d.radical hzk
    rw [p.end_color] at hh
    cases he : color d.radical (p.walk.getVert (p.walk.length-1)) <;> simp_all
  refine ⟨hzk,?_,?_⟩
  · apply Q_le_adjacent_h d.radical hk
    have hh := p.walk.adj_getVert_succ (i := p.walk.length-2) (by omega)
    rw [show p.walk.length-2+1=p.walk.length-1 by omega] at hh
    exact (cosetGraph_adj d.radical _ _).mp hh
  · apply Z_le_Q_of_dist_lt d.radical a ((replacementGeometry h d).exists_critical a p.start_color)
    rw [(replacementGeometry h d).distance_constant a p.start_color,p.dist_start (Nat.sub_le _ _)]
    change p.walk.length-1 < replacementDistance h d
    omega

include s in
private theorem normalized_radius_le_slice_at (hc : DistanceTwo.CentralLayer d)
    (hb : 2 < replacementDistance h d) {a z : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a z)
    (D : Subgroup (FreeAmalgam d.radical)) (hDV : D ≤ V d.radical a)
    (hDN : stabilizer d.radical a ≤ normalizer (D : Set (FreeAmalgam d.radical)))
    (hcomm : ⁅D,Z d.radical z⁆ ≤ Z d.radical a) :
    D ≤ B d.radical a ((replacementGeometry h d).Z_normal _) := by
  obtain ⟨g,hga⟩ := exists_mVertex_of_color d.radical p.start_color
  subst a
  have hbase : act d.radical g⁻¹ (mVertex d.radical g) = alpha d.radical := by
    simp only [act_mVertex,mul_inv_cancel]
    rfl
  let j := (MulAut.conj (g⁻¹)⁻¹).toMonoidHom
  have hh := normalized_radius_le_slice_of_critical_commutator s hc hb (a' := act d.radical g⁻¹ z)
  rw [←hbase] at hh
  have hm := hh (p.act g⁻¹) (D.map j)
    (by rw [V_act]; exact map_mono hDV)
    (by rw [stabilizer_act]; exact (map_mono hDN).trans (D.le_normalizer_map j))
    (by rw [Z_act,Z_act,←map_commutator]; exact map_mono hcomm)
  rw [Escape.PairingControl.FirstPairing.B_act hb g⁻¹ (mVertex d.radical g) p.start_color] at hm
  exact (map_le_map_iff_of_injective (MulAut.conj (g⁻¹)⁻¹).injective).mp hm

include s in
private theorem edge_normalized_radius_le_slice (hc : DistanceTwo.CentralLayer d)
    (hb : 2 < replacementDistance h d) {a z t : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a z)
    (hat : Adjacent d.radical a t)
    (hgen : Q d.radical t ⊔ Z d.radical z = stabilizer d.radical a)
    (D : Subgroup (FreeAmalgam d.radical)) (hDV : D ≤ V d.radical a)
    (hDN : Q d.radical t ≤ normalizer (D : Set (FreeAmalgam d.radical)))
    (hcomm : ⁅D,Z d.radical z⁆ ≤ Z d.radical a) :
    D ≤ B d.radical a ((replacementGeometry h d).Z_normal _) := by
  let N := D ⊔ Z d.radical a
  have htG : Q d.radical t ≤ stabilizer d.radical a :=
    fun _ hx => hx.2 _ (adjacent_symm d.radical hat)
  have hcom : ⁅N,Z d.radical z⁆ ≤ Z d.radical a :=
    commutator_sup_le_of_relative_normal (stabilizer d.radical a) D (Z d.radical a)
      (Z d.radical z) (Z d.radical a) (Z_normalized d.radical a)
      (hDV.trans ((replacementGeometry h d).V_local a p.start_color (by
        rw [(replacementGeometry h d).distance_constant a p.start_color]
        exact hb)))
      (Z_le_stabilizer d.radical a) hcomm
      (((critical_Z_commutator_le_moving (h := h) p).trans inf_le_left).trans (DistanceEight.U_le_Z d.radical a))
  have hnorm : stabilizer d.radical a ≤ normalizer (N : Set (FreeAmalgam d.radical)) := by
    rw [←hgen]
    apply sup_le
    · exact (le_inf hDN (htG.trans (Z_normalized d.radical a))).trans
        (normalizer_inf_normalizer_le_normalizer_sup _ _)
    · exact le_normalizer_iff_commutator_le_left.mpr (hcom.trans le_sup_right)
  exact le_sup_left.trans (normalized_radius_le_slice_at s hc hb p N
    (sup_le hDV (Z_le_VBall d.radical a 2)) hnorm hcom)

/-- An edge-normalized radius span outside the Baumann slice forces the
small critical image and a nonzero commutator with the full reverse kernel.
The latter has order two on either cover, without identifying its line. -/
theorem common_kernel_span_small_line (hc : DistanceTwo.CentralLayer d)
    (hb : 2 < replacementDistance h d) (u : S)
    (hR : d.radical.map s.projection ≤ pointCore.map (MulAut.conj u).toMonoidHom)
    {a z t : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a z)
    (hat : Adjacent d.radical a t)
    (hgen : Q d.radical t ⊔ Z d.radical z = stabilizer d.radical a)
    (D : Subgroup (FreeAmalgam d.radical)) (hDV : D ≤ V d.radical a)
    (hDpre : D ≤ Q d.radical (p.walk.getVert (p.walk.length-2)))
    (hDN : Q d.radical t ≤ normalizer (D : Set (FreeAmalgam d.radical)))
    (hDB : ¬ D ≤ B d.radical a ((replacementGeometry h d).Z_normal _)) :
    (Q d.radical z).relIndex (Z d.radical a) = 2 ∧
    Nat.card (⁅D,Z d.radical z ⊓ Q d.radical a⁆ : Subgroup (FreeAmalgam d.radical)) = 2 := by
  have hsmall : (Q d.radical z).relIndex (Z d.radical a) < 4 := by
    by_contra! hh
    exact hDB (edge_normalized_radius_le_slice s hc hb p hat hgen D hDV hDN
      ((commutator_mono (le_inf hDV hDpre) le_rfl).trans
        (critical_radius_commutator_le_Z s hc u hR hb p hh)))
  have hne : ⁅D,Z d.radical z ⊓ Q d.radical a⁆ ≠ ⊥ := by
    intro hh
    exact hDB (edge_normalized_radius_le_slice s hc hb p hat hgen D hDV hDN
      (small_critical_predecessor_commutator s hc hb p hsmall D hDpre
        (commutator_eq_bot_iff_le_centralizer.mp hh)))
  have hedge := last_edge_data (h := h) hb p
  let k := p.walk.getVert (p.walk.length-1)
  let := finite_Z d.radical z
  let : Finite (U d.radical z) := Finite.of_injective
    (inclusion (DistanceEight.U_le_Z d.radical z)) (inclusion_injective _)
  have hidx : (centralizer (Z d.radical a : Set (FreeAmalgam d.radical))).relIndex
      (U d.radical z) ≤ 2 := by
    have hC : Q d.radical a ≤ centralizer (Z d.radical a : Set (FreeAmalgam d.radical)) :=
      le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp
        (Z_centralizes_Q d.radical a p.start_color))
    exact ((relIndex_le_of_le_left hC index_ne_zero_of_finite).trans
      (relIndex_le_of_le_right (DistanceEight.U_le_Z d.radical z) index_ne_zero_of_finite)).trans_eq
        (small_critical_indices s hc p hsmall).2
  have hcard := small_edge_fixed_card_at s hc u hR p.end_color hedge.1
    (Z d.radical a) hedge.2.2 p.critical.2 hidx
  have hK : Z d.radical z ⊓ Q d.radical a =
      Z d.radical z ⊓ centralizer (Z d.radical a : Set (FreeAmalgam d.radical)) := by
    rw [←C_eq_Q s hc a p.start_color]
    apply le_antisymm (inf_le_inf_left _ inf_le_right)
    apply le_inf inf_le_left
    exact le_inf (inf_le_left.trans (critical_Z_le_stabilizer d.radical
      (replacementGeometry h d) a p.start_color (by
        rw [(replacementGeometry h d).distance_constant a p.start_color]
        exact replacementDistance_pos h d) p.critical)) inf_le_right
  have hbound : ⁅D,Z d.radical z ⊓ Q d.radical a⁆ ≤
      ⁅Z d.radical z ⊓ centralizer (Z d.radical a : Set (FreeAmalgam d.radical)),Q d.radical k⁆ := by
    rw [commutator_comm,hK]
    exact commutator_mono le_rfl (hDpre.trans hedge.2.1)
  have hDZ : D ≤ stabilizer d.radical z :=
    (hDpre.trans hedge.2.1).trans (fun _ hx => hx.2 _ (adjacent_symm d.radical hedge.1))
  have hlineZ : ⁅D,Z d.radical z ⊓ Q d.radical a⁆ ≤ Z d.radical z :=
    (commutator_mono le_rfl inf_le_left).trans
      (le_normalizer_iff_commutator_le_right.mp (hDZ.trans (Z_normalized d.radical z)))
  have hbigZ : ⁅Z d.radical z ⊓ centralizer (Z d.radical a : Set (FreeAmalgam d.radical)),Q d.radical k⁆ ≤ Z d.radical z :=
    (commutator_mono inf_le_left le_rfl).trans
      (le_normalizer_iff_commutator_le_left.mp
        ((show Q d.radical k ≤ stabilizer d.radical z from
          fun _ hx => hx.2 _ (adjacent_symm d.radical hedge.1)).trans (Z_normalized d.radical z)))
  let : Finite (⁅D,Z d.radical z ⊓ Q d.radical a⁆ : Subgroup (FreeAmalgam d.radical)) :=
    Finite.of_injective (inclusion hlineZ) (inclusion_injective _)
  let : Finite (⁅Z d.radical z ⊓ centralizer (Z d.radical a : Set (FreeAmalgam d.radical)),Q d.radical k⁆ : Subgroup (FreeAmalgam d.radical)) :=
    Finite.of_injective (inclusion hbigZ) (inclusion_injective _)
  have hbnd := (card_le_of_le hbound).trans hcard
  have hpos := (one_lt_card_iff_ne_bot _).mpr hne
  exact ⟨(small_critical_indices s hc p hsmall).1,by omega⟩

private theorem common_edge_derived_le_core
    (hab : ⁅d.radical.map s.projection,d.radical.map s.projection⁆ = ⊥)
    {a t : Vertex d.radical} (ha : color d.radical a = false)
    (hat : Adjacent d.radical a t) :
    ⁅Q d.radical t,Q d.radical t⁆ ≤ Q d.radical a := by
  have hr : ⁅d.radical,d.radical⁆ ≤ pCore 2 d.overgroup := by
    rw [←s.projection_kernel,←Subgroup.map_eq_bot_iff,map_commutator]
    exact hab
  have hbase : ⁅Q d.radical (beta d.radical),Q d.radical (beta d.radical)⁆ ≤
      Q d.radical (alpha d.radical) := by
    rw [Q_beta,Q_alpha d.radical (replacement_radical_isPGroup h d)
      (replacement_core_le_radical h d),←map_commutator]
    exact map_mono hr
  obtain ⟨g,hg|hg⟩ := (adjacent_iff_exists_common d.radical a t).mp hat
  · rcases hg with ⟨rfl,rfl⟩
    have hh := map_mono (f := (MulAut.conj g⁻¹).toMonoidHom) hbase
    rw [map_commutator,←Q_act,←Q_act] at hh
    simpa only [alpha,beta,act_mVertex,act_hVertex,one_mul] using hh
  · rw [hg.1] at ha
    cases ha

private theorem common_fixed_mod_central_normalizes_line {H : Type*} [Group H]
    (A Q D : Subgroup H) (hAQ : A ≤ normalizer (Q : Set H))
    (hDQ : D ≤ normalizer (Q : Set H))
    (hDA : ⁅D,A⁆ ≤ centralizer (Q : Set H)) :
    D ≤ normalizer ((⁅A,Q⁆ : Subgroup H) : Set H) := by
  apply le_normalizer_closure_iff.mpr
  rintro d hd _ ⟨a,ha,q,hq,rfl⟩
  have hq' : d*q*d⁻¹ ∈ Q := (mem_normalizer_iff.mp (hDQ hd) q).mp hq
  have hk : ⁅d,a⁆ ∈ centralizer (Q : Set H) := hDA (commutator_mem_commutator hd ha)
  have hcomm : ⁅a,d*q*d⁻¹⁆ ∈ Q :=
    le_normalizer_iff_commutator_le_right.mp hAQ (commutator_mem_commutator ha hq')
  have hzero : ⁅⁅d,a⁆,d*q*d⁻¹⁆ = 1 :=
    commutatorElement_eq_one_iff_mul_comm.mpr (hk _ hq').symm
  rw [conjugate_commutatorElement,show d*a*d⁻¹ = ⁅d,a⁆*a by
    simp [commutatorElement_def,mul_assoc],commutatorElement_mul_left_eq_conj_mul,
    hzero,mul_one,←hk _ hcomm,mul_inv_cancel_right]
  exact commutator_mem_commutator ha hq'

private theorem small_common_edge_commutator_central
    (hab : ⁅d.radical.map s.projection,d.radical.map s.projection⁆ = ⊥)
    {a t : Vertex d.radical} (ha : color d.radical a = false) (hat : Adjacent d.radical a t)
    (A : Subgroup (FreeAmalgam d.radical)) (hA : A ≤ Q d.radical t)
    (hcard : Nat.card (⁅Z d.radical a,A⁆ : Subgroup (FreeAmalgam d.radical)) ≤ 2) :
    ⁅Z d.radical a,A⁆ ≤ centralizer (Q d.radical t : Set (FreeAmalgam d.radical)) := by
  have hQtG : Q d.radical t ≤ stabilizer d.radical a :=
    fun _ hx => hx.2 a (adjacent_symm d.radical hat)
  have hQtZ := hQtG.trans (Z_normalized d.radical a)
  have hcomm : ⁅Q d.radical t,A⁆ ≤ centralizer (Z d.radical a : Set (FreeAmalgam d.radical)) :=
    ((commutator_mono le_rfl hA).trans (common_edge_derived_le_core s hab ha hat)).trans
      (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp
        (Z_centralizes_Q d.radical a ha)))
  have hn := common_fixed_mod_central_normalizes_line A (Z d.radical a) (Q d.radical t)
    (hA.trans hQtZ) hQtZ hcomm
  rw [commutator_comm A (Z d.radical a)] at hn
  have hNZ : ⁅Z d.radical a,A⁆ ≤ Z d.radical a :=
    le_normalizer_iff_commutator_le_left.mp (hA.trans hQtZ)
  let := finite_Z d.radical a
  let : Finite (⁅Z d.radical a,A⁆ : Subgroup (FreeAmalgam d.radical)) :=
    Finite.of_injective (inclusion hNZ) (inclusion_injective _)
  by_cases he : Nat.card (⁅Z d.radical a,A⁆ : Subgroup (FreeAmalgam d.radical)) = 2
  · exact le_centralizer_iff.mp
      (hn.trans (normalizer_le_centralizer_of_card_two _ he))
  · rw [eq_bot_of_card_le _ (by omega : Nat.card (⁅Z d.radical a,A⁆ : Subgroup (FreeAmalgam d.radical)) ≤ 1)]
    exact bot_le

/-- A common-edge seed family outside the slice has a nonzero reverse-kernel
line fixed by the whole starting stabilizer. This line is disjoint from the
noncentral critical line; no equality of their quotient lifts is inferred. -/
theorem common_edge_family_central_line (hc : DistanceTwo.CentralLayer d)
    (hb : 2 < replacementDistance h d) (u : S)
    (hR : d.radical.map s.projection ≤ pointCore.map (MulAut.conj u).toMonoidHom)
    {a z t : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a z)
    (hat : Adjacent d.radical a t)
    (hgen : Q d.radical t ⊔ Z d.radical z = stabilizer d.radical a)
    {ι : Type*} (v k : ι → Vertex d.radical)
    (hv : ∀ i, color d.radical (v i) = false)
    (hvk : ∀ i, Adjacent d.radical (v i) (k i))
    (hk : ∀ i, Q d.radical (k i) = Q d.radical t)
    (hDV : (⨆ i,Z d.radical (v i)) ≤ V d.radical a)
    (hDpre : (⨆ i,Z d.radical (v i)) ≤ Q d.radical (p.walk.getVert (p.walk.length-2)))
    (hDN : Q d.radical t ≤ normalizer ((⨆ i,Z d.radical (v i) : Subgroup (FreeAmalgam d.radical)) : Set (FreeAmalgam d.radical)))
    (hDB : ¬ (⨆ i,Z d.radical (v i)) ≤ B d.radical a ((replacementGeometry h d).Z_normal _)) :
    let J := ⁅⨆ i,Z d.radical (v i),Z d.radical z ⊓ Q d.radical a⁆
    (Q d.radical z).relIndex (Z d.radical a) = 2 ∧ Nat.card J = 2 ∧
    J ≤ Z d.radical z ∧
    J ≤ centralizer (stabilizer d.radical a : Set (FreeAmalgam d.radical)) ∧
    J ⊓ ⁅Z d.radical a,Z d.radical z⁆ = ⊥ := by
  let D := ⨆ i,Z d.radical (v i)
  let K := Z d.radical z ⊓ Q d.radical a
  let J := ⁅D,K⁆
  have hsmall := common_kernel_span_small_line s hc hb u hR p hat hgen D hDV hDpre hDN hDB
  have hedge := last_edge_data (h := h) hb p
  have hDz : D ≤ stabilizer d.radical z :=
    (hDpre.trans hedge.2.1).trans (fun _ hx => hx.2 _ (adjacent_symm d.radical hedge.1))
  have hJZ : J ≤ Z d.radical z := (commutator_mono le_rfl inf_le_left).trans
    (le_normalizer_iff_commutator_le_right.mp (hDz.trans (Z_normalized d.radical z)))
  let := finite_Z d.radical z
  let : Finite J := Finite.of_injective (inclusion hJZ) (inclusion_injective _)
  have ht : color d.radical t = true := by
    have hh := adjacent_color_ne d.radical hat
    rw [p.start_color] at hh
    cases he : color d.radical t <;> simp_all
  have hQt : Q d.radical a ≤ Q d.radical t := Q_le_adjacent_h d.radical ht hat
  have hDQ : D ≤ Q d.radical t := hDV.trans
    (((replacementGeometry h d).V_le_Q hb a p.start_color).trans hQt)
  have hKQt : K ≤ Q d.radical t := inf_le_right.trans hQt
  have hab : ⁅d.radical.map s.projection,d.radical.map s.projection⁆ = ⊥ := by
    let := pointCore_elementary
    let : IsElementaryAbelian 2 (pointCore.map (MulAut.conj u).toMonoidHom) := IsElementaryAbelian.map _
    let helem : IsElementaryAbelian 2 (d.radical.map s.projection) := IsElementaryAbelian.of_le hR
    exact commutator_eq_bot_iff_le_centralizer.mpr
      (le_centralizer_iff_isMulCommutative.mpr helem.toIsMulCommutative)
  have hJQt : J ≤ centralizer (Q d.radical t : Set (FreeAmalgam d.radical)) := by
    apply commutator_iSup_le_of_relative_normal (Q d.radical t) K
      (centralizer (Q d.radical t : Set (FreeAmalgam d.radical))) (fun i => Z d.radical (v i))
      ((le_centralizer_iff.mp le_rfl).trans (Subgroup.centralizer_le_normalizer _))
      (fun i => (le_iSup (fun i => Z d.radical (v i)) i).trans hDQ)
    intro i
    have hi : Nat.card (⁅Z d.radical (v i),K⁆ : Subgroup (FreeAmalgam d.radical)) ≤ 2 :=
      (card_le_of_le (commutator_mono (le_iSup (fun i => Z d.radical (v i)) i) le_rfl)).trans_eq hsmall.2
    rw [←hk i]
    exact small_common_edge_commutator_central s hab (hv i) (hvk i) K (by rwa [hk i]) hi
  have hJG : J ≤ centralizer (stabilizer d.radical a : Set (FreeAmalgam d.radical)) := by
    apply le_centralizer_iff.mp
    rw [←hgen]
    apply sup_le (le_centralizer_iff.mp hJQt)
    let := (replacementGeometry h d).Z_elementary (replacementDistance_pos h d) z p.end_color
    exact le_centralizer_iff.mp (hJZ.trans (le_centralizer_iff_isMulCommutative.mpr inferInstance))
  refine ⟨hsmall.1,hsmall.2,hJZ,hJG,?_⟩
  apply le_bot_iff.mp
  rw [←small_critical_commutator_inf_centralizer s hc p (by rw [hsmall.1]; decide)]
  exact le_inf inf_le_right (inf_le_left.trans hJG)

private theorem exists_span_line_generator {F : Type*} [Group F]
    (H P K : Subgroup F)
    (hcard : Nat.card (⁅conjugateSpanBy H P,K⁆ : Subgroup F) = 2) :
    ∃ x : P, ⁅H.map (MulAut.conj (x : F)).toMonoidHom,K⁆ = ⁅conjugateSpanBy H P,K⁆ := by
  let J := ⁅conjugateSpanBy H P,K⁆
  let : Finite J := Nat.finite_of_card_ne_zero (by rw [hcard]; decide)
  have hne : J ≠ ⊥ := by
    intro he
    have hc : Nat.card J = 2 := hcard
    rw [he,card_bot] at hc
    omega
  have hex : ∃ x : P, ⁅H.map (MulAut.conj (x : F)).toMonoidHom,K⁆ ≠ ⊥ := by
    by_contra! hh
    apply hne
    apply commutator_eq_bot_iff_le_centralizer.mpr
    rw [conjugateSpanBy_eq_iSup_conj]
    exact iSup_le (fun x => commutator_eq_bot_iff_le_centralizer.mp (hh x))
  obtain ⟨x,hx⟩ := hex
  have hsub : ⁅H.map (MulAut.conj (x : F)).toMonoidHom,K⁆ ≤ J :=
    commutator_mono (show H.map (MulAut.conj (x : F)).toMonoidHom ≤ conjugateSpanBy H P by
      rw [conjugateSpanBy_eq_iSup_conj]
      exact le_iSup (fun y : P => H.map (MulAut.conj (y : F)).toMonoidHom) x) le_rfl
  let : Finite (⁅H.map (MulAut.conj (x : F)).toMonoidHom,K⁆ : Subgroup F) :=
    Finite.of_injective (inclusion hsub) (inclusion_injective _)
  have hpos := (one_lt_card_iff_ne_bot _).mpr hx
  have he : ⁅H.map (MulAut.conj (x : F)).toMonoidHom,K⁆ = J :=
    eq_of_le_of_card_ge hsub (by rw [hcard]; omega)
  exact ⟨x,he⟩

private theorem central_span_line_le_seed {F : Type*} [Group F]
    (H P K : Subgroup F)
    (hcard : Nat.card (⁅conjugateSpanBy H P,K⁆ : Subgroup F) = 2)
    (hcentral : ⁅conjugateSpanBy H P,K⁆ ≤ centralizer (P : Set F))
    (hn : ∀ x : P, K ≤ normalizer (H.map (MulAut.conj (x : F)).toMonoidHom : Set F)) :
    ⁅conjugateSpanBy H P,K⁆ ≤ H := by
  let J := ⁅conjugateSpanBy H P,K⁆
  obtain ⟨x,he⟩ := exists_span_line_generator H P K hcard
  have hJ : J ≤ H.map (MulAut.conj (x : F)).toMonoidHom := by
    change ⁅conjugateSpanBy H P,K⁆ ≤ _
    rw [←he]
    exact le_normalizer_iff_commutator_le_left.mp (hn x)
  intro z hz
  obtain ⟨w,hw,heq⟩ := hJ hz
  have hcomm := hcentral hz (x : F) x.property
  have he : w = z := by
    apply (MulAut.conj (x : F)).injective
    change (x : F)*w*(x : F)⁻¹=(x : F)*z*(x : F)⁻¹
    calc
      (x : F)*w*(x : F)⁻¹ = z := heq
      _ = (x : F)*z*(x : F)⁻¹ := by rw [hcomm,mul_inv_cancel_right]
  exact he ▸ hw

/-- In the actual full-point, small-forward-slice configuration, the same
component conjugator and every shared path vertex give a central nonzero
reverse-kernel line at the shifted start. Its small critical line is distinct.
Both central covers and the canonical natural quotient are retained. -/
theorem full_point_small_shifted_central_line_knownSimple
    {h : SmallMSPair KnownSimple.IsKnownSimple L R} {e : CentralMarking L}
    {hz : center (L ⧸ pCore 2 L) = ⊥} {hn : InitialNatural h e hz}
    {d : Replacement L R} (hb : 4 < replacementDistance h d)
    (u : Equiv.Perm (Fin 6))
    (hfull : d.radical.map (SourceReduction.projection h e hz hn d) =
      pointCore.map (MulAut.conj u).toMonoidHom)
    {a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) a')
    (hslice : (B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _)).relIndex
      (U d.radical (p.walk.getVert 2)) ≤ 2)
    (hsmall : (Q d.radical a').relIndex (Z d.radical (alpha d.radical)) < 4) :
    let c := p.walk.getVert 2
    let T := Q d.radical (alpha d.radical) ⊓ centralizer
      (U d.radical c ⊓ B d.radical (alpha d.radical)
        ((replacementGeometry h d).Z_normal _) : Set (FreeAmalgam d.radical))
    let H := ⁅U d.radical c,T⁆
    ∃ z, ∃ q : CriticalPath d.radical (replacementGeometry h d) c z,
      (cosetGraph d.radical).dist a' z = 2 ∧
      (∀ i ≤ p.walk.length-2, q.walk.getVert i = p.walk.getVert (i+2)) ∧
      q.walk.getVert (q.walk.length-2) = a' ∧
      ∃ t, Adjacent d.radical c t ∧
        Q d.radical t ⊔ Z d.radical z = stabilizer d.radical c ∧
      ∃ y ∈ Ltilde d.radical c,
        let a := act d.radical y⁻¹ (alpha d.radical)
        let H₂ := H.map (MulAut.conj y).toMonoidHom
        let P := stabilizer d.radical c ⊓ centralizer (H₂ : Set (FreeAmalgam d.radical))
        let D := conjugateSpanBy (Z d.radical a) P
        let J := ⁅D,Z d.radical z ⊓ Q d.radical c⁆
        H₂ ≤ U d.radical c ⊓ Z d.radical t ∧
        P ⊔ Z d.radical z = stabilizer d.radical c ∧
        ¬ H₂ ≤ centralizer (Z d.radical z : Set (FreeAmalgam d.radical)) ∧
        D ≤ Q d.radical a' ∧
        (Q d.radical z).relIndex (Z d.radical c) = 2 ∧
        Nat.card J = 2 ∧ J ≤ Z d.radical z ∧
        J ≤ centralizer (stabilizer d.radical c : Set (FreeAmalgam d.radical)) ∧
        J ⊓ ⁅Z d.radical c,Z d.radical z⁆ = ⊥ ∧
        J ≤ fixedCore d.radical c ∧ J ≤ Z d.radical a ∧ J ≠ H₂ ∧
        ∃ x ∈ P, ⁅(Z d.radical a).map (MulAut.conj x).toMonoidHom,
          Z d.radical z ⊓ Q d.radical c⁆ = J := by
  let s := fullSymmetricAction_knownSimple h e hz hn d (by omega)
  have hc := DistanceTwo.centralLayer_knownSimple G L R h e hz hn d
  have hfull' : d.radical.map s.projection = pointCore.map (MulAut.conj u).toMonoidHom := by
    rwa [SourceReduction.fullSymmetricAction_projection_unique h e hz hn d s]
  obtain ⟨z,q,haz,hover,hpre,t,hct,hQtgen,y,hy,
    hPgen,hHmove,hT,hZcY,hYV,hYN,hYB,hHZa,hHcard,hHCa,hcomm,
    hZaQ,hYQ,hZspanQ,hYspanQ,hZaVc,hZaBc,hHseed,hnorm,hkeq,hQtN,hall⟩ :=
    full_point_small_compatible_shifted_spans_knownSimple hb u hfull p hslice hsmall
  let c := p.walk.getVert 2
  let k := act d.radical y⁻¹ (p.walk.getVert 1)
  let a := act d.radical y⁻¹ (alpha d.radical)
  let T := Q d.radical (alpha d.radical) ⊓ centralizer
    (U d.radical c ⊓ B d.radical (alpha d.radical)
      ((replacementGeometry h d).Z_normal _) : Set (FreeAmalgam d.radical))
  let H₂ := (⁅U d.radical c,T⁆ : Subgroup (FreeAmalgam d.radical)).map (MulAut.conj y).toMonoidHom
  let P := stabilizer d.radical c ⊓ centralizer (H₂ : Set (FreeAmalgam d.radical))
  let D := conjugateSpanBy (Z d.radical a) P
  let v : P → Vertex d.radical := fun x => act d.radical (x : FreeAmalgam d.radical)⁻¹ a
  let ks : P → Vertex d.radical := fun x => act d.radical (x : FreeAmalgam d.radical)⁻¹ k
  have hD : (⨆ x,Z d.radical (v x)) = D := by
    change (⨆ x,Z d.radical (v x)) = conjugateSpanBy (Z d.radical a) P
    rw [conjugateSpanBy_eq_iSup_conj]
    simp only [v,Z_act,inv_inv]
  have hak : Adjacent d.radical a k := by
    apply (adjacent_act_iff d.radical y⁻¹ _ _).mpr
    apply (cosetGraph_adj d.radical _ _).mp
    simpa only [SimpleGraph.Walk.getVert_zero] using p.walk.adj_getVert_succ (i := 0)
      (by have hl : p.walk.length = replacementDistance h d := p.length_eq_b; omega)
  have hDV : D ≤ V d.radical c :=
    conjugateSpanBy_le hZaVc (inf_le_left.trans (V_normalized c))
  have hDB : ¬ D ≤ B d.radical c ((replacementGeometry h d).Z_normal _) :=
    fun hh => hZaBc ((le_conjugateSpanBy (Z d.radical a) P).trans hh)
  have hh := common_edge_family_central_line s hc (by omega) u hfull'.le q hct hQtgen
    v ks (fun x => by simp only [v,a,action_preserves_color]; rfl)
    (fun x => (adjacent_act_iff d.radical _ _ _).mpr hak)
    (fun x => hall x x.property)
    (by rwa [hD]) (by rw [hD,hpre]; exact hZspanQ)
    (by rwa [hD]) (by rwa [hD])
  rw [hD] at hh
  obtain ⟨hidx,hJcard,hJZ,hJG,hJcrit⟩ := hh
  let K := Z d.radical z ⊓ Q d.radical c
  let J := ⁅D,K⁆
  have hZzG : Z d.radical z ≤ stabilizer d.radical c :=
    critical_Z_le_stabilizer d.radical (replacementGeometry h d) c q.start_color (by
      rw [(replacementGeometry h d).distance_constant c q.start_color]
      exact replacementDistance_pos h d) q.critical
  have hJcore : J ≤ fixedCore d.radical c := by
    refine le_inf ?_ (hJG.trans (centralizer_le (Ltilde_le_stabilizer c)))
    rw [←C_eq_Q s hc c q.start_color]
    exact le_inf (hJZ.trans hZzG) (hJG.trans (centralizer_le (Z_le_stabilizer d.radical c)))
  have hJseed : J ≤ Z d.radical a := by
    apply central_span_line_le_seed (Z d.radical a) P K hJcard
      (hJG.trans (centralizer_le inf_le_left))
    intro x
    have hvk := (adjacent_act_iff d.radical (x : FreeAmalgam d.radical)⁻¹ a k).mpr hak
    have hnormK : K ≤ stabilizer d.radical (v x) := by
      have ht : color d.radical t = true := by
        have hh := adjacent_color_ne d.radical hct
        rw [q.start_color] at hh
        cases he : color d.radical t <;> simp_all
      have hKt : K ≤ Q d.radical t := inf_le_right.trans (Q_le_adjacent_h d.radical ht hct)
      rw [←hall x x.property] at hKt
      exact hKt.trans (fun _ hx => hx.2 _ (adjacent_symm d.radical hvk))
    have he : Z d.radical (v x) = (Z d.radical a).map (MulAut.conj (x : FreeAmalgam d.radical)).toMonoidHom := by
      simp only [v,Z_act,inv_inv]
    rw [←he]
    exact hnormK.trans (Z_normalized d.radical (v x))
  have hJne : J ≠ H₂ := by
    intro he
    apply hHmove
    change H₂ ≤ centralizer (Z d.radical z : Set (FreeAmalgam d.radical))
    rw [←he]
    exact hJG.trans (centralizer_le hZzG)
  obtain ⟨x,hx⟩ := exists_span_line_generator (Z d.radical a) P K hJcard
  exact ⟨z,q,haz,hover,hpre,t,hct,hQtgen,y,hy,hHseed,hPgen,hHmove,hZspanQ,
    hidx,hJcard,hJZ,hJG,hJcrit,hJcore,hJseed,hJne,x,x.property,hx⟩

end AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
