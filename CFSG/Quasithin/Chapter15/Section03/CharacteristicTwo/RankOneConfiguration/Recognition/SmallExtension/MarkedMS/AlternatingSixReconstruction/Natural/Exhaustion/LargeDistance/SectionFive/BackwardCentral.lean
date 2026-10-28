module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.BackwardNonzero

/-!
# Centrality of the eligible backward line

In the full-point branch, failure of backward escape leaves seed index two.
The part of the backward seed fixed by the full reverse critical kernel lies
in the starting Baumann slice: its product with the starting seed is normalized
by the generating edge and the opposite critical seed. The inverse movement
bound then identifies the moving slice with that fixed subgroup, without an
assumed slice index.

The slice centralizer in the starting two-core is normal in the starting
stabilizer and contains both the predecessor seed and the full reverse kernel.
Its commutator with the backward cover has order at most two and lies in the
common edge seed. If that line were noncentral at the start, the full-seed
conjugate generator and the controlled-line argument would force the eligible
cover into the Baumann slice. Thus the nonzero backward-kernel commutator is
exactly this central line. It remains noncentral at the backward vertex.

The final application constructs the generating edge and eligible vertex on
the actual characteristic replacement under failure of radius escape. Both
central covers and the full reverse kernel are retained; the central line of
the order-32 cover is never discarded.

Source: Meierfrankenfeld--Stellmacher (1993), (5.7)--(5.8), printed pp.919--920,
and the full-seed controlled-line argument in (5.9), pp.920--922.
Containment of the reverse kernel in the predecessor Baumann slice is a
different assertion and remains unproved. The remaining radical-image cases,
exact-four exclusion, intermediate R4/R6 noncentrality, both terminal
contradictions, largeDistance_knownSimple and unconditional replacementDistance
= 2 remain with qt-e-ms-small-a6-exhaustion-large-distance. Final whole-core
reconstruction remains with qt-e-ms-small-a6-reconstruction.
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

private theorem abelian_action_preserves_fixed {H : Type*} [Group H]
    (P V A : Subgroup H) (hPV : P ≤ normalizer (V : Set H)) (hA : A ≤ P)
    (hcom : ⁅P,P⁆ ≤ centralizer (V : Set H)) :
    P ≤ normalizer ((V ⊓ centralizer (A : Set H) : Subgroup H) : Set H) := by
  let f : P →* MulAut V := V.normalizerMonoidHom.comp (inclusion hPV)
  have hf (p q : P) : Commute (f p) (f q) := by
    apply commutatorElement_eq_one_iff_mul_comm.mp
    rw [←map_commutatorElement]
    ext v
    change ⁅(p:H),(q:H)⁆*(v:H)*⁅(p:H),(q:H)⁆⁻¹ = (v:H)
    rw [←hcom (commutator_mem_commutator p.property q.property) v v.property,mul_inv_cancel_right]
  apply le_normalizer_iff.mpr
  intro g hg v hv
  have hgv : g*v*g⁻¹ ∈ V := (mem_normalizer_iff.mp (hPV hg) v).mp hv.1
  refine ⟨hgv,?_⟩
  intro a ha
  have hvfix : f ⟨a,hA ha⟩ ⟨v,hv.1⟩ = (⟨v,hv.1⟩:V) := by
    apply Subtype.ext
    change a*v*a⁻¹ = v
    rw [hv.2 a ha,mul_inv_cancel_right]
  have hh := DFunLike.congr_fun (hf ⟨a,hA ha⟩ ⟨g,hg⟩).eq (⟨v,hv.1⟩:V)
  change f ⟨a,hA ha⟩ (f ⟨g,hg⟩ ⟨v,hv.1⟩) = f ⟨g,hg⟩ (f ⟨a,hA ha⟩ ⟨v,hv.1⟩) at hh
  rw [hvfix] at hh
  have he : a*(g*v*g⁻¹)*a⁻¹ = g*v*g⁻¹ := congrArg Subtype.val hh
  exact mul_inv_eq_iff_eq_mul.mp he

include s in
private theorem edge_preserves_seed_fixer (u : Equiv.Perm (Fin 6))
    (hR : d.radical.map s.projection ≤ pointCore.map (MulAut.conj u).toMonoidHom)
    {c t : Vertex d.radical} (hcol : color d.radical c = false)
    (hct : Adjacent d.radical c t)
    (A : Subgroup (FreeAmalgam d.radical)) (hA : A ≤ Q d.radical t) :
    Q d.radical t ≤ normalizer ((Z d.radical c ⊓ centralizer
      (A : Set (FreeAmalgam d.radical)) : Subgroup (FreeAmalgam d.radical)) : Set (FreeAmalgam d.radical)) := by
  let := pointCore_elementary
  let : IsElementaryAbelian 2 (pointCore.map (MulAut.conj u).toMonoidHom) := IsElementaryAbelian.map _
  let helem : IsElementaryAbelian 2 (d.radical.map s.projection) := IsElementaryAbelian.of_le hR
  have hbase : ⁅Q d.radical (beta d.radical),Q d.radical (beta d.radical)⁆ ≤
      Q d.radical (alpha d.radical) := by
    rw [Q_beta,Q_alpha d.radical (replacement_radical_isPGroup h d)
      (replacement_core_le_radical h d),←map_commutator]
    apply map_mono
    rw [←s.projection_kernel,←Subgroup.map_eq_bot_iff,map_commutator]
    exact commutator_eq_bot_iff_le_centralizer.mpr
      (le_centralizer_iff_isMulCommutative.mpr helem.toIsMulCommutative)
  have hderived : ⁅Q d.radical t,Q d.radical t⁆ ≤ Q d.radical c := by
    obtain ⟨g,hg|hg⟩ := (adjacent_iff_exists_common d.radical c t).mp hct
    · rcases hg with ⟨rfl,rfl⟩
      have hh := map_mono (f := (MulAut.conj g⁻¹).toMonoidHom) hbase
      rw [map_commutator,←Q_act,←Q_act] at hh
      simpa only [alpha,beta,act_mVertex,act_hVertex,one_mul] using hh
    · rw [hg.1] at hcol
      cases hcol
  have htG : Q d.radical t ≤ stabilizer d.radical c := fun _ hx => hx.2 _ (adjacent_symm d.radical hct)
  exact abelian_action_preserves_fixed _ _ A (htG.trans (Z_normalized d.radical c)) hA
    (hderived.trans (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp
      (Z_centralizes_Q d.radical c hcol))))

include s in
/-- The full backward seed fixed by the reverse kernel lies in the starting Baumann slice. -/
theorem backward_seed_fixer_le_slice (hc : DistanceTwo.CentralLayer d)
    (hb : 2 < replacementDistance h d) (u : Equiv.Perm (Fin 6))
    (hR : d.radical.map s.projection ≤ pointCore.map (MulAut.conj u).toMonoidHom)
    {a' c t : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) a')
    (hsmall : (Q d.radical a').relIndex (Z d.radical (alpha d.radical)) < 4)
    (hat : Adjacent d.radical (alpha d.radical) t) (hct : Adjacent d.radical c t)
    (hgen : Q d.radical t ⊔ Z d.radical a' = stabilizer d.radical (alpha d.radical))
    (hbad : Z d.radical c ≤ Q d.radical (p.walk.getVert (p.walk.length-2))) :
    Z d.radical c ⊓ centralizer
      (Z d.radical a' ⊓ Q d.radical (alpha d.radical) : Set (FreeAmalgam d.radical)) ≤
        B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _) := by
  let K := Z d.radical a' ⊓ Q d.radical (alpha d.radical)
  let F := Z d.radical c ⊓ centralizer (K : Set (FreeAmalgam d.radical))
  let Y := F ⊔ Z d.radical (alpha d.radical)
  have hl : 2 < p.walk.length := p.length_eq_b ▸ hb
  have hcol : color d.radical c = false := by
    have h1 := adjacent_color_ne d.radical hat
    have h2 := adjacent_color_ne d.radical hct
    change false ≠ color d.radical t at h1
    cases hc : color d.radical c <;> cases ht : color d.radical t <;> simp_all
  have ht : color d.radical t = true := by
    have hh := adjacent_color_ne d.radical hat
    change false ≠ color d.radical t at hh
    cases he : color d.radical t <;> simp_all
  have hdist : (cosetGraph d.radical).dist c (alpha d.radical) ≤ 2 := by
    have h1 : (cosetGraph d.radical).dist c t = 1 :=
      SimpleGraph.dist_eq_one_iff_adj.mpr ((cosetGraph_adj d.radical _ _).mpr hct)
    have h2 : (cosetGraph d.radical).dist t (alpha d.radical) = 1 :=
      SimpleGraph.dist_eq_one_iff_adj.mpr ((cosetGraph_adj d.radical _ _).mpr (adjacent_symm d.radical hat))
    simpa only [h1,h2] using (cosetGraph_connected d.radical).dist_triangle
      (u := c) (v := t) (w := alpha d.radical)
  have hZV : Z d.radical c ≤ V d.radical (alpha d.radical) :=
    (Z_le_localZSpan d.radical _ _).trans (localZSpan_le_V d.radical hdist)
  have hFt := edge_preserves_seed_fixer s u hR hcol hct K
    (inf_le_right.trans (Q_le_adjacent_h d.radical ht hat))
  have hmove : ⁅F,Z d.radical a'⁆ ≤ Z d.radical (alpha d.radical) :=
    small_critical_predecessor_commutator s hc hb p hsmall F
      (inf_le_left.trans hbad) inf_le_right
  have hYmove : ⁅Y,Z d.radical a'⁆ ≤ Z d.radical (alpha d.radical) :=
    commutator_sup_le_of_relative_normal (stabilizer d.radical (alpha d.radical))
      F (Z d.radical (alpha d.radical)) (Z d.radical a') (Z d.radical (alpha d.radical))
      (Z_normalized d.radical _) ((inf_le_left.trans hZV).trans
        ((replacementGeometry h d).V_local _ rfl hb)) (Z_le_stabilizer d.radical _) hmove
      (((critical_Z_commutator_le_moving (h := h) p).trans inf_le_left).trans (DistanceEight.U_le_Z d.radical _))
  have hYn : stabilizer d.radical (alpha d.radical) ≤ normalizer (Y : Set (FreeAmalgam d.radical)) := by
    rw [←hgen]
    apply sup_le
    · exact (le_inf hFt ((show Q d.radical t ≤ stabilizer d.radical (alpha d.radical) from
        fun _ hx => hx.2 _ (adjacent_symm d.radical hat)).trans (Z_normalized d.radical _))).trans
          (normalizer_inf_normalizer_le_normalizer_sup _ _)
    · exact le_normalizer_iff_commutator_le_left.mpr (hYmove.trans le_sup_right)
  have hFB : F ≤ B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _) :=
    le_sup_left.trans (normalized_radius_le_slice_of_critical_commutator s hc hb p Y
      (sup_le (inf_le_left.trans hZV) (Z_le_VBall d.radical _ 2)) hYn hYmove)
  exact hFB
include s in
/-- Every two-edge slice of index at most two gives a kernel commutator in the common edge seed, of order at most two. -/
theorem edge_slice_kernel_line (hc : DistanceTwo.CentralLayer d)
    (hb : 2 < replacementDistance h d)
    {c t : Vertex d.radical}
    (hat : Adjacent d.radical (alpha d.radical) t) (hct : Adjacent d.radical c t)
    (hslice : (B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _)).relIndex
      (U d.radical c) ≤ 2) :
    let T := Q d.radical (alpha d.radical) ⊓ centralizer
      (U d.radical c ⊓ B d.radical (alpha d.radical)
        ((replacementGeometry h d).Z_normal _) : Set (FreeAmalgam d.radical))
    Nat.card (⁅U d.radical c,T⁆ : Subgroup (FreeAmalgam d.radical)) ≤ 2 ∧
      ⁅U d.radical c,T⁆ ≤ Z d.radical t := by
  let K := U d.radical c ⊓ B d.radical (alpha d.radical)
    ((replacementGeometry h d).Z_normal _)
  let T := Q d.radical (alpha d.radical) ⊓ centralizer (K : Set (FreeAmalgam d.radical))
  let H := ⁅U d.radical c,T⁆
  have hcol : color d.radical c = false := by
    have h1 := adjacent_color_ne d.radical hat
    have h2 := adjacent_color_ne d.radical hct
    change false ≠ color d.radical t at h1
    cases hc : color d.radical c <;> cases ht : color d.radical t <;> simp_all
  have ht : color d.radical t = true := by
    have hh := adjacent_color_ne d.radical hat
    change false ≠ color d.radical t at hh
    cases he : color d.radical t <;> simp_all
  have hTG : T ≤ stabilizer d.radical c :=
    (inf_le_left.trans (Q_le_adjacent_h d.radical ht hat)).trans
      (fun _ hx => hx.2 _ (adjacent_symm d.radical hct))
  let := finite_Z d.radical c
  let : Finite (U d.radical c) := Finite.of_injective
    (inclusion (DistanceEight.U_le_Z d.radical c)) (inclusion_injective _)
  have hfix : K ≤ centralizer (T : Set (FreeAmalgam d.radical)) :=
    le_centralizer_iff.mp inf_le_right
  have hidx : (centralizer (T : Set (FreeAmalgam d.radical))).relIndex (U d.radical c) ≤ 2 := by
    have hh := relIndex_le_of_le_left hfix (index_ne_zero_of_finite (H := K.subgroupOf (U d.radical c)))
    change (centralizer (T : Set (FreeAmalgam d.radical))).relIndex (U d.radical c) ≤
      K.relIndex (U d.radical c) at hh
    exact hh.trans (by simpa only [K,inf_relIndex_left] using hslice)
  have hcard : Nat.card H ≤ 2 := moving_small_fixed_commutator_card s hc hcol T hTG hidx
  have hTN : stabilizer d.radical (alpha d.radical) ≤ normalizer (T : Set (FreeAmalgam d.radical)) :=
    selected_forward_kernel_normalized hb rfl hat hct
  have htGa : Q d.radical t ≤ stabilizer d.radical (alpha d.radical) :=
    fun _ hx => hx.2 _ (adjacent_symm d.radical hat)
  have htGc : Q d.radical t ≤ stabilizer d.radical c :=
    fun _ hx => hx.2 _ (adjacent_symm d.radical hct)
  have hHN : Q d.radical t ≤ normalizer (H : Set (FreeAmalgam d.radical)) := by
    intro x hx
    rw [mem_normalizer_iff_map_conj_eq]
    change H.map (MulAut.conj x).toMonoidHom = H
    dsimp only [H]
    have hUm : (U d.radical c).map (MulAut.conj x).toMonoidHom = U d.radical c :=
      mem_normalizer_iff_map_conj_eq.mp (U_normalized c (htGc hx))
    have hTm : T.map (MulAut.conj x).toMonoidHom = T :=
      mem_normalizer_iff_map_conj_eq.mp (hTN (htGa hx))
    rw [map_commutator,hUm,hTm]
  have hHU : H ≤ U d.radical c :=
    le_normalizer_iff_commutator_le_left.mp (hTG.trans (U_normalized c))
  let : Finite H := Finite.of_injective (inclusion hHU) (inclusion_injective _)
  have hHC : H ≤ centralizer (Q d.radical t : Set (FreeAmalgam d.radical)) := by
    by_cases he : H = ⊥
    · rw [he]; exact bot_le
    · have hh := (one_lt_card_iff_ne_bot H).mpr he
      exact le_centralizer_iff.mp (hHN.trans
        (normalizer_le_centralizer_of_card_two H (by omega)))
  have hUQ : U d.radical c ≤ Q d.radical c :=
    (DistanceEight.U_le_Z d.radical c).trans (by
      apply Z_le_Q_of_dist_lt d.radical c ((replacementGeometry h d).exists_critical c hcol)
      rw [SimpleGraph.dist_self,(replacementGeometry h d).distance_constant c hcol]
      exact replacementDistance_pos h d)
  let := (replacementGeometry h d).Z_elementary (replacementDistance_pos h d) c hcol
  refine ⟨hcard,?_⟩
  intro x hx
  rw [Z,if_neg (by simp [ht])]
  exact mem_omegaCenter_iff.mpr
    ⟨(hHU.trans (hUQ.trans (Q_le_adjacent_h d.radical ht hct))) hx,
      elemPow_eq_one_of_isElementaryAbelian x ((hHU.trans (DistanceEight.U_le_Z d.radical c)) hx),
      hHC hx⟩
include s in
/-- The eligible backward Baumann slice is exactly the fixed subgroup of
 the full reverse kernel. Eligibility and failure of backward escape supply
 both index-two bounds; no numerical slice premise is assumed. -/
theorem eligible_backward_slice_eq_fixer
    (hc : DistanceTwo.CentralLayer d) (hb : 2 < replacementDistance h d)
    (u : Equiv.Perm (Fin 6))
    (hR : d.radical.map s.projection ≤ pointCore.map (MulAut.conj u).toMonoidHom)
    {a' c t : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) a')
    (hat : Adjacent d.radical (alpha d.radical) t) (hct : Adjacent d.radical c t)
    (hgen : Q d.radical t ⊔ Z d.radical a' = stabilizer d.radical (alpha d.radical))
    (hel : ¬ U d.radical c ≤ B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _))
    (hbad : Z d.radical c ≤ Q d.radical (p.walk.getVert (p.walk.length-2))) :
    U d.radical c ⊓ B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _) =
      U d.radical c ⊓ centralizer
        (Z d.radical a' ⊓ Q d.radical (alpha d.radical) : Set (FreeAmalgam d.radical)) := by
  let K := Z d.radical a' ⊓ Q d.radical (alpha d.radical)
  let E := U d.radical c ⊓ B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _)
  let F := U d.radical c ⊓ centralizer (K : Set (FreeAmalgam d.radical))
  have hl := eligible_backward_failure_line s hc hb u hR p hat hct hgen hel hbad
  have hs : (Q d.radical a').relIndex (Z d.radical (alpha d.radical)) < 4 := by omega
  have hFB := backward_seed_fixer_le_slice s hc hb u hR p hs hat hct hgen hbad
  have hFE : F ≤ E := le_inf inf_le_left
    ((inf_le_inf_right _ (DistanceEight.U_le_Z d.radical c)).trans hFB)
  have ht : color d.radical t = true := by
    have hh := adjacent_color_ne d.radical hat
    change false ≠ color d.radical t at hh
    cases he : color d.radical t <;> simp_all
  have hcol : color d.radical c = false := by
    have hh := adjacent_color_ne d.radical hct
    rw [ht] at hh
    cases he : color d.radical c <;> simp_all
  have hKG : K ≤ stabilizer d.radical c :=
    (inf_le_right.trans (Q_le_adjacent_h d.radical ht hat)).trans
      (fun _ hx => hx.2 _ (adjacent_symm d.radical hct))
  let H := ⁅K,Z d.radical c⁆
  let : Finite H := Nat.finite_of_card_ne_zero (by have hh : Nat.card H = 2 := hl.2.2.1; omega)
  have hcard : Nat.card (⁅U d.radical c,K⁆ : Subgroup (FreeAmalgam d.radical)) ≤ 2 := by
    have hh : ⁅U d.radical c,K⁆ ≤ H := by
      rw [commutator_comm]
      exact commutator_mono le_rfl (DistanceEight.U_le_Z d.radical c)
    exact (card_le_of_le hh).trans_eq hl.2.2.1
  have hidx := moving_small_commutator_fixed_index s hc hcol K hKG hcard
  let := finite_Z d.radical c
  let : Finite (U d.radical c) := Finite.of_injective
    (inclusion (DistanceEight.U_le_Z d.radical c)) (inclusion_injective _)
  let : Finite E := Finite.of_injective (inclusion (show E ≤ U d.radical c from inf_le_left))
    (inclusion_injective _)
  have hF : F.relIndex (U d.radical c) ≤ 2 := by simpa only [F,inf_relIndex_left] using hidx
  have hE : E.relIndex (U d.radical c) = 2 := by simpa only [E,inf_relIndex_left] using hl.2.1
  have hm := relIndex_mul_relIndex F E (U d.radical c) hFE inf_le_left
  have hp : 0 < F.relIndex E := Nat.pos_of_ne_zero index_ne_zero_of_finite
  rw [hE] at hm
  have hi : F.relIndex E = 1 := by omega
  exact le_antisymm (relIndex_eq_one.mp hi) hFE

include s in
private theorem backward_slice_line_central_of_inner
    (hlayer : DistanceTwo.CentralLayer d)
    (hb : 2 < replacementDistance h d) {a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) a')
    (hsmall : (Q d.radical a').relIndex (Z d.radical (alpha d.radical)) < 4)
    {c t : Vertex d.radical}
    (hat : Adjacent d.radical (alpha d.radical) t) (hct : Adjacent d.radical c t)
    (hslice : (B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _)).relIndex
      (U d.radical c) ≤ 2)
    (hinner : Z d.radical (p.walk.getVert (p.walk.length-2)) ⊔ (Z d.radical a' ⊓ Q d.radical (alpha d.radical)) ≤
      Q d.radical (alpha d.radical) ⊓ centralizer
        (U d.radical c ⊓ B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _) : Set (FreeAmalgam d.radical))) :
    ⁅U d.radical c,Q d.radical (alpha d.radical) ⊓ centralizer
      (U d.radical c ⊓ B d.radical (alpha d.radical)
        ((replacementGeometry h d).Z_normal _) : Set (FreeAmalgam d.radical))⁆ ≤
      centralizer (stabilizer d.radical (alpha d.radical) : Set (FreeAmalgam d.radical)) := by
  let T := Q d.radical (alpha d.radical) ⊓ centralizer
    (U d.radical c ⊓ B d.radical (alpha d.radical)
      ((replacementGeometry h d).Z_normal _) : Set (FreeAmalgam d.radical))
  let H := ⁅U d.radical c,T⁆
  change H ≤ centralizer (stabilizer d.radical (alpha d.radical) : Set (FreeAmalgam d.radical))
  by_contra hnon
  have hne : H ≠ ⊥ := by intro he; exact hnon (he ▸ bot_le)
  have hline := edge_slice_kernel_line s hlayer hb hat hct hslice
  have hHZ : H ≤ Z d.radical (alpha d.radical) :=
    hline.2.trans (adjacent_Z_le d.radical rfl hat)
  let := finite_Z d.radical (alpha d.radical)
  let : Finite H := Finite.of_injective (inclusion hHZ) (inclusion_injective _)
  have hcard : Nat.card H = 2 := by
    have hp := (one_lt_card_iff_ne_bot H).mpr hne
    have hh : Nat.card H ≤ 2 := hline.1
    omega
  have hUB : ¬ U d.radical c ≤ B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _) := by
    intro hh
    apply hne
    apply commutator_eq_bot_iff_le_centralizer.mpr
    apply le_centralizer_iff.mp
    intro x hx y hy
    exact hx.2 y ⟨hy,hh hy⟩
  have hdist : (cosetGraph d.radical).dist c (alpha d.radical) ≤ 2 := by
    have h1 : (cosetGraph d.radical).dist c t = 1 :=
      SimpleGraph.dist_eq_one_iff_adj.mpr ((cosetGraph_adj d.radical _ _).mpr hct)
    have h2 : (cosetGraph d.radical).dist t (alpha d.radical) = 1 :=
      SimpleGraph.dist_eq_one_iff_adj.mpr ((cosetGraph_adj d.radical _ _).mpr (adjacent_symm d.radical hat))
    simpa only [h1,h2] using (cosetGraph_connected d.radical).dist_triangle
      (u := c) (v := t) (w := alpha d.radical)
  have hUV : U d.radical c ≤ V d.radical (alpha d.radical) :=
    (DistanceEight.U_le_Z d.radical c).trans
      ((Z_le_localZSpan d.radical c (alpha d.radical)).trans (localZSpan_le_V d.radical hdist))
  have hTN : stabilizer d.radical (alpha d.radical) ≤ normalizer (T : Set (FreeAmalgam d.radical)) :=
    selected_forward_kernel_normalized hb rfl hat hct
  obtain ⟨g,hg,hgen,hmove⟩ := exists_seed_line_generator s hlayer p hsmall H hHZ hcard hnon
  have hgG := Ltilde_le_stabilizer (alpha d.radical) hg
  let f := (MulAut.conj g).toMonoidHom
  let A := (U d.radical c).map f
  let J := H.map f
  have hVm : (V d.radical (alpha d.radical)).map f = V d.radical (alpha d.radical) :=
    mem_normalizer_iff_map_conj_eq.mp (DistanceEight.V_normalized d.radical _ hgG)
  have hBm : (B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _)).map f =
      B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _) :=
    mem_normalizer_iff_map_conj_eq.mp (Escape.Propagation.Rigidity.B_normalized hb _ rfl hgG)
  have hTm : T.map f = T := mem_normalizer_iff_map_conj_eq.mp (hTN hgG)
  have hZm : (Z d.radical (alpha d.radical)).map f = Z d.radical (alpha d.radical) :=
    mem_normalizer_iff_map_conj_eq.mp (Z_normalized d.radical _ hgG)
  have hAV : A ≤ V d.radical (alpha d.radical) := hVm ▸ map_mono hUV
  have hAB : ¬ A ≤ B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _) := by
    intro hh
    apply hUB
    apply (map_le_map_iff_of_injective (f := f) (MulAut.conj g).injective).mp
    rwa [hBm]
  have hJZ : J ≤ Z d.radical (alpha d.radical) := hZm ▸ map_mono hHZ
  have hJcard : Nat.card J ≤ 2 := by
    rw [show Nat.card J = Nat.card H from card_map_of_injective (MulAut.conj g).injective,hcard]
  have hcomm : ⁅A,T⁆ ≤ J := by
    change ⁅(U d.radical c).map f,T⁆ ≤ H.map f
    rw [show H = ⁅U d.radical c,T⁆ from rfl,map_commutator,hTm]
  exact small_critical_controlled_line_false s hlayer hb p hsmall A T J
    hAV hAB inf_le_left hTN hJZ hJcard hmove hgen hcomm
    hinner
include h e hz in
private theorem edge_seed_commutator_eq_moving
    {c t : Vertex d.radical} (hcol : color d.radical c = false)
    (hct : Adjacent d.radical c t)
    (D : Subgroup (FreeAmalgam d.radical)) (hD : D ≤ Q d.radical t) :
    ⁅Z d.radical c,D⁆ = ⁅U d.radical c,D⁆ := by
  have ht : color d.radical t = true := by
    have hh := adjacent_color_ne d.radical hct
    rw [hcol] at hh
    cases he : color d.radical t <;> simp_all
  have hseed : Z d.radical t ≤ centralizer (Q d.radical t : Set (FreeAmalgam d.radical)) := by
    intro x hx
    rw [Z,if_neg (by simp [ht])] at hx
    exact (mem_omegaCenter_iff.mp hx).2.2
  have hn : Z d.radical t ≤ normalizer (U d.radical c : Set (FreeAmalgam d.radical)) :=
    ((adjacent_Z_le d.radical hcol hct).trans (Z_le_stabilizer d.radical c)).trans (U_normalized c)
  apply le_antisymm _ (commutator_mono (DistanceEight.U_le_Z d.radical c) le_rfl)
  rw [DistanceTwo.CentralLayer.Z_eq_moving_sup_edge_at h e hz d hcol hct]
  apply commutator_le.mpr
  intro x hx r hr
  have hp : x ∈ (U d.radical c : Set (FreeAmalgam d.radical)) *
      (Z d.radical t : Set (FreeAmalgam d.radical)) := by
    rw [←coe_mul_of_right_le_normalizer_left (U d.radical c) (Z d.radical t) hn]
    exact hx
  obtain ⟨w,hw,z,hz,rfl⟩ := hp
  have hzero : ⁅z,r⁆ = 1 := commutatorElement_eq_one_iff_mul_comm.mpr (hseed hz r (hD hr)).symm
  rw [commutatorElement_mul_left_eq_conj_mul,hzero,mul_one,mul_inv_cancel,one_mul]
  exact commutator_mem_commutator hw hr

include s in
/-- The eligible backward line is central at the original starting vertex
and is precisely the full commutator of the backward cover with its slice
kernel. It lies in the actual common edge seed. The full reverse kernel,
both cover orders, and the chosen generating edge are retained. -/
theorem eligible_backward_line_central
    (hc : DistanceTwo.CentralLayer d) (hb : 2 < replacementDistance h d)
    (u : Equiv.Perm (Fin 6))
    (hR : d.radical.map s.projection ≤ pointCore.map (MulAut.conj u).toMonoidHom)
    {a' c t : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) a')
    (hat : Adjacent d.radical (alpha d.radical) t) (hct : Adjacent d.radical c t)
    (hgen : Q d.radical t ⊔ Z d.radical a' = stabilizer d.radical (alpha d.radical))
    (hel : ¬ U d.radical c ≤ B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _))
    (hbad : Z d.radical c ≤ Q d.radical (p.walk.getVert (p.walk.length-2))) :
    let K := Z d.radical a' ⊓ Q d.radical (alpha d.radical)
    let T := Q d.radical (alpha d.radical) ⊓ centralizer
      (U d.radical c ⊓ B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _) : Set (FreeAmalgam d.radical))
    ⁅K,Z d.radical c⁆ = ⁅U d.radical c,T⁆ ∧
      ⁅K,Z d.radical c⁆ ≤ Z d.radical t ∧
      ⁅K,Z d.radical c⁆ ≤ centralizer
        (stabilizer d.radical (alpha d.radical) : Set (FreeAmalgam d.radical)) := by
  let K := Z d.radical a' ⊓ Q d.radical (alpha d.radical)
  let E := U d.radical c ⊓ B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _)
  let T := Q d.radical (alpha d.radical) ⊓ centralizer (E : Set (FreeAmalgam d.radical))
  let H := ⁅U d.radical c,T⁆
  have hl := eligible_backward_failure_line s hc hb u hR p hat hct hgen hel hbad
  have hs : (Q d.radical a').relIndex (Z d.radical (alpha d.radical)) < 4 := by omega
  have heq := eligible_backward_slice_eq_fixer s hc hb u hR p hat hct hgen hel hbad
  have hKT : K ≤ T := le_inf inf_le_right (le_centralizer_iff.mp (by
    change U d.radical c ⊓ B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _) ≤ _
    rw [heq]
    exact inf_le_right))
  have hcol : color d.radical c = false := by
    have h1 := adjacent_color_ne d.radical hat
    have h2 := adjacent_color_ne d.radical hct
    change false ≠ color d.radical t at h1
    cases hc : color d.radical c <;> cases ht : color d.radical t <;> simp_all
  have ht : color d.radical t = true := by
    have hh := adjacent_color_ne d.radical hct
    rw [hcol] at hh
    cases he : color d.radical t <;> simp_all
  have hpred : color d.radical (p.walk.getVert (p.walk.length-2)) = false := by
    apply (p.vertex_color (Nat.sub_le _ _)).mpr
    have he := replacementDistance_even h d
    rw [Nat.even_iff] at he ⊢
    have hh : p.walk.length = replacementDistance h d := p.length_eq_b
    omega
  have hpreQ : Z d.radical (p.walk.getVert (p.walk.length-2)) ≤ Q d.radical (alpha d.radical) := by
    apply Z_le_Q_of_dist_lt d.radical _ ((replacementGeometry h d).exists_critical _ hpred)
    rw [SimpleGraph.dist_comm,(replacementGeometry h d).distance_constant _ hpred,
      p.dist_start (Nat.sub_le _ _)]
    have hh : p.walk.length = replacementDistance h d := p.length_eq_b
    change p.walk.length-2 < replacementDistance h d
    omega
  have hinner : Z d.radical (p.walk.getVert (p.walk.length-2)) ⊔ K ≤ T := by
    apply sup_le _ hKT
    exact le_inf hpreQ ((commutator_eq_bot_iff_le_centralizer.mp
      (Z_centralizes_Q d.radical _ hpred)).trans
        (centralizer_le ((inf_le_left.trans (DistanceEight.U_le_Z d.radical c)).trans hbad)))
  have hindex : (B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _)).relIndex
      (U d.radical c) ≤ 2 := hl.2.1.le
  have hline := edge_slice_kernel_line s hc hb hat hct hindex
  have hcentral := backward_slice_line_central_of_inner s hc hb p hs hat hct hindex hinner
  have hRle : ⁅K,Z d.radical c⁆ ≤ H := by
    rw [commutator_comm,edge_seed_commutator_eq_moving (h := h) (e := e) (hz := hz)
      hcol hct K (inf_le_right.trans (Q_le_adjacent_h d.radical ht hat))]
    exact commutator_mono le_rfl hKT
  let := finite_Z d.radical t
  let : Finite H := Finite.of_injective (inclusion hline.2) (inclusion_injective _)
  have hsame : ⁅K,Z d.radical c⁆ = H := eq_of_le_of_card_ge hRle (by
    have hh : Nat.card (⁅K,Z d.radical c⁆ : Subgroup (FreeAmalgam d.radical)) = 2 := hl.2.2.1
    have hH : Nat.card H ≤ 2 := hline.1
    omega)
  exact ⟨hsame,hRle.trans hline.2,hRle.trans hcentral⟩

/-- The full-point replacement constructs the actual generating edge and
eligible backward vertex. Failure of radius escape identifies its slice
and gives a line central at the start and noncentral at the backward vertex,
without assuming either slice placement or commutator centrality. -/
theorem radius_failure_central_backward_line_knownSimple
    {h : SmallMSPair KnownSimple.IsKnownSimple L R} {e : CentralMarking L}
    {hz : center (L ⧸ pCore 2 L) = ⊥} {hn : InitialNatural h e hz}
    {d : Replacement L R} (hb : 2 < replacementDistance h d)
    (u : Equiv.Perm (Fin 6))
    (hfull : d.radical.map (SourceReduction.projection h e hz hn d) =
      pointCore.map (MulAut.conj u).toMonoidHom)
    {a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) a')
    (hbad : V d.radical (alpha d.radical) ≤ Q d.radical (p.walk.getVert (p.walk.length-2))) :
    ∃ t c, Adjacent d.radical (alpha d.radical) t ∧ Adjacent d.radical c t ∧
      Q d.radical t ⊔ Z d.radical a' = stabilizer d.radical (alpha d.radical) ∧
      (Q d.radical a').relIndex (Z d.radical (alpha d.radical)) = 2 ∧
      (B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _)).relIndex
        (U d.radical c) = 2 ∧
      U d.radical c ⊓ B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _) =
        U d.radical c ⊓ centralizer
          (Z d.radical a' ⊓ Q d.radical (alpha d.radical) : Set (FreeAmalgam d.radical)) ∧
      Nat.card (⁅Z d.radical a' ⊓ Q d.radical (alpha d.radical),Z d.radical c⁆ :
        Subgroup (FreeAmalgam d.radical)) = 2 ∧
      ⁅Z d.radical a' ⊓ Q d.radical (alpha d.radical),Z d.radical c⁆ ≤ Z d.radical t ∧
      ⁅Z d.radical a' ⊓ Q d.radical (alpha d.radical),Z d.radical c⁆ ≤
        centralizer (stabilizer d.radical (alpha d.radical) : Set (FreeAmalgam d.radical)) ∧
      ¬ ⁅Z d.radical a' ⊓ Q d.radical (alpha d.radical),Z d.radical c⁆ ≤
        centralizer (stabilizer d.radical c : Set (FreeAmalgam d.radical)) := by
  let s := fullSymmetricAction_knownSimple h e hz hn d hb
  have hc := DistanceTwo.centralLayer_knownSimple G L R h e hz hn d
  have hfull' : d.radical.map s.projection = pointCore.map (MulAut.conj u).toMonoidHom := by
    rwa [SourceReduction.fullSymmetricAction_projection_unique h e hz hn d s]
  obtain ⟨t,hat,hgen⟩ := full_point_generating_neighbor s hc u hfull' p
  obtain ⟨c,hct,hel⟩ := exists_eligible_neighbor_at_edge s hc hb rfl hat
  have hdist : (cosetGraph d.radical).dist c (alpha d.radical) ≤ 2 := by
    have h1 : (cosetGraph d.radical).dist c t = 1 :=
      SimpleGraph.dist_eq_one_iff_adj.mpr ((cosetGraph_adj d.radical _ _).mpr hct)
    have h2 : (cosetGraph d.radical).dist t (alpha d.radical) = 1 :=
      SimpleGraph.dist_eq_one_iff_adj.mpr
        ((cosetGraph_adj d.radical _ _).mpr (adjacent_symm d.radical hat))
    simpa only [h1,h2] using (cosetGraph_connected d.radical).dist_triangle
      (u := c) (v := t) (w := alpha d.radical)
  have hcQ : Z d.radical c ≤ Q d.radical (p.walk.getVert (p.walk.length-2)) :=
    ((Z_le_localZSpan d.radical _ _).trans (localZSpan_le_V d.radical hdist)).trans hbad
  have hline := eligible_backward_failure_line s hc hb u hfull'.le p hat hct hgen hel hcQ
  have hsmall : (Q d.radical a').relIndex (Z d.radical (alpha d.radical)) < 4 := by omega
  have hcentral := eligible_backward_line_central s hc hb u hfull'.le p hat hct hgen hel hcQ
  exact ⟨t,c,hat,hct,hgen,hline.1,hline.2.1,
    eligible_backward_slice_eq_fixer s hc hb u hfull'.le p hat hct hgen hel hcQ,
    hline.2.2.1,hcentral.2.1,hcentral.2.2,
    eligible_backward_kernel_not_central s hc hb p hsmall hat hct hgen hel hcQ⟩


end AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
