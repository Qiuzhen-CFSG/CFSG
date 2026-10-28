module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.OriginalSylow.SmallShifts
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.OriginalSylow.BorelFixed
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.OriginalSylow.BorelOppositePair
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicOmegaControl
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicOmegaGeneration
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicPlaneSelectors

public import Theory.GroupTheory.PerfectFiveSectionSmallCore

/-!
# Distinct Borel movers containing the starting core

For distinct Thompson movers on one edge, containment of the starting
two-core in the opposite mover excludes central generation of the entire
omega layer. The full reverse critical kernel then normalizes the neighboring
seed. Full omega control makes each trapped critical endpoint normalize the
two-seed span, and the paired generation identity makes that span normal
in the starting stabilizer.

The quotient of this span by the starting seed has order dividing eight.
Its automorphism group has order prime to five, so the actual alternating-six
component acts trivially. The proof uses the original surjective cubic
projection and retains its kernel E, including the odd quotient E/Q.
Consequently the span lies in the Baumann slice. A strict slice excludes
simultaneous trapping and supplies one of the two compatible backward paths,
with the same component switch, neighbor transporter and all overlap vertices.

This completes the small-image shift for distinct movers containing the
starting core. Movers omitting that core, the central-generation case for
equal movers, strict-slice construction and the terminal distance exclusions
remain necessary for whole-core reconstruction. Both full moving-cover
orders, sixteen and thirty-two, are retained.

The private imports share the original graph coordinates and omega transport
inside this reconstruction package; no natural replacement graph is used.

Source: Meierfrankenfeld--Stellmacher, Pushing up weak BN-pairs of rank two
(1993), (5.5)(c) and (5.7), printed pp.916--919;
Aschbacher--Smith C.1.31--32, pp.135--136.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
open Theory.SpecificGroups.SymmetricSix Theory.SpecificGroups.SymmetricSix.BinaryFlags
open scoped commutatorElement IsMulCommutative Pointwise
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Exceptional.OriginalSylow
open Exhaustion Exhaustion.LargeDistance Exhaustion.LargeDistance.CubicFull
universe u
variable {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
  (h : SmallMSPair KnownSimple.IsKnownSimple L R) (e : CentralMarking L)
  (hz : Nat.card (center (L ⧸ pCore 2 L)) = 3)
  (hk : layerKernel L R = extensionKernel h)
local notation "Rg" => edge L R
local notation "π" => CubicAction.projection h e hz hk

local notation "M" => (L ⊔ R : Subgroup G)

include h e hz hk in
private theorem component_le_ker_of_five_coprime
    {H : Type*} [Group H] [Finite H] (f : M →* H)
    (hf : Nat.Coprime 5 (Nat.card H)) : L.subgroupOf M ≤ f.ker := by
  let K := L.subgroupOf M
  let := h.component_perfect
  let d := subgroupOfEquivOfLe (show L ≤ L ⊔ R from le_sup_left)
  let : Group.IsPerfect K := Group.IsPerfect.ofSurjective
    (f := d.symm.toMonoidHom) d.symm.surjective
  apply perfect_le_of_le_sup_two K f.ker (pCore 2 M) pCore_isPGroup
  rcases normal_over_core_dichotomy h e (f.ker ⊔ pCore 2 M) le_sup_right with he | hc
  · have hkE : f.ker ≤ (π).ker := by
      rw [CubicAction.projection_kernel h e hz hk]
      exact le_sup_left.trans he
    have hdiv := index_dvd_of_le hkE
    rw [index_ker,index_ker,MonoidHom.range_eq_top.mpr
      (CubicEven.projection_surjective h e hz hk),Nat.card_congr (topEquiv : (⊤ : Subgroup S) ≃* S).toEquiv] at hdiv
    have hfive : 5 ∣ Nat.card S := by
      simp only [S,Nat.card_eq_fintype_card,Fintype.card_perm,Fintype.card_fin]
      decide
    exact (Nat.prime_five.coprime_iff_not_dvd.mp hf
      (hfive.trans (hdiv.trans f.range.card_subgroup_dvd_card))).elim
  · exact hc

include h e hz hk in
private theorem small_normal_section_commutator
    (D N : Subgroup M) [D.Normal] [N.Normal]
    (hsmall : N.relIndex D ∣ 8) : ⁅D,L.subgroupOf M⁆ ≤ N := by
  let q := QuotientGroup.mk' N
  let V := D.map q
  let : V.Normal := Normal.map inferInstance q (QuotientGroup.mk'_surjective N)
  let f : M →* MulAut V := (MulAut.conjNormal : (M ⧸ N) →* MulAut V).comp q
  have hc : Nat.card V ∣ 8 := by
    change Nat.card (D.map q) ∣ 8
    rw [←relIndex_ker D q]
    simpa only [q,QuotientGroup.ker_mk'] using hsmall
  have hK := component_le_ker_of_five_coprime h e hz hk f
    (five_coprime_card_mulAut_of_card_dvd_eight hc)
  have hcent : (L.subgroupOf M).map q ≤ centralizer (V : Set (M ⧸ N)) := by
    rintro _ ⟨k,hkK,rfl⟩ v hv
    have he := congrArg (fun a : MulAut V => (a ⟨v,hv⟩ : M ⧸ N)) (hK hkK)
    change q k * v * (q k)⁻¹ = v at he
    exact (mul_inv_eq_iff_eq_mul.mp he).symm
  rw [←QuotientGroup.ker_mk' N,←Subgroup.map_eq_bot_iff,map_commutator]
  exact commutator_eq_bot_iff_le_centralizer.mpr (le_centralizer_iff.mp hcent)

include h e hz hk in
private theorem small_normal_radius_le_slice
    (D : Subgroup (FreeAmalgam Rg))
    (hDV : D ≤ V Rg (alpha Rg))
    (hDN : stabilizer Rg (alpha Rg) ≤ normalizer (D : Set (FreeAmalgam Rg)))
    (hsmall : (Z Rg (alpha Rg)).relIndex D ∣ 8) :
    D ≤ B Rg (alpha Rg) ((sourceGeometry h).Z_normal _) := by
  have hb := distance_gt_two h e hz hk
  let D₀ := D.comap (embedM Rg)
  let Z₀ := (Z Rg (alpha Rg)).comap (embedM Rg)
  have hDm : D₀.map (embedM Rg) = D := map_comap_eq_self
    ((hDV.trans ((sourceGeometry h).V_local _ rfl hb)).trans_eq (stabilizer_m_base Rg))
  have hZm : Z₀.map (embedM Rg) = Z Rg (alpha Rg) := map_comap_eq_self
    ((Z_le_stabilizer Rg _).trans_eq (stabilizer_m_base Rg))
  have hg (m : M) : embedM Rg m ∈ stabilizer Rg (alpha Rg) := by
    change embedM Rg m ∈ stabilizer Rg (mVertex Rg 1)
    rw [stabilizer_m_base]
    exact ⟨m,rfl⟩
  let : D₀.Normal := ⟨by
    intro z hd m
    change embedM Rg (m*z*m⁻¹) ∈ D
    rw [map_mul,map_mul,map_inv]
    exact (mem_normalizer_iff.mp (hDN (hg m)) (embedM Rg z)).mp hd⟩
  let : Z₀.Normal := ⟨by
    intro z hd m
    change embedM Rg (m*z*m⁻¹) ∈ Z Rg (alpha Rg)
    rw [map_mul,map_mul,map_inv]
    exact (mem_normalizer_iff.mp ((Z_normalized Rg _) (hg m)) (embedM Rg z)).mp hd⟩
  have hs : Z₀.relIndex D₀ ∣ 8 := by
    rw [←relIndex_map_map_of_injective _ _ (embedM_injective Rg),hDm,hZm]
    exact hsmall
  have hm := map_mono (f := embedM Rg) (small_normal_section_commutator h e hz hk D₀ Z₀ hs)
  rw [map_commutator,hDm,hZm,show (L.subgroupOf M).map (embedM Rg) = Ltilde Rg (alpha Rg) by
    rw [Ltilde_alpha,h.relative_residual]] at hm
  intro z hd
  apply (mem_B_iff Rg (alpha Rg) _ ((sourceGeometry h).V_local _ rfl hb) z).mpr
  refine ⟨hDV hd,?_⟩
  intro l hl
  rw [commutator_comm] at hm
  exact hm (commutator_mem_commutator hl hd)

include h e hz hk in
theorem borel_distinct_containing_core_omega_control
    (u : S) (hR : (Rg).map π = borel.map (MulAut.conj u).toMonoidHom)
    {a c t v w : Vertex Rg} (ha : color Rg a = false) (hc : color Rg c = false)
    (hat : Adjacent Rg a t) (hct : Adjacent Rg c t)
    (hne : edgeOffenderJoin a t ≠ edgeOffenderJoin c t)
    (hcore : Q Rg a ≤ edgeOffenderJoin c t)
    (p : CriticalPath Rg (sourceGeometry h) v w)
    (hsmall : (Q Rg w).relIndex (Z Rg v) < 4)
    (Y : Subgroup (FreeAmalgam Rg)) (hYG : Y ≤ stabilizer Rg v)
    (hfix : Y ≤ centralizer
      ((⁅X Rg v,Z Rg w⁆ : Subgroup (FreeAmalgam Rg)) : Set (FreeAmalgam Rg))) :
    ⁅Y,X Rg v⁆ ≤ ⁅X Rg v,Z Rg w⁆ ⊔ ⁅Y,X Rg v ⊓ Q Rg w⁆ := by
  rcases small_critical_omega_generation_or_control_at h e hz hk p hsmall with hgen | hcontrol
  · exact (borel_opposite_containing_core_nonsplit h e hz hk u hR ha hc hat hct hne hcore
      (omega_generation_transport p.start_color ha hgen)).elim
  · exact hcontrol Y hYG hfix

include h e hz hk in
theorem borel_distinct_containing_core_trapped_normalization
    (u : S) (hR : (Rg).map π = borel.map (MulAut.conj u).toMonoidHom)
    {a c t z : Vertex Rg}
    (p : CriticalPath Rg (sourceGeometry h) a z)
    (hp : (Q Rg z).relIndex (Z Rg a) < 4)
    (hc : color Rg c = false) (hat : Adjacent Rg a t) (hct : Adjacent Rg c t)
    (hne : edgeOffenderJoin a t ≠ edgeOffenderJoin c t)
    (hcore : Q Rg a ≤ edgeOffenderJoin c t)
    (hbad : Z Rg c ≤ Q Rg (p.walk.getVert (p.walk.length-2))) :
    X Rg z ≤ normalizer ((Z Rg c ⊔ Z Rg a : Subgroup (FreeAmalgam Rg)) : Set (FreeAmalgam Rg)) := by
  have hb := distance_gt_two h e hz hk
  have hdist : (cosetGraph Rg).dist c a ≤ 2 := by
    have h₁ := SimpleGraph.dist_eq_one_iff_adj.mpr ((cosetGraph_adj Rg _ _).mpr hct)
    have h₂ := SimpleGraph.dist_eq_one_iff_adj.mpr
      ((cosetGraph_adj Rg _ _).mpr (adjacent_symm Rg hat))
    have hh := (cosetGraph_connected Rg).dist_triangle (u := c) (v := t) (w := a)
    omega
  have hZQ : Z Rg c ≤ Q Rg a :=
    ((Z_le_localZSpan Rg _ _).trans (localZSpan_le_V Rg hdist)).trans
      ((sourceGeometry h).V_le_Q hb a p.start_color)
  have hl : 2 < p.walk.length := p.length_eq_b ▸ hb
  let last := p.walk.getVert (p.walk.length-1)
  have hzlast : Adjacent Rg z last := by
    have hh := p.walk.adj_getVert_succ (i := p.walk.length-1) (by omega)
    rw [show p.walk.length-1+1=p.walk.length by omega,p.walk.getVert_length] at hh
    exact adjacent_symm Rg ((cosetGraph_adj Rg _ _).mp hh)
  have hlast : color Rg last = true := by
    have hh := adjacent_color_ne Rg hzlast
    rw [p.end_color] at hh
    cases he : color Rg last <;> simp_all
  have hprevlast : Adjacent Rg (p.walk.getVert (p.walk.length-2)) last := by
    have hh := p.walk.adj_getVert_succ (i := p.walk.length-2) (by omega)
    rw [show p.walk.length-2+1=p.walk.length-1 by omega] at hh
    exact (cosetGraph_adj Rg _ _).mp hh
  have hlocal : Z Rg c ≤ stabilizer Rg z :=
    (hbad.trans (Q_le_adjacent_h Rg hlast hprevlast)).trans
      (fun _ hx => hx.2 _ (adjacent_symm Rg hzlast))
  have hrev := critical_reverse Rg (sourceGeometry h) (sourceEdgeCentralizer h e)
    a p.start_color (by rw [(sourceGeometry h).distance_constant a p.start_color]; exact sourceDistance_pos h)
    z p.end_color p.critical
  let q : CriticalPath Rg (sourceGeometry h) z a := CriticalPath.ofPair p.end_color hrev
  have hs : (Q Rg a).relIndex (Z Rg z) < 4 := by
    rw [(small_critical_indices h e hz hk p hp).2]
    decide
  have hXN : X Rg z ≤ normalizer (Z Rg a : Set (FreeAmalgam Rg)) :=
    (critical_X_le_vertex h e z p.end_color a hrev).trans (Z_normalized Rg a)
  have hRZ : ⁅X Rg z,Z Rg a⁆ ≤ Z Rg a := le_normalizer_iff_commutator_le_right.mp hXN
  have hfix : Z Rg c ≤ centralizer
      ((⁅X Rg z,Z Rg a⁆ : Subgroup (FreeAmalgam Rg)) : Set (FreeAmalgam Rg)) :=
    (hZQ.trans (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp
      (Z_centralizes_Q Rg a p.start_color)))).trans (centralizer_le hRZ)
  have hJN := remaining_edge_thompson h e hz hk u (Or.inr hR) hc hct
  have hQN : Q Rg a ≤ normalizer (Z Rg c : Set (FreeAmalgam Rg)) :=
    ((hcore.trans hJN.2.2.1).trans
      (fun _ hx => hx.2 _ (adjacent_symm Rg hct))).trans (Z_normalized Rg c)
  have hcom : ⁅X Rg z,Z Rg c⁆ ≤ Z Rg c ⊔ Z Rg a := by
    rw [commutator_comm]
    exact (borel_distinct_containing_core_omega_control h e hz hk u hR p.start_color hc hat hct
      hne hcore q hs _ hlocal hfix).trans
      (sup_le (hRZ.trans le_sup_right)
        ((le_normalizer_iff_commutator_le_left.mp (inf_le_right.trans hQN)).trans le_sup_left))
  apply le_normalizer_iff.mpr
  intro x hx v hv
  have hm : (Z Rg c ⊔ Z Rg a).map (MulAut.conj x).toMonoidHom ≤ Z Rg c ⊔ Z Rg a := by
    rw [Subgroup.map_sup]
    refine sup_le ?_ ((mem_normalizer_iff_map_conj_eq.mp (hXN hx)).le.trans le_sup_right)
    rintro _ ⟨y,hy,rfl⟩
    have hh := (Z Rg c ⊔ Z Rg a).mul_mem
      (hcom (commutator_mem_commutator hx hy)) (mem_sup_left hy)
    simpa [MulAut.conj_apply,commutatorElement_def,mul_assoc] using hh
  exact hm (mem_map_of_mem (MulAut.conj x).toMonoidHom hv)

include h e hz hk in
private theorem borel_seed_edge_index
    (u : S) (hR : (Rg).map π = borel.map (MulAut.conj u).toMonoidHom)
    {a c t : Vertex Rg} (ha : color Rg a = false) (hc : color Rg c = false)
    (hat : Adjacent Rg a t) (hct : Adjacent Rg c t)
    (hne : edgeOffenderJoin a t ≠ edgeOffenderJoin c t) :
    (Z Rg t).relIndex (Z Rg c) = 8 := by
  let := finite_Z Rg t
  have hZN : Z Rg t ≤ normalizer (U Rg c : Set (FreeAmalgam Rg)) :=
    ((adjacent_Z_le Rg hc hct).trans (Z_le_stabilizer Rg c)).trans (U_normalized c)
  rw [vertex_seed_eq_moving_sup_edge h e hz hc hct,
    relIndex_sup_of_normalizes (U Rg c) (Z Rg t) hZN]
  have he := borel_cross_thompson_seed_fixed h e hz hk u hR hc ha hct hat (Ne.symm hne)
  have hfix : U Rg c ⊓ Z Rg t =
      U Rg c ⊓ centralizer (edgeOffenderJoin a t : Set (FreeAmalgam Rg)) := by
    rw [←he,←inf_assoc,inf_eq_left.mpr (DistanceEight.U_le_Z Rg c)]
  rw [←inf_relIndex_right,inf_comm (Z Rg t),hfix,inf_relIndex_left]
  exact borel_cross_thompson_fixed_index_eq_eight h e hz hk u hR hc ha hct hat (Ne.symm hne)

include h e hz hk in
/-- Distinct opposite movers containing the starting core force a trapped
pair of backward seeds into the actual Baumann slice. The proof uses the
full reverse omega kernels and the order-eight quotient of the seed span. -/
theorem borel_distinct_containing_core_trapped_slice
    (u : S) (hR : (Rg).map π = borel.map (MulAut.conj u).toMonoidHom)
    {z z' c t : Vertex Rg}
    (p : CriticalPath Rg (sourceGeometry h) (alpha Rg) z)
    (q : CriticalPath Rg (sourceGeometry h) (alpha Rg) z')
    (hp : (Q Rg z).relIndex (Z Rg (alpha Rg)) < 4)
    (hq : (Q Rg z').relIndex (Z Rg (alpha Rg)) < 4)
    (hat : Adjacent Rg (alpha Rg) t) (hct : Adjacent Rg c t)
    (hne : edgeOffenderJoin (alpha Rg) t ≠ edgeOffenderJoin c t)
    (hcore : Q Rg (alpha Rg) ≤ edgeOffenderJoin c t)
    (hgen : (edgeOffenderJoin (alpha Rg) t ⊔ Z Rg z) ⊔ Z Rg z' = stabilizer Rg (alpha Rg))
    (hbad : Z Rg c ≤ Q Rg (p.walk.getVert (p.walk.length-2)))
    (hbad' : Z Rg c ≤ Q Rg (q.walk.getVert (q.walk.length-2))) :
    Z Rg c ≤ B Rg (alpha Rg) ((sourceGeometry h).Z_normal _) := by
  have hb := distance_gt_two h e hz hk
  have ht : color Rg t = true := by
    have hh := adjacent_color_ne Rg hat
    change false ≠ color Rg t at hh
    cases he : color Rg t <;> simp_all
  have hc : color Rg c = false := by
    have hh := adjacent_color_ne Rg hct
    rw [ht] at hh
    cases he : color Rg c <;> simp_all
  have hdist : (cosetGraph Rg).dist c (alpha Rg) ≤ 2 := by
    have h₁ := SimpleGraph.dist_eq_one_iff_adj.mpr ((cosetGraph_adj Rg _ _).mpr hct)
    have h₂ := SimpleGraph.dist_eq_one_iff_adj.mpr
      ((cosetGraph_adj Rg _ _).mpr (adjacent_symm Rg hat))
    have hh := (cosetGraph_connected Rg).dist_triangle (u := c) (v := t) (w := alpha Rg)
    omega
  have hZV : Z Rg c ≤ V Rg (alpha Rg) :=
    (Z_le_localZSpan Rg _ _).trans (localZSpan_le_V Rg hdist)
  let Y := Z Rg c ⊔ Z Rg (alpha Rg)
  have hseed (v : Vertex Rg) (hv : color Rg v = false) : Z Rg v ≤ X Rg v :=
    (sourceGeometry h).omega_bound v hv (by
      rw [(sourceGeometry h).distance_constant v hv]
      exact sourceDistance_pos h)
  have hTNa : Q Rg t ≤ normalizer (Z Rg (alpha Rg) : Set (FreeAmalgam Rg)) :=
    (show Q Rg t ≤ stabilizer Rg (alpha Rg) from
      fun _ hx => hx.2 _ (adjacent_symm Rg hat)).trans (Z_normalized Rg _)
  have hTNc : Q Rg t ≤ normalizer (Z Rg c : Set (FreeAmalgam Rg)) :=
    (show Q Rg t ≤ stabilizer Rg c from
      fun _ hx => hx.2 _ (adjacent_symm Rg hct)).trans (Z_normalized Rg _)
  have hYN : stabilizer Rg (alpha Rg) ≤ normalizer (Y : Set (FreeAmalgam Rg)) := by
    rw [←hgen]
    refine sup_le (sup_le ?_ ?_) ?_
    · exact ((remaining_edge_thompson h e hz hk u (Or.inr hR) rfl hat).2.2.1.trans
        (le_inf hTNc hTNa)).trans (normalizer_inf_normalizer_le_normalizer_sup _ _)
    · exact (hseed z p.end_color).trans
        (borel_distinct_containing_core_trapped_normalization h e hz hk u hR p hp hc hat hct hne hcore hbad)
    · exact (hseed z' q.end_color).trans
        (borel_distinct_containing_core_trapped_normalization h e hz hk u hR q hq hc hat hct hne hcore hbad')
  have hZaT : Z Rg (alpha Rg) ≤ Q Rg t :=
    ((hseed _ rfl).trans (omegaCenter_le _)).trans (Q_le_adjacent_h Rg ht hat)
  let := finite_Z Rg (alpha Rg)
  have hsmall : (Z Rg (alpha Rg)).relIndex Y ∣ 8 := by
    change (Z Rg (alpha Rg)).relIndex (Z Rg c ⊔ Z Rg (alpha Rg)) ∣ 8
    rw [relIndex_sup_of_normalizes (Z Rg c) (Z Rg (alpha Rg)) (hZaT.trans hTNc)]
    have hd := relIndex_dvd_of_le_left (Z Rg c) (adjacent_Z_le Rg rfl hat)
    rw [borel_seed_edge_index h e hz hk u hR rfl hc hat hct hne] at hd
    exact hd
  exact le_sup_left.trans (small_normal_radius_le_slice h e hz hk Y
    (sup_le hZV (Z_le_VBall Rg _ 2)) hYN hsmall)

include h e hz hk in
/-- A distinct opposite Borel mover containing the starting core supplies a
compatible backward critical path at every strict forward slice. Both full
cover orders, the component switch and all path overlaps are retained. -/
theorem borel_distinct_containing_core_small_shift
    (u : S) (hR : (Rg).map π = borel.map (MulAut.conj u).toMonoidHom)
    {z delta : Vertex Rg}
    (p : CriticalPath Rg (sourceGeometry h) (alpha Rg) z)
    (hp : (Q Rg z).relIndex (Z Rg (alpha Rg)) < 4)
    (hd : Adjacent Rg delta (p.walk.getVert 1))
    (hne : edgeOffenderJoin (alpha Rg) (p.walk.getVert 1) ≠
      edgeOffenderJoin delta (p.walk.getVert 1))
    (hcore : Q Rg (alpha Rg) ≤ edgeOffenderJoin delta (p.walk.getVert 1))
    (hs : 2 < (B Rg (alpha Rg) ((sourceGeometry h).Z_normal _)).relIndex (U Rg delta)) :
    ∃ t, Adjacent Rg (alpha Rg) t ∧ ∃ r ∈ L.subgroupOf M,
      let x := (embedM Rg r)⁻¹
      ∃ q : CriticalPath Rg (sourceGeometry h) (alpha Rg) (act Rg x z),
        (∀ i, q.walk.getVert i = act Rg x (p.walk.getVert i)) ∧
        (Q Rg (act Rg x z)).relIndex (Z Rg (alpha Rg)) < 4 ∧
        (edgeOffenderJoin (alpha Rg) t ⊔ Z Rg z) ⊔ Z Rg (act Rg x z) = stabilizer Rg (alpha Rg) ∧
        edgeOffenderJoin (alpha Rg) t ⊔ edgeOffenderJoin (alpha Rg) (act Rg x t) = stabilizer Rg (alpha Rg) ∧
        x ∈ normalizer (edgeOffenderJoin (alpha Rg) (p.walk.getVert 1) : Set (FreeAmalgam Rg)) ∧
        Z Rg z ⊔ Z Rg (act Rg x z) ≤ edgeOffenderJoin (alpha Rg) (p.walk.getVert 1) ∧
        ∃ g ∈ stabilizer Rg (alpha Rg), act Rg g (p.walk.getVert 1) = t ∧
          let c := act Rg g delta
          2 < (B Rg (alpha Rg) ((sourceGeometry h).Z_normal _)).relIndex (U Rg c) ∧
          ((∃ b : CriticalPath Rg (sourceGeometry h) c (p.walk.getVert (p.walk.length-2)),
              b.walk.getVert 1 = t ∧
              ∀ i ≤ p.walk.length-2, b.walk.getVert (i+2) = p.walk.getVert i) ∨
           (∃ b : CriticalPath Rg (sourceGeometry h) c (q.walk.getVert (q.walk.length-2)),
              b.walk.getVert 1 = t ∧
              ∀ i ≤ q.walk.length-2, b.walk.getVert (i+2) = q.walk.getVert i)) := by
  obtain ⟨t,hat,r,hr,hgen,hpair,_,_,_,_,_,_,hnorm,hinside,_,g,hg,hgt,_⟩ :=
    borel_small_critical_seed_selectors_with_opposite h e hz hk u hR p hp
  let x := (embedM Rg r)⁻¹
  let c := act Rg g delta
  have hxG : x ∈ stabilizer Rg (alpha Rg) := by
    change x ∈ stabilizer Rg (mVertex Rg 1)
    rw [stabilizer_m_base]
    exact ⟨r⁻¹,by rw [map_inv]⟩
  have hxa : act Rg x (alpha Rg) = alpha Rg := hxG
  have hpact : ∃ q : CriticalPath Rg (sourceGeometry h)
      (act Rg x (alpha Rg)) (act Rg x z),
      ∀ i, q.walk.getVert i = act Rg x (p.walk.getVert i) :=
    ⟨p.act x,fun i => by simp only [CriticalPath.act,actWalk_getVert]⟩
  rw [hxa] at hpact
  obtain ⟨q,hqverts⟩ := hpact
  have hqs : (Q Rg (act Rg x z)).relIndex (Z Rg (alpha Rg)) < 4 := by
    rw [←hxa,Q_act,Z_act,relIndex_map_map_of_injective _ _ (MulAut.conj x⁻¹).injective]
    exact hp
  have hct : Adjacent Rg c t := by
    rw [←hgt]
    exact (adjacent_act_iff Rg g _ _).mpr hd
  have hc : color Rg c = false := by
    have h₁ := adjacent_color_ne Rg hat
    have h₂ := adjacent_color_ne Rg hct
    change false ≠ color Rg t at h₁
    cases he : color Rg c <;> cases he' : color Rg t <;> simp_all
  have hb := distance_gt_two h e hz hk
  have hB : (B Rg (alpha Rg) ((sourceGeometry h).Z_normal _)).map
      (MulAut.conj g⁻¹).toMonoidHom = B Rg (alpha Rg) ((sourceGeometry h).Z_normal _) :=
    mem_normalizer_iff_map_conj_eq.mp (Escape.Propagation.Rigidity.B_normalized
      hb (alpha Rg) rfl ((stabilizer Rg (alpha Rg)).inv_mem hg))
  have hstrict : 2 < (B Rg (alpha Rg) ((sourceGeometry h).Z_normal _)).relIndex (U Rg c) := by
    change 2 < (B Rg (alpha Rg) _).relIndex (U Rg (act Rg g delta))
    rw [U_act,←hB,relIndex_map_map_of_injective _ _ (MulAut.conj g⁻¹).injective]
    exact hs
  have hfirst : Adjacent Rg (alpha Rg) (p.walk.getVert 1) := by
    apply (cosetGraph_adj Rg _ _).mp
    simpa only [SimpleGraph.Walk.getVert_zero] using
      p.walk.adj_getVert_succ (i := 0) (p.length_eq_b ▸ sourceDistance_pos h)
  have hdcol : color Rg delta = false := by
    simpa only [c,action_preserves_color] using hc
  have hga : act Rg g (alpha Rg) = alpha Rg := hg
  have hJa := remaining_edge_join_act h e hz hk u (Or.inr hR) rfl hfirst g
  have hJd := remaining_edge_join_act h e hz hk u (Or.inr hR) hdcol hd g
  simp only [hga,hgt] at hJa hJd
  have hnec : edgeOffenderJoin (alpha Rg) t ≠ edgeOffenderJoin c t := by
    intro he
    apply hne
    apply map_injective (f := (MulAut.conj g⁻¹).toMonoidHom) (MulAut.conj g⁻¹).injective
    exact hJa.symm.trans (he.trans hJd)
  have hcorec : Q Rg (alpha Rg) ≤ edgeOffenderJoin c t := by
    have hh := map_mono (f := (MulAut.conj g⁻¹).toMonoidHom) hcore
    rw [←Q_act,hga,←hJd] at hh
    exact hh
  have extend (w : Vertex Rg) (s : CriticalPath Rg (sourceGeometry h) (alpha Rg) w)
      (hn : ¬ Z Rg c ≤ Q Rg (s.walk.getVert (s.walk.length-2))) :
      ∃ b : CriticalPath Rg (sourceGeometry h) c (s.walk.getVert (s.walk.length-2)),
        b.walk.getVert 1 = t ∧ ∀ i ≤ s.walk.length-2, b.walk.getVert (i+2) = s.walk.getVert i := by
    let v : (cosetGraph Rg).Walk c (alpha Rg) :=
      .cons ((cosetGraph_adj Rg _ _).mpr hct)
        (.cons ((cosetGraph_adj Rg _ _).mpr (adjacent_symm Rg hat)) .nil)
    have hv : v.length = 2 := rfl
    let b := s.prepend_two (Nat.le_of_lt hb) hc v hv hn
    refine ⟨b,?_,fun i hi => s.prepend_two_overlap _ _ _ _ _ hi⟩
    simp only [b,CriticalPath.prepend_two_walk,SimpleGraph.Walk.getVert_append,
      hv,show 1<2 from by decide,ite_true,v,SimpleGraph.Walk.getVert_cons_succ,
      SimpleGraph.Walk.getVert_zero]
  by_cases hbad : Z Rg c ≤ Q Rg (p.walk.getVert (p.walk.length-2))
  · by_cases hbad' : Z Rg c ≤ Q Rg (q.walk.getVert (q.walk.length-2))
    · have hZB := borel_distinct_containing_core_trapped_slice h e hz hk u hR
        p q hp hqs hat hct hnec hcorec hgen hbad hbad'
      have hi := relIndex_eq_one.mpr ((DistanceEight.U_le_Z Rg c).trans hZB)
      omega
    · exact ⟨t,hat,r,hr,q,hqverts,hqs,hgen,hpair,hnorm,hinside,g,hg,hgt,
        hstrict,Or.inr (extend _ q hbad')⟩
  · exact ⟨t,hat,r,hr,q,hqverts,hqs,hgen,hpair,hnorm,hinside,g,hg,hgt,
      hstrict,Or.inl (extend _ p hbad)⟩

end AlternatingSixReconstruction.Exceptional.OriginalSylow
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
