module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicSliceShift

/-!
# The shifted span lies in the old endpoint core

A normal radius subgroup that fixes the full reverse critical kernel is
contained in the Baumann slice. For a small critical image this follows
from the exact full-kernel centralizer. For a large image, the marked
cover provides a restricted reverse actor preserving the entire critical
commutator. Its nonzero movement makes it escape the original two-core,
and the escaping-actor theorem controls the normal section modulo the
full seed. Transport to arbitrary component vertices uses the literal
graph action, preserving the cubic kernel E and both cover orders.

Apply this to the shifted span from MS93 (5.9). If its center were critical
with the old endpoint, inner-layer centralization would force the whole
span into its Baumann slice, contradicting eligibility. Thus the full
shifted span lies in the old endpoint's two-core and the old endpoint
seed lies in the shifted center's two-core. The whole-core and literal
C.1.32 applications now have no shifted-critical alternative.

The remaining centralizer-orbit argument for strict small slices, other
radical images, R4/R6 and MS93 (5.11)--(5.12) remain necessary, together
with independent natural exhaustion and final assembly of both outcomes.

Source: Meierfrankenfeld--Stellmacher (1993), (3.3)(ii), pp.866--867,
and (5.9), p.921, the paragraph immediately following equation (**).
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender BinaryPermutation
open scoped IsMulCommutative commutatorElement Pointwise
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicFull
open Theory.SpecificGroups.SymmetricSix.BinaryFlags
open CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup
universe u
variable {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
  (h : SmallMSPair KnownSimple.IsKnownSimple L R) (e : CentralMarking L)
  (hz : Nat.card (center (L ⧸ pCore 2 L)) = 3)
  (hk : layerKernel L R = extensionKernel h)
local notation "M" => (L ⊔ R : Subgroup G)
local notation "Rg" => edge L R
include h e hz in
private theorem normalized_radius_le_slice_of_controlled_actor_base
    (hb : 2 < sourceDistance h)
    (D A : Subgroup (FreeAmalgam Rg)) (hDV : D ≤ V Rg (alpha Rg))
    (hDN : stabilizer Rg (alpha Rg) ≤ normalizer (D : Set (FreeAmalgam Rg)))
    (hAG : A ≤ stabilizer Rg (alpha Rg)) (hA : IsPGroup 2 A)
    (hne : ¬ A ≤ Q Rg (alpha Rg))
    (hcomm : ⁅D,A⁆ ≤ Z Rg (alpha Rg)) :
    D ≤ B Rg (alpha Rg) ((sourceGeometry h).Z_normal _) := by
  let D₀ := D.comap (embedM Rg)
  let Z₀ := (Z Rg (alpha Rg)).comap (embedM Rg)
  let A₀ := A.comap (embedM Rg)
  have hDG : D ≤ (embedM Rg).range :=
    (hDV.trans ((sourceGeometry h).V_local (alpha Rg) rfl hb)).trans_eq (stabilizer_m_base Rg)
  have hDm : D₀.map (embedM Rg) = D := map_comap_eq_self hDG
  have hZm : Z₀.map (embedM Rg) = Z Rg (alpha Rg) :=
    map_comap_eq_self ((Z_le_stabilizer Rg (alpha Rg)).trans_eq (stabilizer_m_base Rg))
  have hAm : A₀.map (embedM Rg) = A := map_comap_eq_self
    (hAG.trans_eq (stabilizer_m_base Rg))
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
  have hcomm₀ : ⁅D₀,A₀⁆ ≤ Z₀ := by
    apply (map_le_map_iff_of_injective (embedM_injective Rg)).mp
    rwa [map_commutator,hDm,hAm,hZm]
  have hne : ¬ A₀ ≤ pCore 2 M := by
    intro he
    have hh := map_mono (f := embedM Rg) he
    rw [hAm,←Q_alpha Rg (h.relative_radical.isPGroup) (h.relative_radical.twoCore_le)] at hh
    exact hne hh
  have hAtwo : IsPGroup 2 A₀ := hA.comap_of_injective _ (embedM_injective Rg)
  have hDL := CubicAction.normal_commutator_le_of_escaping_two h e hz D₀ Z₀ A₀ hAtwo hne hcomm₀
  have hm := map_mono (f := embedM Rg) hDL
  rw [map_commutator,hDm,hZm,show (L.subgroupOf (L ⊔ R)).map (embedM Rg) = Ltilde Rg (alpha Rg) by
    rw [Ltilde_alpha,h.relative_residual]] at hm
  intro z hd
  apply (mem_B_iff Rg (alpha Rg) _ ((sourceGeometry h).V_local (alpha Rg) rfl hb) z).mpr
  refine ⟨hDV hd,?_⟩
  intro l hl
  rw [commutator_comm] at hm
  exact hm (commutator_mem_commutator hl hd)

include h e hz in
/-- An escaping two-actor fixing a normal radius section modulo its full seed
forces that section into the Baumann slice, at any component vertex. -/
theorem normalized_radius_le_slice_of_controlled_actor
    (hb : 2 < sourceDistance h) {a : Vertex Rg} (ha : color Rg a = false)
    (D A : Subgroup (FreeAmalgam Rg)) (hDV : D ≤ V Rg a)
    (hDN : stabilizer Rg a ≤ normalizer (D : Set (FreeAmalgam Rg)))
    (hAG : A ≤ stabilizer Rg a) (hA : IsPGroup 2 A)
    (hne : ¬ A ≤ Q Rg a) (hcomm : ⁅D,A⁆ ≤ Z Rg a) :
    D ≤ B Rg a ((sourceGeometry h).Z_normal _) := by
  obtain ⟨g,hg⟩ := exists_mVertex_of_color Rg ha
  have hbase : act Rg g⁻¹ a = alpha Rg := by
    rw [hg,act_mVertex,mul_inv_cancel]
    rfl
  let f := (MulAut.conj g).toMonoidHom
  have hV : (V Rg a).map f = V Rg (alpha Rg) := by
    simpa only [inv_inv,hbase] using (V_act Rg g⁻¹ a).symm
  have hZ : (Z Rg a).map f = Z Rg (alpha Rg) := by
    simpa only [inv_inv,hbase] using (Z_act Rg g⁻¹ a).symm
  have hQ : (Q Rg a).map f = Q Rg (alpha Rg) := by
    simpa only [inv_inv,hbase] using (Q_act Rg g⁻¹ a).symm
  have hG : (stabilizer Rg a).map f = stabilizer Rg (alpha Rg) := by
    simpa only [inv_inv,hbase] using (stabilizer_act Rg g⁻¹ a).symm
  have hB : (B Rg a ((sourceGeometry h).Z_normal _)).map f =
      B Rg (alpha Rg) ((sourceGeometry h).Z_normal _) := by
    simpa only [inv_inv,hbase] using
      (Escape.PairingControl.FirstPairing.B_act (geometry := sourceGeometry h) hb g⁻¹ a ha).symm
  have hN : stabilizer Rg (alpha Rg) ≤ normalizer (D.map f : Set (FreeAmalgam Rg)) := by
    rw [←hG]
    exact (map_mono hDN).trans (le_normalizer_map f)
  have hh := normalized_radius_le_slice_of_controlled_actor_base h e hz hb
    (D.map f) (A.map f) ((map_mono hDV).trans_eq hV) hN
    ((map_mono hAG).trans_eq hG) (hA.map f) (by
      intro hle
      apply hne
      exact (map_le_map_iff_of_injective (f := f) (MulAut.conj g).injective).mp (hle.trans_eq hQ.symm))
    (by rw [←map_commutator]; exact (map_mono hcomm).trans_eq hZ)
  apply (map_le_map_iff_of_injective (f := f) (MulAut.conj g).injective).mp
  exact hh.trans_eq hB.symm

include h e hz hk in
/-- A normal radius subgroup fixing the full reverse critical kernel lies
in the Baumann slice. Large critical images use a restricted actor preserving
all the original movement; the cubic kernel and central cover remain intact. -/
theorem critical_kernel_normal_radius_le_slice
    (hb : 2 < sourceDistance h) {a a' : Vertex Rg}
    (p : CriticalPath Rg (sourceGeometry h) a a')
    (D : Subgroup (FreeAmalgam Rg)) (hDV : D ≤ V Rg a)
    (hDN : stabilizer Rg a ≤ normalizer (D : Set (FreeAmalgam Rg)))
    (hDe : D ≤ stabilizer Rg a')
    (hfix : D ≤ centralizer (Z Rg a' ⊓ Q Rg a : Set (FreeAmalgam Rg))) :
    D ≤ B Rg a ((sourceGeometry h).Z_normal _) := by
  let q : CriticalPath Rg (sourceGeometry h) a' a := CriticalPath.ofPair p.end_color
    (critical_reverse Rg (sourceGeometry h) (sourceEdgeCentralizer h e)
      a p.start_color (by
        rw [(sourceGeometry h).distance_constant a p.start_color]
        exact sourceDistance_pos h) a' p.end_color p.critical)
  have hAe : Z Rg a' ≤ stabilizer Rg a :=
    critical_Z_le_stabilizer Rg (sourceGeometry h) a p.start_color
      (by rw [(sourceGeometry h).distance_constant a p.start_color]; exact sourceDistance_pos h) p.critical
  have hR : ⁅U Rg a',Z Rg a⁆ ≤ Z Rg a := by
    rw [commutator_comm]
    exact (commutator_mono le_rfl (DistanceEight.U_le_Z Rg a')).trans
      (le_normalizer_iff_commutator_le_left.mp (hAe.trans (Z_normalized Rg a)))
  let := (sourceGeometry h).Z_elementary (sourceDistance_pos h) a p.start_color
  let := (sourceGeometry h).Z_elementary (sourceDistance_pos h) a' p.end_color
  by_cases hs : (Q Rg a').relIndex (Z Rg a) < 4
  · apply normalized_radius_le_slice_of_controlled_actor h e hz hb p.start_color D
      (Z Rg a') hDV hDN hAe (IsElementaryAbelian.isPGroup 2 _) q.critical.2
    exact (small_critical_kernel_commutator h e hz hk p hs D hDe hfix).trans
      (le_normalizer_iff_commutator_le_left.mp (hAe.trans (Z_normalized Rg a)))
  · have hlarge : 4 ≤ (Q Rg a').relIndex (Z Rg a) := by omega
    have hAq : ⁅U Rg a',Z Rg a⁆ ≤ centralizer (Z Rg a : Set (FreeAmalgam Rg)) :=
      hR.trans (le_centralizer_iff_isMulCommutative.mpr inferInstance)
    have hDc : D ≤ centralizer (Z Rg a : Set (FreeAmalgam Rg)) :=
      (hDV.trans ((sourceGeometry h).V_le_Q hb a p.start_color)).trans
        (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp
          (Z_centralizes_Q Rg a p.start_color)))
    have hAD := hR.trans (le_centralizer_iff.mp hDc)
    obtain ⟨i,hi,hir,hiQ,_,hiU,_⟩ := graph_cover h e hz hk a' p.end_color
    have hAr : Z Rg a ≤ i.range := by
      rw [hir]
      exact Z_le_stabilizer_of_dist_le a _ p.critical.1.le
    obtain ⟨A,hA,_,hpres,hcontrol⟩ := embedded_cover_restriction_preserving h e hz hk i hi
      (Z Rg a) hAr (hiQ.symm ▸ hlarge) (hiU.symm ▸ hAq)
    have hAU : A ≤ U Rg a' := hiU ▸ hA
    have hAZ := hAU.trans (DistanceEight.U_le_Z Rg a')
    have hAn : ¬ A ≤ Q Rg a := by
      intro hn
      have hzA : ⁅A,Z Rg a⁆ = ⊥ := commutator_eq_bot_iff_le_centralizer.mpr
        (hn.trans (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp
          (Z_centralizes_Q Rg a p.start_color))))
      have hp : ⁅A,Z Rg a⁆ = ⁅U Rg a',Z Rg a⁆ := hiU ▸ hpres
      exact critical_moving_commutator_not_central h e hz hk q
        ((hp.symm.trans hzA).le.trans bot_le)
    have hbound : ⁅D,A⁆ ≤ Z Rg a := by
      rw [commutator_comm]
      have hh := hcontrol D (hDe.trans_eq hir.symm) (hiU.symm ▸ hAD)
      rw [hiU] at hh
      exact hh.trans hR
    exact normalized_radius_le_slice_of_controlled_actor h e hz hb p.start_color
      D A hDV hDN (hAZ.trans hAe) ((IsElementaryAbelian.isPGroup 2 (Z Rg a')).to_le hAZ)
      hAn hbound

namespace SmallSliceShift
variable {h} {a' : Vertex (edge L R)}
  {p : CriticalPath (edge L R) (sourceGeometry h) (alpha (edge L R)) a'}
  (s : SmallSliceShift h p)

include e hz hk in
/-- The shifted center cannot be critical with the old endpoint: its whole
normal span fixes the reverse kernel and would lie in its own Baumann slice. -/
theorem not_critical_old_endpoint (hb : 4 < sourceDistance h)
    (hsmall : (Q Rg a').relIndex (Z Rg (alpha Rg)) < 4)
    (hslice : (B Rg (alpha Rg) ((sourceGeometry h).Z_normal _)).relIndex
      (U Rg (p.walk.getVert 2)) ≤ 2)
    (heligible : ¬ U Rg (p.walk.getVert 2) ≤ B Rg (alpha Rg) ((sourceGeometry h).Z_normal _)) :
    ¬ CriticalPair Rg s.centerVertex a' ((sourceGeometry h).exists_critical _ s.center_color) := by
  intro hc
  let q : CriticalPath Rg (sourceGeometry h) s.centerVertex a' :=
    CriticalPath.ofPair s.center_color hc
  have hi := s.inner_control e hz hk hb hsmall hslice heligible
  have hDV : s.span ≤ V Rg s.centerVertex := by
    apply localZSpan_le_V
    rw [SimpleGraph.dist_comm]
    change (cosetGraph Rg).dist (act Rg s.conjugator⁻¹ (alpha Rg)) (p.walk.getVert 2) ≤ 2
    rw [←s.fixes_second,dist_act]
    rw [p.dist_start (by have hl : p.walk.length = sourceDistance h := p.length_eq_b; omega)]
  have hfix : s.span ≤ centralizer (Z Rg a' ⊓ Q Rg s.centerVertex : Set (FreeAmalgam Rg)) := by
    intro x hx z hz
    have hz' : z ∈ (Z Rg (p.walk.getVert (p.walk.length-2)) ⊔
        (Z Rg a' ⊓ Q Rg s.centerVertex) : Subgroup (FreeAmalgam Rg)) :=
      Subgroup.mem_sup_right hz
    exact (commutator_eq_bot_iff_le_centralizer.mp hi.2.2) hx z hz'
  exact s.span_not_le_slice (by omega) heligible
    (critical_kernel_normal_radius_le_slice h e hz hk (by omega) q s.span hDV
      (localZSpan_normalized Rg _ _) hi.2.1 hfix)

include e hz hk in
/-- The entire shifted span lies in the old endpoint's two-core, with the
full old endpoint seed in the shifted center's two-core. This discharges
the critical-pair alternative in the saved (5.9) shift. -/
theorem old_endpoint_core (hb : 4 < sourceDistance h)
    (hsmall : (Q Rg a').relIndex (Z Rg (alpha Rg)) < 4)
    (hslice : (B Rg (alpha Rg) ((sourceGeometry h).Z_normal _)).relIndex
      (U Rg (p.walk.getVert 2)) ≤ 2)
    (heligible : ¬ U Rg (p.walk.getVert 2) ≤ B Rg (alpha Rg) ((sourceGeometry h).Z_normal _)) :
    Z Rg a' ≤ Q Rg s.centerVertex ∧ s.span ≤ Q Rg a' :=
  (s.old_endpoint_alternative e hz hk hb hsmall hslice heligible).resolve_left
    (s.not_critical_old_endpoint e hz hk hb hsmall hslice heligible)

end SmallSliceShift

omit hk in
include h e hz in
/-- Whole-core application: the full point-core branch constructs the
small-slice shift together with its now unconditional endpoint containment. -/
theorem coreExhaustion_or_cubic_shifted_span_core :
    CoreExhaustion L R ∨ ∃ hk : layerKernel L R = extensionKernel h,
      Function.Surjective (CubicAction.projection h e hz hk) ∧
      2 < sourceDistance h ∧
      (∀ a : Vertex Rg, color Rg a = false → Nat.card (U Rg a) = 16 ∨ Nat.card (U Rg a) = 32) ∧
      ∀ (u : Equiv.Perm (Fin 6)),
        (Rg).map (CubicAction.projection h e hz hk) = pointCore.map (MulAut.conj u).toMonoidHom →
        ∀ (a' : Vertex Rg) (p : CriticalPath Rg (sourceGeometry h) (alpha Rg) a'),
          (Q Rg a').relIndex (Z Rg (alpha Rg)) < 4 →
          (B Rg (alpha Rg) ((sourceGeometry h).Z_normal _)).relIndex (U Rg (p.walk.getVert 2)) ≤ 2 →
          ¬ U Rg (p.walk.getVert 2) ≤ B Rg (alpha Rg) ((sourceGeometry h).Z_normal _) →
          ∃ s : SmallSliceShift h p,
            ⁅s.span,s.kernel⁆ = s.line ∧ Nat.card s.line = 2 ∧
            s.line ≤ centralizer (stabilizer Rg s.centerVertex : Set (FreeAmalgam Rg)) ∧
            (¬ s.span ≤ B Rg s.centerVertex ((sourceGeometry h).Z_normal _)) ∧
            (4 < sourceDistance h →
              s.span ≤ Q Rg (p.walk.getVert (p.walk.length-2)) ∧
              Z Rg a' ≤ Q Rg s.centerVertex ∧ s.span ≤ Q Rg a') := by
  rcases CubicEven.coreExhaustion_or_cubic_fullSymmetric h e hz with hx | ⟨hk,hs,hb⟩
  · exact Or.inl hx
  · refine Or.inr ⟨hk,hs,hb,graph_U_card h e hz hk,?_⟩
    intro u hfull a' p hsmall hslice hel
    obtain ⟨s⟩ := exists_small_slice_shift h e hz hk hb u hfull p hsmall hslice hel
    have hf := s.line_facts e hz hk hb hsmall hslice hel
    refine ⟨s,s.span_commutator e hz hk hb hsmall hslice,hf.1,hf.2,s.span_not_le_slice hb hel,?_⟩
    intro hb4
    exact ⟨(s.inner_control e hz hk hb4 hsmall hslice hel).1,
      s.old_endpoint_core e hz hk hb4 hsmall hslice hel⟩

omit hk in
include h e hz in
/-- Literal C.1.32 application of the shifted-span containment. Strict slice
exclusion and the remaining source branches are still assembly obligations. -/
theorem rankTwo_or_cubic_shifted_span_core :
    RankTwoAlternatives L R ∨ ∃ hk : layerKernel L R = extensionKernel h,
      Function.Surjective (CubicAction.projection h e hz hk) ∧
      2 < sourceDistance h ∧
      (∀ a : Vertex Rg, color Rg a = false → Nat.card (U Rg a) = 16 ∨ Nat.card (U Rg a) = 32) ∧
      ∀ (u : Equiv.Perm (Fin 6)),
        (Rg).map (CubicAction.projection h e hz hk) = pointCore.map (MulAut.conj u).toMonoidHom →
        ∀ (a' : Vertex Rg) (p : CriticalPath Rg (sourceGeometry h) (alpha Rg) a'),
          (Q Rg a').relIndex (Z Rg (alpha Rg)) < 4 →
          (B Rg (alpha Rg) ((sourceGeometry h).Z_normal _)).relIndex (U Rg (p.walk.getVert 2)) ≤ 2 →
          ¬ U Rg (p.walk.getVert 2) ≤ B Rg (alpha Rg) ((sourceGeometry h).Z_normal _) →
          ∃ s : SmallSliceShift h p,
            ⁅s.span,s.kernel⁆ = s.line ∧ Nat.card s.line = 2 ∧
            s.line ≤ centralizer (stabilizer Rg s.centerVertex : Set (FreeAmalgam Rg)) ∧
            (¬ s.span ≤ B Rg s.centerVertex ((sourceGeometry h).Z_normal _)) ∧
            (4 < sourceDistance h →
              s.span ≤ Q Rg (p.walk.getVert (p.walk.length-2)) ∧
              Z Rg a' ≤ Q Rg s.centerVertex ∧ s.span ≤ Q Rg a') :=
  (coreExhaustion_or_cubic_shifted_span_core h e hz).imp (rankTwo_of_exhaustion h e hz) id

end AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicFull
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
