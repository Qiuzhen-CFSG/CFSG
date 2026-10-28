module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingNontrivial.OmegaGeneration
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingNontrivial.LocalGeneration
public import Theory.GroupTheory.Commutator.NormalSpan

/-!
# The entire quotient omega-center acts quadratically

Let A=V_beta∩Q_alpha' and let X be the intersection of the centers at all
neighbors of alpha'. Proved 8.1(i) puts H in X. The preceding vertex puts
A in C(X). The actual moving-edge normalizer preserves X and Z_lambda.
Its conjugates of A therefore centralize X and send Z_lambda into X.
The quotient omega-generation theorem identifies their span modulo Q_lambda
with the entire Ω₁(Z(T/Q_lambda)). Since Q_lambda centralizes Z_lambda,
the full preimage centralizes H and acts quadratically on Z_lambda.

This proves DGS, *Groups and Graphs* (1985), 8.1(h), pp.132–134, with the
whole quotient-center retained. The normalizer-span proof avoids selecting
an odd complement and includes all small source models. The graph need not
be a tree. `ReducedOmegaAction` is the literal reduced F1.11 application.
-/

@[expose] public noncomputable section
open Subgroup
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingNontrivial
open Subgroup.CosetGeometry.RankTwo
variable {G : Type*} [Group G]

/-- The original ambient preimage of Ω₁(Z(S/Q)), with its literal inclusion. -/
def quotientSylowOmegaPreimage (L : Subgroup G) (S : Sylow 2 L) : Subgroup G :=
  ((omegaCenterIn ((S : Subgroup L).map (QuotientGroup.mk' (pCore 2 L)) :
    Subgroup (L ⧸ pCore 2 L))).comap (QuotientGroup.mk' (pCore 2 L))).map L.subtype

private theorem omega_preimage_action (L : Subgroup G) [Finite L]
    (M : IsRankOneModel (L ⧸ pCore 2 L)) (S : Sylow 2 L)
    (A X Z : Subgroup G) [IsElementaryAbelian 2 A]
    (hAL : A ≤ L) (hAS : A ≤ (S : Subgroup L).map L.subtype)
    (hne : (A.subgroupOf L).map (QuotientGroup.mk' (pCore 2 L)) ≠ ⊥)
    (hNX : (normalizer (S : Set L)).map L.subtype ≤ normalizer (X : Set G))
    (hNZ : (normalizer (S : Set L)).map L.subtype ≤ normalizer (Z : Set G))
    (hAX : A ≤ centralizer (X : Set G)) (hAZ : ⁅A,Z⁆ ≤ X)
    (hXZ : X ≤ Z) (hQZ : L.pCoreIn 2 ≤ centralizer (Z : Set G)) :
    ⁅Z, quotientSylowOmegaPreimage L S⁆ ≤ X ∧
      X ≤ centralizer (quotientSylowOmegaPreimage L S : Set G) := by
  let N := (normalizer (S : Set L)).map L.subtype
  let D := conjugateSpanBy A N
  have hAN : A ≤ N := hAS.trans (map_mono (S : Subgroup L).le_normalizer)
  have hDX : D ≤ centralizer (X : Set G) :=
    conjugateSpanBy_le hAX (hNX.trans (normalizer_le_normalizer_centralizer _))
  have hDZ : ⁅D,Z⁆ ≤ X := by
    rw [commutator_conjugateSpanBy_of_normalized_right A N Z hAN hNZ]
    exact conjugateSpanBy_le hAZ hNX
  let : IsElementaryAbelian 2 (A.subgroupOf L) := IsElementaryAbelian.subgroupOf hAL
  have hA'S : A.subgroupOf L ≤ S := by
    intro a ha
    obtain ⟨s, hs, he⟩ := hAS ha
    exact (Subtype.ext he : s = a) ▸ hs
  have he := source_rank_one_omega_preimage (QuotientGroup.mk' (pCore 2 L))
    (QuotientGroup.mk'_surjective _) M S
    (by rw [QuotientGroup.ker_mk']; exact pCore_isPGroup.le_sylow_of_normal S)
    (A.subgroupOf L) hA'S hne
  have hY : quotientSylowOmegaPreimage L S = D ⊔ L.pCoreIn 2 := by
    unfold quotientSylowOmegaPreimage
    change (omegaCenterIn ((S : Subgroup L).map (QuotientGroup.mk' (pCore 2 L)))).comap
      (QuotientGroup.mk' (pCore 2 L)) = _ at he
    rw [he, Subgroup.map_sup, map_conjugateSpanBy, map_subgroupOf_eq_of_le hAL,
      QuotientGroup.ker_mk']
    rfl
  have hQX : L.pCoreIn 2 ≤ centralizer (X : Set G) := hQZ.trans (centralizer_le hXZ)
  rw [hY]
  refine ⟨?_, le_centralizer_iff.mp (sup_le hDX hQX)⟩
  rw [commutator_comm]
  exact commutator_sup_le_of_relative_normal (centralizer (X : Set G)) D (L.pCoreIn 2) Z X
    (Subgroup.centralizer_le_normalizer _) hDX hQX hDZ
    (commutator_eq_bot_iff_le_centralizer.mpr hQZ |>.le.trans bot_le)

/-- The intersection of all centers neighboring a vertex. -/
def neighborCenterIntersection (F : Bool → Subgroup G) (v : Vertex F) : Subgroup G :=
  ⨅ w : (graph F).neighborSet v, Z F w.val

/-- The whole stabilizer preserves the neighboring-center intersection. -/
theorem neighborCenterIntersection_normalized (F : Bool → Subgroup G) [∀ i, Finite (F i)]
    (v : Vertex F) :
    stabilizer F v ≤ normalizer (neighborCenterIntersection F v : Set G) := by
  apply le_normalizer_iff.mpr
  intro g hg x hx
  apply mem_iInf.mpr
  intro w
  have hgw : (graph F).Adj v (g⁻¹ • w.val) := by
    have he := (Subgroup.CosetGeometry.translationGraphIso F g⁻¹).map_adj_iff.mpr w.property
    change (graph F).Adj (g⁻¹ • v) (g⁻¹ • w.val) at he
    rwa [show g⁻¹ • v = v from (stabilizer F v).inv_mem hg] at he
  have hxz : x ∈ Z F (g⁻¹ • w.val) := mem_iInf.mp hx ⟨g⁻¹ • w.val,hgw⟩
  have hm := mem_map_of_mem (MulAut.conj g).toMonoidHom hxz
  rw [← Z_translate, smul_inv_smul] at hm
  exact hm

/-- Source 8.1(h), for the entire quotient Sylow omega-center at any moving
neighbor. Normality, generation, and the quotient action are proved on the
actual source graph. Only the genuine earlier local inputs remain. -/
theorem source_critical_quotient_omega_action
    {P : Fin 2 → Subgroup G} {B : Subgroup G} (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (d : EarlierLocalTheorems (family P))
    {a beta a' : Vertex (family P)} (hc : IsCriticalPair (family P) a a')
    (hab : (graph (family P)).Adj a beta)
    (hd : (graph (family P)).dist beta a' + 1 = b (family P))
    (hb : 1 < b (family P)) (hcomm : ⁅Z (family P) a, Z (family P) a'⁆ = ⊥)
    (models : ∀ v : Vertex (family P), IsRankOneModel (d.localGroup v ⧸ pCore 2 (d.localGroup v)))
    (w : (graph (family P)).neighborSet a')
    (hm : ⁅V (family P) beta 1 ⊓ Q (family P) a', Z (family P) w.val⁆ ≠ ⊥)
    (R : Sylow 2 (d.localGroup w.val))
    (hR : (R : Subgroup (d.localGroup w.val)).map (d.localGroup w.val).subtype =
      (stabilizer (family P) w.val ⊓ stabilizer (family P) a').pCoreIn 2) :
    let F := family P
    let H := ⁅V F beta 1 ⊓ Q F a', V F a' 1⁆
    let Y := quotientSylowOmegaPreimage (d.localGroup w.val) R
    H ≤ Z F w.val ⊓ centralizer (Y : Set G) ∧ ⁅⁅Z F w.val,Y⁆,Y⁆ = ⊥ := by
  dsimp only
  let := finite_endpoints h
  let F := family P
  let L := d.localGroup w.val
  let A := V F beta 1 ⊓ Q F a'
  let X := neighborCenterIntersection F a'
  let H := ⁅A,V F a' 1⁆
  let N := (normalizer (R : Set L)).map L.subtype
  let Y := quotientSylowOmegaPreimage L R
  let : Finite L := Finite.of_injective (inclusion (d.local_le w.val)) (inclusion_injective _)
  obtain ⟨_, hb3, _, _, prev, hp, _, hVP, _⟩ := source_critical_geometry h d hc hab hd hb hcomm
  let : IsElementaryAbelian 2 (V F beta 1) := CommutingThreeProfile.V_elementary F h.generate
    (fun v => (source_Z_Q_U h v).1) d.kernel_sylow (by change 2 < b (family P); omega) beta
  let : IsElementaryAbelian 2 A := IsElementaryAbelian.of_le inf_le_left
  obtain ⟨_, hAL, _, hescape, _⟩ := source_moving_actor h d hc hab hd hb hcomm w hm
  obtain ⟨_, hHZ, _⟩ := source_critical_commutator_structure h hB d hc hab hd hb hcomm models
  have hHX : H ≤ X := by
    change H ≤ ⨅ z : (graph F).neighborSet a', Z F z.val
    exact le_iInf (fun z => hHZ z)
  have hXZ : X ≤ Z F w.val := iInf_le (fun z : (graph F).neighborSet a' => Z F z.val) w
  have hAX : A ≤ centralizer (X : Set G) := by
    have hAP : A ≤ Q F prev := (show A ≤ V F beta 1 from inf_le_left).trans hVP
    have hXP : X ≤ Z F prev := iInf_le (fun z : (graph F).neighborSet a' => Z F z.val) ⟨prev,hp⟩
    exact hAP.trans ((le_centralizer_iff.mp
      (Z_centralizes_Q F prev (source_Z_Q_U h prev).1)).trans (centralizer_le hXP))
  have hAR : A ≤ (R : Subgroup L).map L.subtype := by
    rw [hR]
    exact inf_le_right.trans (by
      simpa only [inf_comm] using Noncommuting.graph_Q_le_edgeCore h w.property)
  have hNend : N ≤ stabilizer F a' := by
    have hn := (source_edge_local_normalizer h d w.property.symm (models w.val) R hR).2
    rintro x ⟨l, hl, rfl⟩
    have hl' : l ∈ (stabilizer F a').subgroupOf L := hn.symm ▸ hl
    exact hl'
  have hNw : N ≤ stabilizer F w.val := (map_subtype_le _).trans (d.local_le w.val)
  have hne : (A.subgroupOf L).map (QuotientGroup.mk' (pCore 2 L)) ≠ ⊥ := by
    intro he
    have hk := (Subgroup.map_eq_bot_iff (f := QuotientGroup.mk' (pCore 2 L))
      (A.subgroupOf L)).mp he
    rw [QuotientGroup.ker_mk'] at hk
    apply hescape
    rw [← localGroup_core_eq F d w.val]
    intro x hx
    exact ⟨⟨x,hAL hx⟩, hk hx, rfl⟩
  obtain ⟨hZY,hXY⟩ := omega_preimage_action L (models w.val) R A X (Z F w.val)
    hAL hAR hne (hNend.trans (neighborCenterIntersection_normalized F a'))
    (hNw.trans (stabilizer_normalizes_Z F w.val)) hAX
    ((commutator_mono le_rfl (Z_neighbor_le_V F w.property)).trans hHX) hXZ
    (by rw [localGroup_core_eq F d w.val]
        exact le_centralizer_iff.mp (Z_centralizes_Q F w.val (source_Z_Q_U h w.val).1))
  exact ⟨le_inf (hHZ w) (hHX.trans hXY),
    eq_bot_iff.mpr ((commutator_mono hZY le_rfl).trans
      (commutator_eq_bot_iff_le_centralizer.mpr hXY).le)⟩

end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingNontrivial
