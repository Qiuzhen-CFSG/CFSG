module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingNontrivial.ResidualCentral

/-!
# Quotient omega centralizes the entire neighboring-center intersection

A moving seed A = V_beta ∩ Q_alpha' centralizes the intersection X of all
centers neighboring alpha'. Transport A along L_alpha' to an arbitrary
neighbor. The transported elementary seed still centralizes X and escapes
the new neighbor core. The full edge normalizer preserves X, so its span of
the seed, together with the core, centralizes X. The rank-one omega-generation
theorem identifies that span with the entire quotient Sylow omega preimage.

In particular H centralizes this preimage even at the preceding nonmoving
neighbor. This strengthens the moving-edge formulation of DGS 8.1(h) and
supplies the opposed-root comparison in 8.7. Source: DGS, *Groups and Graphs*
(1985), 8.1(h,i), printed pp.132--134, and 8.7, printed p.140.
-/

@[expose] public noncomputable section
open Subgroup Representation BenderSuzuki.MatrixGroups
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingNontrivial
open Subgroup.CosetGeometry.RankTwo Theory.GroupTheory.AmalgamGraph
universe u
variable {G : Type u} [Group G] {P : Fin 2 → Subgroup G} {B : Subgroup G}

private theorem omega_preimage_centralizes (L : Subgroup G) [Finite L]
    (M : IsRankOneModel (L ⧸ pCore 2 L)) (S : Sylow 2 L)
    (A X : Subgroup G) [IsElementaryAbelian 2 A]
    (hAL : A ≤ L) (hAS : A ≤ (S : Subgroup L).map L.subtype)
    (hne : (A.subgroupOf L).map (QuotientGroup.mk' (pCore 2 L)) ≠ ⊥)
    (hNX : (normalizer (S : Set L)).map L.subtype ≤ normalizer (X : Set G))
    (hAX : A ≤ centralizer (X : Set G))
    (hQX : L.pCoreIn 2 ≤ centralizer (X : Set G)) :
    X ≤ centralizer (quotientSylowOmegaPreimage L S : Set G) := by
  let N := (normalizer (S : Set L)).map L.subtype
  let D := conjugateSpanBy A N
  have hDX : D ≤ centralizer (X : Set G) :=
    conjugateSpanBy_le hAX (hNX.trans (normalizer_le_normalizer_centralizer _))
  let : IsElementaryAbelian 2 (A.subgroupOf L) := IsElementaryAbelian.subgroupOf hAL
  have hA'S : A.subgroupOf L ≤ S := by
    intro a ha
    obtain ⟨s,hs,he⟩ := hAS ha
    exact (Subtype.ext he : s=a) ▸ hs
  have he := source_rank_one_omega_preimage (QuotientGroup.mk' (pCore 2 L))
    (QuotientGroup.mk'_surjective _) M S
    (by rw [QuotientGroup.ker_mk']; exact pCore_isPGroup.le_sylow_of_normal S)
    (A.subgroupOf L) hA'S hne
  have hY : quotientSylowOmegaPreimage L S = D ⊔ L.pCoreIn 2 := by
    unfold quotientSylowOmegaPreimage
    change (omegaCenterIn ((S : Subgroup L).map (QuotientGroup.mk' (pCore 2 L)))).comap
      (QuotientGroup.mk' (pCore 2 L)) = _ at he
    rw [he,Subgroup.map_sup,map_conjugateSpanBy,map_subgroupOf_eq_of_le hAL,
      QuotientGroup.ker_mk']
    rfl
  rw [hY]
  exact le_centralizer_iff.mp (sup_le hDX hQX)

theorem source_neighbor_intersection_omega_fixed
    (h : LocallyRankOneTriple P B) (d : EarlierLocalTheorems (family P))
    {a beta a' : Vertex (family P)} (hc : IsCriticalPair (family P) a a')
    (hab : (graph (family P)).Adj a beta)
    (hd : (graph (family P)).dist beta a' + 1 = b (family P))
    (hb : 1 < b (family P)) (hcomm : ⁅Z (family P) a,Z (family P) a'⁆ = ⊥)
    (w : (graph (family P)).neighborSet a')
    (hm : ⁅V (family P) beta 1 ⊓ Q (family P) a',Z (family P) w.val⁆ ≠ ⊥)
    (z : (graph (family P)).neighborSet a')
    (M : IsRankOneModel (d.localGroup z.val ⧸ pCore 2 (d.localGroup z.val)))
    (R : Sylow 2 (d.localGroup z.val))
    (hR : (R : Subgroup (d.localGroup z.val)).map (d.localGroup z.val).subtype =
      (stabilizer (family P) z.val ⊓ stabilizer (family P) a').pCoreIn 2) :
    neighborCenterIntersection (family P) a' ≤
      centralizer (quotientSylowOmegaPreimage (d.localGroup z.val) R : Set G) := by
  let := finite_endpoints h
  let F := family P
  let A := V F beta 1 ⊓ Q F a'
  let X := neighborCenterIntersection F a'
  let L := d.localGroup z.val
  let : Finite L := Finite.of_injective (inclusion (d.local_le z.val)) (inclusion_injective _)
  obtain ⟨_,hb3,_,_,prev,hp,_,hVP,_⟩ := source_critical_geometry h d hc hab hd hb hcomm
  let : IsElementaryAbelian 2 (V F beta 1) := CommutingThreeProfile.V_elementary F h.generate
    (fun v => (source_Z_Q_U h v).1) d.kernel_sylow (by change 2 < b (family P); omega) beta
  let : IsElementaryAbelian 2 A := IsElementaryAbelian.of_le inf_le_left
  have hAX : A ≤ centralizer (X : Set G) := by
    have hAP : A ≤ Q F prev := inf_le_left.trans hVP
    have hXP : X ≤ Z F prev := iInf_le (fun z : (graph F).neighborSet a' => Z F z.val) ⟨prev,hp⟩
    exact hAP.trans ((le_centralizer_iff.mp
      (Z_centralizes_Q F prev (source_Z_Q_U h prev).1)).trans (centralizer_le hXP))
  obtain ⟨g,hg,hgz⟩ := d.transitive a' w z
  let f := MulAut.conj g
  let A' := A.map f.toMonoidHom
  let : IsElementaryAbelian 2 A' := IsElementaryAbelian.map _
  have hga : g • a' = a' := d.local_le a' hg
  have hgz' : g • w.val = z.val := hgz
  have hQ : (Q F a').map f.toMonoidHom = Q F a' := by rw [←Q_translate,hga]
  have hA'Q : A' ≤ Q F a' := hQ ▸ map_mono (show A ≤ Q F a' from inf_le_right)
  have hA'R : A' ≤ (R : Subgroup L).map L.subtype := by
    rw [hR]
    exact hA'Q.trans (by simpa only [inf_comm] using Noncommuting.graph_Q_le_edgeCore h z.property)
  have hA'L : A' ≤ L := hA'R.trans (map_subtype_le _)
  have hA'X : A' ≤ centralizer (X : Set G) := by
    have hn := normalizer_le_normalizer_centralizer X
      ((neighborCenterIntersection_normalized F a') (d.local_le a' hg))
    rintro x ⟨y,hy,rfl⟩
    exact le_normalizer_iff.mp (show normalizer (centralizer (X : Set G) : Set G) ≤
      normalizer (centralizer (X : Set G) : Set G) from le_rfl) g hn y (hAX hy)
  have hA'escape : ¬ A' ≤ Q F z.val := by
    have hAQ : ¬ A ≤ Q F w.val := (source_moving_actor h d hc hab hd hb hcomm w hm).2.2.2.1
    have hQw : (Q F w.val).map f.toMonoidHom = Q F z.val := by rw [←Q_translate,hgz']
    rw [←hQw]
    exact fun hh => hAQ ((map_le_map_iff_of_injective f.injective).mp hh)
  have hne : (A'.subgroupOf L).map (QuotientGroup.mk' (pCore 2 L)) ≠ ⊥ := by
    intro he
    have hk := (Subgroup.map_eq_bot_iff _).mp he
    rw [QuotientGroup.ker_mk'] at hk
    apply hA'escape
    rw [←localGroup_core_eq F d z.val]
    intro x hx
    exact ⟨⟨x,hA'L hx⟩,hk hx,rfl⟩
  have hNX : (normalizer (R : Set L)).map L.subtype ≤ normalizer (X : Set G) := by
    rw [←(source_edge_local_normalizer h d z.property.symm M R hR).2]
    rintro x ⟨l,hl,rfl⟩
    exact (neighborCenterIntersection_normalized F a') hl
  have hQX : L.pCoreIn 2 ≤ centralizer (X : Set G) := by
    rw [localGroup_core_eq F d z.val]
    exact (le_centralizer_iff.mp (Z_centralizes_Q F z.val (source_Z_Q_U h z.val).1)).trans
      (centralizer_le (iInf_le (fun y : (graph F).neighborSet a' => Z F y.val) z))
  exact omega_preimage_centralizes L M R A' X hA'L hA'R hne hNX hA'X hQX

/-- The original nonzero critical displacement centralizes the full quotient
omega at every neighboring edge, including the preceding nonmoving edge. -/
theorem source_critical_neighbor_omega_fixed
    (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (d : EarlierLocalTheorems (family P))
    (models : ∀ v : Vertex (family P),
      IsRankOneModel (d.localGroup v ⧸ pCore 2 (d.localGroup v)))
    {a beta a' : Vertex (family P)} (hc : IsCriticalPair (family P) a a')
    (hab : (graph (family P)).Adj a beta)
    (hd : (graph (family P)).dist beta a' + 1 = b (family P))
    (hb : 1 < b (family P)) (hcomm : ⁅Z (family P) a,Z (family P) a'⁆ = ⊥)
    (hne : ⁅V (family P) beta 1 ⊓ Q (family P) a',V (family P) a' 1⁆ ≠ ⊥)
    (z : (graph (family P)).neighborSet a')
    (R : Sylow 2 (d.localGroup z.val))
    (hR : (R : Subgroup (d.localGroup z.val)).map (d.localGroup z.val).subtype =
      (stabilizer (family P) z.val ⊓ stabilizer (family P) a').pCoreIn 2) :
    let H := ⁅V (family P) beta 1 ⊓ Q (family P) a',V (family P) a' 1⁆
    H ≤ Z (family P) z.val ⊓
      centralizer (quotientSylowOmegaPreimage (d.localGroup z.val) R : Set G) := by
  obtain ⟨w,hm,_⟩ := exists_moving_neighbor (family P)
    (fun v => (source_Z_Q_U h v).1) beta a' hne
  have hHZ := (source_critical_commutator_structure h hB d hc hab hd hb hcomm models).2.1
  exact le_inf (hHZ z) ((le_iInf hHZ).trans
    (source_neighbor_intersection_omega_fixed h d hc hab hd hb hcomm w hm z (models z.val) R hR))

end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingNontrivial
