module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingNontrivial.ResidualCentral

/-!
# Quotient-omega displacement in the original residual denominator

The moving elementary actor has displacement in H. The whole edge
normalizer preserves the local residual at the ending vertex, so all its
conjugates have displacement in C_Z_lambda(O²(L_alpha')). The quotient
omega-generation theorem identifies their span modulo Q_lambda with the
full quotient Sylow omega-center. The kernel centralizes Z_lambda, giving
the printed inclusion [Z_lambda,Z] ≤ A before the torus comparison.

Source: DGS, Groups and Graphs (1985), 8.3, p.135. This is weaker than the
8.3 conclusion [Z_lambda,Z] ≤ H; that conclusion still requires the paired
residual-module inequalities.
-/

@[expose] public noncomputable section
open Subgroup
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingNontrivial
open Subgroup.CosetGeometry.RankTwo Theory.GroupTheory.AmalgamGraph
universe u
variable {G : Type u} [Group G] {P : Fin 2 → Subgroup G} {B : Subgroup G}

/-- The full quotient omega-center has displacement in the literal residual
fixed subgroup A at the moving neighbor. The rank-one normalizer generates
the full actor, and the original core is killed by actual centralization. -/
theorem source_omega_displacement_residual_fixed (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (d : EarlierLocalTheorems (family P))
    {a beta a' : Vertex (family P)} (hc : IsCriticalPair (family P) a a')
    (hab : (graph (family P)).Adj a beta)
    (hd : (graph (family P)).dist beta a' + 1 = b (family P))
    (hb : 1 < b (family P)) (hcomm : ⁅Z (family P) a,Z (family P) a'⁆ = ⊥)
    (models : ∀ v : Vertex (family P), IsRankOneModel (d.localGroup v ⧸ pCore 2 (d.localGroup v)))
    (w : (graph (family P)).neighborSet a')
    (hm : ⁅V (family P) beta 1 ⊓ Q (family P) a',Z (family P) w.val⁆ ≠ ⊥)
    (hescape : ¬ Q (family P) w.val ≤ Q (family P) a')
    (R : Sylow 2 (d.localGroup w.val))
    (hR : (R : Subgroup (d.localGroup w.val)).map (d.localGroup w.val).subtype =
      (stabilizer (family P) w.val ⊓ stabilizer (family P) a').pCoreIn 2) :
    let F := family P
    ⁅quotientSylowOmegaPreimage (d.localGroup w.val) R,Z F w.val⁆ ≤
      Z F w.val ⊓ centralizer
        ((pResidual 2 (d.localGroup a')).map (d.localGroup a').subtype : Set G) := by
  let := finite_endpoints h
  let F := family P
  let L := d.localGroup w.val
  let A := V F beta 1 ⊓ Q F a'
  let N := (normalizer (R : Set L)).map L.subtype
  let C := Z F w.val ⊓ centralizer
    ((pResidual 2 (d.localGroup a')).map (d.localGroup a').subtype : Set G)
  let D := conjugateSpanBy A N
  let : Finite L := Finite.of_injective (inclusion (d.local_le w.val)) (inclusion_injective _)
  have hb3 : 3 ≤ b F := (source_critical_geometry h d hc hab hd hb hcomm).2.1
  let : IsElementaryAbelian 2 (V F beta 1) := CommutingThreeProfile.V_elementary F h.generate
    (fun v => (source_Z_Q_U h v).1) d.kernel_sylow (by omega) beta
  let : IsElementaryAbelian 2 A := IsElementaryAbelian.of_le inf_le_left
  obtain ⟨_,hAL,_,hAQ,_⟩ := source_moving_actor h d hc hab hd hb hcomm w hm
  have hAR : A ≤ (R : Subgroup L).map L.subtype := by
    rw [hR]
    exact inf_le_right.trans (by simpa only [inf_comm] using Noncommuting.graph_Q_le_edgeCore h w.property)
  have hAN : A ≤ N := hAR.trans (map_mono (R : Subgroup L).le_normalizer)
  have hNend : N ≤ stabilizer F a' := by
    have he := (source_edge_local_normalizer h d w.property.symm (models w.val) R hR).2
    rintro x ⟨l,hl,rfl⟩
    have hl' : l ∈ (stabilizer F a').subgroupOf L := he.symm ▸ hl
    exact hl'
  have hNZ : N ≤ normalizer (Z F w.val : Set G) :=
    ((map_subtype_le _).trans (d.local_le w.val)).trans (stabilizer_normalizes_Z F w.val)
  have hNL : N ≤ normalizer (d.localGroup a' : Set G) := by
    intro g hg
    apply mem_normalizer_iff_map_conj_eq.mpr
    exact (d.conjugate g a').symm.trans (congrArg d.localGroup (hNend hg))
  have hNC : N ≤ normalizer (C : Set G) :=
    (le_inf hNZ ((hNL.trans (normalizer_le_normalizer_characteristic_image
      (d.localGroup a') (pResidual 2 (d.localGroup a')))).trans
      (normalizer_le_normalizer_centralizer _))).trans inf_normalizer_le_normalizer_inf
  have hAC : ⁅A,Z F w.val⁆ ≤ C := by
    have hH := source_critical_displacement_residual_fixed h hB d hc hab hd hb hcomm models w hescape
    have hHZ := (source_critical_commutator_structure h hB d hc hab hd hb hcomm models).2.1 w
    exact (commutator_mono le_rfl (Z_neighbor_le_V F w.property)).trans
      (le_inf hHZ (hH.trans inf_le_right))
  have hDC : ⁅D,Z F w.val⁆ ≤ C := by
    rw [commutator_conjugateSpanBy_of_normalized_right A N _ hAN hNZ]
    exact conjugateSpanBy_le hAC hNC
  let : IsElementaryAbelian 2 (A.subgroupOf L) := IsElementaryAbelian.subgroupOf hAL
  have hAS : A.subgroupOf L ≤ R := by
    intro x hx
    obtain ⟨y,hy,he⟩ := hAR hx
    exact (Subtype.ext he : y=x) ▸ hy
  have hne : (A.subgroupOf L).map (QuotientGroup.mk' (pCore 2 L)) ≠ ⊥ := by
    intro he
    have hk := (Subgroup.map_eq_bot_iff _).mp he
    rw [QuotientGroup.ker_mk'] at hk
    apply hAQ
    rw [←localGroup_core_eq F d w.val]
    intro x hx
    exact ⟨⟨x,hAL hx⟩,hk hx,rfl⟩
  have he := source_rank_one_omega_preimage (QuotientGroup.mk' (pCore 2 L))
    (QuotientGroup.mk'_surjective _) (models w.val) R
    (by rw [QuotientGroup.ker_mk']; exact pCore_isPGroup.le_sylow_of_normal R)
    (A.subgroupOf L) hAS hne
  have hY : quotientSylowOmegaPreimage L R = D ⊔ L.pCoreIn 2 := by
    unfold quotientSylowOmegaPreimage
    change (omegaCenterIn ((R : Subgroup L).map (QuotientGroup.mk' (pCore 2 L)))).comap
      (QuotientGroup.mk' (pCore 2 L)) = _ at he
    rw [he,Subgroup.map_sup,map_conjugateSpanBy,map_subgroupOf_eq_of_le hAL,QuotientGroup.ker_mk']
    rfl
  have hQZ : L.pCoreIn 2 ≤ centralizer (Z F w.val : Set G) := by
    rw [localGroup_core_eq F d w.val]
    exact le_centralizer_iff.mp (Z_centralizes_Q F w.val (source_Z_Q_U h w.val).1)
  rw [hY]
  exact commutator_sup_le_of_relative_normal (normalizer (C : Set G)) D (L.pCoreIn 2)
    (Z F w.val) C le_rfl ((conjugateSpanBy_le_self hAN).trans hNC)
    ((hQZ.trans (centralizer_le inf_le_left)).trans (centralizer_le_normalizer _)) hDC
    ((commutator_eq_bot_iff_le_centralizer.mpr hQZ).le.trans bot_le)

end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingNontrivial
