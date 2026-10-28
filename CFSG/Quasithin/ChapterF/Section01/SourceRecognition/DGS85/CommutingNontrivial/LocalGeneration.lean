module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingNontrivial.EdgeDisplacement
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingNontrivial.SylowSeparation
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.Noncommuting.PathControl

/-!
# The full moving edge generates the terminal local group

An actual edge Sylow has its normalizer equal to the edge stabilizer inside
L, and fixes only its marked neighbor. If the elementary span V_beta were
contained in the moving edge, its escaping image modulo Q would force the
preceding and moving edge Sylows to coincide. Their unique fixed neighbor
would then contradict the nonzero moving commutator. The rank-one proper
overgroup theorem consequently gives generation by V_beta and that edge
Sylow. Together with the proved displacement this establishes relative
normality of H, containment in every neighboring center, and the 6.5
centralizer obstruction, without local generation or displacement premises.

Source: DGS, *Groups and Graphs* (1985), 5.1(c,d), pp.104--105;
8.1(g,i), pp.132--133. The actual earlier 6.1 quotient markings include D₁₀.
The later distance, equal-field and natural-module conclusions remain separate.
-/

@[expose] public noncomputable section
open Subgroup Representation.RankOne.QuadraticRecognition
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingNontrivial
open Subgroup.CosetGeometry.RankTwo Theory.GroupTheory.AmalgamGraph
variable {G : Type*} [Group G] {P : Fin 2 → Subgroup G} {B : Subgroup G}

private theorem restrict_sylow_image (D L : Subgroup G) (hLD : L ≤ D)
    (T : Sylow 2 D) (hTL : (T : Subgroup D).map D.subtype ≤ L) :
    ∃ R : Sylow 2 L, (R : Subgroup L).map L.subtype = (T : Subgroup D).map D.subtype := by
  let f : L →* D := inclusion hLD
  have hr : (T : Subgroup D) ≤ f.range := fun t ht =>
    ⟨⟨t, hTL (mem_map_of_mem D.subtype ht)⟩, rfl⟩
  let R := T.comapOfInjective f (inclusion_injective _) hr
  refine ⟨R, ?_⟩
  have he : (R : Subgroup L).map f = T := map_comap_eq_self hr
  have hm := congrArg (Subgroup.map D.subtype) he
  rw [map_map] at hm
  exact hm

/-- The full edge core is the actual image of a Sylow of the local actor. -/
theorem source_edge_core_local_sylow (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (d : EarlierLocalTheorems (family P))
    {v w : Vertex (family P)} (hvw : (graph (family P)).Adj v w) :
    ∃ R : Sylow 2 (d.localGroup v),
      (R : Subgroup (d.localGroup v)).map (d.localGroup v).subtype =
        (stabilizer (family P) v ⊓ stabilizer (family P) w).pCoreIn 2 := by
  let := finite_endpoints h
  obtain ⟨T, T', hTT⟩ := d.common_sylow v w hvw
  have hTE : (T : Subgroup (stabilizer (family P) v)).map
      (stabilizer (family P) v).subtype ≤ stabilizer (family P) v ⊓ stabilizer (family P) w :=
    le_inf (map_subtype_le _) (hTT ▸ map_subtype_le _)
  obtain ⟨R, hR⟩ := restrict_sylow_image _ _ (d.local_le v) T (d.sylow_le v T)
  exact ⟨R, hR.trans (sylow_image_eq_edge_core _ _ inf_le_left
    (source_edge_core_sylow h hB hvw) T hTE)⟩

private theorem normalizer_image_comap (L : Subgroup G) (R : Subgroup L) :
    (normalizer (R.map L.subtype : Set G)).subgroupOf L = normalizer (R : Set L) := by
  rw [subgroupOf, comap_normalizer_eq_of_le_range (map_le_range _ _),
    comap_map_eq_self_of_injective L.subtype_injective]

/-- The point stabilizer in the local actor is precisely the normalizer
of its actual edge Sylow. The full stabilizer and full edge are retained. -/
theorem source_edge_local_normalizer (h : LocallyRankOneTriple P B)
    (d : EarlierLocalTheorems (family P))
    {v w : Vertex (family P)} (hvw : (graph (family P)).Adj v w)
    (M : IsRankOneModel (d.localGroup v ⧸ pCore 2 (d.localGroup v)))
    (R : Sylow 2 (d.localGroup v))
    (hR : (R : Subgroup (d.localGroup v)).map (d.localGroup v).subtype =
      (stabilizer (family P) v ⊓ stabilizer (family P) w).pCoreIn 2) :
    stabilizer (family P) v ⊓ normalizer
      ((R : Subgroup (d.localGroup v)).map (d.localGroup v).subtype : Set G) =
        stabilizer (family P) v ⊓ stabilizer (family P) w ∧
    (stabilizer (family P) w).subgroupOf (d.localGroup v) = normalizer (R : Set (d.localGroup v)) := by
  let := finite_endpoints h
  let L := d.localGroup v
  let : Finite L := Finite.of_injective (inclusion (d.local_le v)) (inclusion_injective _)
  let E := stabilizer (family P) v ⊓ stabilizer (family P) w
  have hnorm : E ≤ normalizer ((R : Subgroup L).map L.subtype : Set G) := by
    rw [hR]
    exact E.le_normalizer.trans (normalizer_le_normalizer_characteristic_image E (pCore 2 E))
  have heq : stabilizer (family P) v ⊓ normalizer ((R : Subgroup L).map L.subtype : Set G) = E := by
    rcases source_edge_maximal h hvw _ (le_inf inf_le_left hnorm) inf_le_left with he | he
    · exact he
    · exfalso
      have htop : normalizer (R : Set L) = ⊤ := by
        change normalizer ((R : Subgroup L) : Set L) = ⊤
        rw [← normalizer_image_comap L (R : Subgroup L)]
        apply eq_top_iff.mpr
        intro l _
        exact ((he.ge (d.local_le v l.property)).2)
      exact (rankOneSylowFacts_of_quotient R (M.rankOneSylowFacts _)).proper.ne htop
  refine ⟨heq, ?_⟩
  change (stabilizer (family P) w).subgroupOf L = normalizer ((R : Subgroup L) : Set L)
  rw [← normalizer_image_comap L (R : Subgroup L)]
  ext l
  change (l : G) ∈ stabilizer (family P) w ↔
    (l : G) ∈ normalizer ((R : Subgroup L).map L.subtype : Set G)
  exact ⟨fun hl => (heq.ge ⟨d.local_le v l.property, hl⟩).2,
    fun hl => (heq.le ⟨d.local_le v l.property, hl⟩).2⟩

private theorem sylow_unique_fixed {X : Type*} [MulAction G X]
    (L : Subgroup G) [Finite L] (R : Sylow 2 L) (x : X)
    (hstab : (MulAction.stabilizer G x).subgroupOf L = normalizer (R : Set L))
    (g : L)
    (hfix : ∀ t ∈ (R : Subgroup L), (t : G) • ((g : G) • x) = (g : G) • x) :
    (g : G) • x = x := by
  let S := R.mapSurjective (f := (MulAut.conj g⁻¹).toMonoidHom) (MulAut.conj g⁻¹).surjective
  have hn : (S : Subgroup L) ≤ normalizer (R : Set L) := by
    rw [← hstab]
    rintro s ⟨t, ht, rfl⟩
    change (((g : G)⁻¹ * (t : G) * (g : G)⁻¹⁻¹) • x) = x
    rw [inv_inv, mul_smul, mul_smul, hfix t ht, inv_smul_smul]
  have hs : (S : Subgroup L) ≤ R := by
    have hi := S.isPGroup'.inf_normalizer_sylow R
    rw [inf_eq_left.mpr hn] at hi
    exact inf_eq_left.mp hi.symm
  have he : S = R := Sylow.ext (S.is_maximal' R.isPGroup' hs).symm
  have hg : g⁻¹ ∈ normalizer (R : Set L) := mem_normalizer_iff_map_conj_eq.mpr
    (congrArg (fun T : Sylow 2 L => (T : Subgroup L)) he)
  have hg' : g ∈ normalizer (R : Set L) := by
    simpa only [inv_inv] using (normalizer (R : Set L)).inv_mem hg
  rw [← hstab] at hg'
  exact hg'

/-- One edge Sylow fixes exactly its marked neighbor under the actual local action. -/
theorem source_edge_sylow_unique_neighbor (h : LocallyRankOneTriple P B)
    (d : EarlierLocalTheorems (family P))
    {v w z : Vertex (family P)} (hvw : (graph (family P)).Adj v w)
    (hvz : (graph (family P)).Adj v z)
    (M : IsRankOneModel (d.localGroup v ⧸ pCore 2 (d.localGroup v)))
    (R : Sylow 2 (d.localGroup v))
    (hR : (R : Subgroup (d.localGroup v)).map (d.localGroup v).subtype =
      (stabilizer (family P) v ⊓ stabilizer (family P) w).pCoreIn 2)
    (hRz : (R : Subgroup (d.localGroup v)).map (d.localGroup v).subtype ≤ stabilizer (family P) z) :
    z = w := by
  let := finite_endpoints h
  let : Finite (d.localGroup v) := Finite.of_injective (inclusion (d.local_le v)) (inclusion_injective _)
  obtain ⟨g, hg, hgz⟩ := d.transitive v ⟨w, hvw⟩ ⟨z, hvz⟩
  have he := sylow_unique_fixed (d.localGroup v) R w
    (source_edge_local_normalizer h d hvw M R hR).2 ⟨g, hg⟩ (by
      intro t ht
      rw [hgz]
      exact hRz (mem_map_of_mem _ ht))
  exact hgz.symm.trans he

/-- The nonzero moving commutator forces V_beta to escape the entire moving
edge. This is the missing geometric premise of source 8.1(g). -/
theorem source_span_escapes_moving_edge (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (d : EarlierLocalTheorems (family P))
    {a beta a' : Vertex (family P)} (hc : IsCriticalPair (family P) a a')
    (hab : (graph (family P)).Adj a beta)
    (hd : (graph (family P)).dist beta a' + 1 = b (family P))
    (hb : 1 < b (family P)) (hcomm : ⁅Z (family P) a, Z (family P) a'⁆ = ⊥)
    (M : IsRankOneModel (d.localGroup a' ⧸ pCore 2 (d.localGroup a')))
    (w : (graph (family P)).neighborSet a')
    (hm : ⁅V (family P) beta 1 ⊓ Q (family P) a', Z (family P) w.val⁆ ≠ ⊥) :
    ¬ V (family P) beta 1 ≤ stabilizer (family P) a' ⊓ stabilizer (family P) w.val := by
  let := finite_endpoints h
  let F := family P
  let L := d.localGroup a'
  let A := V F beta 1
  let : Finite L := Finite.of_injective (inclusion (d.local_le a')) (inclusion_injective _)
  obtain ⟨_, hb3, _, _, prev, hp, _, hAP, _⟩ := source_critical_geometry h d hc hab hd hb hcomm
  let : IsElementaryAbelian 2 A := CommutingThreeProfile.V_elementary F h.generate
    (fun v => (source_Z_Q_U h v).1) d.kernel_sylow (by change 2 < b (family P); omega) beta
  obtain ⟨R, hR⟩ := source_edge_core_local_sylow h hB d hp
  obtain ⟨T, hT⟩ := source_edge_core_local_sylow h hB d w.property
  have hAR : A ≤ (R : Subgroup L).map L.subtype := by
    rw [hR]
    exact hAP.trans (by simpa only [inf_comm] using Noncommuting.graph_Q_le_edgeCore h hp.symm)
  have hAL : A ≤ L := hAR.trans (map_subtype_le _)
  let : IsElementaryAbelian 2 (A.subgroupOf L) := IsElementaryAbelian.subgroupOf hAL
  let : Finite ↥(stabilizer F a' ⊓ stabilizer F w.val : Subgroup G) :=
    Finite.of_injective (inclusion (show stabilizer F a' ⊓ stabilizer F w.val ≤
      stabilizer F a' from inf_le_left)) (inclusion_injective _)
  intro hAE
  have hAT : A ≤ (T : Subgroup L).map L.subtype := by
    rw [hT]
    exact pGroup_le_core_of_core_sylow _ A hAE (IsElementaryAbelian.isPGroup 2 A)
      (source_edge_core_sylow h hB w.property)
  have hRT : R = T := local_sylow_eq_of_elementary_escape M R T (A.subgroupOf L)
    (by intro x hx; obtain ⟨y, hy, he⟩ := hAR hx; exact (Subtype.ext he : y = x) ▸ hy)
    (by intro x hx; obtain ⟨y, hy, he⟩ := hAT hx; exact (Subtype.ext he : y = x) ▸ hy) (by
      intro he
      apply hc.2
      apply (Z_neighbor_le_V F hab.symm).trans
      intro x hx
      apply (source_Z_Q_U h a').2
      rw [← localGroup_core_eq F d a']
      exact ⟨⟨x, hAL hx⟩, he hx, rfl⟩)
  have hpw : prev = w.val := source_edge_sylow_unique_neighbor h d w.property hp M T hT (by
    rw [← hRT, hR]
    exact (pCoreIn_le 2 _).trans inf_le_right)
  apply hm
  apply commutator_eq_bot_iff_le_centralizer.mpr
  exact (inf_le_left.trans (hpw ▸ hAP)).trans
    (le_centralizer_iff.mp (Z_centralizes_Q F w.val (source_Z_Q_U h w.val).1))

/-- Source 8.1(g) on the full edge: V_beta and its actual edge Sylow
generate the terminal local group. -/
theorem source_moving_edge_generation (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (d : EarlierLocalTheorems (family P))
    {a beta a' : Vertex (family P)} (hc : IsCriticalPair (family P) a a')
    (hab : (graph (family P)).Adj a beta)
    (hd : (graph (family P)).dist beta a' + 1 = b (family P))
    (hb : 1 < b (family P)) (hcomm : ⁅Z (family P) a, Z (family P) a'⁆ = ⊥)
    (M : IsRankOneModel (d.localGroup a' ⧸ pCore 2 (d.localGroup a')))
    (w : (graph (family P)).neighborSet a')
    (hm : ⁅V (family P) beta 1 ⊓ Q (family P) a', Z (family P) w.val⁆ ≠ ⊥) :
    ∃ T : Sylow 2 ↥(stabilizer (family P) a' ⊓ stabilizer (family P) w.val : Subgroup G),
      V (family P) beta 1 ⊔
        (T : Subgroup ↥(stabilizer (family P) a' ⊓ stabilizer (family P) w.val : Subgroup G)).map
          (stabilizer (family P) a' ⊓ stabilizer (family P) w.val).subtype = d.localGroup a' := by
  let := finite_endpoints h
  let F := family P
  let L := d.localGroup a'
  let A := V F beta 1
  let E := stabilizer F a' ⊓ stabilizer F w.val
  let : Finite L := Finite.of_injective (inclusion (d.local_le a')) (inclusion_injective _)
  obtain ⟨_, hb3, _, _, prev, hp, _, hAP, _⟩ := source_critical_geometry h d hc hab hd hb hcomm
  let : IsElementaryAbelian 2 A := CommutingThreeProfile.V_elementary F h.generate
    (fun v => (source_Z_Q_U h v).1) d.kernel_sylow (by change 2 < b (family P); omega) beta
  have hAL : A ≤ L := pGroup_le_localGroup F d a' A (IsElementaryAbelian.isPGroup 2 A)
    (V_le_stabilizer_of_dist_add_le_b F h.generate beta a' 1 hd.le)
  obtain ⟨R, hR⟩ := source_edge_core_local_sylow h hB d w.property
  have hEL : E.pCoreIn 2 ≤ L := hR ▸ map_subtype_le _
  have hjoin : A ⊔ E.pCoreIn 2 = L := by
    apply le_antisymm (sup_le hAL hEL)
    rcases relative_rankOne_overgroup L (A ⊔ E.pCoreIn 2)
      ((sup_le hAL hEL).trans L.le_normalizer) R
      (fun H hRH hn => (rankOneSylowFacts_of_quotient R
        (M.rankOneSylowFacts _)).unique_maximal H hRH (lt_top_iff_ne_top.mpr hn))
      (hR ▸ le_sup_right) with hle | hn
    · exact hle
    · exact (source_span_escapes_moving_edge h hB d hc hab hd hb hcomm M w hm
        ((le_inf (hAL.trans (d.local_le a')) (le_sup_left.trans hn)).trans_eq
          (source_edge_local_normalizer h d w.property M R hR).1)).elim
  obtain ⟨T, hT⟩ := source_edge_core_sylow h hB w.property
  refine ⟨T, ?_⟩
  rw [hT]
  exact hjoin

/-- Source 8.1(i), with both local generation and displacement proved.
The remaining inputs are the earlier local results and the actual 6.1
quotient models, including D₁₀. Normality is relative to L at the end. -/
theorem source_critical_commutator_structure (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (d : EarlierLocalTheorems (family P))
    {a beta a' : Vertex (family P)} (hc : IsCriticalPair (family P) a a')
    (hab : (graph (family P)).Adj a beta)
    (hd : (graph (family P)).dist beta a' + 1 = b (family P))
    (hb : 1 < b (family P)) (hcomm : ⁅Z (family P) a, Z (family P) a'⁆ = ⊥)
    (models : ∀ v : Vertex (family P), IsRankOneModel (d.localGroup v ⧸ pCore 2 (d.localGroup v))) :
    let H := ⁅V (family P) beta 1 ⊓ Q (family P) a', V (family P) a' 1⁆
    (H.subgroupOf (d.localGroup a')).Normal ∧
      (∀ w : (graph (family P)).neighborSet a', H ≤ Z (family P) w.val) ∧
      ∀ w : (graph (family P)).neighborSet a',
        ¬ ∃ T : Sylow 2 ↥(d.localGroup a' ⊓ centralizer (H : Set G) : Subgroup G),
          (T : Subgroup ↥(d.localGroup a' ⊓ centralizer (H : Set G) : Subgroup G)).map
            (d.localGroup a' ⊓ centralizer (H : Set G)).subtype = Q (family P) w.val :=
  source_critical_normality_of_generation h d hc hab hd hb hcomm (fun w => models w.val)
    (fun w hw => source_moving_edge_generation h hB d hc hab hd hb hcomm (models a') w hw)

end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingNontrivial
