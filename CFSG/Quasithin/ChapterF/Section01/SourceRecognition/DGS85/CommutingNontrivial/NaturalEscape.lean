module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingNontrivial.LocalGeneration
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.Noncommuting.CenterCommutators

/-!
# Reciprocal escape in the natural-center case of DGS 8.2

The full radius-one commutator strictly contains H: otherwise the moving
edge generation theorem would make a nonzero neighboring center normal
under both transitive local actors, contradicting graph faithfulness.

For an actual natural center, every escaping subgroup of the full edge
Sylow has the neighboring center as its commutator. Conjugating the literal
subgroups gives this calculation at every edge in the orbit, and hence on
the entire closed radius-one span. If V_alpha' were contained in Q_beta,
the two span commutators would be Z_beta and Z_alpha'. The latter centers
are conjugate and nested, so they coincide, contradicting the strict gap.

Source: Delgado--Goldschmidt--Stellmacher, *Groups and Graphs* (1985),
8.2, printed p.134, first case; 8.1(g,i), pp.132--133. The natural-center
hypothesis has actual matrix coordinates and the exact core kernel.
`RecognizedEscape` connects corrected 5.12 to this case and supplies the
reduced F1.11 application. The nonnatural case and 8.3--8.7 remain separate.
-/

@[expose] public noncomputable section
open Subgroup Representation
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingNontrivial
open Subgroup.CosetGeometry.RankTwo Theory.GroupTheory.AmalgamGraph
universe u
variable {G : Type u} [Group G] {P : Fin 2 → Subgroup G} {B : Subgroup G}

/-- The full radius-one commutator cannot lie in a moving neighboring center. -/
theorem source_full_commutator_not_le_moving_center (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (d : EarlierLocalTheorems (family P))
    {a beta a' : Vertex (family P)} (hc : IsCriticalPair (family P) a a')
    (hab : (graph (family P)).Adj a beta)
    (hd : (graph (family P)).dist beta a' + 1 = b (family P))
    (hb : 1 < b (family P)) (hcomm : ⁅Z (family P) a, Z (family P) a'⁆ = ⊥)
    (M : IsRankOneModel (d.localGroup a' ⧸ pCore 2 (d.localGroup a')))
    (w : (graph (family P)).neighborSet a')
    (hm : ⁅V (family P) beta 1 ⊓ Q (family P) a', Z (family P) w.val⁆ ≠ ⊥) :
    ¬ ⁅V (family P) beta 1, V (family P) a' 1⁆ ≤ Z (family P) w.val := by
  let := finite_endpoints h
  intro hle
  obtain ⟨T, hT⟩ := source_moving_edge_generation h hB d hc hab hd hb hcomm M w hm
  have hnorm : d.localGroup a' ≤ normalizer (Z (family P) w.val : Set G) := by
    rw [← hT]
    apply sup_le
    · exact le_normalizer_iff_commutator_le_right.mpr
        ((commutator_mono le_rfl (Z_neighbor_le_V (family P) w.property)).trans hle)
    · exact ((map_subtype_le _).trans inf_le_right).trans
        (stabilizer_normalizes_Z (family P) w.val)
  have hz : Z (family P) w.val = ⊥ := by
    apply source_normalized_edge_eq_bot h w.property _
      (le_inf (((source_Z_Q_U h w.val).1.trans (map_subtype_le _)).trans
        ((source_Z_Q_U h w.val).2.trans
          ((ballKernel_one_le_edge (family P) w.property.symm).trans inf_le_right)))
        (Z_le_stabilizer (family P) w.val))
    · intro z hz
      obtain ⟨g,hg,hgz⟩ := d.transitive a' w ⟨z,hz⟩
      exact ⟨g,hnorm hg,hgz⟩
    · intro z hz
      obtain ⟨g,hg,hgz⟩ := d.transitive w.val ⟨a',(show (graph (family P)).Adj a' w.val from w.property).symm⟩ ⟨z,hz⟩
      exact ⟨g,stabilizer_normalizes_Z (family P) w.val (d.local_le w.val hg),hgz⟩
  exact hm (by rw [hz,commutator_bot_right])

/-- The nonzero branch has a genuinely larger full commutator than H. -/
theorem source_commutator_strict_gap (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (d : EarlierLocalTheorems (family P))
    {a beta a' : Vertex (family P)} (hc : IsCriticalPair (family P) a a')
    (hab : (graph (family P)).Adj a beta)
    (hd : (graph (family P)).dist beta a' + 1 = b (family P))
    (hb : 1 < b (family P)) (hcomm : ⁅Z (family P) a, Z (family P) a'⁆ = ⊥)
    (models : ∀ v : Vertex (family P), IsRankOneModel (d.localGroup v ⧸ pCore 2 (d.localGroup v)))
    (hne : ⁅V (family P) beta 1 ⊓ Q (family P) a', V (family P) a' 1⁆ ≠ ⊥) :
    ⁅V (family P) beta 1 ⊓ Q (family P) a', V (family P) a' 1⁆ <
      ⁅V (family P) beta 1, V (family P) a' 1⁆ := by
  refine lt_of_le_not_ge (commutator_mono inf_le_left le_rfl) ?_
  obtain ⟨w,hm,_⟩ := exists_moving_neighbor (family P) (fun v => (source_Z_Q_U h v).1) beta a' hne
  have hHZ := (source_critical_commutator_structure h hB d hc hab hd hb hcomm models).2.1 w
  exact fun hle => source_full_commutator_not_le_moving_center h hB d hc hab hd hb hcomm
    (models a') w hm (hle.trans hHZ)

private theorem omega_eq_bot_of_center_eq_bot (L : Subgroup G) (hz : center L = ⊥) :
    Stellmacher.omegaOneCenterAmbient L = ⊥ := by
  apply bot_unique
  intro x hx
  obtain ⟨hxL,_,hxc⟩ := (Stellmacher.mem_omegaOneCenterAmbient_iff _ _).mp hx
  have hm : (⟨x,hxL⟩ : L) ∈ center L :=
    mem_center_iff.mpr (fun l => Subtype.ext (hxc l l.property))
  rw [hz,mem_bot] at hm
  exact congrArg Subtype.val hm

/-- At a central neighboring orbit, the full edge omega-center is its center span. -/
theorem source_central_edge_seed (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (d : EarlierLocalTheorems (family P)) {v w : Vertex (family P)}
    (he : (graph (family P)).Adj v w)
    (hcentral : Z (family P) w = omegaCenterIn (d.localGroup w)) :
    omegaCenterIn ((stabilizer (family P) v ⊓ stabilizer (family P) w).pCoreIn 2) =
      Z (family P) w ∧
    omegaCenterIn ((stabilizer (family P) v ⊓ stabilizer (family P) w).pCoreIn 2) ≤
      Z (family P) v := by
  let := finite_endpoints h
  obtain ⟨T,R,hTR⟩ := d.common_sylow v w he
  have hTS : (T : Subgroup (stabilizer (family P) v)).map (stabilizer (family P) v).subtype =
      (stabilizer (family P) v ⊓ stabilizer (family P) w).pCoreIn 2 :=
    sylow_image_eq_edge_core _ _ inf_le_left (source_edge_core_sylow h hB he) T
      (le_inf (map_subtype_le _) (hTR ▸ map_subtype_le _))
  have hRS := hTR.symm.trans hTS
  refine ⟨le_antisymm ?_ ?_, ?_⟩
  · rw [←hRS]
    exact le_iSup (fun R : Sylow 2 (stabilizer (family P) w) =>
      omegaCenterIn ((R : Subgroup (stabilizer (family P) w)).map
        (stabilizer (family P) w).subtype)) R
  · intro z hz
    apply (mem_omegaCenterIn_iff _ _).mpr
    refine ⟨?_, ?_, ?_⟩
    · rw [←hRS]
      exact pCoreIn_le_sylow _ R ((map_subtype_le _) ((source_Z_Q_U h w).1 hz))
    · have hSL : (stabilizer (family P) v ⊓ stabilizer (family P) w).pCoreIn 2 ≤
          d.localGroup w := hRS ▸ d.sylow_le w R
      exact centralizer_le hSL ((mem_omegaCenterIn_iff _ _).mp (hcentral ▸ hz)).2.1
    · exact ((mem_omegaCenterIn_iff _ _).mp ((source_Z_Q_U h w).1 hz)).2.2
  · rw [←hTS]
    exact le_iSup (fun T : Sylow 2 (stabilizer (family P) v) =>
      omegaCenterIn ((T : Subgroup (stabilizer (family P) v)).map
        (stabilizer (family P) v).subtype)) T

/-- Every escaping subgroup of the original full edge Sylow has the same
commutator on an actual natural center, namely the neighboring center span. -/
theorem source_natural_edge_commutator (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (d : EarlierLocalTheorems (family P)) {v w : Vertex (family P)}
    (he : (graph (family P)).Adj v w)
    (hcentral : Z (family P) w = omegaCenterIn (d.localGroup w))
    (hnat : Noncommuting.HasNaturalCenter (d.localGroup v) (Z (family P) v) (Q (family P) v))
    (A : Subgroup G)
    (hAS : A ≤ (stabilizer (family P) v ⊓ stabilizer (family P) w).pCoreIn 2)
    (hAQ : ¬ A ≤ Q (family P) v) :
    ⁅Z (family P) v,A⁆ = Z (family P) w := by
  let := finite_endpoints h
  let := CommutingOneProfile.source_center_elementary h v
  let L := d.localGroup v
  let S := (stabilizer (family P) v ⊓ stabilizer (family P) w).pCoreIn 2
  let : Finite L := Finite.of_injective (inclusion (d.local_le v)) (inclusion_injective _)
  obtain ⟨R,hR⟩ := source_edge_core_local_sylow h hB d he
  have hSL : S ≤ L := by
    change (stabilizer (family P) v ⊓ stabilizer (family P) w).pCoreIn 2 ≤ d.localGroup v
    rw [←hR]
    exact map_subtype_le _
  have hAL : A ≤ L := hAS.trans hSL
  obtain ⟨k,hk,hfin,halg,π,hπ,hker,⟨δ⟩⟩ := hnat
  have hz := local_center_eq_bot_of_neighbor_central h d he hcentral
  have hω := omega_eq_bot_of_center_eq_bot L hz
  let δ₀ : BinaryConjugationSection L (Z (family P) v) ⊥
      (SL2NaturalOffenders.NoStrong.natural.comp π) := hω ▸ δ
  let T := R.mapSurjective (f := π) hπ
  have hT : (S.subgroupOf L).map π = T := by
    have hh : S.subgroupOf L = R := by
      apply map_injective L.subtype_injective
      rw [map_subgroupOf_eq_of_le hSL]
      exact hR.symm
    rw [hh]
    rfl
  have hne : (A.subgroupOf L).map π ≠ ⊥ := by
    intro hh
    have hl := (Subgroup.map_eq_bot_iff _).mp hh
    rw [hker] at hl
    exact hAQ (fun a ha => hl (show (⟨a,hAL ha⟩ : L) ∈ A.subgroupOf L from ha))
  rw [Noncommuting.natural_section_commutator L (Z (family P) v) π δ₀ A S hAL hSL T hT hAS hne]
  have hseed := source_central_edge_seed h hB d he hcentral
  have hs : Stellmacher.omegaOneCenterAmbient S = omegaCenterIn S := rfl
  rw [Noncommuting.elementary_fixed_eq_seed (Z (family P) v) S
    (((source_Z_Q_U h v).1.trans (map_subtype_le _)).trans
      (Noncommuting.graph_Q_le_edgeCore h he)) (hs.symm ▸ hseed.2),hs]
  exact hseed.1

/-- Natural edge commutators with a subgroup of the opposite core are zero
or precisely the opposite center. -/
theorem source_natural_core_commutator (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (d : EarlierLocalTheorems (family P)) {v w : Vertex (family P)}
    (he : (graph (family P)).Adj v w)
    (hcentral : Z (family P) w = omegaCenterIn (d.localGroup w))
    (hnat : Noncommuting.HasNaturalCenter (d.localGroup v) (Z (family P) v) (Q (family P) v))
    (A : Subgroup G) (hA : A ≤ Q (family P) w) :
    ⁅Z (family P) v,A⁆ = ⊥ ∨ ⁅Z (family P) v,A⁆ = Z (family P) w := by
  by_cases hAQ : A ≤ Q (family P) v
  · exact Or.inl (commutator_eq_bot_iff_le_centralizer.mpr
      ((Z_centralizes_Q (family P) v (source_Z_Q_U h v).1).trans (centralizer_le hAQ)))
  · exact Or.inr (source_natural_edge_commutator h hB d he hcentral hnat A
      (hA.trans (by simpa only [inf_comm] using Noncommuting.graph_Q_le_edgeCore h he.symm)) hAQ)

private theorem ordered_edges_translate (F : Bool → Subgroup G)
    {a beta v w : Vertex F} (hab : (graph F).Adj a beta) (hvw : (graph F).Adj v w)
    (ht : beta.type = w.type) : ∃ g : G, g • a = v ∧ g • beta = w := by
  obtain ⟨g,hg⟩ := (same_orbit_iff F beta w).mpr ht
  have hga : (graph F).Adj w (g • a) := by
    rw [←hg]
    exact (Subgroup.CosetGeometry.translationGraphIso F g).map_adj_iff.mpr hab.symm
  obtain ⟨l,hl,hlv⟩ := locally_transitive F hga hvw.symm
  refine ⟨l*g, ?_, ?_⟩
  · exact (mul_smul l g a).trans hlv
  · rw [mul_smul,hg]
    exact hl

/-- The same natural core calculation at every oriented edge in the orbit.
Only commutators are transported; the original actor is never replaced by
a group-family label. -/
theorem source_natural_core_commutator_at_orbit (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (d : EarlierLocalTheorems (family P)) {a beta v w : Vertex (family P)}
    (hab : (graph (family P)).Adj a beta) (hvw : (graph (family P)).Adj v w)
    (ht : beta.type = w.type)
    (hcentral : Z (family P) beta = omegaCenterIn (d.localGroup beta))
    (hnat : Noncommuting.HasNaturalCenter (d.localGroup a) (Z (family P) a) (Q (family P) a))
    (A : Subgroup G) (hA : A ≤ Q (family P) w) :
    ⁅Z (family P) v,A⁆ = ⊥ ∨ ⁅Z (family P) v,A⁆ = Z (family P) w := by
  let := finite_endpoints h
  obtain ⟨g,hga,hgb⟩ := ordered_edges_translate (family P) hab hvw ht
  have hib : g⁻¹ • w = beta := by rw [←hgb,inv_smul_smul]
  have hAback : A.map (MulAut.conj g⁻¹).toMonoidHom ≤ Q (family P) beta := by
    have hh := map_mono (f := (MulAut.conj g⁻¹).toMonoidHom) hA
    rwa [←Q_translate,hib] at hh
  have hmap : (A.map (MulAut.conj g⁻¹).toMonoidHom).map (MulAut.conj g).toMonoidHom = A := by
    rw [map_map]
    convert map_id A using 1
    ext x
    simp [mul_assoc]
  rcases source_natural_core_commutator h hB d hab hcentral hnat _ hAback with hz | hz
  · left
    have hh := congrArg (map (MulAut.conj g).toMonoidHom) hz
    rwa [map_commutator,←Z_translate,hga,hmap,Subgroup.map_bot] at hh
  · right
    have hh := congrArg (map (MulAut.conj g).toMonoidHom) hz
    rwa [map_commutator,←Z_translate,←Z_translate,hga,hgb,hmap] at hh

/-- Natural centers on one orbit control the entire radius-one commutator
at the other orbit, including the center vertex of the closed ball. -/
theorem source_natural_span_commutator (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (d : EarlierLocalTheorems (family P)) {a beta w : Vertex (family P)}
    (hab : (graph (family P)).Adj a beta) (ht : beta.type = w.type)
    (hcentral : Z (family P) beta = omegaCenterIn (d.localGroup beta))
    (hnat : Noncommuting.HasNaturalCenter (d.localGroup a) (Z (family P) a) (Q (family P) a))
    (A : Subgroup G) (hA : A ≤ Q (family P) w)
    (hne : ⁅V (family P) w 1,A⁆ ≠ ⊥) :
    ⁅V (family P) w 1,A⁆ = Z (family P) w := by
  let := finite_endpoints h
  let F := family P
  have hzc : ⁅Z F w,A⁆ = ⊥ := commutator_eq_bot_iff_le_centralizer.mpr
    ((Z_centralizes_Q F w (source_Z_Q_U h w).1).trans (centralizer_le hA))
  have hlocal (z : (graph F).neighborSet w) : ⁅Z F z.val,A⁆ = ⊥ ∨ ⁅Z F z.val,A⁆ = Z F w :=
    source_natural_core_commutator_at_orbit h hB d hab
      (show (graph F).Adj w z.val from z.property).symm ht hcentral hnat A hA
  have hlow : Z F w ≤ ⁅V F w 1,A⁆ := by
    have hex : ∃ z : (graph F).neighborSet w, ⁅Z F z.val,A⁆ ≠ ⊥ := by
      by_contra! hall
      apply hne
      apply commutator_eq_bot_iff_le_centralizer.mpr
      rw [V_one_eq_sup_neighbors]
      exact sup_le (commutator_eq_bot_iff_le_centralizer.mp hzc)
        (iSup_le fun z => commutator_eq_bot_iff_le_centralizer.mp (hall z))
    obtain ⟨z,hz⟩ := hex
    rw [←(hlocal z).resolve_left hz]
    exact commutator_mono (Z_neighbor_le_V F z.property) le_rfl
  apply le_antisymm ?_ hlow
  have hV : V F w 1 = ⨆ z : ball F w 1, Z F z.val := by simp only [V,iSup_subtype]
  rw [hV]
  apply commutator_iSup_le_of_relative_normal (stabilizer F w) A (Z F w) _
    (stabilizer_normalizes_Z F w)
  · intro z
    rcases (mem_ball_one F w z.val).mp z.property with hz | hz
    · exact ((source_Z_Q_U h z.val).1.trans (map_subtype_le _)).trans
        ((source_Z_Q_U h z.val).2.trans ((ballKernel_one_le_edge F hz.symm).trans inf_le_right))
    · rw [←hz]
      exact Z_le_stabilizer F w
  · intro z
    rcases (mem_ball_one F w z.val).mp z.property with hz | hz
    · exact (hlocal ⟨z.val,hz⟩).elim (fun he => he.le.trans bot_le) Eq.le
    · rw [←hz,hzc]
      exact bot_le

/-- The natural-center case of DGS 8.2, marked at any edge in the orbit. The natural
coordinates are a genuine conditional case hypothesis, not a conclusion of
this theorem. All local transport and the faithfulness contradiction are proved. -/
theorem source_reciprocal_escape_of_natural_edge (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (d : EarlierLocalTheorems (family P))
    {a beta a' : Vertex (family P)} (hc : IsCriticalPair (family P) a a')
    (hab : (graph (family P)).Adj a beta)
    (hd : (graph (family P)).dist beta a' + 1 = b (family P))
    (hb : 1 < b (family P)) (hcomm : ⁅Z (family P) a, Z (family P) a'⁆ = ⊥)
    (models : ∀ v : Vertex (family P), IsRankOneModel (d.localGroup v ⧸ pCore 2 (d.localGroup v)))
    (hne : ⁅V (family P) beta 1 ⊓ Q (family P) a', V (family P) a' 1⁆ ≠ ⊥)
    {v u : Vertex (family P)} (hvu : (graph (family P)).Adj v u)
    (hut : u.type = beta.type)
    (hcentral : Z (family P) u = omegaCenterIn (d.localGroup u))
    (hnat : Noncommuting.HasNaturalCenter (d.localGroup v) (Z (family P) v) (Q (family P) v)) :
    ¬ V (family P) a' 1 ≤ Q (family P) beta := by
  let := finite_endpoints h
  let F := family P
  intro hreverse
  obtain ⟨hodd,_,_,_⟩ := source_critical_geometry h d hc hab hd hb hcomm
  have ht : beta.type = a'.type := by
    apply (even_dist_iff F h.generate beta a').mp
    obtain ⟨n,hn⟩ := hodd
    change (graph F).dist beta a' + 1 = b F at hd
    change b F = 2*n+1 at hn
    exact ⟨n,by omega⟩
  have hM : ⁅V F beta 1,V F a' 1⁆ = Z F beta :=
    source_natural_span_commutator h hB d hvu hut hcentral hnat _ hreverse
      (radius_one_commutator_ne_bot F beta a' hne)
  have hH : ⁅V F beta 1 ⊓ Q F a',V F a' 1⁆ = Z F a' := by
    rw [commutator_comm]
    exact source_natural_span_commutator h hB d hvu (hut.trans ht) hcentral hnat _ inf_le_right
      (by rwa [commutator_comm])
  have hle : Z F a' ≤ Z F beta := by
    rw [←hH,←hM]
    exact commutator_mono inf_le_left le_rfl
  have hcard : Nat.card (Z F beta) = Nat.card (Z F a') := by
    obtain ⟨g,hg⟩ := (same_orbit_iff F beta a').mpr ht
    rw [←hg,Z_translate]
    exact (card_map_of_injective (MulAut.conj g).injective).symm
  let : Finite (Z F beta) := Finite.of_injective
    (inclusion (Z_le_stabilizer F beta)) (inclusion_injective _)
  have heq := eq_of_le_of_card_ge hle hcard.le
  have hgap := source_commutator_strict_gap h hB d hc hab hd hb hcomm models hne
  rw [hH,hM,heq] at hgap
  exact (lt_irrefl _ hgap)

/-- The natural-center case in the first paragraph of DGS 8.2. The natural
coordinates are a genuine conditional case hypothesis, not a conclusion of
this theorem. All local transport and the faithfulness contradiction are proved. -/
theorem source_reciprocal_escape_of_natural_center (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (d : EarlierLocalTheorems (family P))
    {a beta a' : Vertex (family P)} (hc : IsCriticalPair (family P) a a')
    (hab : (graph (family P)).Adj a beta)
    (hd : (graph (family P)).dist beta a' + 1 = b (family P))
    (hb : 1 < b (family P)) (hcomm : ⁅Z (family P) a, Z (family P) a'⁆ = ⊥)
    (models : ∀ v : Vertex (family P), IsRankOneModel (d.localGroup v ⧸ pCore 2 (d.localGroup v)))
    (hne : ⁅V (family P) beta 1 ⊓ Q (family P) a', V (family P) a' 1⁆ ≠ ⊥)
    (hnat : Noncommuting.HasNaturalCenter (d.localGroup a) (Z (family P) a) (Q (family P) a)) :
    ¬ V (family P) a' 1 ≤ Q (family P) beta := by
  exact source_reciprocal_escape_of_natural_edge h hB d hc hab hd hb hcomm models hne hab rfl
    (source_critical_geometry h d hc hab hd hb hcomm).2.2.1 hnat

/-- Natural coordinates at the actual moving neighbor give the same reciprocal
escape, with the complete orbit transport already discharged. -/
theorem source_reciprocal_escape_of_natural_moving_neighbor (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (d : EarlierLocalTheorems (family P))
    {a beta a' : Vertex (family P)} (hc : IsCriticalPair (family P) a a')
    (hab : (graph (family P)).Adj a beta)
    (hd : (graph (family P)).dist beta a' + 1 = b (family P))
    (hb : 1 < b (family P)) (hcomm : ⁅Z (family P) a, Z (family P) a'⁆ = ⊥)
    (models : ∀ v : Vertex (family P), IsRankOneModel (d.localGroup v ⧸ pCore 2 (d.localGroup v)))
    (hne : ⁅V (family P) beta 1 ⊓ Q (family P) a', V (family P) a' 1⁆ ≠ ⊥)
    (w : (graph (family P)).neighborSet a')
    (hnat : Noncommuting.HasNaturalCenter (d.localGroup w.val) (Z (family P) w.val) (Q (family P) w.val)) :
    ¬ V (family P) a' 1 ≤ Q (family P) beta := by
  let := finite_endpoints h
  have hend := critical_end_center_of_commuting (family P) h.generate
    (fun v => (source_Z_Q_U h v).1) (fun v => (source_Z_Q_U h v).2) hc hcomm
    (d.localGroup a') (d.sylow_or_center a')
  have hodd := (source_critical_geometry h d hc hab hd hb hcomm).1
  have ht : a'.type = beta.type := by
    symm
    apply (even_dist_iff (family P) h.generate beta a').mp
    obtain ⟨n,hn⟩ := hodd
    exact ⟨n,by omega⟩
  exact source_reciprocal_escape_of_natural_edge h hB d hc hab hd hb hcomm models hne
    (show (graph (family P)).Adj a' w.val from w.property).symm ht hend hnat

end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingNontrivial
