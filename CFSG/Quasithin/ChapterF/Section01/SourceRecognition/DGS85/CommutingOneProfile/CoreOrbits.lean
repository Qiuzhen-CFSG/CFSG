module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingOneProfile.LinearCoreGeneration
public import Theory.GroupAction.MatchedPointOrbit
public import Theory.SpecificGroups.Suzuki.SylowNeighborOrbits

/-!
# Core generation from the beta root orbit

The actual quotient Sylow action lifts through the local point stabilizer,
which is its Sylow normalizer. If the edge radical is transitive away from
alpha in the beta star, conjugation of one opposite seed supplies every
seed modulo Q_alpha. Normalization by both adjacent cores then identifies
its supplement with the full corrected beta span. Intersecting with Q_beta
proves the literal pair-core identity, without assuming that the two centers
are transitive on the entire beta star.

A linear alpha marking supplies the full-span supplement; the nonbinary
Suzuki root orbit consequently proves (11.3)(h) and (11.4) in that candidate
branch. This does not exclude the candidate or select the alpha model.
The local groups, full kernels and original quotient markings are retained.
Source: Delgado--Goldschmidt--Stellmacher, Groups and Graphs (1985),
(11.3)(h)--(11.5), printed pp.169--172; rank-one root action (5.1).
-/

public noncomputable section
open Subgroup
open scoped Pointwise MatrixGroups
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingOneProfile
open Subgroup.CosetGeometry.RankTwo CommutingNontrivial Theory.GroupTheory.AmalgamGraph
variable {G : Type*} [Group G] {P : Fin 2 → Subgroup G} {B : Subgroup G}

/-- Transfer an actual quotient Sylow orbit through the literal local action. -/
theorem source_edge_core_orbit_of_model_action
    {D X : Type*} [Group D] [MulAction D X]
    (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (d : EarlierLocalTheorems (family P))
    {a b c w : Vertex (family P)} (hab : (graph (family P)).Adj a b)
    (hbc : (graph (family P)).Adj b c) (hbw : (graph (family P)).Adj b w)
    (hca : c ≠ a) (hwa : w ≠ a)
    (M : IsRankOneModel (d.localGroup b ⧸ pCore 2 (d.localGroup b)))
    (e : (d.localGroup b ⧸ pCore 2 (d.localGroup b)) ≃* D)
    (horbit : ∀ R : Sylow 2 D, ∃ p : X,
      normalizer (R : Set D) = MulAction.stabilizer D p ∧
      ∀ x y : X, x ≠ p → y ≠ p → ∃ t ∈ (R : Subgroup D), t • x = y) :
    ∃ t ∈ (stabilizer (family P) a ⊓ stabilizer (family P) b).pCoreIn 2, t • c = w := by
  let := finite_endpoints h
  let L := d.localGroup b
  let : Finite L := Finite.of_injective (inclusion (d.local_le b)) (inclusion_injective _)
  let q : L →* D := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))
  have hq : Function.Surjective q := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hk : q.ker = pCore 2 L := by
    ext x
    change e ((QuotientGroup.mk' (pCore 2 L)) x) = 1 ↔ _
    rw [←e.map_one,e.injective.eq_iff]
    exact QuotientGroup.eq_one_iff x
  obtain ⟨T,hT⟩ := source_edge_core_local_sylow h hB d hab.symm
  let R := T.mapSurjective hq
  obtain ⟨p,hp,ht⟩ := horbit R
  have hRT : (R : Subgroup D).comap q = (T : Subgroup L) := by
    change ((T : Subgroup L).map q).comap q = _
    apply comap_map_eq_self
    rw [hk]
    exact pCore_isPGroup.le_sylow_of_normal T
  have hstab : (MulAction.stabilizer D p).comap q = MulAction.stabilizer L a := by
    rw [←hp]
    change (normalizer ((R : Subgroup D) : Set D)).comap q = _
    rw [comap_normalizer_eq_of_surjective _ hq,hRT,Sylow.coe_coe,
      ←(source_edge_local_normalizer h d hab.symm M T hT).2]
    rfl
  obtain ⟨u,hu,huc⟩ := d.transitive b ⟨a,hab.symm⟩ ⟨c,hbc⟩
  obtain ⟨v,hv,hvw⟩ := d.transitive b ⟨a,hab.symm⟩ ⟨w,hbw⟩
  obtain ⟨t,htT,hte⟩ := Theory.GroupAction.MatchedPointOrbit.transitive_away_from_base
    q (T : Subgroup L) a p hstab ht (⟨u,hu⟩ : L) (⟨v,hv⟩ : L)
    (by simpa only [Subgroup.mk_smul,huc] using hca)
    (by simpa only [Subgroup.mk_smul,hvw] using hwa)
  refine ⟨t,?_,?_⟩
  · have hh := mem_map_of_mem L.subtype htT
    rw [hT,inf_comm] at hh
    exact hh
  · change (t : G) • (u • a) = v • a at hte
    rwa [huc,hvw] at hte

/-- The full corrected span has the same image as one opposite seed when
 the edge radical is transitive on the remaining beta neighbors. -/
theorem source_seed_supplement_of_edge_orbit (h : LocallyRankOneTriple P B)
    {a b c : Vertex (family P)} (hab : (graph (family P)).Adj a b)
    (hbc : (graph (family P)).Adj b c)
    (hsupp : (stabilizer (family P) a ⊓ stabilizer (family P) b).pCoreIn 2 =
      betaSpan (stabilizer (family P) b) (Z (family P) a) ⊔ Q (family P) a)
    (horbit : ∀ w, (graph (family P)).Adj b w → w ≠ a →
      ∃ t ∈ (stabilizer (family P) a ⊓ stabilizer (family P) b).pCoreIn 2, t • c = w) :
    (stabilizer (family P) a ⊓ stabilizer (family P) b).pCoreIn 2 =
      (Z (family P) c ⊓ Q (family P) b) ⊔ Q (family P) a := by
  let := finite_endpoints h
  let N := (Z (family P) c ⊓ Q (family P) b) ⊔ Q (family P) a
  have hQn : Q (family P) b ≤ normalizer (N : Set G) := by
    apply (le_inf ?_ (source_adjacent_core_normalizes_core h hab.symm)).trans
      (normalizer_inf_normalizer_le_normalizer_sup _ _)
    exact (le_inf (source_adjacent_core_normalizes_center h hbc.symm)
      (Q (family P) b).le_normalizer).trans inf_normalizer_le_normalizer_inf
  have hSn : (stabilizer (family P) a ⊓ stabilizer (family P) b).pCoreIn 2 ≤
      normalizer (N : Set G) := by
    rw [hsupp]
    exact sup_le ((betaSpan_le_core _ _).trans hQn) (le_sup_right.trans N.le_normalizer)
  have hVN : betaSpan (stabilizer (family P) b) (Z (family P) a) ≤ N := by
    rw [source_betaSpan_eq_neighbor_span h hab]
    apply iSup_le
    intro w
    by_cases hwa : w.val = a
    · rw [hwa]
      exact inf_le_left.trans (((source_Z_Q_U h a).1.trans (map_subtype_le _)).trans le_sup_right)
    · obtain ⟨t,ht,htc⟩ := horbit w.val w.property hwa
      have htb : t • b = b := ((pCoreIn_le 2 _).trans inf_le_right) ht
      have he : (Z (family P) c ⊓ Q (family P) b).map (MulAut.conj t).toMonoidHom =
          Z (family P) w.val ⊓ Q (family P) b := by
        rw [map_inf _ _ _ (MulAut.conj t).injective,←Z_translate,←Q_translate,htc,htb]
      rw [←he]
      exact (map_mono (show Z (family P) c ⊓ Q (family P) b ≤ N from le_sup_left)).trans_eq
        (mem_normalizer_iff_map_conj_eq.mp (hSn ht))
  apply le_antisymm
  · rw [hsupp]
    exact sup_le hVN le_sup_right
  · rw [hsupp]
    exact sup_le (le_sup_right.trans (source_pairSpan_le_betaSpan h hab hbc) |>.trans le_sup_left)
      le_sup_right

/-- Intersect the opposite-seed supplement with the actual beta core. -/
theorem source_pair_core_of_seed_supplement (h : LocallyRankOneTriple P B)
    {a b c : Vertex (family P)} (hab : (graph (family P)).Adj a b)
    (hsupp : (stabilizer (family P) a ⊓ stabilizer (family P) b).pCoreIn 2 =
      (Z (family P) c ⊓ Q (family P) b) ⊔ Q (family P) a) :
    Q (family P) b = pairSpan (Z (family P) a) (Z (family P) c) (Q (family P) b) ⊔
      (Q (family P) a ⊓ Q (family P) b) := by
  have hQ : Q (family P) b ≤ (Z (family P) c ⊓ Q (family P) b) ⊔ Q (family P) a := by
    rw [←hsupp]
    simpa only [inf_comm] using Noncommuting.graph_Q_le_edgeCore h hab.symm
  have hn : Z (family P) c ⊓ Q (family P) b ≤ normalizer (Q (family P) a : Set G) :=
    inf_le_right.trans (source_adjacent_core_normalizes_core h hab.symm)
  apply le_antisymm ?_ (sup_le (pairSpan_le_core _ _ _) inf_le_right)
  intro x hx
  have hx' : x ∈ ((Z (family P) c ⊓ Q (family P) b : Subgroup G) : Set G) * (Q (family P) a : Set G) := by
    rw [←coe_mul_of_left_le_normalizer_right _ _ hn]
    exact hQ hx
  obtain ⟨v,hv,y,hy,rfl⟩ := hx'
  have hyQ : y ∈ Q (family P) b := by
    have hh := (Q (family P) b).mul_mem ((Q (family P) b).inv_mem hv.2) hx
    simpa only [inv_mul_cancel_left] using hh
  exact mul_mem (mem_sup_left (mem_sup_right hv)) (mem_sup_right ⟨hy,hyQ⟩)

variable {k : Type*} [Field k] [Finite k] [CharP k 2]

/-- The literal pair-core identity for a linear alpha and nonbinary Suzuki beta. -/
theorem source_linear_suzuki_core_identities (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (d : EarlierLocalTheorems (family P))
    {a b c : Vertex (family P)} (hc : IsCriticalPair (family P) a b)
    (hb : DGS85.b (family P) = 1)
    (hbc : (graph (family P)).Adj b c) (hac : a ≠ c)
    (Ma : IsRankOneModel (d.localGroup a ⧸ pCore 2 (d.localGroup a)))
    (ea : (d.localGroup a ⧸ pCore 2 (d.localGroup a)) ≃* SL(2,k))
    {m : ℕ} (hm : 0 < m)
    (eb : (d.localGroup b ⧸ pCore 2 (d.localGroup b)) ≃*
      BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m) :
    (stabilizer (family P) a ⊓ stabilizer (family P) b).pCoreIn 2 =
        Q (family P) a ⊔ Q (family P) b ∧
      Q (family P) b = pairSpan (Z (family P) a) (Z (family P) c) (Q (family P) b) ⊔
        (Q (family P) a ⊓ Q (family P) b) := by
  have Mb : IsRankOneModel (d.localGroup b ⧸ pCore 2 (d.localGroup b)) := .suzuki m ⟨eb⟩
  have hab := source_critical_one_adjacent hc hb
  have hsupp := source_seed_supplement_of_edge_orbit h hab hbc
    (source_linear_betaSpan_supplement h hB d hc hb hbc hac Ma Mb ea)
    (fun w hw hwa => source_edge_core_orbit_of_model_action h hB d hab hbc hw
      hac.symm hwa Mb eb (BenderSuzuki.MatrixGroups.suzuki_sylow_remaining_orbit hm))
  exact ⟨source_linear_edge_core_product h hB d hc hb hbc hac Ma Mb ea,
    source_pair_core_of_seed_supplement h hab hsupp⟩

end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingOneProfile
