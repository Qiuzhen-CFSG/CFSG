module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingOneProfile.FullCoreShortPaths
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingOneProfile.SuzukiShortExclusion
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingOneProfile.SourceCoreSelection
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.LocalStructure.FullGraphObstruction

/-!
# Excluding Suzuki beta quotients from the commuting critical edge

The marked Suzuki beta action is transitive on two-edge walks from alpha.
The source seed argument on such a walk proves the full adjacent-core
product and selects a linear alpha quotient. Both local actions are then
non-dihedral, so the core product supplies three-walk transitivity in both
vertex orbits. The short escaping-walk argument proves the Suzuki
contradiction, including Sz(2), without a four-walk premise.

The original application uses the canonical earlier-local theorems and
transports the quotient through the literal reduced-group inclusion. The
alpha rank-one catalogue remains explicit. The nonelementary full-Borel
consumer is in OriginalNonElementarySource.
Source: DGS, Groups and Graphs (1985), (11.4)--(11.6) and the Suzuki
contradiction in (11.8), printed pp.171--176.
-/

public noncomputable section
open Subgroup SimpleGraph SimpleGraph.PathTransitivePolygon
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingOneProfile
open Subgroup.CosetGeometry.RankTwo CommutingNontrivial Theory.GroupTheory.AmalgamGraph
open BenderSuzuki.MatrixGroups
variable {G : Type*} [Group G] {P : Fin 2 → Subgroup G} {B : Subgroup G}

private theorem two_walk_transitive_of_edge_action
    {a b : Vertex (family P)} (hab : (graph (family P)).Adj a b)
    (ht : ∀ x y : Vertex (family P), (graph (family P)).Adj b x →
      (graph (family P)).Adj b y → x ≠ a → y ≠ a →
      ∃ g ∈ stabilizer (family P) a ⊓ stabilizer (family P) b, g • x = y) :
    RootPathTransitive (graph (family P)) G a 2 := by
  intro p q hp hq
  let x := (p.1 : Vertex (family P))
  let y := (q.1 : Vertex (family P))
  let z := (p.2.1 : Vertex (family P))
  let w := (q.2.1 : Vertex (family P))
  obtain ⟨g,hga,hgx⟩ := locally_transitive (family P) p.1.property hab
  obtain ⟨k,hka,hky⟩ := locally_transitive (family P) q.1.property hab
  have hgadj : (graph (family P)).Adj b (g • z) := by
    have hh := (Subgroup.CosetGeometry.translationGraphIso (family P) g).map_adj_iff.mpr p.2.1.property
    change (graph (family P)).Adj (g • x) (g • z) at hh
    rwa [hgx] at hh
  have hkadj : (graph (family P)).Adj b (k • w) := by
    have hh := (Subgroup.CosetGeometry.translationGraphIso (family P) k).map_adj_iff.mpr q.2.1.property
    change (graph (family P)).Adj (k • y) (k • w) at hh
    rwa [hky] at hh
  have hgz : g • z ≠ a := by
    intro he
    exact hp.1 ((MulAction.injective g) (he.trans (show g • a = a from hga).symm))
  have hkw : k • w ≠ a := by
    intro he
    exact hq.1 ((MulAction.injective k) (he.trans (show k • a = a from hka).symm))
  obtain ⟨t,ht,htz⟩ := ht (g • z) (k • w) hgadj hkadj hgz hkw
  refine ⟨k⁻¹*t*g,?_,?_⟩
  · change (k⁻¹*t*g) • a = a
    rw [mul_smul,mul_smul,show g • a = a from hga,show t • a = a from ht.1]
    exact inv_mem hka
  · change [a,x,z].map ((k⁻¹*t*g) • ·) = [a,y,w]
    simp only [List.map_cons,List.map_nil,List.cons.injEq,and_true]
    refine ⟨?_,?_,?_⟩
    · rw [mul_smul,mul_smul,show g • a = a from hga,show t • a = a from ht.1]
      exact inv_mem hka
    · rw [mul_smul,mul_smul,hgx,show t • b = b from ht.2,←hky,inv_smul_smul]
    · rw [mul_smul,mul_smul,htz,inv_smul_smul]

private def quotient_at (d : EarlierLocalTheorems (family P))
    (u v : Vertex (family P)) (ht : u.type = v.type) :
    (d.localGroup v ⧸ pCore 2 (d.localGroup v)) ≃*
      (d.localGroup u ⧸ pCore 2 (d.localGroup u)) := by
  let g := Classical.choose ((same_orbit_iff (family P) u v).mpr ht)
  have hg : g • u = v := Classical.choose_spec ((same_orbit_iff (family P) u v).mpr ht)
  have he : (d.localGroup u).map (MulAut.conj g).toMonoidHom = d.localGroup v := by
    rw [←d.conjugate,hg]
  let e := ((d.localGroup u).equivMapOfInjective (MulAut.conj g).toMonoidHom
    (MulAut.conj g).injective).trans (MulEquiv.subgroupCongr he)
  exact (QuotientGroup.congr _ _ e (pCore_map_iso 2 e)).symm

private theorem initial_neighbor_other (h : LocallyRankOneTriple P B)
    (hS : ∀ i, ∃ T : Sylow 2 (P i), (T : Subgroup (P i)).map (P i).subtype ≤ B)
    (a b : Vertex (family P)) :
    ∃ c, (graph (family P)).Adj b c ∧ a ≠ c := by
  let := finite_endpoints h
  have hv := card_neighbors_of_indices (family P)
    (fun i => ((family P (!i)).subgroupOf (family P i)).index) (fun _ => rfl) b
  have hc : 1 < ((graph (family P)).neighborSet b).ncard := by
    rw [←Nat.card_coe_set_eq,hv]
    have := source_valence_ge_three h hS b.type
    omega
  obtain ⟨c,hc,hca⟩ := Set.exists_ne_of_one_lt_ncard hc a
  exact ⟨c,hc,Ne.symm hca⟩

private theorem suzuki_not_dihedral (m : ℕ) :
    ¬ Nonempty (SuzukiMatrixGroup m ≃* DihedralGroup 5) := by
  rintro ⟨e⟩
  let T : Sylow 2 (SuzukiMatrixGroup m) := Classical.choice inferInstance
  let := dihedral_model_sylow_elementary e T
  have hω : omegaCenterIn (T : Subgroup (SuzukiMatrixGroup m)) = T := by
    apply le_antisymm (map_subtype_le _)
    intro x hx
    exact (mem_omegaCenterIn_iff _ _).mpr ⟨hx,
      fun y hy => congrArg Subtype.val (mul_comm (⟨y,hy⟩ : T) (⟨x,hx⟩ : T)),
      elemPow_eq_one_of_isElementaryAbelian x hx⟩
  have hi := (suzukiSylow_omegaCenter_card_index m T).2
  rw [hω,relIndex_self] at hi
  have hp := one_lt_pow₀ (by decide : 1 < (2:ℕ)) (by omega : 2*m+1 ≠ 0)
  omega

/-- The actual Suzuki beta action supplies two-walk transitivity at alpha,
including the cyclic Sylow of Sz(2). -/
theorem source_suzuki_beta_two_walk_transitive
    (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (d : EarlierLocalTheorems (family P))
    {a b : Vertex (family P)} (hab : (graph (family P)).Adj a b)
    (m : ℕ) (eb : (d.localGroup b ⧸ pCore 2 (d.localGroup b)) ≃* SuzukiMatrixGroup m) :
    RootPathTransitive (graph (family P)) G a 2 := by
  have M : IsRankOneModel (d.localGroup b ⧸ pCore 2 (d.localGroup b)) := .suzuki m ⟨eb⟩
  have ht := (source_edge_transitive_or_dihedral h hB d hab.symm M).resolve_right
    (fun e => suzuki_not_dihedral m ⟨eb.symm.trans e.some⟩)
  apply two_walk_transitive_of_edge_action hab
  intro x y hx hy hxa hya
  obtain ⟨g,hg,he⟩ := ht x y hx hy hxa hya
  exact ⟨g,⟨hg.2,d.local_le b hg.1⟩,he⟩

/-- Every Suzuki beta quotient is impossible at a commuting critical edge.
The alpha marking, full core product, escape and three-walk transitivity
are constructed from the actual local catalogue and source hypotheses. -/
theorem source_suzuki_beta_exclusion
    (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (hS : ∀ i, ∃ T : Sylow 2 (P i), (T : Subgroup (P i)).map (P i).subtype ≤ B)
    (d : EarlierLocalTheorems (family P))
    {a b : Vertex (family P)} (hc : IsCriticalPair (family P) a b)
    (hb : DGS85.b (family P) = 1) (hcomm : ⁅Z (family P) a,Z (family P) b⁆ = ⊥)
    (Ma : IsRankOneModel (d.localGroup a ⧸ pCore 2 (d.localGroup a)))
    (m : ℕ) (eb : (d.localGroup b ⧸ pCore 2 (d.localGroup b)) ≃* SuzukiMatrixGroup m) : False := by
  have hab := source_critical_one_adjacent hc hb
  obtain ⟨c,hbc,hac⟩ := initial_neighbor_other h hS a b
  let Mb : IsRankOneModel (d.localGroup b ⧸ pCore 2 (d.localGroup b)) := .suzuki m ⟨eb⟩
  let p : BasedWalk (graph (family P)) 2 a := ⟨⟨b,hab⟩,⟨⟨c,hbc⟩,PUnit.unit⟩⟩
  have hp : p.Nonbacktracking := ⟨Ne.symm hac,trivial⟩
  obtain ⟨hprod,n,hn,hi⟩ := source_core_product_and_alpha_on_path h hB d hc hb hcomm
    hbc hac Ma Mb (source_suzuki_beta_two_walk_transitive h hB d hab m eb) p hp
    (by change a ∈ [a,b,c]; simp) (by change b ∈ [a,b,c]; simp) (by change c ∈ [a,b,c]; simp)
  have local_data (v : Vertex (family P)) :
      IsRankOneModel (d.localGroup v ⧸ pCore 2 (d.localGroup v)) ∧
        ¬ Nonempty ((d.localGroup v ⧸ pCore 2 (d.localGroup v)) ≃* DihedralGroup 5) := by
    by_cases hav : a.type = v.type
    · let e := quotient_at d a v hav
      exact ⟨Ma.of_equiv e,fun ei => source_alpha_dihedral_exclusion h hB d hc hb hcomm
        hbc hac Mb (e.symm.trans ei.some)⟩
    · have hbv : b.type = v.type := by
        have hh := hab.1
        cases ha : a.type <;> cases hb : b.type <;> cases hv : v.type <;> simp_all
      let e := quotient_at d b v hbv
      exact ⟨Mb.of_equiv e,fun ei => suzuki_not_dihedral m ⟨eb.symm.trans (e.symm.trans ei.some)⟩⟩
  have ht := source_three_walk_transitive_of_full_core_product h hB d hab hprod
    (fun v => (local_data v).1) (fun v => (local_data v).2)
  obtain ⟨k,_,_,hk,⟨ea⟩⟩ := hi
  let : Fintype k := Fintype.ofFinite k
  let : CharP k 2 := charP_of_card_eq_prime_pow
    (by simpa only [Nat.card_eq_fintype_card] using hk)
  let ep : SL(2,k) ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) k :=
    MulEquiv.ofBijective (BenderSuzuki.Converse.pi k)
      ⟨BenderSuzuki.Converse.pi_injective,BenderSuzuki.Converse.pi_surjective⟩
  exact source_linear_suzuki_exclusion_of_three_walks h hB hS d hc hb hcomm Ma
    (ea.trans ep.symm) m eb hprod ht

section Original
variable {L₀ : Fin 2 → Subgroup G} {S₀ : Subgroup G}
local notation "F₀" => Reduction.reducedFamily L₀ S₀
local notation "G₀" => Reduction.G₀ L₀ S₀

/-- Suzuki exclusion on the literal original quotient, with the earlier-local
record, alpha selection, escape and path-transitivity inputs discharged. -/
theorem original_reduced_suzuki_beta_exclusion
    (h : HypothesisF11 L₀ S₀)
    {a b : Vertex F₀} (hc : IsCriticalPair F₀ a b)
    (hb : DGS85.b F₀ = 1) (hcomm : ⁅Z F₀ a,Z F₀ b⁆ = ⊥)
    (Ma : IsRankOneModel ((graphLocalGroup F₀ a).map (G₀).subtype ⧸
      pCore 2 ((graphLocalGroup F₀ a).map (G₀).subtype)))
    (m : ℕ) (eb : ((graphLocalGroup F₀ b).map (G₀).subtype ⧸
      pCore 2 ((graphLocalGroup F₀ b).map (G₀).subtype)) ≃* SuzukiMatrixGroup m) : False := by
  let d := Reduction.reducedFullEarlierLocalTheorems h
  let ea := (d.localGroup a).equivMapOfInjective (G₀).subtype (G₀).subtype_injective
  let eqa := QuotientGroup.congr _ _ ea (pCore_map_iso 2 ea)
  let eβ := (d.localGroup b).equivMapOfInjective (G₀).subtype (G₀).subtype_injective
  let eqβ := QuotientGroup.congr _ _ eβ (pCore_map_iso 2 eβ)
  exact source_suzuki_beta_exclusion (Reduction.reduced_triple h)
    (Reduction.reduced_borel_core_sylow h) (Reduction.reduced_vertex_sylow h) d hc hb hcomm
    (Ma.of_equiv eqa) m (eqβ.trans eb)

end Original
end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingOneProfile
