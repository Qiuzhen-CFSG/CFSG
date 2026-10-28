module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingOneProfile.SourceCenterOrders
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingNontrivial.ModulePreparation

/-!
# The characteristic-two field equation in Chapter 11

The starting local group is centerless by (11.1). Its actual conjugation
representation on Z_alpha therefore has no fixed vectors. A nonzero simple
submodule has binary dimension at least twice the linear field degree.
Consequently |Z_alpha| is at least q_alpha squared. The proved (11.6)(c)
count |Z_alpha| = q_alpha q_beta squared gives the upper field bound;
(11.3)(g) gives the reverse bound. Thus q_alpha = q_beta squared for every
beta catalogue alternative, including both unitary covers and binary fields.

The alpha field is identified with the literal opposite-seed index by the
actual edge Sylow and the proved core supplement. No linear-beta formula
or faithful representation hypothesis is assumed. ReducedFieldParameters
transports the equation to the original completion and applies it to the
nonelementary quotient of the full original Borel.
Source: DGS85, Groups and Graphs (1985), (5.7), (11.1), (11.6)(c,d),
printed pp.108,167,172--174; applied in (11.8), pp.175--176.
-/

public noncomputable section
open Subgroup
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingOneProfile
open Subgroup.CosetGeometry.RankTwo CommutingNontrivial Theory.GroupTheory.AmalgamGraph
open Representation Representation.BinaryOffender
open SimpleGraph SimpleGraph.PathTransitivePolygon
variable {G : Type*} [Group G] {P : Fin 2 → Subgroup G} {B : Subgroup G}
variable {k : Type*} [Field k] [Finite k] [CharP k 2]

private theorem linear_center_order_lower
    (h : LocallyRankOneTriple P B) (d : EarlierLocalTheorems (family P))
    {a b : Vertex (family P)} (hc : IsCriticalPair (family P) a b)
    (hb : DGS85.b (family P) = 1) (hcomm : ⁅Z (family P) a,Z (family P) b⁆ = ⊥)
    (ea : (d.localGroup a ⧸ pCore 2 (d.localGroup a)) ≃* SL(2,k))
    (n : ℕ) (hn : 0 < n) (hk : Nat.card k = 2^n) :
    (Nat.card k)^2 ≤ Nat.card (Z (family P) a) := by
  let := finite_endpoints h
  let := source_center_elementary h a
  let V := Z (family P) a
  let : Finite V := Finite.of_injective (inclusion (Z_le_stabilizer _ a)) (inclusion_injective _)
  have hV : V ≠ ⊥ := by
    intro he
    apply hc.2
    change V ≤ U (family P) b
    rw [he]
    exact bot_le
  let : Nontrivial V := (Subgroup.nontrivial_iff_ne_bot V).mpr hV
  have hz := local_center_eq_bot_of_neighbor_central h d (source_critical_one_adjacent hc hb)
    (critical_end_center_of_commuting (family P) h.generate
      (fun v => (source_Z_Q_U h v).1) (fun v => (source_Z_Q_U h v).2) hc hcomm
      (d.localGroup b) (d.sylow_or_center b))
  obtain ⟨ρ,hact⟩ := source_exists_center_quotient_action h d a ea
  obtain ⟨S,_,_,hres⟩ := source_center_module_prepared_of_center_eq_bot h d a hz default ea ρ hact
  have hfix : ρ.invariants = ⊥ := by
    apply bot_unique
    intro v hv
    exact hres.le (fun g => hv g.val)
  obtain ⟨A,hA,_⟩ := (eq_bot_or_exists_atom_le (⊤ : Subrepresentation ρ)).resolve_left top_ne_bot
  let : A.toRepresentation.IsIrreducible := (Subrepresentation.irreducible_iff_isAtom A).mpr hA
  have hnt : ∃ g, A.toRepresentation g ≠ 1 := by
    by_contra! hh
    have habot : A = ⊥ := by
      apply Subrepresentation.toSubmodule_injective
      apply bot_unique
      intro v hv
      apply hfix.le
      intro g
      exact congrArg Subtype.val (congrArg (fun f : Module.End (ZMod 2) A.toSubmodule =>
        f ⟨v,hv⟩) (hh g))
    exact hA.ne_bot habot
  have hlo := (Representation.SL2.Unsigned.irreducible_finrank_bound 2
    A.toRepresentation hnt n (by omega) hk).trans (Submodule.finrank_le A.toSubmodule)
  have hcard : Nat.card (Additive V) = 2^Module.finrank (ZMod 2) (Additive V) := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod]
  change (Nat.card k)^2 ≤ Nat.card (Additive V)
  rw [hk,hcard,←pow_mul,Nat.mul_comm n 2]
  exact Nat.pow_le_pow_right (by decide) hlo

private theorem linear_edge_core_index
    (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (d : EarlierLocalTheorems (family P))
    {a b : Vertex (family P)} (hab : (graph (family P)).Adj a b)
    (ea : (d.localGroup a ⧸ pCore 2 (d.localGroup a)) ≃* SL(2,k)) :
    (Q (family P) a).relIndex
      ((stabilizer (family P) a ⊓ stabilizer (family P) b).pCoreIn 2) = Nat.card k := by
  let := finite_endpoints h
  let L := d.localGroup a
  let : Finite L := Finite.of_injective (inclusion (d.local_le a)) (inclusion_injective _)
  obtain ⟨T,hT⟩ := source_edge_core_local_sylow h hB d hab
  rw [←hT,←localGroup_core_eq (family P) d a]
  change ((pCore 2 L).map L.subtype).relIndex ((T : Subgroup L).map L.subtype) = _
  rw [relIndex_map_map_of_injective _ _ L.subtype_injective]
  let q := ea.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))
  have hq : Function.Surjective q := ea.surjective.comp (QuotientGroup.mk'_surjective _)
  have hk : q.ker = pCore 2 L := by
    rw [MonoidHom.ker_comp_of_injective _ _ ea.injective,QuotientGroup.ker_mk']
  rw [←hk,relIndex_ker]
  exact Nat.card_congr (Matrix.SpecialLinearGroup.sylowEquivAdditive k 2
    (T.mapSurjective hq)).symm.toEquiv

private theorem core_sup_index (Q C : Subgroup G)
    (hCQ : C ≤ normalizer (Q : Set G)) : Q.relIndex (Q ⊔ C) = Q.relIndex C := by
  let H := Q ⊔ C
  let : (Q.subgroupOf H).Normal := normal_subgroupOf_of_le_normalizer
    (sup_le Q.le_normalizer hCQ)
  have he := relIndex_sup_left (C.subgroupOf H) (Q.subgroupOf H)
  rw [←subgroupOf_sup le_sup_left le_sup_right,relIndex_subgroupOf le_rfl,
    relIndex_subgroupOf le_sup_right] at he
  exact he

/-- The characteristic-two field equation for every beta catalogue alternative. -/
theorem source_field_parameters_on_escaping_path
    (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (hS : ∀ i, ∃ T : Sylow 2 (P i), (T : Subgroup (P i)).map (P i).subtype ≤ B)
    (d : EarlierLocalTheorems (family P))
    {a b c : Vertex (family P)} (hc : IsCriticalPair (family P) a b)
    (hb : DGS85.b (family P) = 1) (hcomm : ⁅Z (family P) a,Z (family P) b⁆ = ⊥)
    (hbc : (graph (family P)).Adj b c) (hac : a ≠ c)
    (Ma : IsRankOneModel (d.localGroup a ⧸ pCore 2 (d.localGroup a)))
    (Mb : IsRankOneModel (d.localGroup b ⧸ pCore 2 (d.localGroup b)))
    (g : G) (hga : g ∈ stabilizer (family P) a) (hgb : g • b ≠ b)
    (hesc : ¬ Z (family P) b ≤ Q (family P) (g • b))
    {v : Vertex (family P)} {r : ℕ}
    (ht : RootPathTransitive (graph (family P)) G v (r+1))
    (p : BasedWalk (graph (family P)) (r+1) v) (hp : p.Nonbacktracking)
    (ha : a ∈ p.vertices) (hbp : b ∈ p.vertices) (hcp : c ∈ p.vertices)
    (hgbp : g • b ∈ p.vertices) (hgcp : g • c ∈ p.vertices) :
    let qα := (Q (family P) a).relIndex (Z (family P) c ⊓ Q (family P) b)
    let qβ := (Q (family P) b).relIndex (Z (family P) a)
    qα = qβ^2 ∧
      ∃ n, 1 < n ∧ ClassicalGroup.IsPSL (d.localGroup a ⧸ pCore 2 (d.localGroup a)) 2 (2^n) ∧
        2^n = qα := by
  obtain ⟨hprod,n,hn,hi⟩ := source_core_product_and_alpha_on_path h hB d hc hb hcomm
    hbc hac Ma Mb ht p hp ha hbp hcp
  obtain ⟨k,_,_,hk,⟨ea⟩⟩ := hi
  let : Fintype k := Fintype.ofFinite k
  let : CharP k 2 := charP_of_card_eq_prime_pow
    (by simpa only [Nat.card_eq_fintype_card] using hk)
  let ep : SL(2,k) ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) k :=
    MulEquiv.ofBijective (BenderSuzuki.Converse.pi k)
      ⟨BenderSuzuki.Converse.pi_injective,BenderSuzuki.Converse.pi_surjective⟩
  have hab := source_critical_one_adjacent hc hb
  have hcore := source_rankOne_pair_core_span_on_path h hB d hc hb hbc hac Ma Mb
    ht p hp ha hbp hcp
  have hsupp := alpha_supplement_of_pair_generation _ _ _ _ _ hprod hcore
    ((source_Z_Q_U h a).1.trans (map_subtype_le _))
  have hiq := linear_edge_core_index h hB d hab (ea.trans ep.symm)
  rw [hsupp,core_sup_index _ _
    (inf_le_right.trans (source_adjacent_core_normalizes_core h hab.symm))] at hiq
  have hlow := linear_center_order_lower h d hc hb hcomm (ea.trans ep.symm) n (by omega) hk
  have horders := source_center_seed_pair_orders_on_escaping_path h hB hS d hc hb hcomm
    hbc hac Ma Mb g hga hgb hesc ht p hp ha hbp hcp hgbp hgcp
  have hsquare := source_seed_square_on_path h hB d hc hb hcomm hbc hac Ma Mb
    ht p hp ha hbp hcp
  dsimp only at horders hsquare ⊢
  rw [horders.2.2.1,hiq] at hlow
  have hkpos : 0 < Nat.card k := Nat.card_pos
  have heq : (Q (family P) a).relIndex (Z (family P) c ⊓ Q (family P) b) =
      ((Q (family P) b).relIndex (Z (family P) a))^2 := by
    apply le_antisymm
    · rw [hiq]
      nlinarith
    · exact hsquare
  exact ⟨heq,n,hn,⟨k,inferInstance,inferInstance,hk,⟨ea⟩⟩,hk.symm.trans hiq.symm⟩

end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingOneProfile
