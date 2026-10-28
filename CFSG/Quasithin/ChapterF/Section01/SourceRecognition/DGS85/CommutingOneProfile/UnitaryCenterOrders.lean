module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingOneProfile.UnitaryNeighborCore
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingOneProfile.SourceFieldParameters

/-!
# Unitary center orders and the field equation from short paths

The neighboring-core calculation supplies the beta-center order without
four-walk transitivity. Two-walk transitivity suffices for the alpha
selection, the core supplement and the seed indices. Counting the two
seeds gives the alpha-center and pair-span orders. The faithful linear
center module gives the lower bound that identifies q_alpha = q_beta².
The actual unitary Sylow omega-center evaluates q_beta in the input field.

The final profile retains that field degree and both PSU and SU markings,
and constructs its own neighbors and escaping turn. `OriginalUnitaryCenters`
applies it through the literal reduced-group inclusion and supplies both
original graph valences. No later core-order or path-profile theorem is used.
Source: DGS85, Groups and Graphs, (11.6)(c,d), pp.172--174, and (5.7), p.108.
-/

public noncomputable section
open Subgroup
open SimpleGraph SimpleGraph.PathTransitivePolygon
open scoped Pointwise MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingOneProfile
open Subgroup.CosetGeometry.RankTwo CommutingNontrivial Theory.GroupTheory.AmalgamGraph
open Representation Representation.BinaryOffender
variable {G : Type*} [Group G] {P : Fin 2 → Subgroup G} {B : Subgroup G}

private theorem core_sup_index (Q C : Subgroup G)
    (hCQ : C ≤ normalizer (Q : Set G)) : Q.relIndex (Q ⊔ C) = Q.relIndex C := by
  let H := Q ⊔ C
  let : (Q.subgroupOf H).Normal := normal_subgroupOf_of_le_normalizer
    (sup_le Q.le_normalizer hCQ)
  have he := relIndex_sup_left (C.subgroupOf H) (Q.subgroupOf H)
  rw [←subgroupOf_sup le_sup_left le_sup_right,relIndex_subgroupOf le_rfl,
    relIndex_subgroupOf le_sup_right] at he
  exact he

private theorem normalized_product_card (A C : Subgroup G)
    (hn : C ≤ normalizer (A : Set G)) :
    Nat.card A * Nat.card C = Nat.card (A ⊓ C : Subgroup G) * Nat.card (A ⊔ C : Subgroup G) := by
  have hi : A.relIndex (A ⊔ C) = (A ⊓ C).relIndex C :=
    (core_sup_index A C hn).trans (inf_relIndex_right A C).symm
  have hH := relIndex_mul_relIndex (⊥ : Subgroup G) A (A ⊔ C) bot_le le_sup_left
  have hC := relIndex_mul_relIndex (⊥ : Subgroup G) (A ⊓ C) C bot_le inf_le_right
  simp only [relIndex_bot_left] at hH hC
  rw [hi] at hH
  rw [←hC,←hH]
  ac_rfl

/-- The two center orders and the corrected pair-span order, with the source
path and center-index premises discharged. -/
theorem source_unitary_center_seed_pair_orders
    (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (hS : ∀ i, ∃ T : Sylow 2 (P i), (T : Subgroup (P i)).map (P i).subtype ≤ B)
    (d : EarlierLocalTheorems (family P))
    {a b c : Vertex (family P)} (hc : IsCriticalPair (family P) a b)
    (hb : DGS85.b (family P) = 1) (hcomm : ⁅Z (family P) a,Z (family P) b⁆ = ⊥)
    (hbc : (graph (family P)).Adj b c) (hac : a ≠ c)
    (Ma : IsRankOneModel (d.localGroup a ⧸ pCore 2 (d.localGroup a)))
    {m : ℕ} (hm : 0 < m)
    (mark : ClassicalGroup.IsPSU (d.localGroup b ⧸ pCore 2 (d.localGroup b)) 3 (2^m) ∨
      IsSU (d.localGroup b ⧸ pCore 2 (d.localGroup b)) 3 (2^m))
 :
    let qα := (Q (family P) a).relIndex (Z (family P) c ⊓ Q (family P) b)
    let qβ := (Q (family P) b).relIndex (Z (family P) a)
    Nat.card (Z (family P) b) = qβ ∧
      Nat.card (Z (family P) a ⊓ Q (family P) b : Subgroup G) = qα * qβ ∧
      Nat.card (Z (family P) a) = qα * qβ^2 ∧
      Nat.card (pairSpan (Z (family P) a) (Z (family P) c) (Q (family P) b)) = qα^2 * qβ := by
  have hab := source_critical_one_adjacent hc hb
  let p : BasedWalk (graph (family P)) 2 a := ⟨⟨b,hab⟩,⟨⟨c,hbc⟩,PUnit.unit⟩⟩
  have hp : p.Nonbacktracking := ⟨hac.symm,trivial⟩
  have ht := source_unitary_beta_two_walk_transitive h hB d hab hm mark
  have ha : a ∈ p.vertices := by change a ∈ [a,b,c]; simp
  have hbp : b ∈ p.vertices := by change b ∈ [a,b,c]; simp
  have hcp : c ∈ p.vertices := by change c ∈ [a,b,c]; simp
  have Mb : IsRankOneModel (d.localGroup b ⧸ pCore 2 (d.localGroup b)) := by
    rcases mark with hi | hi
    · exact .projective_unitary m hm hi
    · exact .special_unitary m hm hi
  let := finite_endpoints h
  let : Finite (Z (family P) b) := Finite.of_injective
    (inclusion (Z_le_stabilizer _ b)) (inclusion_injective _)
  let qα := (Q (family P) a).relIndex (Z (family P) c ⊓ Q (family P) b)
  let qβ := (Q (family P) b).relIndex (Z (family P) a)
  let E := Z (family P) a ⊓ Q (family P) b
  let C := Z (family P) c ⊓ Q (family P) b
  obtain ⟨n,hn,hi⟩ := (source_core_product_and_alpha_on_path h hB d hc hb hcomm
    hbc hac Ma Mb ht p hp ha hbp hcp).2
  obtain ⟨k,_,_,hk,⟨ea⟩⟩ := hi
  let : Fintype k := Fintype.ofFinite k
  let : CharP k 2 := charP_of_card_eq_prime_pow
    (by simpa only [Nat.card_eq_fintype_card] using hk)
  let ep : SL(2,k) ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) k :=
    MulEquiv.ofBijective (BenderSuzuki.Converse.pi k)
      ⟨BenderSuzuki.Converse.pi_injective,BenderSuzuki.Converse.pi_surjective⟩
  have hcent := source_linear_rankOne_center_intersections h hB d hc hb hcomm hbc hac Ma Mb (ea.trans ep.symm)
  have hz : Nat.card (Z (family P) b) = qβ :=
    (source_unitary_neighbor_core_center_from_marking h hB hS d hc hb hcomm Ma hm mark).2
  have hic : Q (family P) a ⊓ C = Z (family P) b := by
    change Q (family P) a ⊓ (Z (family P) c ⊓ Q (family P) b) = _
    rw [←inf_assoc,hcent.2.1,inf_eq_left.mpr ((source_Z_Q_U h b).1.trans (map_subtype_le _))]
  have hZC : Z (family P) b ≤ C := hic ▸ inf_le_right
  have hidx : (Z (family P) b).relIndex C = qα := by
    rw [←hic,inf_relIndex_right]
  have hcount := relIndex_mul_relIndex (⊥ : Subgroup G) (Z (family P) b) C bot_le hZC
  rw [relIndex_bot_left,relIndex_bot_left,hidx,hz] at hcount
  obtain ⟨t,_,_,_,he⟩ := source_neighbor_conjugate h hab hbc
  have hconj : Nat.card C = Nat.card E := by
    change Nat.card (Z (family P) c ⊓ Q (family P) b : Subgroup G) = _
    rw [←he,card_map_of_injective (MulAut.conj t).injective]
  have hE : Nat.card E = qα * qβ := by
    rw [hconj] at hcount
    exact hcount.symm.trans (Nat.mul_comm _ _)
  have hC : Nat.card C = qα * qβ := hconj.trans hE
  have hcount' := relIndex_mul_relIndex (⊥ : Subgroup G) E (Z (family P) a) bot_le inf_le_left
  have hidx' : E.relIndex (Z (family P) a) = qβ := inf_relIndex_left _ _
  rw [relIndex_bot_left,relIndex_bot_left,hidx',hE] at hcount'
  have hZa : Nat.card (Z (family P) a) = qα * qβ^2 := hcount'.symm.trans (by ring)
  have hnC : C ≤ normalizer (E : Set G) := inf_le_right.trans
    ((le_inf (source_adjacent_core_normalizes_center h hab)
      (Q (family P) b).le_normalizer).trans inf_normalizer_le_normalizer_inf)
  have hprod := normalized_product_card E C hnC
  rw [hE,hC,hcent.2.2.2,hz] at hprod
  refine ⟨hz,hE,hZa,?_⟩
  change Nat.card (E ⊔ C : Subgroup G) = qα^2*qβ
  apply Nat.eq_of_mul_eq_mul_left (show 0 < qβ from hz ▸ Nat.card_pos)
  exact hprod.symm.trans (by ring)

private theorem omega_card_transport {H D : Type*} [Group H] [Group D] [Finite H]
    (e : H ≃* D) (T : Sylow 2 H) :
    Nat.card (omegaCenterIn (T.mapSurjective (f := e.toMonoidHom) e.surjective : Subgroup D)) =
      Nat.card (omegaCenterIn (T : Subgroup H)) := by
  change Nat.card (omegaCenterIn ((T : Subgroup H).map e.toMonoidHom)) = _
  rw [←NilesRankOneKernel.omegaCenterIn_map_injective e.toMonoidHom e.injective,
    card_map_of_injective e.injective]

/-- The beta-center order uses the exact input unitary degree, including degree one. -/
theorem source_unitary_center_card_from_marking
    (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (hS : ∀ i, ∃ T : Sylow 2 (P i), (T : Subgroup (P i)).map (P i).subtype ≤ B)
    (d : EarlierLocalTheorems (family P))
    {a b c : Vertex (family P)} (hc : IsCriticalPair (family P) a b)
    (hb : DGS85.b (family P) = 1) (hcomm : ⁅Z (family P) a,Z (family P) b⁆ = ⊥)
    (hbc : (graph (family P)).Adj b c) (hac : a ≠ c)
    (Ma : IsRankOneModel (d.localGroup a ⧸ pCore 2 (d.localGroup a)))
    {m : ℕ} (hm : 0 < m)
    (mark : ClassicalGroup.IsPSU (d.localGroup b ⧸ pCore 2 (d.localGroup b)) 3 (2^m) ∨
      IsSU (d.localGroup b ⧸ pCore 2 (d.localGroup b)) 3 (2^m))
 :
    Nat.card (Z (family P) b) = 2^m := by
  have hab := source_critical_one_adjacent hc hb
  let p : BasedWalk (graph (family P)) 2 a := ⟨⟨b,hab⟩,⟨⟨c,hbc⟩,PUnit.unit⟩⟩
  have hp : p.Nonbacktracking := ⟨hac.symm,trivial⟩
  have ht := source_unitary_beta_two_walk_transitive h hB d hab hm mark
  have ha : a ∈ p.vertices := by change a ∈ [a,b,c]; simp
  have hbp : b ∈ p.vertices := by change b ∈ [a,b,c]; simp
  have hcp : c ∈ p.vertices := by change c ∈ [a,b,c]; simp
  have Mb : IsRankOneModel (d.localGroup b ⧸ pCore 2 (d.localGroup b)) := by
    rcases mark with hi | hi
    · exact .projective_unitary m hm hi
    · exact .special_unitary m hm hi
  let : Finite (d.localGroup b ⧸ pCore 2 (d.localGroup b)) := Mb.finite
  have hz := (source_unitary_neighbor_core_center_from_marking h hB hS d hc hb hcomm Ma hm mark).2
  obtain ⟨Ta,Tb,_,_,_,hidx⟩ := source_core_product_indices_on_path h hB d hc hb hbc hac
    Ma Mb ht p hp ha hbp hcp
  apply (hz.trans hidx.symm).trans
  rcases mark with mark | mark
  · obtain ⟨E,_,_,J,hcard,hconj,⟨eb⟩⟩ := mark
    have hm := BenderSuzuki.MatrixGroups.HermitianForm.SylowOmegaIndex.projective J hm hcard hconj
      (Tb.mapSurjective (f := eb.toMonoidHom) eb.surjective)
    exact (omega_card_transport eb Tb).symm.trans hm.1
  · obtain ⟨E,_,_,J,hcard,hconj,⟨eb⟩⟩ := mark
    have hm := BenderSuzuki.MatrixGroups.HermitianForm.SylowOmegaIndex.special J hm hcard hconj
      (Tb.mapSurjective (f := eb.toMonoidHom) eb.surjective)
    exact (omega_card_transport eb Tb).symm.trans hm.1

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

/-- The alpha field equals the square of the critical-center index, without
a four-walk hypothesis or an independent alpha marking. -/
theorem source_unitary_field_parameters_from_marking
    (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (hS : ∀ i, ∃ T : Sylow 2 (P i), (T : Subgroup (P i)).map (P i).subtype ≤ B)
    (d : EarlierLocalTheorems (family P))
    {a b c : Vertex (family P)} (hc : IsCriticalPair (family P) a b)
    (hb : DGS85.b (family P) = 1) (hcomm : ⁅Z (family P) a,Z (family P) b⁆ = ⊥)
    (hbc : (graph (family P)).Adj b c) (hac : a ≠ c)
    (Ma : IsRankOneModel (d.localGroup a ⧸ pCore 2 (d.localGroup a)))
    {m : ℕ} (hm : 0 < m)
    (mark : ClassicalGroup.IsPSU (d.localGroup b ⧸ pCore 2 (d.localGroup b)) 3 (2^m) ∨
      IsSU (d.localGroup b ⧸ pCore 2 (d.localGroup b)) 3 (2^m))
 :
    let qα := (Q (family P) a).relIndex (Z (family P) c ⊓ Q (family P) b)
    let qβ := (Q (family P) b).relIndex (Z (family P) a)
    qα = qβ^2 ∧
      ∃ n, 1 < n ∧ ClassicalGroup.IsPSL (d.localGroup a ⧸ pCore 2 (d.localGroup a)) 2 (2^n) ∧
        2^n = qα := by
  have hab := source_critical_one_adjacent hc hb
  let p : BasedWalk (graph (family P)) 2 a := ⟨⟨b,hab⟩,⟨⟨c,hbc⟩,PUnit.unit⟩⟩
  have hp : p.Nonbacktracking := ⟨hac.symm,trivial⟩
  have ht := source_unitary_beta_two_walk_transitive h hB d hab hm mark
  have ha : a ∈ p.vertices := by change a ∈ [a,b,c]; simp
  have hbp : b ∈ p.vertices := by change b ∈ [a,b,c]; simp
  have hcp : c ∈ p.vertices := by change c ∈ [a,b,c]; simp
  have Mb : IsRankOneModel (d.localGroup b ⧸ pCore 2 (d.localGroup b)) := by
    rcases mark with hi | hi
    · exact .projective_unitary m hm hi
    · exact .special_unitary m hm hi
  obtain ⟨hprod,n,hn,hi⟩ := source_core_product_and_alpha_on_path h hB d hc hb hcomm
    hbc hac Ma Mb ht p hp ha hbp hcp
  obtain ⟨k,_,_,hk,⟨ea⟩⟩ := hi
  let : Fintype k := Fintype.ofFinite k
  let : CharP k 2 := charP_of_card_eq_prime_pow
    (by simpa only [Nat.card_eq_fintype_card] using hk)
  let ep : SL(2,k) ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) k :=
    MulEquiv.ofBijective (BenderSuzuki.Converse.pi k)
      ⟨BenderSuzuki.Converse.pi_injective,BenderSuzuki.Converse.pi_surjective⟩
  have hcore := source_rankOne_pair_core_span_on_path h hB d hc hb hbc hac Ma Mb
    ht p hp ha hbp hcp
  have hsupp := alpha_supplement_of_pair_generation _ _ _ _ _ hprod hcore
    ((source_Z_Q_U h a).1.trans (map_subtype_le _))
  have hiq := linear_edge_core_index h hB d hab (ea.trans ep.symm)
  rw [hsupp,core_sup_index _ _
    (inf_le_right.trans (source_adjacent_core_normalizes_core h hab.symm))] at hiq
  have hlow := linear_center_order_lower h d hc hb hcomm (ea.trans ep.symm) n (by omega) hk
  have horders := source_unitary_center_seed_pair_orders h hB hS d hc hb hcomm hbc hac Ma hm mark
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

/-- The original unitary marking determines both center orders, the neighboring
core intersection and the alpha field, with no path or escape input. -/
theorem source_unitary_marked_center_profile
    (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (hS : ∀ i, ∃ T : Sylow 2 (P i), (T : Subgroup (P i)).map (P i).subtype ≤ B)
    (d : EarlierLocalTheorems (family P))
    {a b : Vertex (family P)} (hc : IsCriticalPair (family P) a b)
    (hb : DGS85.b (family P) = 1) (hcomm : ⁅Z (family P) a,Z (family P) b⁆ = ⊥)
    (Ma : IsRankOneModel (d.localGroup a ⧸ pCore 2 (d.localGroup a)))
    {m : ℕ} (hm : 0 < m)
    (mark : ClassicalGroup.IsPSU (d.localGroup b ⧸ pCore 2 (d.localGroup b)) 3 (2^m) ∨
      IsSU (d.localGroup b ⧸ pCore 2 (d.localGroup b)) 3 (2^m))
 :
    neighborCoreIntersection (family P) b = Z (family P) b ∧
      Nat.card (Z (family P) b) = 2^m ∧
      Nat.card (Z (family P) a) = 2^(4*m) ∧
      ClassicalGroup.IsPSL (d.localGroup a ⧸ pCore 2 (d.localGroup a)) 2 (2^(2*m)) := by
  obtain ⟨c,hbc,hac,_,_,_,_,_⟩ := source_unitary_beta_escaping_four_walk
    h hB hS d hc hb hcomm Ma hm mark
  have hcens := source_unitary_center_seed_pair_orders h hB hS d hc hb hcomm hbc hac Ma hm mark
  have hβ := source_unitary_center_card_from_marking h hB hS d hc hb hcomm hbc hac Ma hm mark
  obtain ⟨hfield,n,hn,hi,hα⟩ := source_unitary_field_parameters_from_marking
    h hB hS d hc hb hcomm hbc hac Ma hm mark
  have hqβ : (Q (family P) b).relIndex (Z (family P) a) = 2^m := hcens.1.symm.trans hβ
  have hqα : (Q (family P) a).relIndex (Z (family P) c ⊓ Q (family P) b) = 2^(2*m) := by
    rw [hfield,hqβ,←pow_mul,Nat.mul_comm]
  refine ⟨(source_unitary_neighbor_core_center_from_marking h hB hS d hc hb hcomm Ma hm mark).1,hβ,?_,?_⟩
  · rw [hcens.2.2.1,hqα,hqβ,←pow_mul,←pow_add]
    congr 1
    omega
  · rw [←hqα,←hα]
    exact hi

end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingOneProfile
