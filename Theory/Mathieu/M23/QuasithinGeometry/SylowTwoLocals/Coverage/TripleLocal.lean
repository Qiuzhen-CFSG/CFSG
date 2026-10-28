module
public import Theory.Mathieu.M23.QuasithinGeometry.CommonFour.Cores
public import Theory.Mathieu.M23.QuasithinGeometry.SylowTwoLocals.Coverage.FixedPoints
public import Theory.Mathieu.M23.QuasithinGeometry.SylowTwoLocals.Basic
public import Theory.GroupTheory.TwoLocalTransport

/-!
# Triple stabilizers are actual two-locals of native M23

The five octads through the standard tetrad recover its sextet, by uniqueness
of the octad through five points. Thus an M23 permutation preserving the three
remaining points of that tetrad preserves the marked quintet. Its intrinsic
E16 core, already identified with the first elementary Sylow candidate, fixes
exactly those three points. Its full normalizer is consequently the triple
stabilizer. Three-transitivity transports this result to every natural triple.

This provides the locality, as well as actual conjugacy with the published
candidate, needed in the exhaustive local calculation from GLS3 Table 5.3d
and Aschbacher--Smith 15.3.41--42, printed p.1138. No ordinary maximality
hypothesis is used.
-/

@[expose] public section
open Subgroup
open scoped Pointwise
namespace Sporadic.Mathieu.M23Geometry.SylowTwoLocals.Coverage
open M24LocalGeometry MathieuCode CommonFour
set_option maxRecDepth 100000
set_option Elab.async false

private theorem octad_through_tetrad (B : Finset (Fin 24)) (hB : B ∈ m24Blocks)
    (hAB : standardTetrad 0 ⊆ B) :
    ∃ i : Fin 6, i ≠ 0 ∧ B = standardTetrad 0 ∪ standardTetrad i := by
  obtain ⟨x,hx,hx0⟩ := Finset.exists_mem_notMem_of_card_lt_card
    (show (standardTetrad 0).card < B.card by rw [standardTetrad_card, m24Blocks_card B hB]; decide)
  have hcover : ∃ i : Fin 6, x ∈ standardTetrad i := by
    have hc : x ∈ standardSextet.parts.biUnion id := standardSextet.cover.symm ▸ Finset.mem_univ x
    obtain ⟨A,hA,hxA⟩ := Finset.mem_biUnion.mp hc
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hA
    exact ⟨i,hxA⟩
  obtain ⟨i,hi⟩ := hcover
  have hi0 : i ≠ 0 := fun h => hx0 (h ▸ hi)
  have hcard : (insert x (standardTetrad 0)).card = 5 := by
    rw [Finset.card_insert_of_notMem hx0, standardTetrad_card]
  obtain ⟨C,hC⟩ := Finset.card_eq_one.mp (m24Blocks_unique_block _ hcard)
  have hmem (D : Finset (Fin 24)) (hD : D ∈ m24Blocks)
      (hAD : insert x (standardTetrad 0) ⊆ D) : D = C := by
    have hm : D ∈ m24Blocks.filter (insert x (standardTetrad 0) ⊆ ·) :=
      Finset.mem_filter.mpr ⟨hD,hAD⟩
    simpa only [hC, Finset.mem_singleton] using hm
  refine ⟨i,hi0,(hmem B (hB) (Finset.insert_subset_iff.mpr ⟨hx,hAB⟩)).trans ?_⟩
  apply Eq.symm
  apply hmem _ (standardTetrad_union_mem 0 i hi0.symm)
  exact Finset.insert_subset_iff.mpr ⟨Finset.mem_union_right _ hi, Finset.subset_union_left⟩

private theorem tetrad_stabilizer_le_sextet :
    MulAction.stabilizer M24 (standardTetrad 0) ≤ sextetStabilizer standardSextet := by
  intro g hg
  have hg0 : g • standardTetrad 0 = standardTetrad 0 := hg
  apply MulAction.mem_stabilizer_finset'.mpr
  intro A hA
  obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hA
  by_cases hi : i = 0
  · subst i
    rw [hg0]
    exact Finset.mem_image.mpr ⟨0, Finset.mem_univ _, rfl⟩
  have hB : g • (standardTetrad 0 ∪ standardTetrad i) ∈ m24Blocks := by
    have hp := (mem_M24_iff g.val).mp g.property
    change g.val • (standardTetrad 0 ∪ standardTetrad i) ∈ (m24Blocks : Set (Finset (Fin 24)))
    rw [← hp]
    exact Set.smul_mem_smul_set (standardTetrad_union_mem 0 i (Ne.symm hi))
  obtain ⟨j,hj,he⟩ := octad_through_tetrad _ hB (by
    rw [Finset.smul_finset_union, hg0]
    exact Finset.subset_union_left)
  have hl : (g • (standardTetrad 0 ∪ standardTetrad i)) \ standardTetrad 0 =
      g • standardTetrad i := by
    calc
      _ = (g • (standardTetrad 0 ∪ standardTetrad i)) \ (g • standardTetrad 0) := by rw [hg0]
      _ = g • ((standardTetrad 0 ∪ standardTetrad i) \ standardTetrad 0) :=
        Finset.smul_finset_sdiff.symm
      _ = _ := by rw [Finset.union_sdiff_cancel_left (standardTetrad_disjoint 0 i (Ne.symm hi))]
  have hd := congrArg (fun F : Finset (Fin 24) => F \ standardTetrad 0) he
  rw [hl, Finset.union_sdiff_cancel_left (standardTetrad_disjoint 0 j hj.symm)] at hd
  exact Finset.mem_image.mpr ⟨j, Finset.mem_univ _, hd.symm⟩

private def markedTriple : Finset (Fin 23) := {1, 2, 3}

private theorem markedTriple_le_quintet :
    MulAction.stabilizer M23 markedTriple ≤ quintetStabilizer := by
  intro g hg
  apply tetrad_stabilizer_le_sextet
  apply MulAction.mem_stabilizer_finset'.mpr
  intro a ha
  have hh : standardTetrad 0 = insert 0 (markedTriple.image m23PointEmbedding) := by decide +kernel
  rw [hh] at ha ⊢
  rcases Finset.mem_insert.mp ha with rfl | ha
  · change (pointEmbedding g).val 0 ∈ _
    rw [pointEmbedding_fixed]
    exact Finset.mem_insert_self _ _
  · obtain ⟨b,hb,rfl⟩ := Finset.mem_image.mp ha
    apply Finset.mem_insert_of_mem
    have hb' : g • b ∈ markedTriple := MulAction.mem_stabilizer_finset'.mp hg hb
    exact Finset.mem_image.mpr ⟨g • b, hb', (pointEmbedding_apply g b).symm⟩

private theorem first_candidate_fixed : ∀ a : Fin 23,
    a ∈ fixedTriple ↔ ∀ i : Fin 16, FusionCertificate.pointTable
      (ElementarySylow.candidateIndex 0 i) a = a := by decide +kernel

private theorem transport_triple : transportPerm • fixedTriple = markedTriple := by decide +kernel

private theorem marked_core_fixed (a : Fin 23) :
    a ∈ markedTriple ↔ ∀ u ∈ standardCandidate 0, u • a = a := by
  have hmem : a ∈ markedTriple ↔ transport⁻¹ • a ∈ fixedTriple := by
    have ht : transport • fixedTriple = markedTriple := transport_triple
    rw [← ht]
    constructor
    · intro ha
      obtain ⟨b,hb,rfl⟩ := Finset.mem_smul_finset.mp ha
      simpa only [inv_smul_smul] using hb
    · intro ha
      exact Finset.mem_smul_finset.mpr ⟨transport⁻¹ • a, ha, smul_inv_smul _ _⟩
  rw [hmem, first_candidate_fixed]
  constructor
  · intro ha u hu
    obtain ⟨v,hv,rfl⟩ := hu
    obtain ⟨i,hi⟩ := (ElementarySylow.mem_candidate 0 v).mp hv
    have hf : v • (transport⁻¹ • a) = transport⁻¹ • a := by
      change v.val _ = _
      rw [← hi]
      exact ha i
    change (transport * v * transport⁻¹) • a = a
    rw [mul_smul, mul_smul, hf, smul_inv_smul]
  · intro ha i
    let v : M23 := ⟨FusionCertificate.perm (ElementarySylow.candidateIndex 0 i),
      FusionCertificate.rawSubgroup_le (FusionCertificate.perm_mem _)⟩
    have hv : v ∈ ElementarySylow.candidate 0 := ⟨i,rfl⟩
    have hh := ha _ (Subgroup.mem_map.mpr ⟨v,hv,rfl⟩)
    change (transport * v * transport⁻¹) • a = a at hh
    have he := congrArg (fun x : Fin 23 => transport⁻¹ • x) hh
    change v • (transport⁻¹ • a) = transport⁻¹ • a
    simpa only [mul_smul, inv_smul_smul] using he

private theorem marked_core_normalizer :
    normalizer (standardCandidate 0 : Set M23) = MulAction.stabilizer M23 markedTriple := by
  apply le_antisymm
  · intro g hg
    apply MulAction.mem_stabilizer_finset'.mpr
    intro a ha
    apply (marked_core_fixed _).mpr
    intro u hu
    have hv := (mem_normalizer_iff.mp ((normalizer (standardCandidate 0 : Set M23)).inv_mem hg) u).mp hu
    have hf := (marked_core_fixed a).mp ha _ hv
    have hh := congrArg (fun b : Fin 23 => g • b) hf
    simpa only [inv_inv, mul_smul, smul_inv_smul] using hh
  · apply markedTriple_le_quintet.trans
    rw [← quintet_core_eq]
    have h := le_normalizer_map (H := pCore 2 quintetStabilizer) quintetStabilizer.subtype
    rw [Subgroup.normalizer_eq_top] at h
    exact fun x hx => h ⟨⟨x,hx⟩, Subgroup.mem_top _, rfl⟩

private theorem marked_triple_isTwoLocal : IsTwoLocal (MulAction.stabilizer M23 markedTriple) := by
  refine ⟨standardCandidate 0, ?_, (standardCandidate_elementary 0).isPGroup 2 _,
    marked_core_normalizer.symm⟩
  intro h
  have hc := standardCandidate_card 0
  rw [h, Subgroup.card_bot] at hc
  contradiction

private def tripleEmbedding {α : Type*} (a b c : α)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) : Fin 3 ↪ α where
  toFun := ![a, b, c]
  inj' := by
    intro i j h
    fin_cases i <;> fin_cases j <;> simp_all

/-- Three-transitivity on the actual natural points gives conjugacy of triples. -/
theorem triples_conjugate (F H : Finset (Fin 23)) (hF : F.card = 3) (hH : H.card = 3) :
    ∃ g : M23, g • F = H := by
  obtain ⟨a,b,c,hab,hac,hbc,rfl⟩ := Finset.card_eq_three.mp hF
  obtain ⟨d,e,f,hde,hdf,hef,rfl⟩ := Finset.card_eq_three.mp hH
  let := m23_isFourPretransitive
  let := MulAction.isMultiplyPretransitive_of_le (G := M23) (α := Fin 23)
    (m := 3) (n := 4) (by decide) (by simp)
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq M23
    (tripleEmbedding a b c hab hac hbc) (tripleEmbedding d e f hde hdf hef)
  have ha : g • a = d := congrArg (fun z : Fin 3 ↪ Fin 23 => z 0) hg
  have hb : g • b = e := congrArg (fun z : Fin 3 ↪ Fin 23 => z 1) hg
  have hc : g • c = f := congrArg (fun z : Fin 3 ↪ Fin 23 => z 2) hg
  exact ⟨g, by simp only [Finset.smul_finset_insert, Finset.smul_finset_singleton, ha,hb,hc]⟩

/-- Every natural triple stabilizer is the normalizer of a nontrivial native
two-subgroup, obtained from the marked quintet's intrinsic E16 core. -/
theorem triple_stabilizer_isTwoLocal (F : Finset (Fin 23)) (hF : F.card = 3) :
    IsTwoLocal (MulAction.stabilizer M23 F) := by
  obtain ⟨g,rfl⟩ := triples_conjugate markedTriple F (by decide +kernel) hF
  rw [MulAction.stabilizer_smul_eq_stabilizer_map_conj]
  exact Theory.GroupTheory.isTwoLocal_map (MulAut.conj g) marked_triple_isTwoLocal

/-- The concrete triple candidate covers every natural triple stabilizer by
actual conjugation inside M23. -/
theorem triple_stabilizer_conjugate (F : Finset (Fin 23)) (hF : F.card = 3) :
    ∃ g : M23, MulAction.stabilizer M23 F =
      tripleStabilizer.map (MulAut.conj g).toMonoidHom := by
  obtain ⟨g,rfl⟩ := triples_conjugate {0,1,2} F (by decide +kernel) hF
  exact ⟨g, MulAction.stabilizer_smul_eq_stabilizer_map_conj _ _⟩

end Sporadic.Mathieu.M23Geometry.SylowTwoLocals.Coverage
