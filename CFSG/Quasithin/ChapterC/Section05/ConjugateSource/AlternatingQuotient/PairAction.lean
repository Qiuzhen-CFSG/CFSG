module
public import CFSG.Quasithin.ChapterC.Section05.ConjugateSource.AlternatingQuotient.Preimages
public import CFSG.Quasithin.ChapterC.Section05.ConjugateSource.AlternatingPhiNormalizer
public import Theory.GroupTheory.PairNormalizerIndex

/-!
# The core pair inside the actual quotient four-family

N_R(K)=N_R(U) is normalized by M₁=N_M(Φ(D)): this follows either from the
single-block R-normalization or from the proved two-block Φ-stabilizer
identity. It fixes both cores, while the actual inner exchange in R∩K
moves the two transposition members. The invariant portion of the four-
family is therefore precisely the core pair. The original escaping x
moves that pair, giving its stabilizer index two in M₁.

Source: Aschbacher–Smith C.5.6(5)–(6), printed p.158.
-/

public section
open Subgroup Stellmacher
namespace CFSG.Quasithin.ChapterC.Section05.ConjugateSource.AlternatingQuotient
open RankOne
open CFSG.Quasithin.ChapterE.Section06.InvariantSubspaces.LocalIndex.Conjugates.AlternatingFamily
variable {G : Type*} [Group G] {R K L : Subgroup G}

/-- The original block stabilizer preserves its characteristic core. -/
theorem block_stabilizer_normalizes_core (R K : Subgroup G) :
    R ⊓ normalizer (K : Set G) ≤ normalizer (Q R K : Set G) := by
  have hS := R.le_normalizer.trans (normalizer_le_normalizer_baumann R)
  exact ((le_inf inf_le_right (inf_le_left.trans hS)).trans
    (normalizer_inf_normalizer_le_normalizer_sup K (S R))).trans
    (normalizer_le_normalizer_characteristic_image (K ⊔ S R) (pCore 2 (K ⊔ S R : Subgroup G)))

variable [Finite G]

/-- The genuine source alternatives each yield the same normal block stabilizer. -/
theorem phi_stabilizer_normalizes_block_stabilizer (h : AlternatingPairSetup R K L)
    (hsource : R ≤ normalizer (K : Set G) ∨ Nonempty (AlternatingPairSetup R L K))
    (M : Subgroup G) (hMR : M ≤ normalizer (R : Set G)) :
    M ⊓ normalizer (Phi R K : Set G) ≤
      normalizer ((R ⊓ normalizer (K : Set G) : Subgroup G) : Set G) := by
  rcases hsource with hRK | hrev
  · rw [inf_eq_left.mpr hRK]
    exact inf_le_left.trans hMR
  · obtain ⟨h₂⟩ := hrev
    have hh := h.module_stabilizer_normalized h₂ M hMR
    change M ⊓ normalizer (Phi R K : Set G) ≤
      normalizer ((R ⊓ normalizer (sourceModule K : Set G) : Subgroup G) : Set G) at hh
    rw [← h.block_normalizer_eq_module_normalizer] at hh
    exact hh

/-- Exactly the two original cores are invariant under N_R(K). -/
theorem phiFamily_invariants (h : AlternatingPairSetup R K L)
    (hsource : R ≤ normalizer (K : Set G) ∨ Nonempty (AlternatingPairSetup R L K))
    (x : G) (hx : x ∈ normalizer (R : Set G))
    (hnc : ¬ (U K).map (MulAut.conj x⁻¹).toMonoidHom ≤ centralizer (U K : Set G)) :
    {B ∈ phiFamily h | R ⊓ normalizer (K : Set G) ≤ normalizer (B : Set G)} =
      {Q R K, (Q R K).map (MulAut.conj x⁻¹).toMonoidHom} := by
  let C := R ⊓ normalizer (K : Set G)
  let e := MulAut.conj x⁻¹
  have hQP : Q R K ∈ phiFamily h := by
    obtain ⟨B₀, B₁, hf, _, _⟩ := phiFamily_eq_four h x hx hnc
    rw [hf]
    simp
  have hxP : x⁻¹ ∈ normalizer (Phi R K : Set G) :=
    mem_normalizer_iff_map_conj_eq.mpr (h.frattini_invariant x hx hnc)
  have hxC : x⁻¹ ∈ normalizer (C : Set G) :=
    phi_stabilizer_normalizes_block_stabilizer h hsource (normalizer (R : Set G)) le_rfl
      ⟨(normalizer (R : Set G)).inv_mem hx, hxP⟩
  have hCe : C.map e.toMonoidHom = C := mem_normalizer_iff_map_conj_eq.mp hxC
  have hCQ : C ≤ normalizer (Q R K : Set G) := block_stabilizer_normalizes_core R K
  have hCQ' : C ≤ normalizer ((Q R K).map e.toMonoidHom : Set G) := by
    rw [← hCe]
    exact (map_mono hCQ).trans (le_normalizer_map e.toMonoidHom)
  have hQ'P : (Q R K).map e.toMonoidHom ∈ phiFamily h :=
    phiFamily_map h e (mem_normalizer_iff_map_conj_eq.mp (normalizer_le_normalizer_baumann R
      ((normalizer (R : Set G)).inv_mem hx))) (h.frattini_invariant x hx hnc) _ hQP
  obtain ⟨B₀, B₁, hf, h0, h1⟩ := phiFamily_eq_four h x hx hnc
  have hB₀ : B₀ ∈ phiFamily h := by rw [hf]; simp
  have hB₁ : B₁ ∈ phiFamily h := by rw [hf]; simp
  obtain ⟨r, hr, hra⟩ := h.pairExchange_mem
  have hrC : (r : G) ∈ C := ⟨hr.1, K.le_normalizer hr.2⟩
  have hn0 : ¬ C ≤ normalizer (B₀ : Set G) := by
    intro hn
    exact moved_of_line_zero h.action (hB₀.1.trans le_sup_right) h0 r hra
      (mem_normalizer_iff_map_conj_eq.mp (hn hrC)).symm
  have hn1 : ¬ C ≤ normalizer (B₁ : Set G) := by
    intro hn
    exact moved_of_line_one h.action (hB₁.1.trans le_sup_right) h1 r hra
      (mem_normalizer_iff_map_conj_eq.mp (hn hrC)).symm
  ext B
  constructor
  · rintro ⟨hB, hCB⟩
    rw [hf] at hB
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hB ⊢
    rcases hB with he | he | he | he
    · exact Or.inl he
    · exact Or.inr he
    · exact (hn0 (he ▸ hCB)).elim
    · exact (hn1 (he ▸ hCB)).elim
  · intro hB
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hB
    rcases hB with rfl | rfl
    · exact ⟨hQP, hCQ⟩
    · exact ⟨hQ'P, hCQ'⟩

/-- Every element of the actual Frattini stabilizer preserves the core pair. -/
theorem core_pair_preserved (h : AlternatingPairSetup R K L)
    (hsource : R ≤ normalizer (K : Set G) ∨ Nonempty (AlternatingPairSetup R L K))
    (x : G) (hx : x ∈ normalizer (R : Set G))
    (hnc : ¬ (U K).map (MulAut.conj x⁻¹).toMonoidHom ≤ centralizer (U K : Set G))
    (m : G) (hmR : m ∈ normalizer (R : Set G)) (hmP : m ∈ normalizer (Phi R K : Set G)) :
    (Q R K).map (MulAut.conj m).toMonoidHom = Q R K ∨
      (Q R K).map (MulAut.conj m).toMonoidHom = (Q R K).map (MulAut.conj x⁻¹).toMonoidHom := by
  let C := R ⊓ normalizer (K : Set G)
  let e := MulAut.conj m
  have hCm : m ∈ normalizer (C : Set G) :=
    phi_stabilizer_normalizes_block_stabilizer h hsource (normalizer (R : Set G)) le_rfl ⟨hmR, hmP⟩
  have hCe : C.map e.toMonoidHom = C := mem_normalizer_iff_map_conj_eq.mp hCm
  have hCQ : C ≤ normalizer (Q R K : Set G) := block_stabilizer_normalizes_core R K
  have hCQe : C ≤ normalizer ((Q R K).map e.toMonoidHom : Set G) := by
    rw [← hCe]
    exact (map_mono hCQ).trans (le_normalizer_map e.toMonoidHom)
  have hQP : Q R K ∈ phiFamily h := by
    obtain ⟨B₀, B₁, hf, _, _⟩ := phiFamily_eq_four h x hx hnc
    rw [hf]
    simp
  have hQeP := phiFamily_map h e
    (mem_normalizer_iff_map_conj_eq.mp (normalizer_le_normalizer_baumann R hmR))
    (mem_normalizer_iff_map_conj_eq.mp hmP) _ hQP
  have hh : (Q R K).map e.toMonoidHom ∈
      {B ∈ phiFamily h | C ≤ normalizer (B : Set G)} := ⟨hQeP, hCQe⟩
  rw [phiFamily_invariants h hsource x hx hnc] at hh
  simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hh

/-- The actual core stabilizer has index two in M₁=N_M(Φ(D)). -/
theorem core_normalizer_index (h : AlternatingPairSetup R K L)
    (hsource : R ≤ normalizer (K : Set G) ∨ Nonempty (AlternatingPairSetup R L K))
    (M : Subgroup G) (hMR : M ≤ normalizer (R : Set G)) (x : G) (hx : x ∈ M)
    (hnc : ¬ (U K).map (MulAut.conj x⁻¹).toMonoidHom ≤ centralizer (U K : Set G)) :
    (normalizer (Q R K : Set G)).relIndex (M ⊓ normalizer (Phi R K : Set G)) = 2 := by
  have hxP : x⁻¹ ∈ normalizer (Phi R K : Set G) :=
    mem_normalizer_iff_map_conj_eq.mpr (h.frattini_invariant x (hMR hx) hnc)
  refine normalizer_relIndex_eq_two_of_pair (M ⊓ normalizer (Phi R K : Set G)) (Q R K)
    ((Q R K).map (MulAut.conj x⁻¹).toMonoidHom) ?_ x⁻¹ ⟨M.inv_mem hx, hxP⟩ ?_
  · intro m hm
    exact core_pair_preserved h hsource x (hMR hx) hnc m (hMR hm.1) hm.2
  · intro he
    exact hnc (((map_mono (f := (MulAut.conj x⁻¹).toMonoidHom)
      (show U K ≤ Q R K from le_sup_left.trans_eq h.product.symm)).trans_eq he).trans
        (h.core.le.trans inf_le_right))
end CFSG.Quasithin.ChapterC.Section05.ConjugateSource.AlternatingQuotient
end
