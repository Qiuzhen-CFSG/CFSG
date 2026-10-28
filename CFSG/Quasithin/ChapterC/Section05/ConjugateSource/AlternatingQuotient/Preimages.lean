module
public import CFSG.Quasithin.ChapterC.Section05.ConjugateSource.AlternatingQuotient.Enumeration
public import Stellmacher.ElementaryAbelianMaxFamilyMap

/-!
# The literal preimages of the quotient four-family

The four quotient members have unique preimages in S containing Φ(D).
Their original action images distinguish the two transposition members.
Every ambient automorphism preserving S and Φ(D) permutes this actual
preimage family through the induced quotient automorphism.

Source: Aschbacher–Smith C.5.6(5), printed p.158.
-/

@[expose] public section
open Subgroup Stellmacher
namespace CFSG.Quasithin.ChapterC.Section05.ConjugateSource.AlternatingQuotient
open RankOne
open CFSG.Quasithin.ChapterE.Section06.InvariantSubspaces.LocalIndex.Conjugates.AlternatingFamily
variable {G : Type*} [Group G] {R K : Subgroup G} {T : Type*} [Group T]

theorem image_eq_of_phi_le (f : S R →* T) (hk : f.ker = (Phi R K).subgroupOf (S R))
    (B C : Subgroup G) (hB : B ≤ S R) (hC : C ≤ S R)
    (hPB : Phi R K ≤ B) (hPC : Phi R K ≤ C)
    (he : baumannImage R f B = baumannImage R f C) : B = C := by
  apply le_antisymm
  · intro b hb
    apply (baumannImage_mem_iff f hk C hPC ⟨b, hB hb⟩).mp
    rw [← he]
    exact mem_map_of_mem f hb
  · intro c hc
    apply (baumannImage_mem_iff f hk B hPB ⟨c, hC hc⟩).mp
    rw [he]
    exact mem_map_of_mem f hc

private theorem relative_equiv_map (e : G ≃* G) (hS : (S R).map e.toMonoidHom = S R)
    (B : Subgroup G) (hB : B ≤ S R) :
    (B.subgroupOf (S R)).map
      ((e.subgroupMap (S R)).trans (MulEquiv.subgroupCongr hS)).toMonoidHom =
        (B.map e.toMonoidHom).subgroupOf (S R) := by
  apply map_injective (S R).subtype_injective
  rw [map_map, map_subgroupOf_eq_of_le ((map_mono hB).trans_eq hS)]
  have he : (S R).subtype.comp
      ((e.subgroupMap (S R)).trans (MulEquiv.subgroupCongr hS)).toMonoidHom =
      e.toMonoidHom.comp (S R).subtype := by
    ext s
    rfl
  rw [he, ← map_map, map_subgroupOf_eq_of_le hB]

variable [Finite G] {L : Subgroup G}

/-- The actual family of full preimages in S of A(S/Φ(D)). -/
noncomputable def phiFamily (h : AlternatingPairSetup R K L) : Set (Subgroup G) :=
  letI := h.phi_normal
  let f := QuotientGroup.mk' ((Phi R K).subgroupOf (S R))
  {B | B ≤ S R ∧ Phi R K ≤ B ∧
    baumannImage R f B ∈ elementaryAbelianMaxSubgroups (⊤ : Subgroup ((S R) ⧸ (Phi R K).subgroupOf (S R)))}

/-- Every automorphism preserving the literal quotient permutes its preimage family. -/
theorem phiFamily_map (h : AlternatingPairSetup R K L) (e : G ≃* G)
    (hS : (S R).map e.toMonoidHom = S R) (hP : (Phi R K).map e.toMonoidHom = Phi R K)
    (B : Subgroup G) (hB : B ∈ phiFamily h) : B.map e.toMonoidHom ∈ phiFamily h := by
  let N := (Phi R K).subgroupOf (S R)
  let : N.Normal := h.phi_normal
  let f := QuotientGroup.mk' N
  let eS := (e.subgroupMap (S R)).trans (MulEquiv.subgroupCongr hS)
  have hPS : Phi R K ≤ S R := (map_subtype_le _).trans inf_le_left
  have hNm : N.map eS.toMonoidHom = N := by
    rw [relative_equiv_map e hS _ hPS, hP]
  let eT := QuotientGroup.congr N N eS hNm
  change B ≤ S R ∧ Phi R K ≤ B ∧
    baumannImage R f B ∈ elementaryAbelianMaxSubgroups (⊤ : Subgroup ((S R) ⧸ N)) at hB
  change B.map e.toMonoidHom ≤ S R ∧ Phi R K ≤ B.map e.toMonoidHom ∧ _
  refine ⟨(map_mono hB.1).trans_eq hS, hP ▸ map_mono hB.2.1, ?_⟩
  have hm : baumannImage R f (B.map e.toMonoidHom) =
      (baumannImage R f B).map eT.toMonoidHom := by
    unfold baumannImage
    rw [← relative_equiv_map e hS B hB.1, map_map, map_map]
    congr 1
  have hh := (maxFamily_map_injective_iff eT.toMonoidHom eT.injective ⊤ _).mpr hB.2.2
  have ht : (⊤ : Subgroup ((S R) ⧸ N)).map eT.toMonoidHom = ⊤ :=
    map_top_of_surjective eT.toMonoidHom eT.surjective
  rwa [ht, ← hm] at hh

/-- The exact four preimages, with their original marked action images. -/
theorem phiFamily_eq_four (h : AlternatingPairSetup R K L) (x : G)
    (hx : x ∈ normalizer (R : Set G))
    (hnc : ¬ (U K).map (MulAut.conj x⁻¹).toMonoidHom ≤ centralizer (U K : Set G)) :
    ∃ B₀ B₁ : Subgroup G,
      phiFamily h = {Q R K, (Q R K).map (MulAut.conj x⁻¹).toMonoidHom, B₀, B₁} ∧
      actionImage h.action B₀ = line 0 ∧ actionImage h.action B₁ = line 1 := by
  let N := (Phi R K).subgroupOf (S R)
  let : N.Normal := h.phi_normal
  let f := QuotientGroup.mk' N
  have hf : Function.Surjective f := QuotientGroup.mk'_surjective N
  have hk : f.ker = N := QuotientGroup.ker_mk' N
  have hkD : f.ker ≤ (D R K).subgroupOf (S R) := by
    rw [hk]
    exact subgroupOf_mono _ (map_subtype_le _)
  obtain ⟨A₀, A₁, hfamily, h0, h1⟩ := quotient_family_eq_four h x hx hnc f hf hk.ge hkD
  let lift (A : Subgroup ((S R) ⧸ N)) : Subgroup G := (A.comap f).map (S R).subtype
  have hlS (A) : lift A ≤ S R := map_subtype_le _
  have hlP (A) : Phi R K ≤ lift A := by
    intro p hp
    have hpS : p ∈ S R := ((map_subtype_le _).trans inf_le_left) hp
    refine ⟨⟨p, hpS⟩, ?_, rfl⟩
    change f ⟨p, hpS⟩ ∈ A
    have he : f ⟨p, hpS⟩ = 1 := MonoidHom.mem_ker.mp (hk.symm ▸ hp)
    rw [he]
    exact A.one_mem
  have him (A) : baumannImage R f (lift A) = A := by
    unfold baumannImage lift subgroupOf
    rw [comap_map_eq_self (by rw [(S R).subtype.ker_eq_bot (S R).subtype_injective]; exact bot_le)]
    exact map_comap_eq_self_of_surjective hf A
  have hQ : Q R K ≤ S R := h.core.le.trans inf_le_left
  have hQ' : (Q R K).map (MulAut.conj x⁻¹).toMonoidHom ≤ S R :=
    (h.conjugate_core x hx).le.trans inf_le_left
  have hPQ : Phi R K ≤ Q R K :=
    (map_subtype_le _).trans (le_sup_right.trans_eq h.product.symm)
  have hPQ' : Phi R K ≤ (Q R K).map (MulAut.conj x⁻¹).toMonoidHom :=
    (map_subtype_le _).trans (le_sup_right.trans_eq (h.opposite_eq_conjugate x hx hnc))
  have hqmem : Q R K ∈ phiFamily h := by
    refine ⟨hQ, hPQ, ?_⟩
    change baumannImage R f (Q R K) ∈ _
    rw [hfamily]
    exact Set.mem_insert _ _
  have hq'mem : (Q R K).map (MulAut.conj x⁻¹).toMonoidHom ∈ phiFamily h := by
    refine ⟨hQ', hPQ', ?_⟩
    change baumannImage R f ((Q R K).map (MulAut.conj x⁻¹).toMonoidHom) ∈ _
    rw [hfamily]
    exact Set.mem_insert_of_mem _ (Set.mem_insert _ _)
  have hamem (A) (ha : A ∈ elementaryAbelianMaxSubgroups (⊤ : Subgroup ((S R) ⧸ N))) :
      lift A ∈ phiFamily h := ⟨hlS A, hlP A, by change baumannImage R f (lift A) ∈ _; rwa [him]⟩
  refine ⟨lift A₀, lift A₁, ?_, ?_, ?_⟩
  · ext B
    constructor
    · intro hb
      have hm := hb.2.2
      change baumannImage R f B ∈ elementaryAbelianMaxSubgroups (⊤ : Subgroup ((S R) ⧸ N)) at hm
      rw [hfamily] at hm
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hm ⊢
      rcases hm with he | he | he | he
      · exact Or.inl (image_eq_of_phi_le f hk B _ hb.1 hQ hb.2.1 hPQ he)
      · exact Or.inr (Or.inl (image_eq_of_phi_le f hk B _ hb.1 hQ' hb.2.1 hPQ' he))
      · exact Or.inr (Or.inr (Or.inl (image_eq_of_phi_le f hk B _ hb.1 (hlS _) hb.2.1 (hlP _) (he.trans (him _).symm))))
      · exact Or.inr (Or.inr (Or.inr (image_eq_of_phi_le f hk B _ hb.1 (hlS _) hb.2.1 (hlP _) (he.trans (him _).symm))))
    · intro hb
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hb
      rcases hb with rfl | rfl | rfl | rfl
      · exact hqmem
      · exact hq'mem
      · exact hamem _ (by rw [hfamily]; simp)
      · exact hamem _ (by rw [hfamily]; simp)
  · change ((lift A₀).subgroupOf (K ⊔ S R)).map h.action = line 0
    rw [← image_action h f hf hkD _ (hlS _), him, h0]
  · change ((lift A₁).subgroupOf (K ⊔ S R)).map h.action = line 1
    rw [← image_action h f hf hkD _ (hlS _), him, h1]
end CFSG.Quasithin.ChapterC.Section05.ConjugateSource.AlternatingQuotient
end
