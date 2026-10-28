module
public import CFSG.Quasithin.ChapterC.Section05.ConjugateSource.RankOne.Family.Quotient
public import CFSG.Quasithin.ChapterC.Section05.ConjugateSource.RankOne.Family.EvenOrder
public import Theory.GroupTheory.PairNormalizerIndex

/-!
# The original normalizer action on the quotient family

An ambient automorphism preserving S and Φ(D) induces an automorphism of
the actual quotient. Its two maximum elementary subgroups lift precisely
to Q and Qˣ. Thus the original normalizer of Φ(D) preserves this pair,
and the original escaping conjugator acts as its transposition.

Source: Aschbacher–Smith C.5.6(5), printed p.157.
-/

public section
open Subgroup Stellmacher
open scoped Pointwise
namespace CFSG.Quasithin.ChapterC.Section05.ConjugateSource.RankOne
variable {G : Type*} [Group G] [Finite G] {R L : Subgroup G} {F : Type*} [Field F]

omit [Finite G] in
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

omit [Finite G] in
private theorem image_eq_of_kernel_contained {T : Type*} [Group T]
    (f : S R →* T) (hk : f.ker = (Phi R L).subgroupOf (S R))
    (B C : Subgroup G) (hB : B ≤ S R) (hC : C ≤ S R)
    (hNB : Phi R L ≤ B) (hNC : Phi R L ≤ C)
    (he : baumannImage R f B = baumannImage R f C) : B = C := by
  apply le_antisymm
  · intro b hb
    apply (baumannImage_mem_iff f hk C hNC ⟨b, hB hb⟩).mp
    rw [← he]
    exact mem_map_of_mem f hb
  · intro c hc
    apply (baumannImage_mem_iff f hk B hNB ⟨c, hC hc⟩).mp
    rw [he]
    exact mem_map_of_mem f hc

/-- Every automorphism preserving the source quotient preserves its two
literal core preimages. No quotient action or pair invariance is assumed. -/
theorem Setup.quotient_pair_preserved (h : Setup R L F) {x : G}
    (hx : x ∈ normalizer (R : Set G))
    (hnc : ¬ (U L).map (MulAut.conj x⁻¹).toMonoidHom ≤ centralizer (U L : Set G))
    (e : G ≃* G) (hS : (S R).map e.toMonoidHom = S R)
    (hN : (Phi R L).map e.toMonoidHom = Phi R L) :
    (Q R L).map e.toMonoidHom = Q R L ∨
      (Q R L).map e.toMonoidHom = (Q R L).map (MulAut.conj x⁻¹).toMonoidHom := by
  let N := (Phi R L).subgroupOf (S R)
  let : N.Normal := h.phi_normal hx hnc
  let f := QuotientGroup.mk' N
  let eS := (e.subgroupMap (S R)).trans (MulEquiv.subgroupCongr hS)
  have hNS : Phi R L ≤ S R := (map_subtype_le _).trans inf_le_left
  have hNm : N.map eS.toMonoidHom = N := by
    rw [relative_equiv_map e hS _ hNS, hN]
  let eT := QuotientGroup.congr N N eS hNm
  have hm (B : Subgroup G) (hB : B ≤ S R) :
      baumannImage R f (B.map e.toMonoidHom) = (baumannImage R f B).map eT.toMonoidHom := by
    unfold baumannImage
    rw [← relative_equiv_map e hS B hB, map_map, map_map]
    congr 1
  have hQ : Q R L ≤ S R := h.core ▸ inf_le_left
  have hQ' : (Q R L).map (MulAut.conj x⁻¹).toMonoidHom ≤ S R :=
    (h.conjugate_core hx).le.trans inf_le_left
  have hNQ := h.phi_le_core hx hnc
  have hNQ' : Phi R L ≤ (Q R L).map (MulAut.conj x⁻¹).toMonoidHom := by
    have hh := map_mono (f := (MulAut.conj x⁻¹).toMonoidHom) hNQ
    have hi : (Phi R L).map (MulAut.conj x⁻¹).toMonoidHom = Phi R L := h.frattini_invariant hx hnc
    exact hi ▸ hh
  have hNQe : Phi R L ≤ (Q R L).map e.toMonoidHom := hN ▸ map_mono hNQ
  have hQmem : baumannImage R f (Q R L) ∈ elementaryAbelianMaxSubgroups (⊤ : Subgroup ((S R) ⧸ N)) := by
    rw [h.quotient_maximum_family hx hnc f (QuotientGroup.mk'_surjective N) (QuotientGroup.ker_mk' N)]
    exact Set.mem_insert _ _
  have hmem := (maxFamily_map_injective_iff eT.toMonoidHom eT.injective ⊤ _).mpr hQmem
  have ht : (⊤ : Subgroup ((S R) ⧸ N)).map eT.toMonoidHom = ⊤ :=
    map_top_of_surjective eT.toMonoidHom eT.surjective
  rw [ht, ← hm _ hQ,
    h.quotient_maximum_family hx hnc f (QuotientGroup.mk'_surjective N) (QuotientGroup.ker_mk' N)] at hmem
  rcases Set.mem_insert_iff.mp hmem with he | he
  · exact Or.inl (image_eq_of_kernel_contained f (QuotientGroup.ker_mk' N) _ _
      ((map_mono hQ).trans_eq hS) hQ hNQe hNQ he)
  · exact Or.inr (image_eq_of_kernel_contained f (QuotientGroup.ker_mk' N) _ _
      ((map_mono hQ).trans_eq hS) hQ' hNQe hNQ' (Set.mem_singleton_iff.mp he))

/-- The genuine M₁=N_M(Φ(D)) from C.5.6 has core stabilizer of index two. -/
theorem Setup.frattini_stabilizer_index (h : Setup R L F) (M : Subgroup G)
    (hMR : M ≤ normalizer (R : Set G)) {x : G} (hx : x ∈ M)
    (hnc : ¬ (U L).map (MulAut.conj x⁻¹).toMonoidHom ≤ centralizer (U L : Set G)) :
    (normalizer (Q R L : Set G)).relIndex (M ⊓ normalizer (Phi R L : Set G)) = 2 := by
  have hxN : x⁻¹ ∈ normalizer (Phi R L : Set G) :=
    mem_normalizer_iff_map_conj_eq.mpr (h.frattini_invariant (hMR hx) hnc)
  refine normalizer_relIndex_eq_two_of_pair (M ⊓ normalizer (Phi R L : Set G)) (Q R L)
    ((Q R L).map (MulAut.conj x⁻¹).toMonoidHom) ?_ x⁻¹ ⟨M.inv_mem hx, hxN⟩ ?_
  · intro m hm
    exact h.quotient_pair_preserved (hMR hx) hnc (MulAut.conj m)
      (mem_normalizer_iff_map_conj_eq.mp (Stellmacher.normalizer_le_normalizer_baumann R (hMR hm.1)))
      (mem_normalizer_iff_map_conj_eq.mp hm.2)
  · intro he
    exact hnc (((map_mono (f := (MulAut.conj x⁻¹).toMonoidHom) h.module_le_core).trans_eq he).trans
      (h.core ▸ inf_le_right))
end CFSG.Quasithin.ChapterC.Section05.ConjugateSource.RankOne
end

public section
open Subgroup
open scoped Pointwise
namespace CFSG.Quasithin.ChapterC.Section05.ConjugateSource.RankOne
variable {G : Type*} [Group G] [Finite G] {R L : Subgroup G} {F : Type*} [Field F]

/-- Without any Frattini-zero assumption, the original x exchanges Q and Qˣ. -/
theorem Setup.conjugate_core_swap_unconditionally (h : Setup R L F) {x : G}
    (hx : x ∈ normalizer (R : Set G))
    (hnc : ¬ (U L).map (MulAut.conj x⁻¹).toMonoidHom ≤ centralizer (U L : Set G)) :
    ((Q R L).map (MulAut.conj x⁻¹).toMonoidHom).map (MulAut.conj x⁻¹).toMonoidHom = Q R L := by
  let e := MulAut.conj x⁻¹
  have hN : (Phi R L).map e.toMonoidHom = Phi R L := h.frattini_invariant hx hnc
  have hS2 : (S R).map (e * e).toMonoidHom = S R := by
    change (S R).map (e.toMonoidHom.comp e.toMonoidHom) = S R
    rw [← map_map, h.stable hx, h.stable hx]
  have hN2 : (Phi R L).map (e * e).toMonoidHom = Phi R L := by
    change (Phi R L).map (e.toMonoidHom.comp e.toMonoidHom) = Phi R L
    rw [← map_map, hN, hN]
  have he := h.quotient_pair_preserved hx hnc (e * e) hS2 hN2
  change ((Q R L).map e.toMonoidHom).map e.toMonoidHom = Q R L
  change (Q R L).map (e.toMonoidHom.comp e.toMonoidHom) = Q R L ∨
    (Q R L).map (e.toMonoidHom.comp e.toMonoidHom) = (Q R L).map e.toMonoidHom at he
  rw [← map_map] at he
  rcases he with he | he
  · exact he
  · have hQ := (map_injective e.injective) he
    exact (hnc (((map_mono (f := e.toMonoidHom) h.module_le_core).trans_eq hQ).trans
      (h.core ▸ inf_le_right))).elim

/-- C.5.6(5): the original escaping conjugator has even order. -/
theorem Setup.even_order (h : Setup R L F) {x : G}
    (hx : x ∈ normalizer (R : Set G))
    (hnc : ¬ (U L).map (MulAut.conj x⁻¹).toMonoidHom ≤ centralizer (U L : Set G)) :
    Even (orderOf x) := by
  let e := MulAut.conj x⁻¹
  have hfix : e ^ 2 • Q R L = Q R L := by
    rw [pow_two, mul_smul]
    exact h.conjugate_core_swap_unconditionally hx hnc
  have hd := MulAction.pow_smul_eq_iff_period_dvd.mp hfix
  have hn : MulAction.period e (Q R L) ≠ 1 := by
    intro he
    have hm := MulAction.period_eq_one_iff.mp he
    have hQ : (Q R L).map e.toMonoidHom = Q R L := hm
    exact hnc (((map_mono (f := e.toMonoidHom) h.module_le_core).trans_eq hQ).trans
      (h.core ▸ inf_le_right))
  have hp : MulAction.period e (Q R L) = 2 :=
    ((Nat.dvd_prime Nat.prime_two).mp hd).resolve_left hn
  apply even_iff_two_dvd.mpr
  have he := (hp ▸ MulAction.period_dvd_orderOf e (Q R L)).trans
    (orderOf_map_dvd MulAut.conj x⁻¹)
  simpa only [orderOf_inv] using he
end CFSG.Quasithin.ChapterC.Section05.ConjugateSource.RankOne
end
