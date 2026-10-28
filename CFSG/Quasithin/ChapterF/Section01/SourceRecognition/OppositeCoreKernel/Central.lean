module

public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.OppositeCoreKernel
public import Theory.GroupTheory.NormalizedSupCard

/-!
# The central opposite-core kernel satisfies the source order bound

Let K be the normal core in A of the embedded O₂(B), in the original
core-free Goldschmidt pair. If K is central in A, its embedded image U
has a disjoint conjugate under B, with both subgroups inside O₂(B).
Indeed two conjugates of the common Sylow generate B. An element in the
intersection of U and the corresponding conjugate centralizes both
Sylows, hence B, and centralizes A. The common normal core kills it.
Counting the product gives |K|²≤|O₂(B)|. Since |A|=6|O₂(B)| and
|A|=[A:K]|K|, this gives 6|K|≤[A:K]≤48. Thus |K|≤8 and |A|≤384.

This is a proved size branch, rather than an assumed kernel-size clause.
The final reductions show that every larger source pair must have two
noncentral opposite-core kernels, and preserve the literal quotient map
when applied in G/O₂(G). The noncentral branches remain separate.

Source: the faithful degree-three amalgam in Aschbacher–Smith F.1.12 and
F.6.5, printed pp.262–264 and305; the source cites Goldschmidt,
Automorphisms of trivalent graphs, Annals111(1980),377–406.
-/

public section

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterF
variable {G : Type*} [Group G] [Finite G] {A B : Subgroup G}

private theorem exists_conjugate_sup_of_index_three
    {H : Type*} [Group H] [Finite H] (S : Subgroup H)
    (hi : S.index = 3) (hn : ¬ S.Normal) :
    ∃ b : H, S ⊔ S.map (MulAut.conj b).toMonoidHom = ⊤ := by
  classical
  have hex : ∃ b : H, S.map (MulAut.conj b).toMonoidHom ≠ S := by
    by_contra! hh
    exact hn (normal_iff_map_conj_eq.mpr hh)
  obtain ⟨b,hb⟩ := hex
  refine ⟨b,?_⟩
  let M := S ⊔ S.map (MulAut.conj b).toMonoidHom
  have hlt : S < M := by
    refine lt_of_le_of_ne le_sup_left ?_
    intro he
    have hle : S.map (MulAut.conj b).toMonoidHom ≤ S :=
      (show S.map (MulAut.conj b).toMonoidHom ≤ M from le_sup_right).trans he.ge
    exact hb (eq_of_le_of_card_ge hle (by rw [card_map_of_injective (MulAut.conj b).injective]))
  have hd : M.index ∣ 3 := hi ▸ index_dvd_of_le hlt.le
  rcases (Nat.dvd_prime Nat.prime_three).mp hd with h1 | h3
  · exact index_eq_one.mp h1
  · have hh := index_strictAnti hlt
    omega

/-- Two actual conjugates of the original common Sylow generate the opposite vertex. -/
theorem IsGoldschmidtTriple.exists_right_generating_sylow_conjugate
    (h : IsGoldschmidtTriple A B) :
    ∃ b : B, (A ⊓ B) ⊔ (A ⊓ B).map (MulAut.conj (b : G)).toMonoidHom = B := by
  let T := A ⊓ B
  let S := T.subgroupOf B
  have hi : S.index = 3 := by
    have hh := S.index_mul_card
    rw [Nat.card_congr (subgroupOfEquivOfLe (show T ≤ B from inf_le_right)).toEquiv,
      h.symm.local_card_eq_three_mul_intersection,inf_comm B A] at hh
    have hp := Nat.card_pos (α := T)
    change S.index = 3
    nlinarith
  have hS : IsPGroup 2 S := by
    obtain ⟨P,hP⟩ := h.intersection_sylow
    change IsPGroup 2 ((A ⊓ B).subgroupOf B)
    rw [hP]
    exact P.isPGroup'.comap_subtype
  have hn : ¬ S.Normal := by
    intro hnormal
    let _ := hnormal
    have hSQ : S ≤ pCore 2 B := le_sSup ⟨hnormal,hS⟩
    have hd := index_dvd_of_le hSQ
    have hiQ : (pCore 2 B).index = 6 := by
      change Nat.card (B ⧸ pCore 2 B) = 6
      rw [Nat.card_congr h.quotient_right.some.toEquiv]
      norm_num [Nat.card_eq_fintype_card,Fintype.card_perm]
    rw [hiQ,hi] at hd
    norm_num at hd
  obtain ⟨b,hb⟩ := exists_conjugate_sup_of_index_three S hi hn
  have hh := congrArg (map B.subtype) hb
  rw [Subgroup.map_sup,← MonoidHom.range_eq_map,range_subtype,map_subgroupOf_eq_of_le
    (show T ≤ B from inf_le_right)] at hh
  have hm : (S.map (MulAut.conj b).toMonoidHom).map B.subtype =
      T.map (MulAut.conj (b : G)).toMonoidHom := by
    rw [map_map]
    have he : B.subtype.comp (MulAut.conj b).toMonoidHom =
        (MulAut.conj (b : G)).toMonoidHom.comp B.subtype := by ext x; rfl
    rw [he,← map_map,map_subgroupOf_eq_of_le (show T ≤ B from inf_le_right)]
  rw [hm] at hh
  exact ⟨b,hh⟩

omit [Finite G] in
private theorem centralizes_map {U V : Subgroup G}
    (hc : U ≤ centralizer (V : Set G)) (b : G) :
    U.map (MulAut.conj b).toMonoidHom ≤
      centralizer (V.map (MulAut.conj b).toMonoidHom : Set G) := by
  have hh := (map_mono (f := (MulAut.conj b).toMonoidHom) hc).trans
    (map_centralizer_le_centralizer_image (V : Set G) (MulAut.conj b).toMonoidHom)
  exact hh

/-- A subgroup central in the original left vertex and contained in the
opposite core has a disjoint opposite-vertex conjugate, inside the same core. -/
theorem IsGoldschmidtTriple.central_subgroup_disjoint_opposite_conjugate
    (h : IsGoldschmidtTriple A B) (hcore : pCore 2 G = ⊥)
    (U : Subgroup G) (hu : U ≤ (pCore 2 B).map B.subtype)
    (hc : U ≤ centralizer (A : Set G)) :
    ∃ b : B, Disjoint U (U.map (MulAut.conj (b : G)).toMonoidHom) ∧
      U.map (MulAut.conj (b : G)).toMonoidHom ≤ (pCore 2 B).map B.subtype := by
  obtain ⟨b,hb⟩ := h.exists_right_generating_sylow_conjugate
  let f := (MulAut.conj (b : G)).toMonoidHom
  let U' := U.map f
  let D := U ⊓ U'
  have huT : U ≤ A ⊓ B := hu.trans
    (by simpa only [inf_comm B A] using h.symm.local_twoCore_le_intersection)
  have hT : U ≤ centralizer (A ⊓ B : Subgroup G) := hc.trans (centralizer_le inf_le_left)
  have hDcentralB : D ≤ centralizer (B : Set G) := by
    apply le_centralizer_iff.mpr
    rw [← hb]
    exact sup_le
      (le_centralizer_iff.mp (inf_le_left.trans hT))
      (le_centralizer_iff.mp (inf_le_right.trans (centralizes_map hT b)))
  have hDcentralA : D ≤ centralizer (A : Set G) := inf_le_left.trans hc
  have hbot : D = ⊥ := h.common_normal_eq_bot hcore D (inf_le_left.trans huT)
    (normal_subgroupOf_of_le_normalizer
      ((le_centralizer_iff.mp hDcentralA).trans (centralizer_le_normalizer _)))
    (normal_subgroupOf_of_le_normalizer
      ((le_centralizer_iff.mp hDcentralB).trans (centralizer_le_normalizer _)))
  refine ⟨b,disjoint_iff.mpr hbot,?_⟩
  have hn := h.symm.left_core_normalized b.property
  have he := mem_normalizer_iff_map_conj_eq.mp hn
  exact (map_mono (f := f) hu).trans he.le

/-- The central-kernel branch has a genuine quadratic order bound, before
any kernel-cardinality assumption. -/
theorem IsGoldschmidtTriple.central_subgroup_card_sq_le_opposite_core
    (h : IsGoldschmidtTriple A B) (hcore : pCore 2 G = ⊥)
    (U : Subgroup G) (hu : U ≤ (pCore 2 B).map B.subtype)
    (hc : U ≤ centralizer (A : Set G)) :
    Nat.card U ^ 2 ≤ Nat.card (pCore 2 B) := by
  obtain ⟨b,hd,hb⟩ := h.central_subgroup_disjoint_opposite_conjugate hcore U hu hc
  let U' := U.map (MulAut.conj (b : G)).toMonoidHom
  have hUA : U' ≤ A := hb.trans (h.symm.local_twoCore_le_intersection.trans inf_le_right)
  have hn : U' ≤ normalizer (U : Set G) :=
    (le_centralizer_iff.mp (hc.trans (centralizer_le hUA))).trans (centralizer_le_normalizer _)
  have he : Nat.card U' = Nat.card U := card_map_of_injective (MulAut.conj (b : G)).injective
  have hp := card_sup_eq_mul_of_normalizes_of_disjoint U U' hn hd
  have hle := card_le_of_le (sup_le hu hb)
  rw [hp,he,card_map_of_injective B.subtype_injective] at hle
  simpa only [pow_two] using hle

/-- A central kernel has order at most its index in the opposite core. -/
theorem IsGoldschmidtTriple.central_opposite_kernel_weighted_bound
    (h : IsGoldschmidtTriple A B) (hcore : pCore 2 G = ⊥)
    (hc : (((pCore 2 B).map B.subtype).subgroupOf A).normalCore ≤ center A) :
    6 * Nat.card (((pCore 2 B).map B.subtype).subgroupOf A).normalCore ≤
      (((pCore 2 B).map B.subtype).subgroupOf A).normalCore.index := by
  let R := ((pCore 2 B).map B.subtype).subgroupOf A
  let K := R.normalCore
  let U := K.map A.subtype
  have hu : U ≤ (pCore 2 B).map B.subtype := by
    rintro x ⟨y,hy,rfl⟩
    exact R.normalCore_le hy
  have huC : U ≤ centralizer (A : Set G) := by
    rintro x ⟨y,hy,rfl⟩ z hz
    exact congrArg Subtype.val (mem_center_iff.mp (hc hy) ⟨z,hz⟩)
  have hsq := h.central_subgroup_card_sq_le_opposite_core hcore U hu huC
  rw [card_map_of_injective A.subtype_injective] at hsq
  have hcard := K.index_mul_card
  rw [show Nat.card A = Nat.card B by
    rw [h.local_card_eq_three_mul_intersection,h.symm.local_card_eq_three_mul_intersection,
      inf_comm B A],SymmetricThreeTwoCore.card_eq h.quotient_right.some] at hcard
  have hp := Nat.card_pos (α := K)
  change 6 * Nat.card K ≤ K.index
  nlinarith

/-- A central literal degree-six kernel has order at most eight. -/
theorem IsGoldschmidtTriple.opposite_kernel_card_le_eight_of_central
    (h : IsGoldschmidtTriple A B) (hcore : pCore 2 G = ⊥)
    (hc : (((pCore 2 B).map B.subtype).subgroupOf A).normalCore ≤ center A) :
    Nat.card (((pCore 2 B).map B.subtype).subgroupOf A).normalCore ≤ 8 := by
  have hw := h.central_opposite_kernel_weighted_bound hcore hc
  have hi := Nat.le_of_dvd (by decide : 0 < 48)
    h.opposite_core_normalCore_index_dvd_forty_eight
  omega

/-- The original vertex and overlap bounds in the central-kernel branch. -/
theorem IsGoldschmidtTriple.local_cards_le_384_of_central_opposite_kernel
    (h : IsGoldschmidtTriple A B) (hcore : pCore 2 G = ⊥)
    (hc : (((pCore 2 B).map B.subtype).subgroupOf A).normalCore ≤ center A) :
    Nat.card A ≤ 384 ∧ Nat.card B ≤ 384 ∧ Nat.card (A ⊓ B : Subgroup G) ≤ 128 := by
  exact h.local_cards_le_384_of_oriented_kernel_bounds
    (Or.inl (Or.inr (Or.inr (h.opposite_kernel_card_le_eight_of_central hcore hc))))


/-- A counterexample to the original 384 bound has noncentral literal
kernels on both sides; centrality of either one already closes the bound. -/
theorem IsGoldschmidtTriple.both_opposite_kernels_noncentral_of_large_vertex
    (h : IsGoldschmidtTriple A B) (hcore : pCore 2 G = ⊥)
    (hlarge : 384 < Nat.card A) :
    ¬ (((pCore 2 B).map B.subtype).subgroupOf A).normalCore ≤ center A ∧
    ¬ (((pCore 2 A).map A.subtype).subgroupOf B).normalCore ≤ center B := by
  constructor
  · intro hc
    exact (not_lt_of_ge (h.local_cards_le_384_of_central_opposite_kernel hcore hc).1) hlarge
  · intro hc
    exact (not_lt_of_ge (h.symm.local_cards_le_384_of_central_opposite_kernel hcore hc).2.1) hlarge

/-- The same source size branch on the literal original quotient images. -/
theorem IsGoldschmidtTriple.quotient_local_cards_le_384_of_central_opposite_kernel
    (h : IsGoldschmidtTriple A B)
    (hc :
      let q := QuotientGroup.mk' (pCore 2 G)
      let A' := A.map q
      let B' := B.map q
      (((pCore 2 B').map B'.subtype).subgroupOf A').normalCore ≤ center A') :
    let q := QuotientGroup.mk' (pCore 2 G)
    Nat.card (A.map q) ≤ 384 ∧ Nat.card (B.map q) ≤ 384 ∧
      Nat.card ((A ⊓ B).map q) ≤ 128 := by
  have hh := h.quotient_twoCore.local_cards_le_384_of_central_opposite_kernel
    h.quotient_twoCore_eq_bot hc
  rw [← h.quotient_twoCore_intersection] at hh
  exact hh

end CFSG.Quasithin.ChapterF
