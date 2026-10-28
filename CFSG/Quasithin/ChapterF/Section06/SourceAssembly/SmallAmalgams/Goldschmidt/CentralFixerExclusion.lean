module
public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.SmallAmalgams.Goldschmidt.SemilocalCentralizer
public import Theory.GroupTheory.DisjointConjugateCenter
public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.SmallAmalgams.Goldschmidt.CentralFixerTerminal

/-!
# Excluding central overlap elements from the semilocal fixer

In Goldschmidt's general residual case, a candidate normalizer whose left
quotient is not three-closed has trivial intersection with the center of the
original overlap. A hypothetical central element lies in the center of the
right two-core because that core is self-centralizing. Inside the finite
right normalizer, its nontrivial normal subgroup supplies a central subgroup
of order two. The cubic centralizer from the first half of (5.3) makes this
subgroup a new candidate.

Maximize its first local normalizer. Its edge subgroup contains the right
two-core, has index at least two in the overlap, and therefore equals that
core. The shared application of (2.15) excludes this equality. Every local
group and subgroup map is the original one; the ambient completion can be
infinite. The earlier track-quotient argument supplies only the displayed
nonnormal Sylow-three premise.

Source: Goldschmidt, *Automorphisms of trivalent graphs* (1980), (5.3),
printed p.395, the second half of the proof, specialized to the standing
residual exclusions of Section 6.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
open Subgroup.CosetGeometry
namespace CFSG.Quasithin.ChapterF.SourceAssembly.Goldschmidt
variable {G : Type*} [Group G] {F : Bool → Subgroup G}

private theorem center_overlap_le_center_right_core (h : CubicTreeAction F)
    (hC : ∀ i, ¬ Nonempty ((pResidual 2 (F i)) ≃* Multiplicative (ZMod 3)))
    (hA : ∀ i, ¬ Nonempty ((pResidual 2 (F i)) ≃* alternatingGroup (Fin 4)))
    (hCT : (pCore 2 (F true)).map (F true).subtype ≤ F false ⊓ F true) :
    centerIn (F false ⊓ F true) ≤ centerIn ((pCore 2 (F true)).map (F true).subtype) := by
  have hs : centralizer (pCore 2 (F true) : Set (F true)) ≤ pCore 2 (F true) := by
    exact (stabilizer_base F true) ▸
      h.stabilizer_centralizer_twoCore_le_of_large_residual hC hA (RankTwo.base F true)
  intro z hz
  have hzB : z ∈ F true := hz.1.2
  have hc : (⟨z, hzB⟩ : F true) ∈ centralizer (pCore 2 (F true) : Set (F true)) := by
    intro x hx
    exact Subtype.ext (hz.2 (x : G) (hCT (mem_map_of_mem (F true).subtype hx)))
  exact ⟨mem_map_of_mem (F true).subtype (hs hc), centralizer_le hCT hz.2⟩

private theorem rightNormalizer_isPGroup (h : CubicTreeAction F)
    {Q : Subgroup G} (hQ : NormalizerCandidate F Q) :
    IsPGroup 2 (localNormalizer F Q true) := by
  let L := localNormalizer F Q true
  let : Finite L := h.finite_localNormalizer Q true
  let E := (F false ⊓ F true).subgroupOf L
  have hp : IsPGroup 2 E := h.primitive.sylow.isPGroup.comap_subtype
  obtain ⟨n, hn⟩ := hp.exists_card_eq
  apply IsPGroup.of_card (n := n + 1)
  rw [← E.index_mul_card, show E.index = 2 from hQ.right_index_two h, hn]
  simp only [pow_succ, Nat.mul_comm]

private theorem left_index_of_cubic_normalizer (h : CubicTreeAction F)
    (D : Subgroup G) (X : Subgroup (F false)) (hX : Nat.card X = 3)
    (hXN : X.map (F false).subtype ≤ normalizer (D : Set G)) :
    (F false ⊓ F true).relIndex (localNormalizer F D false) = 3 := by
  let L := localNormalizer F D false
  let Y := X.map (F false).subtype
  let : Finite L := h.finite_localNormalizer D false
  have hY : Nat.card Y = 3 := by rw [card_map_of_injective (F false).subtype_injective, hX]
  have hpY : IsPGroup 3 Y := IsPGroup.of_card (n := 1) (by simpa using hY)
  have hd : Disjoint (F false ⊓ F true) Y :=
    h.primitive.sylow.isPGroup.disjoint_of_coprime hpY (by decide)
  have hi : (F false ⊓ F true).relIndex Y = 3 := by
    rw [← inf_relIndex_right, hd.eq_bot, relIndex_bot_left, hY]
  have hlo := Subgroup.relIndex_le_of_le_right
    (H := F false ⊓ F true) (show Y ≤ L from le_inf hXN (map_subtype_le X))
    (show (F false ⊓ F true).relIndex L ≠ 0 from Subgroup.index_ne_zero_of_finite)
  have hhi := Subgroup.relIndex_le_of_le_right (H := F false ⊓ F true)
    (show L ≤ F false from inf_le_right)
    (show (F false ⊓ F true).relIndex (F false) ≠ 0 by rw [h.overlap_relIndex false]; decide)
  rw [hi] at hlo
  rw [h.overlap_relIndex false] at hhi
  exact le_antisymm hhi hlo

private theorem central_line_candidate (h : CubicTreeAction F)
    {Q : Subgroup G} (hQ : NormalizerCandidate F Q)
    (P : Sylow 3 (localNormalizer F Q false ⧸ Q.subgroupOf (localNormalizer F Q false)))
    (hP : ¬ (P : Subgroup (localNormalizer F Q false ⧸
      Q.subgroupOf (localNormalizer F Q false))).Normal)
    (D : Subgroup G) (hD : Nat.card D = 2) (hDQ : D ≤ Q)
    (hDN : localNormalizer F Q true ≤ centralizer (D : Set G)) :
    NormalizerCandidate F D := by
  let : Finite (F false) := h.finite false
  let C := (centralizer (Q : Set G)).subgroupOf (F false)
  have hd : 3 ∣ Nat.card C := hQ.three_dvd_card_centralizer h P hP
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := C) 3 hd
  let X : Subgroup (F false) := (zpowers x).map C.subtype
  have hX : Nat.card X = 3 := by
    rw [card_map_of_injective C.subtype_injective, Nat.card_zpowers, hx]
  have hXQ : X.map (F false).subtype ≤ centralizer (Q : Set G) := by
    rintro _ ⟨_, ⟨y, hy, rfl⟩, rfl⟩
    exact y.property
  have hXN : X.map (F false).subtype ≤ normalizer (D : Set G) :=
    (hXQ.trans (centralizer_le hDQ)).trans (Subgroup.centralizer_le_normalizer _)
  refine ⟨?_, hDQ.trans hQ.le_overlap, left_index_of_cubic_normalizer h D X hX hXN, ?_⟩
  · intro hb
    rw [hb, card_bot] at hD
    omega
  · intro hle
    apply hQ.right_mover
    exact (le_inf (hDN.trans (Subgroup.centralizer_le_normalizer _)) inf_le_right).trans hle

private theorem exists_central_line_candidate (h : CubicTreeAction F)
    (hC : ∀ i, ¬ Nonempty ((pResidual 2 (F i)) ≃* Multiplicative (ZMod 3)))
    (hA : ∀ i, ¬ Nonempty ((pResidual 2 (F i)) ≃* alternatingGroup (Fin 4)))
    (hCT : (pCore 2 (F true)).map (F true).subtype ≤ F false ⊓ F true)
    {Q : Subgroup G} (hQ : NormalizerCandidate F Q)
    (P : Sylow 3 (localNormalizer F Q false ⧸ Q.subgroupOf (localNormalizer F Q false)))
    (hP : ¬ (P : Subgroup (localNormalizer F Q false ⧸
      Q.subgroupOf (localNormalizer F Q false))).Normal)
    (hZ : Q ⊓ centerIn (F false ⊓ F true) ≠ ⊥) :
    ∃ D : Subgroup G, NormalizerCandidate F D ∧
      (pCore 2 (F true)).map (F true).subtype ≤ localNormalizer F D false := by
  let C := (pCore 2 (F true)).map (F true).subtype
  let Z := Q ⊓ centerIn C
  let L := localNormalizer F Q true
  let : Finite L := h.finite_localNormalizer Q true
  have hL2 : IsPGroup 2 L := rightNormalizer_isPGroup h hQ
  let : Fact (IsPGroup 2 L) := ⟨hL2⟩
  have hZn : Z ≠ ⊥ := by
    intro hb
    apply hZ
    exact bot_unique ((inf_le_inf le_rfl
      (center_overlap_le_center_right_core h hC hA hCT)).trans hb.le)
  have hZL : Z ≤ L := inf_le_left.trans (hQ.le_edge.trans (edgeNormalizer_le_local Q true))
  have hBN : F true ≤ normalizer (C : Set G) :=
    (F true).le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image (F true) (pCore 2 (F true)))
  have hLN : L ≤ normalizer (Z : Set G) :=
    (le_inf inf_le_left (inf_le_right.trans (normalizes_centerIn hBN))).trans
      inf_normalizer_le_normalizer_inf
  let N := Z.subgroupOf L
  let : N.Normal := normal_subgroupOf_of_le_normalizer hLN
  have hN : N ≠ ⊥ := by
    intro hn
    apply hZn
    rw [← map_subgroupOf_eq_of_le hZL]
    change N.map L.subtype = ⊥
    rw [hn, Subgroup.map_bot]
  obtain ⟨D, _, hDN, hDcard, hDZ⟩ :=
    exists_central_subgroup_card_eq_prime_in_normal (p := 2) N
      ((nontrivial_iff_ne_bot N).mpr hN)
  let J := D.map L.subtype
  have hJcard : Nat.card J = 2 := by rw [card_map_of_injective L.subtype_injective, hDcard]
  have hJQ : J ≤ Q := by
    rintro _ ⟨d, hd, rfl⟩
    exact (hDN hd).1
  have hJC : J ≤ centerIn C := by
    rintro _ ⟨d, hd, rfl⟩
    exact (hDN hd).2
  have hJZL : J ≤ centerIn L := by
    rw [centerIn_eq_map_center]
    exact map_mono hDZ
  have hLJ : L ≤ centralizer (J : Set G) :=
    le_centralizer_iff.mp (hJZL.trans inf_le_right)
  refine ⟨J, central_line_candidate h hQ P hP J hJcard hJQ hLJ, ?_⟩
  exact le_inf ((le_centralizer_iff.mp (hJC.trans inf_le_right)).trans
    (Subgroup.centralizer_le_normalizer _)) (hCT.trans inf_le_left)

private theorem exists_maximal_candidate_right_core (h : CubicTreeAction F)
    (hC : ∀ i, ¬ Nonempty ((pResidual 2 (F i)) ≃* Multiplicative (ZMod 3)))
    (hA : ∀ i, ¬ Nonempty ((pResidual 2 (F i)) ≃* alternatingGroup (Fin 4)))
    (hcore : (pCore 2 (F true)).map (F true).subtype ≤ F false ⊓ F true ∧
      ((pCore 2 (F true)).map (F true).subtype).relIndex (F false ⊓ F true) = 2)
    {Q : Subgroup G} (hQ : NormalizerCandidate F Q)
    (P : Sylow 3 (localNormalizer F Q false ⧸ Q.subgroupOf (localNormalizer F Q false)))
    (hP : ¬ (P : Subgroup (localNormalizer F Q false ⧸
      Q.subgroupOf (localNormalizer F Q false))).Normal)
    (hZ : Q ⊓ centerIn (F false ⊓ F true) ≠ ⊥) :
    ∃ R : Subgroup G, MaximalNormalizerCandidate F R ∧
      edgeNormalizer F R = (pCore 2 (F true)).map (F true).subtype := by
  obtain ⟨D, hD, hCD⟩ := exists_central_line_candidate h hC hA hcore.1 hQ P hP hZ
  obtain ⟨R, hR, hDR⟩ := h.exists_maximalNormalizerCandidate hD
  refine ⟨R, hR, ?_⟩
  let T := F false ⊓ F true
  let C := (pCore 2 (F true)).map (F true).subtype
  let E := edgeNormalizer F R
  let : Finite (F false) := h.finite false
  let : Finite T := Finite.of_injective (inclusion inf_le_left) (inclusion_injective _)
  have hET : E < T := hR.toNormalizerCandidate.edge_lt_overlap h
  let : Finite E := Finite.of_injective (inclusion hET.le) (inclusion_injective _)
  have hCE : C ≤ E := le_inf ((hCD.trans hDR).trans inf_le_left) hcore.1
  have hm := relIndex_mul_relIndex C E T hCE hET.le
  rw [hcore.2] at hm
  have hEn : E.relIndex T ≠ 0 := Subgroup.index_ne_zero_of_finite
  have hEn1 : E.relIndex T ≠ 1 := by
    intro hi
    exact hET.not_ge (relIndex_eq_one.mp hi)
  have hCn : C.relIndex E ≠ 0 := Subgroup.index_ne_zero_of_finite
  have hC1 : C.relIndex E = 1 := by
    have hE2 : 2 ≤ E.relIndex T := by omega
    have hCp : 1 ≤ C.relIndex E := by omega
    nlinarith
  exact le_antisymm (relIndex_eq_one.mp hC1) hCE

/-- The central-fixer exclusion of (5.3) in the general residual case.
The earlier quotient regularity argument supplies the nonnormal Sylow-three
subgroup; all local classification and maximal-normalizer inputs are discharged. -/
theorem NormalizerCandidate.disjoint_center_overlap_of_large_residual
    (h : CubicTreeAction F)
    (hC : ∀ i, ¬ Nonempty ((pResidual 2 (F i)) ≃* Multiplicative (ZMod 3)))
    (hA : ∀ i, ¬ Nonempty ((pResidual 2 (F i)) ≃* alternatingGroup (Fin 4)))
    {Q : Subgroup G} (hQ : NormalizerCandidate F Q)
    (P : Sylow 3 (localNormalizer F Q false ⧸ Q.subgroupOf (localNormalizer F Q false)))
    (hP : ¬ (P : Subgroup (localNormalizer F Q false ⧸
      Q.subgroupOf (localNormalizer F Q false))).Normal) :
    Disjoint Q (centerIn (F false ⊓ F true)) := by
  apply disjoint_iff.mpr
  by_contra hn
  obtain ⟨R, hR, he⟩ := exists_maximal_candidate_right_core h hC hA
    (h.right_twoCore_overlap_of_large_residual hC hA) hQ P hP hn
  exact hR.edge_ne_right_twoCore_of_large_residual h hC hA he

end CFSG.Quasithin.ChapterF.SourceAssembly.Goldschmidt
