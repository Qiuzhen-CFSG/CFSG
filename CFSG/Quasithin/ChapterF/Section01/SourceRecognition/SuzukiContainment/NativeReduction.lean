module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.SuzukiContainment.OddBorel
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.A5PairReduced
public import Theory.SpecificGroups.SL2.FieldCardinality

/-!
# DGS local reduction and restoration for a linear–Suzuki pair

Let S₀ = O₂(B), retaining the full original Borel and factors. On the
reduced pair the Suzuki outer group has odd order, and Borel normality
makes the linear action inner. Their Sylow factorizations identify the
DGS groups LᵢS₀ with the original starred parabolics O₂(Pᵢ)Lᵢ. Both
cores and the quotient maps induced by the original inclusions are retained.
The enlarged local factors satisfy all the genuine F.1.1 clauses.

An isomorphism of finite binary PSL₂ groups determines its field degree.
Consequently the binary linear quotient in the small Ree type rows and
DGS Chapter 13 is incompatible with the original exponent n > 1. The
matching field in DGS (12.9)(c1) forces n odd, so S₀ equals the original
ambient Sylow T. Native reduced core placement, or an actual isomorphism
of the reduced Suzuki-side parabolic with a Ree parabolic, then puts T
in the ORIGINAL factor R. These last two inputs remain explicit; this
module does not prove the critical-pair classification or arbitrary-pair
recognition. The final containment owner must discharge them.

Source: DGS85, Part II, (6.0)–(6.1), pp.118–119, (12.9), pp.186–190,
(13.1), p.191, and the reduction preceding (15.1), pp.225–226;
Aschbacher–Smith F.1.9–F.1.12, pp.261–264.
-/

public noncomputable section
open Subgroup
namespace CFSG.Quasithin.ChapterF.Source.SuzukiContainment
variable {G : Type*} [Group G] [Finite G]
  {L : Fin 2 → Subgroup G} {S : Subgroup G}

/-- Suzuki Sylow factorization for a source two-subgroup, without requiring it
to be Sylow in the ambient group. This applies to the actual reduced S₀. -/
theorem suzuki_local_sylow_factorization
    (h : HypothesisF11 L S) (i : Fin 2) {m : ℕ} (hm : 1 ≤ m)
    (e : (L i ⧸ pCore 2 (L i)) ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m) :
    S = twoCore (L i ⊔ S) ⊔ (S ⊓ L i) := by
  have hz : center (L i ⧸ pCore 2 (L i)) = ⊥ := by
    let := (BenderSuzuki.External.huppert_blackburn_XI_3_6 m (by omega)).1
    have hc : center (BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m) = ⊥ := by
      rcases (inferInstance : (center (BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m)).Normal).eq_bot_or_eq_top with hc | hc
      · exact hc
      · exact (BenderSuzuki.External.suzukiMatrixGroup_not_isSolvable m (by omega)
          (Group.isSolvable_of_comm (fun x y => by
            have hx : x ∈ center (BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m) := hc ▸ mem_top x
            exact (mem_center_iff.mp hx y).symm))).elim
    apply bot_unique
    intro x hx
    have he : e x ∈ center (BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m) :=
      (centerCongr e ⟨x,hx⟩).property
    rw [hc, mem_bot] at he
    exact mem_bot.mpr (e.injective (he.trans (map_one e).symm))
  have ho : Nat.Coprime 2 (Nat.card (MulAut.Outer (L i ⧸ pCore 2 (L i)))) := by
    rw [Nat.card_congr (MulAut.outerCongr e).toEquiv]
    exact (BenderSuzuki.MatrixGroups.suzuki_odd_outer_index m hm).coprime_two_left
  let a := (pCoreJoinAction 2 (h.S_normalizes i)).comp
    (inclusion (show S ≤ L i ⊔ S from le_sup_right))
  let f := (QuotientGroup.mk' (MulAut.innerSubgroup (L i ⧸ pCore 2 (L i)))).comp a
  have hi (s : S) : a s ∈ MulAut.innerSubgroup (L i ⧸ pCore 2 (L i)) := by
    apply (QuotientGroup.eq_one_iff _).mp
    change f s = 1
    obtain ⟨r, hr⟩ := h.S_isP s
    apply orderOf_eq_one_iff.mp
    apply Nat.eq_one_of_dvd_coprimes (ho.pow_left r)
    · apply orderOf_dvd_of_pow_eq_one
      rw [← map_pow, hr, map_one]
    · exact _root_.orderOf_dvd_natCard (f s)
  obtain ⟨P, hP⟩ := h.sylow i
  have hf := sup_core_factor_of_inner_action (L i) S (h.S_normalizes i) h.S_isP hz P
    (hP ▸ inf_le_left) hi
  simpa only [hP, sup_comm, twoCore, pCoreIn] using hf

omit [Finite G] in
private theorem reduced_borels_normalize (h : HypothesisF11 L S) (i : Fin 2) :
    borel (L i) (reducedSylow L S) ≤ normalizer (reducedSylow L S : Set G) :=
  (borel_le_commonBorel i).trans
    ((normal_subgroupOf_iff_le_normalizer le_sup_right).mp (reduced_sylow_normal h))

/-- The two DGS local groups are exactly the original starred parabolics. -/
theorem reduced_localJoin_eq_starred
    {A R : Subgroup G} (h : HypothesisF11 ![A,R] S) {n m : ℕ}
    (he : ClassicalGroup.IsPSL (A ⧸ pCore 2 A) 2 (2 ^ n)) (hm : 1 ≤ m)
    (e : (R ⧸ pCore 2 R) ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m)
    (i : Fin 2) :
    ![A,R] i ⊔ reducedSylow ![A,R] S = starredParabolic ![A,R] S i := by
  have hh := reduced_hypothesis h
  have hn := reduced_borels_normalize h
  have hs : reducedSylow ![A,R] S =
      twoCore (![A,R] i ⊔ reducedSylow ![A,R] S) ⊔
        (reducedSylow ![A,R] S ⊓ ![A,R] i) := by
    fin_cases i
    · obtain ⟨F, hF, hfin, hcard, ⟨f⟩⟩ := he
      let := Fintype.ofFinite F
      let : CharP F 2 := charP_of_card_eq_prime_pow
        (by simpa only [Nat.card_eq_fintype_card] using hcard)
      exact hh.linear_local_sylow_factorization 0 F f (hn 0)
    · exact suzuki_local_sylow_factorization hh 1 hm e
  rw [hh.localJoin_twoCore_eq_parabolic hn i, reduced_parabolic_core h i] at hs
  change _ = twoCore (parabolic ![A,R] S i) ⊔ ![A,R] i
  apply le_antisymm
  · exact sup_le le_sup_right (hs.le.trans
      (sup_le le_sup_left (inf_le_right.trans le_sup_right)))
  · exact sup_le ((parabolic_core_le_reducedSylow h i).trans le_sup_right) le_sup_left

/-- The original local quotient maps to the literal DGS local quotient by inclusion. -/
@[expose] def reduced_localJoinQuotientEquiv
    {A R : Subgroup G} (h : HypothesisF11 ![A,R] S) {n m : ℕ}
    (he : ClassicalGroup.IsPSL (A ⧸ pCore 2 A) 2 (2 ^ n)) (hm : 1 ≤ m)
    (e : (R ⧸ pCore 2 R) ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m)
    (i : Fin 2) :
    (![A,R] i ⧸ pCore 2 (![A,R] i)) ≃*
      ((![A,R] i ⊔ reducedSylow ![A,R] S : Subgroup G) ⧸
        pCore 2 (![A,R] i ⊔ reducedSylow ![A,R] S : Subgroup G)) :=
  (h.starredQuotientEquiv i).trans
    (QuotientGroup.congr _ _
      (MulEquiv.subgroupCongr (reduced_localJoin_eq_starred h he hm e i).symm)
      (pCore_map_iso 2 _))

@[simp] theorem reduced_localJoinQuotientEquiv_mk
    {A R : Subgroup G} (h : HypothesisF11 ![A,R] S) {n m : ℕ}
    (he : ClassicalGroup.IsPSL (A ⧸ pCore 2 A) 2 (2 ^ n)) (hm : 1 ≤ m)
    (e : (R ⧸ pCore 2 R) ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m)
    (i : Fin 2) (x : ![A,R] i) :
    reduced_localJoinQuotientEquiv h he hm e i (QuotientGroup.mk x) =
      QuotientGroup.mk (inclusion (show ![A,R] i ≤ ![A,R] i ⊔ reducedSylow ![A,R] S
        from le_sup_left) x) := rfl

/-- The binary PSL₂ quotient determines its field degree, including degree one. -/
theorem binary_linear_degree_eq {H : Type*} [Group H] {n k : ℕ}
    (hn : ClassicalGroup.IsPSL H 2 (2 ^ n))
    (hk : ClassicalGroup.IsPSL H 2 (2 ^ k)) : n = k := by
  obtain ⟨F, hF, hfinF, hcardF, ⟨eF⟩⟩ := hn
  obtain ⟨E, hE, hfinE, hcardE, ⟨eE⟩⟩ := hk
  let := Fintype.ofFinite F
  let := Fintype.ofFinite E
  let : CharP F 2 := charP_of_card_eq_prime_pow
    (by simpa only [Nat.card_eq_fintype_card] using hcardF)
  let : CharP E 2 := charP_of_card_eq_prime_pow
    (by simpa only [Nat.card_eq_fintype_card] using hcardE)
  exact Matrix.SL2.field_degree_eq_of_equiv
    (((Theory.PSL2.sl2QuotientEquiv F).trans (eF.symm.trans eE)).trans
      (Theory.PSL2.sl2QuotientEquiv E).symm) (by decide) hcardF hcardE

/-- DGS 6.1 on the reduced linear--Suzuki pair, retaining every F.1.1 clause. -/
theorem reduced_localJoin_hypothesis
    {A R : Subgroup G} (h : HypothesisF11 ![A,R] S) {n m : ℕ}
    (he : ClassicalGroup.IsPSL (A ⧸ pCore 2 A) 2 (2 ^ n)) (hm : 1 ≤ m)
    (e : (R ⧸ pCore 2 R) ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m) :
    HypothesisF11 (fun i => ![A,R] i ⊔ reducedSylow ![A,R] S)
      (reducedSylow ![A,R] S) := by
  have hh := reduced_hypothesis h
  have hn := reduced_borels_normalize h
  refine ⟨hh.finite_S, hh.S_isP, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    exact le_sup_right.trans _root_.Subgroup.le_normalizer
  · intro i
    have hi : ¬ 2 ∣ (reducedSylow ![A,R] S).relIndex
        (![A,R] i ⊔ reducedSylow ![A,R] S) := by
      intro hd
      apply hh.parabolic_odd_index i
      rw [← relIndex_mul_relIndex (reducedSylow ![A,R] S)
        (![A,R] i ⊔ reducedSylow ![A,R] S)
        (parabolic ![A,R] (reducedSylow ![A,R] S) i) le_sup_right le_sup_left]
      exact dvd_mul_of_dvd_left hd _
    have hp : IsPGroup 2 ((reducedSylow ![A,R] S).subgroupOf
        (![A,R] i ⊔ reducedSylow ![A,R] S)) := hh.S_isP.comap_subtype
    refine ⟨hp.toSylow hi, ?_⟩
    change ((reducedSylow ![A,R] S).subgroupOf
      (![A,R] i ⊔ reducedSylow ![A,R] S)).map _ = _
    rw [map_subgroupOf_eq_of_le (show reducedSylow ![A,R] S ≤
      ![A,R] i ⊔ reducedSylow ![A,R] S from le_sup_right),
      inf_eq_left.mpr le_sup_right]
  · intro i
    exact (h.quotient i).of_equiv (reduced_localJoinQuotientEquiv h he hm e i).symm
  · intro i
    rw [hh.localJoin_borel_eq hn (other i)]
    exact sup_le (le_sup_right.trans (hh.localJoin_normalizes hn i))
      (le_sup_right.trans _root_.Subgroup.le_normalizer)
  · rw [HypothesisF11.localJoin_generated_eq]
    exact hh.twoCore_free
  · intro i
    rw [hh.localJoin_parabolic_eq hn i]
    exact hh.characteristic_two i

omit [Finite G] in
/-- The cores in the literal DGS local groups are the original parabolic cores. -/
theorem reduced_localJoin_core
    {A R : Subgroup G} (h : HypothesisF11 ![A,R] S) (i : Fin 2) :
    twoCore (![A,R] i ⊔ reducedSylow ![A,R] S) = twoCore (parabolic ![A,R] S i) :=
  ((reduced_hypothesis h).localJoin_twoCore_eq_parabolic
    (reduced_borels_normalize h) i).trans (reduced_parabolic_core h i)

/-- Matching fields in DGS 12.9(c1) forces the ORIGINAL linear exponent odd.
The premise concerns the quotient of the actual DGS local group, not a family tag. -/
theorem original_degree_of_reduced_linear_quotient
    {A R : Subgroup G} (h : HypothesisF11 ![A,R] S) {n m k : ℕ}
    (he : ClassicalGroup.IsPSL (A ⧸ pCore 2 A) 2 (2 ^ n)) (hm : 1 ≤ m)
    (e : (R ⧸ pCore 2 R) ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m)
    (hfield : ClassicalGroup.IsPSL
      ((A ⊔ reducedSylow ![A,R] S : Subgroup G) ⧸
        pCore 2 (A ⊔ reducedSylow ![A,R] S : Subgroup G)) 2 (2 ^ k)) : n = k :=
  binary_linear_degree_eq he
    (hfield.of_mulEquiv (reduced_localJoinQuotientEquiv h he hm e 0))

/-- Both small Ree type rows and the prime-two Chapter 13 row have a binary
linear quotient. The nonbinary original factor excludes this, without recognizing
any type-only row as a marked amalgam. -/
theorem reduced_linear_not_binary
    {A R : Subgroup G} (h : HypothesisF11 ![A,R] S) {n m : ℕ} (hn : 1 < n)
    (he : ClassicalGroup.IsPSL (A ⧸ pCore 2 A) 2 (2 ^ n)) (hm : 1 ≤ m)
    (e : (R ⧸ pCore 2 R) ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m) :
    ¬ ClassicalGroup.IsPSL
      ((A ⊔ reducedSylow ![A,R] S : Subgroup G) ⧸
        pCore 2 (A ⊔ reducedSylow ![A,R] S : Subgroup G)) 2 2 := by
  intro htwo
  have hh := original_degree_of_reduced_linear_quotient h he hm e (k := 1)
    (by simpa only [pow_one] using htwo)
  omega

/-- The odd Suzuki-field degree removes the original-to-reduced Sylow gap.
This restores the full original Borel and parabolics before the core argument. -/
theorem original_sylow_eq_reduced_of_matching_field
    {T : Sylow 2 G} {A R : Subgroup G}
    (h : HypothesisF11 ![A,R] (T : Subgroup G)) {n m k : ℕ}
    (he : ClassicalGroup.IsPSL (A ⧸ pCore 2 A) 2 (2 ^ n)) (hm : 1 ≤ m)
    (e : (R ⧸ pCore 2 R) ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m)
    (hfield : ClassicalGroup.IsPSL
      ((A ⊔ reducedSylow ![A,R] (T : Subgroup G) : Subgroup G) ⧸
        pCore 2 (A ⊔ reducedSylow ![A,R] (T : Subgroup G) : Subgroup G))
      2 (2 ^ (2 * k + 1))) :
    reducedSylow ![A,R] (T : Subgroup G) = (T : Subgroup G) := by
  have hn := original_degree_of_reduced_linear_quotient h he hm e hfield
  exact odd_linear_suzuki_reducedSylow_eq h (hn ▸ ⟨k, rfl⟩) he hm e

/-- Native reduced core placement gives containment of the original Sylow.
The local profile/core producer still has to establish both explicit premises. -/
theorem sylow_le_suzuki_of_reduced_core
    {T : Sylow 2 G} {A R : Subgroup G}
    (h : HypothesisF11 ![A,R] (T : Subgroup G)) {n m k : ℕ}
    (he : ClassicalGroup.IsPSL (A ⧸ pCore 2 A) 2 (2 ^ n)) (hm : 1 ≤ m)
    (e : (R ⧸ pCore 2 R) ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m)
    (hfield : ClassicalGroup.IsPSL
      ((A ⊔ reducedSylow ![A,R] (T : Subgroup G) : Subgroup G) ⧸
        pCore 2 (A ⊔ reducedSylow ![A,R] (T : Subgroup G) : Subgroup G))
      2 (2 ^ (2 * k + 1)))
    (hcore : pCore 2 (parabolic ![A,R] (reducedSylow ![A,R] (T : Subgroup G)) 1) ≤
      solvableResidual (parabolic ![A,R] (reducedSylow ![A,R] (T : Subgroup G)) 1)) :
    (T : Subgroup G) ≤ R := by
  have hs := original_sylow_eq_reduced_of_matching_field h he hm e hfield
  have hh := reduced_hypothesis h
  have hc : twoCore (parabolic ![A,R] (reducedSylow ![A,R] (T : Subgroup G)) 1) ≤ R :=
    (map_mono hcore).trans (hh.parabolic_residual_le_local 1)
  have hfact := suzuki_local_sylow_factorization hh 1 hm e
  rw [hh.localJoin_twoCore_eq_parabolic (reduced_borels_normalize h) 1] at hfact
  have hle : reducedSylow ![A,R] (T : Subgroup G) ≤ R :=
    hfact.le.trans (sup_le hc inf_le_right)
  rwa [hs] at hle

/-- The existing marked Ree endpoint applies already on the reduced pair;
the odd matching field restores the ORIGINAL Sylow, with no extension premise. -/
theorem sylow_le_suzuki_of_reduced_ree_parabolic
    {T : Sylow 2 G} {A R : Subgroup G}
    (h : HypothesisF11 ![A,R] (T : Subgroup G)) {n m k j : ℕ}
    (he : ClassicalGroup.IsPSL (A ⧸ pCore 2 A) 2 (2 ^ n)) (hm : 1 ≤ m)
    (e : (R ⧸ pCore 2 R) ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m)
    (hfield : ClassicalGroup.IsPSL
      ((A ⊔ reducedSylow ![A,R] (T : Subgroup G) : Subgroup G) ⧸
        pCore 2 (A ⊔ reducedSylow ![A,R] (T : Subgroup G) : Subgroup G))
      2 (2 ^ (2 * k + 1)))
    (eP : parabolic ![A,R] (reducedSylow ![A,R] (T : Subgroup G)) 1 ≃*
      ReeF4.Parabolics.parabolic j .suzuki) : (T : Subgroup G) ≤ R := by
  have hs := original_sylow_eq_reduced_of_matching_field h he hm e hfield
  have hh := sylow_le_suzuki_of_ree_parabolic (reduced_hypothesis h) 1 hm e eP
  rwa [hs] at hh

end CFSG.Quasithin.ChapterF.Source.SuzukiContainment
