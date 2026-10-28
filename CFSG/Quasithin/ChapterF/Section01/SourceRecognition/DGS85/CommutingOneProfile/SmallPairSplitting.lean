module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingOneProfile.PairCoprimeSplitting
public import Theory.Representation.BinaryInvolutionProduct
public import Theory.GroupTheory.PrimeRankCyclicSylow

/-!
# Small center-pair actors in Chapter 11

In a beta quotient of two-rank one, both critical-center images are cyclic
of order two. The literal pair-section fixed spaces are complementary, so
the product of their generators fixes only zero. Its order is odd by the
two-rank-one involution theorem. Lift it to the original center pair and
apply coprime decomposition to split Q_beta with exact intersection.

This applies to D10, Sz(2), SU3(2), and PSU3(2); all alpha rows remain
available. No whole-beta-quotient generation is assumed. The complementary
factor has not yet been eliminated, and the large unitary pair actor remains
to be identified. Source: Delgado--Goldschmidt--Stellmacher, Groups and Graphs
(1985), (11.3)(h), printed pp.170--171, using (5.11).
-/

public noncomputable section
open Subgroup Representation Representation.BinaryConjugationSection
open Representation.BinaryOffender Representation.RankOne.QuadraticRecognition
open scoped Pointwise IsMulCommutative MatrixGroups commutatorElement
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingOneProfile
open Subgroup.CosetGeometry.RankTwo CommutingNontrivial Theory.GroupTheory.AmalgamGraph
universe u
variable {G : Type u} [Group G] {P : Fin 2 → Subgroup G} {B : Subgroup G}

private theorem small_elementary_generator {D : Type*} [Group D] [Finite D]
    (hr : primeRank 2 D ≤ 1) (A : Subgroup D) [IsElementaryAbelian 2 A] (hne : A ≠ ⊥) :
    ∃ t : D, IsInvolution t ∧ zpowers t = A := by
  have hu : Nat.card A ≤ 2 := by
    simpa using (primeRank_le_iff_elementary_card_le D).mp hr A inferInstance
  have hcard : Nat.card A = 2 := by
    have hp := Nat.card_pos (α := A)
    have hn : Nat.card A ≠ 1 := fun he => hne (A.eq_bot_iff_card.mpr he)
    omega
  obtain ⟨t,ht⟩ := exists_prime_orderOf_dvd_card' (G := A) 2 (by rw [hcard])
  have ho : orderOf (t : D) = 2 := (Subgroup.orderOf_coe t).trans ht
  refine ⟨t,⟨fun he => by simp only [he,orderOf_one] at ho; omega,
    by simpa only [ho] using pow_orderOf_eq_one (t : D)⟩,?_⟩
  exact eq_of_le_of_card_ge (zpowers_le.mpr t.property) (by rw [Nat.card_zpowers,ho,hcard])

/-- The actual center pair supplies an odd splitting actor whenever the beta
quotient has two-rank one. No alpha row or fixed-point-free actor is assumed. -/
theorem source_small_pair_coprime_splitting
    (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (d : EarlierLocalTheorems (family P))
    {a b c : Vertex (family P)} (hc : IsCriticalPair (family P) a b)
    (hb : DGS85.b (family P) = 1) (hbc : (graph (family P)).Adj b c) (hac : a ≠ c)
    (Ma : IsRankOneModel (d.localGroup a ⧸ pCore 2 (d.localGroup a)))
    (Mb : IsRankOneModel (d.localGroup b ⧸ pCore 2 (d.localGroup b)))
    (hr : primeRank 2 (d.localGroup b ⧸ pCore 2 (d.localGroup b)) ≤ 1) :
    let V := pairSpan (Z (family P) a) (Z (family P) c) (Q (family P) b)
    let J := Z (family P) a ⊓ Z (family P) c
    ∃ y ∈ Z (family P) a ⊔ Z (family P) c, Odd (orderOf y) ∧ y ≠ 1 ∧
      Q (family P) b = V ⊔ (Q (family P) b ⊓ centralizer (zpowers y : Set G)) ∧
      V ⊓ centralizer (zpowers y : Set G) = J := by
  let := finite_endpoints h
  let := source_center_elementary h a
  let := source_center_elementary h c
  let H := (Z (family P) a ⊔ Z (family P) c) ⊔ Q (family P) b
  let V := pairSpan (Z (family P) a) (Z (family P) c) (Q (family P) b)
  let J := Z (family P) a ⊓ Z (family P) c
  let L := d.localGroup b
  let : Finite L := Finite.of_injective (inclusion (d.local_le b)) (inclusion_injective _)
  let : Finite (L ⧸ pCore 2 L) := Finite.of_surjective _ (QuotientGroup.mk'_surjective _)
  obtain ⟨hJ,hE,hQ,σ,s,_,hcompl,_,_⟩ := source_rankOne_pair_section h hB d hc hb hbc hac Ma Mb
  let := hJ
  let := hE
  let := hQ
  let K := H ⧸ (Q (family P) b).subgroupOf H
  let π := QuotientGroup.mk' ((Q (family P) b).subgroupOf H)
  obtain ⟨R,T,_,hHK,e,_⟩ := source_pair_actor_equiv h hB d hc hb hbc hac Mb
  let : Finite H := Finite.of_injective (inclusion hHK) (inclusion_injective _)
  let : Finite K := Finite.of_surjective π (QuotientGroup.mk'_surjective _)
  have hKrank : primeRank 2 K ≤ 1 :=
    (primeRank_le_of_injective 2
      ((omegaCenterIn (R : Subgroup (L ⧸ pCore 2 L)) ⊔
        omegaCenterIn (T : Subgroup (L ⧸ pCore 2 L))).subtype.comp e.toMonoidHom)
      (Subtype.val_injective.comp e.injective)).trans hr
  let A := ((Z (family P) a).subgroupOf H).map π
  let C := ((Z (family P) c).subgroupOf H).map π
  have hZaH : Z (family P) a ≤ H := le_sup_left.trans le_sup_left
  have hZcH : Z (family P) c ≤ H := le_sup_right.trans le_sup_left
  obtain ⟨g,hg,hga⟩ := source_rankOne_center_pair_moves h hB d hc hb hbc Mb
  have hgb : g • b = b := d.local_le b (hHK (mem_sup_left hg))
  have hcc : IsCriticalPair (family P) c b := by
    simpa only [hga,hgb] using criticalPair_translate (family P) hc g
  have hne (z : Vertex (family P)) (hzH : Z (family P) z ≤ H)
      (hz : IsCriticalPair (family P) z b) : ((Z (family P) z).subgroupOf H).map π ≠ ⊥ := by
    intro he
    have hk := (Subgroup.map_eq_bot_iff _).mp he
    rw [QuotientGroup.ker_mk'] at hk
    apply hz.2
    exact (show Z (family P) z ≤ Q (family P) b from fun x hx =>
      hk (show (⟨x,hzH hx⟩ : H) ∈ (Z (family P) z).subgroupOf H from hx)).trans
        (source_Z_Q_U h b).2
  let : IsElementaryAbelian 2 ((Z (family P) a).subgroupOf H) :=
    IsElementaryAbelian.subgroupOf hZaH
  let : IsElementaryAbelian 2 ((Z (family P) c).subgroupOf H) :=
    IsElementaryAbelian.subgroupOf hZcH
  let : IsElementaryAbelian 2 A := IsElementaryAbelian.map π
  let : IsElementaryAbelian 2 C := IsElementaryAbelian.map π
  obtain ⟨t,ht,htA⟩ := small_elementary_generator hKrank A (hne a hZaH hc)
  obtain ⟨r,hrt,hrC⟩ := small_elementary_generator hKrank C (hne c hZcH hcc)
  have hf := source_rankOne_pair_fixed_spaces h hB d hc hb hbc Mb π
    (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _) σ s
  have hd : Disjoint (fixedSpace σ (zpowers t)) (fixedSpace σ (zpowers r)) := by
    rw [htA,hrC,hf.2.1,hf.2.2]
    exact hcompl.disjoint
  have hfixed := involution_product_fixed_eq_bot σ t r
    (by simpa only [pow_two] using ht.2) (by simpa only [pow_two] using hrt.2) hd
  have ho := odd_product_of_two_rank_one hKrank ht hrt
  have htr : t*r ≠ 1 := by
    intro he
    obtain ⟨x,hx,hxQ⟩ := SetLike.not_le_iff_exists.mp
      (source_rankOne_seed_escape h hB d hc hb hbc hac Mb).1
    let v : V := ⟨x,(show Z (family P) a ⊓ Q (family P) b ≤ V from le_sup_left) hx⟩
    have hv : (s.coordinates v).toAdd ∈ fixedSpace σ (zpowers (t*r)) := by
      rw [he]
      apply (mem_fixedSpace_zpowers_iff _ _ _).mpr
      simp only [map_one]
      rfl
    rw [hfixed,Submodule.mem_bot] at hv
    have hxJ := (s.coordinates_eq_one_iff v).mp (Multiplicative.toAdd.injective hv)
    exact hxQ (((source_Z_Q_U h c).1.trans (map_subtype_le _)) hxJ.2)
  apply source_pair_coprime_splitting_of_odd_actor h d hc hb hbc hHK π
    (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _) s.kernel_le (t*r) ho htr
  intro y hy x hx
  rw [←s.fixed_coordinate_iff_commutator_mem y ⟨x,hx⟩]
  change σ (π y) (s.coordinates ⟨x,hx⟩).toAdd = (s.coordinates ⟨x,hx⟩).toAdd ↔ _
  rw [hy,←mem_fixedSpace_zpowers_iff,hfixed,Submodule.mem_bot]
  exact s.coordinates_eq_one_iff ⟨x,hx⟩


open BenderSuzuki.MatrixGroups
private instance {F : Type*} [Field F] [Finite F] : Finite (Matrix.ProjGenLinGroup (Fin 3) F) :=
  Finite.of_surjective Matrix.ProjGenLinGroup.mk Matrix.ProjGenLinGroup.mk_surjective

/-- The four small beta models have two-rank one. The unitary alternatives
retain their distinct special and projective carriers. -/
theorem small_beta_models_two_rank {D : Type*} [Group D] [Finite D]
    (hsmall : Nonempty (D ≃* DihedralGroup 5) ∨ Nonempty (D ≃* SuzukiMatrixGroup 0) ∨
      IsSU D 3 2 ∨ ClassicalGroup.IsPSU D 3 2) : primeRank 2 D ≤ 1 := by
  rcases hsmall with hd | hz | hu | hu
  · obtain ⟨e⟩ := hd
    rw [primeRank_congr 2 e]
    let S : Sylow 2 (DihedralGroup 5) := default
    have hc : Nat.card S = 2 := by
      rw [S.card_eq_multiplicity,DihedralGroup.nat_card,
        Nat.factorization_mul (by decide) (by decide),
        Nat.prime_two.factorization,Nat.prime_five.factorization]
      norm_num
    exact S.primeRank_le_one_of_isCyclic (isCyclic_of_prime_card hc)
  · obtain ⟨e⟩ := hz
    rw [primeRank_congr 2 e]
    let S : Sylow 2 (SuzukiMatrixGroup 0) := Sylow.ofCard (zpowers suzukiZeroRootGenerator) (by
      rw [Nat.card_zpowers,suzukiZeroRootGenerator_order,suzukiZero_card]
      rw [show (20 : ℕ) = 2^2 * 5 from rfl,
        Nat.factorization_mul (by decide) (by decide),Nat.factorization_pow]
      norm_num [Nat.Prime.factorization Nat.prime_two,
        Nat.Prime.factorization (by decide : Nat.Prime 5)])
    exact S.primeRank_le_one_of_isCyclic (inferInstanceAs (IsCyclic (zpowers suzukiZeroRootGenerator)))
  · obtain ⟨F,_,_,J,hcard,hconj,⟨e⟩⟩ := hu
    rw [primeRank_congr 2 e,primeRank_eq_of_surjective_of_coprime 2 J.specialToProjective
      J.specialToProjective_surjective J.odd_card_specialToProjective_ker.coprime_two_left]
    exact (HermitianForm.EvenTwoRank.two_rank J (n := 1) (by decide) hcard hconj).le
  · obtain ⟨F,_,_,J,hcard,hconj,⟨e⟩⟩ := hu
    rw [primeRank_congr 2 e]
    exact (HermitianForm.EvenTwoRank.two_rank J (n := 1) (by decide) hcard hconj).le

/-- Coprime beta-core splitting for D10, Sz(2), SU3(2), and PSU3(2), with
arbitrary alpha and no supplied actor or two-rank hypothesis. -/
theorem source_small_models_pair_coprime_splitting
    (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (d : EarlierLocalTheorems (family P))
    {a b c : Vertex (family P)} (hc : IsCriticalPair (family P) a b)
    (hb : DGS85.b (family P) = 1) (hbc : (graph (family P)).Adj b c) (hac : a ≠ c)
    (Ma : IsRankOneModel (d.localGroup a ⧸ pCore 2 (d.localGroup a)))
    (Mb : IsRankOneModel (d.localGroup b ⧸ pCore 2 (d.localGroup b)))
    (hsmall : Nonempty ((d.localGroup b ⧸ pCore 2 (d.localGroup b)) ≃* DihedralGroup 5) ∨
      Nonempty ((d.localGroup b ⧸ pCore 2 (d.localGroup b)) ≃* SuzukiMatrixGroup 0) ∨
      IsSU (d.localGroup b ⧸ pCore 2 (d.localGroup b)) 3 2 ∨
      ClassicalGroup.IsPSU (d.localGroup b ⧸ pCore 2 (d.localGroup b)) 3 2) :
    let V := pairSpan (Z (family P) a) (Z (family P) c) (Q (family P) b)
    let J := Z (family P) a ⊓ Z (family P) c
    ∃ y ∈ Z (family P) a ⊔ Z (family P) c, Odd (orderOf y) ∧ y ≠ 1 ∧
      Q (family P) b = V ⊔ (Q (family P) b ⊓ centralizer (zpowers y : Set G)) ∧
      V ⊓ centralizer (zpowers y : Set G) = J := by
  let := finite_endpoints h
  let : Finite (d.localGroup b) := Finite.of_injective (inclusion (d.local_le b)) (inclusion_injective _)
  let : Finite (d.localGroup b ⧸ pCore 2 (d.localGroup b)) :=
    Finite.of_surjective _ (QuotientGroup.mk'_surjective _)
  exact source_small_pair_coprime_splitting h hB d hc hb hbc hac Ma Mb (small_beta_models_two_rank hsmall)

end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingOneProfile
