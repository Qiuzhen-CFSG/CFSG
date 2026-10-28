module

public import CFSG.Quasithin.ChapterF.Section01.RankOneBorels.Linear
public import CFSG.Quasithin.ChapterF.Section01.RankOneBorels.Suzuki
public import CFSG.Quasithin.ChapterF.Section01.RankOneBorels.Unitary.StandardAction
public import CFSG.Quasithin.ChapterF.Section01.RankOneBorels.Unitary.FormTransport
public import CFSG.Quasithin.ChapterF.Section01.RankOneBorels.Unitary.SpecialBorel.Basic
public import Theory.GroupTheory.NormalizedSupCard

/-!
# Cyclic Cartans in the three binary rank-one models

The concrete PSL₂, PSU₃ and Suzuki Sylow normalizers split over cyclic
matrix tori. Sylow conjugacy and, for PSU₃, change of Hermitian basis
transport these decompositions. An odd p-subgroup of a normalizer fixes
a coset of its torus: the index is the order of the root group, a power
of two. It is therefore conjugate into a cyclic Cartan.

This is the rank-one torus step in Aschbacher–Smith, combined 1 March 2004
manuscript, Proposition 1.3.4, printed p.511, using Remark A.2.4, p.33,
and Lemma A.3.15(5), pp.50–51. Normalizer containment is an explicit input
here and must be supplied by the source-configuration assembly. The unitary
matrix field has order (2^n)^2, with its specified involution retained.
-/

@[expose] public section

open Subgroup
open scoped Pointwise

namespace CFSG.Quasithin.Chapter1.XiEmbedding.InvariantLarge.EvenActions.RankOne

private def CyclicComplement {G : Type*} [Group G] (U : Subgroup G) : Prop :=
  ∃ C : Subgroup G, C ≤ normalizer (U : Set G) ∧ IsCyclic C ∧
    Disjoint U C ∧ U ⊔ C = normalizer (U : Set G)

private theorem complement_map {G K : Type*} [Group G] [Group K]
    (e : G ≃* K) (U : Subgroup G) (hU : CyclicComplement U) :
    CyclicComplement (U.map e.toMonoidHom) := by
  obtain ⟨C, hC, hcyc, hdis, hsup⟩ := hU
  refine ⟨C.map e.toMonoidHom, ?_, ?_, ?_, ?_⟩
  · rw [← map_normalizer_eq_of_bijective U e.bijective]
    exact map_mono hC
  · exact (C.equivMapOfInjective e.toMonoidHom e.injective).isCyclic.mp hcyc
  · rw [disjoint_iff, ← map_inf _ _ _ e.injective, hdis.eq_bot, Subgroup.map_bot]
  · rw [← Subgroup.map_sup, hsup, map_normalizer_eq_of_bijective U e.bijective]

private theorem complement_all_sylows {G : Type*} [Group G] [Finite G]
    (S T : Sylow 2 G) (hS : CyclicComplement (S : Subgroup G)) :
    CyclicComplement (T : Subgroup G) := by
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G S T
  have hm : (S : Subgroup G).map (MulAut.conj g).toMonoidHom =
      (T : Subgroup G) := congrArg Sylow.toSubgroup hg
  rw [← hm]
  exact complement_map (MulAut.conj g) _ hS

private theorem complement_of_mapped_sylow {G K : Type*} [Group G] [Finite G] [Group K]
    (e : G ≃* K) (S : Sylow 2 G)
    (hK : CyclicComplement
      ((S.mapSurjective (f := e.toMonoidHom) e.surjective : Sylow 2 K) : Subgroup K)) :
    CyclicComplement (S : Subgroup G) := by
  have hh := complement_map e.symm _ hK
  change CyclicComplement (((S : Subgroup G).map e.toMonoidHom).map e.symm.toMonoidHom) at hh
  have he : e.symm.toMonoidHom.comp e.toMonoidHom = MonoidHom.id _ := by
    ext x
    exact e.symm_apply_apply x
  simpa only [map_map, he, map_id] using hh

private theorem complement_psl2 (F : Type*) [Field F] [Finite F] [CharP F 2]
    (T : Sylow 2 (BenderSuzuki.Converse.PSL2 F)) :
    CyclicComplement (T : Subgroup (BenderSuzuki.Converse.PSL2 F)) := by
  open BenderSuzuki.Converse in
  apply complement_all_sylows (ChapterF.Source.Linear.projectiveSylow F) T
  rw [ChapterF.Source.Linear.projectiveSylow_coe]
  refine ⟨PTorus F, ?_, ?_, PUnip_disjoint_PTorus, ?_⟩
  · rw [← ChapterF.Source.Linear.projectiveSylow_coe]
    change PTorus F ≤ normalizer (ChapterF.Source.Linear.projectiveSylow F : Set (PSL2 F))
    rw [ChapterF.Source.Linear.projectiveSylow_normalizer]
    exact PTorus_le_PBorel
  · have : IsCyclic (Torus F) := by
      rw [Torus_eq_range]
      exact isCyclic_of_surjective (torHom F).rangeRestrict
        (torHom F).rangeRestrict_surjective
    exact isCyclic_of_surjective ((pi F).subgroupMap (Torus F))
      ((pi F).subgroupMap_surjective (Torus F))
  · rw [PUnip_sup_PTorus, ← ChapterF.Source.Linear.projectiveSylow_coe]
    exact (ChapterF.Source.Linear.projectiveSylow_normalizer F).symm

private theorem complement_suzuki (m : ℕ) (hm : 0 < m)
    (T : Sylow 2 (BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m)) :
    CyclicComplement (T : Subgroup (BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m)) := by
  open BenderSuzuki.MatrixGroups in
  obtain ⟨S, hS⟩ := suzukiRootSubgroup_isSylow m hm
  apply complement_all_sylows S T
  rw [hS]
  refine ⟨SuzukiSplitTorus m, suzukiSplitTorus_le_normalizer_root m,
    suzukiSplitTorus_isCyclic m hm, suzukiRootSubgroup_disjoint_splitTorus m hm, ?_⟩
  rw [ChapterF.Source.suzuki_root_normalizer_eq_borel, suzukiBorelSubgroup_eq_sup]

private theorem standard_psu3_complement {F : Type*} [Field F] [Finite F]
    (J : BenderSuzuki.MatrixGroups.HermitianForm 3 F)
    (n : ℕ) (hn : 0 < n) (hcard : Nat.card F = (2 ^ n) ^ 2)
    (hconj : ∀ x, J.conj x = x ^ (2 ^ n))
    (hstandard : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0]) :
    ∃ S : Sylow 2 (BenderSuzuki.MatrixGroups.ProjectiveSpecialUnitaryMatrixGroup J),
      CyclicComplement (S : Subgroup
        (BenderSuzuki.MatrixGroups.ProjectiveSpecialUnitaryMatrixGroup J)) := by
  obtain ⟨_, _, S, ⟨D, hD, _, hcyc, hdis, hsup⟩, _⟩ :=
    ChapterF.Source.Unitary.standard_psu_borel_data J n hn hcard hconj hstandard
  exact ⟨S, D, hD, hcyc, hdis, hsup⟩

private theorem complement_psu3 {F : Type*} [Field F] [Finite F]
    (J : BenderSuzuki.MatrixGroups.HermitianForm 3 F)
    (n : ℕ) (hn : 0 < n) (hcard : Nat.card F = (2 ^ n) ^ 2)
    (hconj : ∀ x, J.conj x = x ^ (2 ^ n))
    (T : Sylow 2 (BenderSuzuki.MatrixGroups.ProjectiveSpecialUnitaryMatrixGroup J)) :
    CyclicComplement (T : Subgroup
      (BenderSuzuki.MatrixGroups.ProjectiveSpecialUnitaryMatrixGroup J)) := by
  open BenderSuzuki.MatrixGroups BenderSuzuki.External ChapterF.Source.Unitary in
  classical
  let : Fintype F := Fintype.ofFinite F
  let : Finite (ProjectiveSpecialUnitaryMatrixGroup J) :=
    Finite.of_surjective _ (suProjection_surjective J)
  let J₀ := FormTransport.standardForm J
  let : Finite (ProjectiveSpecialUnitaryMatrixGroup J₀) :=
    Finite.of_surjective _ (suProjection_surjective J₀)
  obtain ⟨C, hC⟩ := FormTransport.exists_standard_basis J n hn hcard hconj
  let e : ProjectiveSpecialUnitaryMatrixGroup J ≃* ProjectiveSpecialUnitaryMatrixGroup J₀ :=
    FormTransport.projectiveEquiv J C hC
  obtain ⟨S, hS⟩ := standard_psu3_complement J₀ n hn hcard hconj rfl
  have ht := complement_all_sylows S (T.mapSurjective (f := e.toMonoidHom) e.surjective)
    hS
  exact complement_of_mapped_sylow e T ht

private theorem conjugate_le_of_index {G : Type*} [Group G]
    {p : ℕ} [Fact p.Prime] (A C : Subgroup G) (hA : IsPGroup p A)
    (hC : ¬ p ∣ C.index) :
    ∃ g : G, A.map (MulAut.conj g).toMonoidHom ≤ C := by
  obtain ⟨x, hx⟩ := hA.nonempty_fixed_point_of_prime_not_dvd_card (G ⧸ C) hC
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
  refine ⟨g⁻¹, ?_⟩
  rintro _ ⟨a, ha, rfl⟩
  have he : (g : G ⧸ C) = (a * g : G) := (hx (⟨a, ha⟩ : A)).symm
  change g⁻¹ * a * (g⁻¹)⁻¹ ∈ C
  simpa only [inv_inv, mul_assoc] using QuotientGroup.eq.mp he

private theorem cyclic_of_complement {G : Type*} [Group G] [Finite G]
    (S : Sylow 2 G) (hS : CyclicComplement (S : Subgroup G))
    {p : ℕ} [Fact p.Prime] (hp : p ≠ 2)
    (B : Subgroup G) (hB : IsPGroup p B)
    (hBN : B ≤ normalizer (S : Set G)) : IsCyclic B := by
  obtain ⟨C, hC, hcyc, hdis, hsup⟩ := hS
  let N := normalizer (S : Set G)
  let C₀ := C.subgroupOf N
  let B₀ := B.subgroupOf N
  have hcard : Nat.card N = Nat.card S * Nat.card C := by
    change Nat.card (normalizer ((S : Subgroup G) : Set G)) = _
    rw [← hsup]
    exact card_sup_eq_mul_of_normalizes_of_disjoint _ _ hC hdis
  have hCcard : Nat.card C₀ = Nat.card C :=
    Nat.card_congr (subgroupOfEquivOfLe hC).toEquiv
  have hindex : C₀.index = Nat.card S := by
    have hh := C₀.card_mul_index
    rw [hCcard, hcard, mul_comm (Nat.card S)] at hh
    exact Nat.eq_of_mul_eq_mul_left Nat.card_pos hh
  have hnot : ¬ p ∣ C₀.index := by
    obtain ⟨a, ha⟩ := S.isPGroup'.exists_card_eq
    rw [hindex, ha]
    intro hd
    exact hp ((Nat.prime_dvd_prime_iff_eq Fact.out Nat.prime_two).mp
      ((Fact.out : p.Prime).dvd_of_dvd_pow hd))
  obtain ⟨g, hg⟩ := conjugate_le_of_index B₀ C₀ hB.comap_subtype hnot
  let : IsCyclic C₀ := (subgroupOfEquivOfLe hC).isCyclic.mpr hcyc
  have hc : IsCyclic B₀ :=
    (B₀.equivMapOfInjective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective).isCyclic.mpr
      (Subgroup.isCyclic_of_le hg)
  exact (subgroupOfEquivOfLe hBN).isCyclic.mp hc

private theorem cyclic_transport {G K : Type*} [Group G] [Finite G] [Group K]
    (e : G ≃* K) (S : Sylow 2 G)
    (hK : CyclicComplement
      ((S.mapSurjective (f := e.toMonoidHom) e.surjective : Sylow 2 K) : Subgroup K))
    {p : ℕ} [Fact p.Prime] (hp : p ≠ 2)
    (B : Subgroup G) (hB : IsPGroup p B)
    (hBN : B ≤ normalizer (S : Set G)) : IsCyclic B := by
  exact cyclic_of_complement S (complement_of_mapped_sylow e S hK) hp B hB hBN

/-- An odd p-subgroup of a binary PSL₂ Sylow normalizer is cyclic.
The model hypothesis contains an actual multiplicative equivalence. -/
theorem psl2_normalizer_isCyclic {G : Type*} [Group G] [Finite G]
    {n p : ℕ} [Fact p.Prime] (_hn : 0 < n)
    (hmodel : ClassicalGroup.IsPSL G 2 (2 ^ n)) (hp : p ≠ 2)
    (S : Sylow 2 G) (B : Subgroup G) (hB : IsPGroup p B)
    (hBN : B ≤ normalizer (S : Set G)) : IsCyclic B := by
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := hmodel
  let : Fintype F := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow
    (by simpa only [Nat.card_eq_fintype_card] using hF)
  exact cyclic_transport e S (complement_psl2 F _) hp B hB hBN

/-- An odd p-subgroup of a Suzuki Sylow normalizer is cyclic. -/
theorem suzuki_normalizer_isCyclic {G : Type*} [Group G] [Finite G]
    {m p : ℕ} [Fact p.Prime] (hm : 0 < m)
    (e : G ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m) (hp : p ≠ 2)
    (S : Sylow 2 G) (B : Subgroup G) (hB : IsPGroup p B)
    (hBN : B ≤ normalizer (S : Set G)) : IsCyclic B :=
  cyclic_transport e S (complement_suzuki m hm _) hp B hB hBN

/-- An odd p-subgroup of a binary PSU₃ Sylow normalizer is cyclic.
`IsPSU G 3 (2^n)` uses matrix-field order `(2^n)^2` and the q-power involution. -/
theorem psu3_normalizer_isCyclic {G : Type*} [Group G] [Finite G]
    {n p : ℕ} [Fact p.Prime] (hn : 0 < n)
    (hmodel : ClassicalGroup.IsPSU G 3 (2 ^ n)) (hp : p ≠ 2)
    (S : Sylow 2 G) (B : Subgroup G) (hB : IsPGroup p B)
    (hBN : B ≤ normalizer (S : Set G)) : IsCyclic B := by
  obtain ⟨F, _, _, J, hF, hconj, ⟨e⟩⟩ := hmodel
  exact cyclic_transport e S (complement_psu3 J n hn hF hconj _) hp B hB hBN

end CFSG.Quasithin.Chapter1.XiEmbedding.InvariantLarge.EvenActions.RankOne
