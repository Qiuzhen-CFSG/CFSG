module

public import Stellmacher.Recognition.GTwoSixtyFourLocal
public import Theory.GroupTheory.QuaternionCentralProductInvolutions

/-!
# The canonical index-two subgroup in the order-64 G₂ configuration

Write A = O₂(Eₐ) and R = Qᵦ ∩ Eᵦ, where b is the first critical step.
Their embedded product, restricted to the distinguished Sylow intersection,
is a normal subgroup U of index two. Moreover that Sylow has an involution
outside U.

Both factors are normal two-subgroups of their respective vertices and hence
lie normally in the common Sylow. The outside inverter of A cannot belong to
AR: otherwise all squares of A would lie in the quaternion group R, which has
only one involution. Since R is nonabelian, the product has order strictly
between 16 and 64, hence 32. The other core Qᵦ is a quaternion central product
of order 32. It cannot contain A, because all its squares lie in a subgroup
of order two. Thus Qᵦ is not contained in AR. Its generation by involutions
supplies the required outside involution, without asserting that the supplied
inverter itself has order two.

Source: Stellmacher (8.6)(a) and the following local-type definition,
`refs/latex/stellmacher-n-group.tex`, printed pp. 41 and 45. Only the actual
exceptional-type data are used; no global Hypothesis 2 assumptions are added.
-/

namespace Stellmacher.Recognition

open Later SectionsFiveToSeven SevenSix

private theorem mapped_normal_two_subgroup
    {G K : Type*} [Group G] [Finite G] [Group K]
    (f : K →* G) (S : Sylow 2 G) (P N : Subgroup K)
    (hNP : N ≤ P) (hNN : (N.subgroupOf P).Normal) (hNtwo : IsPGroup 2 N)
    (hSP : (S : Subgroup G) ≤ P.map f) :
    N.map f ≤ (S : Subgroup G) ∧ ((N.map f).subgroupOf (S : Subgroup G)).Normal := by
  have hmP : N.map f ≤ P.map f := Subgroup.map_mono hNP
  have hPN : P.map f ≤ Subgroup.normalizer (N.map f : Set G) :=
    (Subgroup.map_mono ((Subgroup.normal_subgroupOf_iff_le_normalizer hNP).mp hNN)).trans
      (Subgroup.le_normalizer_map f)
  have hmN : ((N.map f).subgroupOf (P.map f)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hmP).mpr hPN
  have hmS : N.map f ≤ (S : Subgroup G) := by
    let := hmN
    have hmTwo : IsPGroup 2 ((N.map f).subgroupOf (P.map f)) :=
      (hNtwo.map f).of_equiv (Subgroup.subgroupOfEquivOfLe hmP).symm
    have hle := hmTwo.le_sylow_of_normal (S.subtype hSP)
    intro x hx
    exact hle (show (⟨x, hmP hx⟩ : P.map f) ∈ (N.map f).subgroupOf (P.map f) from hx)
  exact ⟨hmS, (Subgroup.normal_subgroupOf_iff_le_normalizer hmS).mpr (hSP.trans hPN)⟩

private theorem mapped_vertex_core
    {G : Type*} [Group G] [Finite G] (data : GTwoTwoDerivedTypeData G)
    : letI := data.groupK
    letI := data.finiteK
    ∀ d : data.Γ.Vertex,
    (data.sylowIntersection : Subgroup G) ≤ (GAt data.Γ d).map data.embedding →
    (QAt data.Γ d).map data.embedding ≤ (data.sylowIntersection : Subgroup G) := by
  let := data.groupK
  let := data.finiteK
  intro d hSP
  have hQ : QAt data.Γ d = twoCoreIn (GAt data.Γ d) := data.Γ.twoCoreAt_def d
  rw [hQ]
  exact (mapped_normal_two_subgroup data.embedding data.sylowIntersection
    (GAt data.Γ d) (twoCoreIn (GAt data.Γ d)) (twoCoreIn_le _)
    (twoCoreIn_normal _) (pCore_isPGroup.map (GAt data.Γ d).subtype) hSP).1

private theorem mapped_residual_core
    {G : Type*} [Group G] [Finite G] (data : GTwoTwoDerivedTypeData G)
    : letI := data.groupK
    letI := data.finiteK
    ∀ d : data.Γ.Vertex,
    (data.sylowIntersection : Subgroup G) ≤ (GAt data.Γ d).map data.embedding →
    (twoCoreIn (EAt data.Γ d)).map data.embedding ≤ (data.sylowIntersection : Subgroup G) ∧
      (((twoCoreIn (EAt data.Γ d)).map data.embedding).subgroupOf
        (data.sylowIntersection : Subgroup G)).Normal := by
  let := data.groupK
  let := data.finiteK
  intro d hSP
  have hE : EAt data.Γ d = twoResidualIn (GAt data.Γ d) := data.Γ.twoResidualAt_def d
  have hEP : EAt data.Γ d ≤ GAt data.Γ d := by rw [hE]; exact twoResidualIn_le _
  have hEN : ((EAt data.Γ d).subgroupOf (GAt data.Γ d)).Normal := by
    rw [hE]; exact twoResidualIn_normal _
  exact mapped_normal_two_subgroup data.embedding data.sylowIntersection
    (GAt data.Γ d) (twoCoreIn (EAt data.Γ d)) ((twoCoreIn_le _).trans hEP)
    (twoCoreIn_normal_of_normal _ _ hEP hEN)
    (pCore_isPGroup.map (EAt data.Γ d).subtype) hSP

private theorem quaternion_factor_eq_residual_core
    {G : Type*} [Group G] [Finite G] (data : GTwoTwoDerivedTypeData G) :
    letI := data.groupK
    letI := data.finiteK
    QAt data.Γ data.criticalPath.firstStep ⊓ EAt data.Γ data.criticalPath.firstStep =
      twoCoreIn (EAt data.Γ data.criticalPath.firstStep) := by
  let := data.groupK
  let := data.finiteK
  rw [show QAt data.Γ data.criticalPath.firstStep =
    twoCoreIn (GAt data.Γ data.criticalPath.firstStep) from data.Γ.twoCoreAt_def _,
    show EAt data.Γ data.criticalPath.firstStep =
    twoResidualIn (GAt data.Γ data.criticalPath.firstStep) from data.Γ.twoResidualAt_def _,
    inf_comm, residual_core_eq_inter_core]

/-- The canonical product of the first residual core and the second quaternion
factor, restricted to the distinguished Sylow intersection. -/
@[expose] public def gTwoCard64TransferSubgroup
    {G : Type*} [Group G] [Finite G] (data : GTwoTwoDerivedTypeData G) :
    Subgroup data.sylowIntersection :=
  letI := data.groupK
  letI := data.finiteK
  (((twoCoreIn (EAt data.Γ data.criticalPath.a)).map data.embedding) ⊔
    ((QAt data.Γ data.criticalPath.firstStep ⊓ EAt data.Γ data.criticalPath.firstStep).map
      data.embedding)).subgroupOf (data.sylowIntersection : Subgroup G)

/-- Both factors of the canonical product really lie in the supplied Sylow. -/
public theorem gTwo_card64_transfer_le_sylow
    {G : Type*} [Group G] [Finite G] (data : GTwoTwoDerivedTypeData G) :
    letI := data.groupK
    letI := data.finiteK
    ((twoCoreIn (EAt data.Γ data.criticalPath.a)).map data.embedding) ⊔
      ((QAt data.Γ data.criticalPath.firstStep ⊓ EAt data.Γ data.criticalPath.firstStep).map
        data.embedding) ≤ (data.sylowIntersection : Subgroup G) := by
  let := data.groupK
  let := data.finiteK
  apply sup_le
  · exact (mapped_residual_core data data.criticalPath.a (by
      rw [← data.intersection_eq]; exact inf_le_left)).1
  · rw [quaternion_factor_eq_residual_core data]
    exact (mapped_residual_core data data.criticalPath.firstStep (by
      rw [← data.intersection_eq]; exact inf_le_right)).1

/-- Each factor of the canonical transfer subgroup is normal in the actual Sylow. -/
public theorem gTwo_card64_transfer_factors_normal
    {G : Type*} [Group G] [Finite G] (data : GTwoTwoDerivedTypeData G) :
    letI := data.groupK
    letI := data.finiteK
    let S := (data.sylowIntersection : Subgroup G)
    (((twoCoreIn (EAt data.Γ data.criticalPath.a)).map data.embedding).subgroupOf S).Normal ∧
      (((QAt data.Γ data.criticalPath.firstStep ⊓ EAt data.Γ data.criticalPath.firstStep).map
        data.embedding).subgroupOf S).Normal := by
  let := data.groupK
  let := data.finiteK
  constructor
  · exact (mapped_residual_core data data.criticalPath.a (by
      rw [← data.intersection_eq]; exact inf_le_left)).2
  · rw [quaternion_factor_eq_residual_core data]
    exact (mapped_residual_core data data.criticalPath.firstStep (by
      rw [← data.intersection_eq]; exact inf_le_right)).2

/-- The canonical product has index two and there is an involution outside it. -/
public theorem gTwo_card64_transfer_structure
    {G : Type*} [Group G] [Finite G] (data : GTwoTwoDerivedTypeData G)
    (hcard : Nat.card data.sylowIntersection = 64) :
    (gTwoCard64TransferSubgroup data).Normal ∧
      (gTwoCard64TransferSubgroup data).index = 2 ∧
      ∃ t : data.sylowIntersection, orderOf t = 2 ∧ t ∉ gTwoCard64TransferSubgroup data := by
  let := data.groupK
  let := data.finiteK
  let S := data.sylowIntersection
  let A0 := twoCoreIn (EAt data.Γ data.criticalPath.a)
  let R0 := QAt data.Γ data.criticalPath.firstStep ⊓ EAt data.Γ data.criticalPath.firstStep
  let A := (A0.map data.embedding).subgroupOf (S : Subgroup G)
  let R := (R0.map data.embedding).subgroupOf (S : Subgroup G)
  let U := gTwoCard64TransferSubgroup data
  have hSPa : (S : Subgroup G) ≤ (GAt data.Γ data.criticalPath.a).map data.embedding := by
    rw [← data.intersection_eq]; exact inf_le_left
  have hSPb : (S : Subgroup G) ≤ (GAt data.Γ data.criticalPath.firstStep).map data.embedding := by
    rw [← data.intersection_eq]; exact inf_le_right
  obtain ⟨hAmS, hAN⟩ := mapped_residual_core data data.criticalPath.a hSPa
  have hRfacts : R0.map data.embedding ≤ (S : Subgroup G) ∧ R.Normal := by
    dsimp [R, R0]
    rw [quaternion_factor_eq_residual_core data]
    exact mapped_residual_core data data.criticalPath.firstStep hSPb
  obtain ⟨hRmS, hRN⟩ := hRfacts
  let := hAN
  let := hRN
  have hUeq : U = A ⊔ R := (Subgroup.subgroupOf_sup hAmS hRmS)
  have hUN : U.Normal := by rw [hUeq]; infer_instance
  have hA : Nonempty (A ≃* C4 × C4) := by
    obtain ⟨e⟩ := data.caseA.twoCore_model
    exact ⟨((Subgroup.subgroupOfEquivOfLe hAmS).trans
      (A0.equivMapOfInjective data.embedding data.embedding_injective).symm).trans e⟩
  have hR : Nonempty (R ≃* Q8) := by
    obtain ⟨e⟩ := data.caseA.next_twoCore.2
    exact ⟨((Subgroup.subgroupOfEquivOfLe hRmS).trans
      (R0.equivMapOfInjective data.embedding data.embedding_injective).symm).trans e⟩
  obtain ⟨t, htQ, _, hinv, _⟩ := gTwo_card64_outside_inverter data hcard
  have htS : data.embedding t ∈ (S : Subgroup G) :=
    mapped_vertex_core data data.criticalPath.a hSPa ⟨t, htQ, rfl⟩
  let tS : S := ⟨data.embedding t, htS⟩
  have htInv : ∀ x ∈ A, tS * x * tS⁻¹ = x⁻¹ := by
    intro x hx
    obtain ⟨y, hy, heq⟩ := hx
    change data.embedding y = (x : G) at heq
    apply Subtype.ext
    change data.embedding t * (x : G) * (data.embedding t)⁻¹ = (x : G)⁻¹
    rw [← heq, ← map_inv, ← map_mul, ← map_mul, hinv y hy, map_inv]
  have hUi : U.index = 2 := by
    rw [hUeq]
    exact Subgroup.c4_square_sup_quaternion_index_two hcard A R hA hR tS htInv
  refine ⟨hUN, hUi, ?_⟩
  let B0 := A0 ⊔ R0
  have hBmapS : B0.map data.embedding ≤ (S : Subgroup G) := by
    rw [Subgroup.map_sup]
    exact sup_le hAmS hRmS
  have hUmap : U = (B0.map data.embedding).subgroupOf (S : Subgroup G) := by
    dsimp [U, gTwoCard64TransferSubgroup, B0, A0, R0]
    rw [Subgroup.map_sup]
  have hBcard : Nat.card B0 = 32 := by
    have hcount := U.card_mul_index
    rw [hUi, hcard, hUmap,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBmapS).toEquiv,
      Subgroup.card_map_of_injective data.embedding_injective] at hcount
    omega
  obtain ⟨_, _, hQbCard, _, hQbModel⟩ := gTwo_card64_vertex_structure data hcard
  obtain ⟨V, W, hV, hW, hQeq, hinter, hcomm, _⟩ := hQbModel
  have hQnle : ¬ QAt data.Γ data.criticalPath.firstStep ≤ B0 := by
    intro hle
    have heq : QAt data.Γ data.criticalPath.firstStep = B0 :=
      Subgroup.eq_of_le_of_card_ge hle (by rw [hBcard, hQbCard])
    apply Subgroup.c4_square_not_le_quaternion_central_product A0 V W
      data.caseA.twoCore_model hV hW hinter hcomm
    rw [← hQeq, heq]
    exact le_sup_left
  have hgen : Subgroup.closure {x : data.K |
      x ∈ QAt data.Γ data.criticalPath.firstStep ∧ x ^ 2 = 1} =
        QAt data.Γ data.criticalPath.firstStep := by
    rw [hQeq]
    exact Subgroup.quaternion_central_product_involutions_generate V W hV hW hinter hcomm
  have hex : ∃ x : data.K,
      x ∈ QAt data.Γ data.criticalPath.firstStep ∧ x ^ 2 = 1 ∧ x ∉ B0 := by
    by_contra! hnone
    apply hQnle
    rw [← hgen]
    exact (Subgroup.closure_le _).mpr (fun x hx => hnone x hx.1 hx.2)
  obtain ⟨x, hxQ, hx2, hxB⟩ := hex
  have hxS : data.embedding x ∈ (S : Subgroup G) :=
    mapped_vertex_core data data.criticalPath.firstStep hSPb ⟨x, hxQ, rfl⟩
  let xS : S := ⟨data.embedding x, hxS⟩
  have hxU : xS ∉ U := by
    intro h
    rw [hUmap] at h
    obtain ⟨y, hy, heq⟩ := h
    exact hxB (data.embedding_injective heq ▸ hy)
  refine ⟨xS, orderOf_eq_prime ?_ ?_, hxU⟩
  · apply Subtype.ext
    change data.embedding x ^ 2 = 1
    rw [← map_pow, hx2, map_one]
  · intro heq
    exact hxU (heq ▸ U.one_mem)

/-- The canonical subgroup has index exactly two. -/
public theorem gTwo_card64_transfer_index
    {G : Type*} [Group G] [Finite G] (data : GTwoTwoDerivedTypeData G)
    (hcard : Nat.card data.sylowIntersection = 64) :
    (gTwoCard64TransferSubgroup data).index = 2 :=
  (gTwo_card64_transfer_structure data hcard).2.1

/-- An actual involution of the distinguished Sylow lies outside the canonical subgroup. -/
public theorem gTwo_card64_outside_involution
    {G : Type*} [Group G] [Finite G] (data : GTwoTwoDerivedTypeData G)
    (hcard : Nat.card data.sylowIntersection = 64) :
    ∃ t : data.sylowIntersection, orderOf t = 2 ∧ t ∉ gTwoCard64TransferSubgroup data :=
  (gTwo_card64_transfer_structure data hcard).2.2

/-- The initial core supplies an inverter outside the canonical transfer subgroup. -/
public theorem gTwo_card64_initial_inverter_outside_transfer
    {G : Type*} [Group G] [Finite G] (data : GTwoTwoDerivedTypeData G)
    (hcard : Nat.card data.sylowIntersection = 64) :
    letI := data.groupK
    letI := data.finiteK
    ∃ t : data.sylowIntersection,
      (t : G) ∈ (QAt data.Γ data.criticalPath.a).map data.embedding ∧
      t ∉ gTwoCard64TransferSubgroup data ∧
      ∀ x ∈ (twoCoreIn (EAt data.Γ data.criticalPath.a)).map data.embedding,
        (t : G) * x * (t : G)⁻¹ = x⁻¹ := by
  let := data.groupK
  let := data.finiteK
  let S := data.sylowIntersection
  let A0 := twoCoreIn (EAt data.Γ data.criticalPath.a)
  let R0 := QAt data.Γ data.criticalPath.firstStep ⊓ EAt data.Γ data.criticalPath.firstStep
  let A := (A0.map data.embedding).subgroupOf (S : Subgroup G)
  let R := (R0.map data.embedding).subgroupOf (S : Subgroup G)
  have hSPa : (S : Subgroup G) ≤ (GAt data.Γ data.criticalPath.a).map data.embedding := by
    rw [← data.intersection_eq]; exact inf_le_left
  have hSPb : (S : Subgroup G) ≤ (GAt data.Γ data.criticalPath.firstStep).map data.embedding := by
    rw [← data.intersection_eq]; exact inf_le_right
  obtain ⟨hAmS, _⟩ := mapped_residual_core data data.criticalPath.a hSPa
  have hRf : R0.map data.embedding ≤ (S : Subgroup G) ∧ R.Normal := by
    dsimp [R, R0]
    rw [quaternion_factor_eq_residual_core data]
    exact mapped_residual_core data data.criticalPath.firstStep hSPb
  obtain ⟨hRmS, hRN⟩ := hRf
  let := hRN
  have hA : Nonempty (A ≃* C4 × C4) := by
    obtain ⟨e⟩ := data.caseA.twoCore_model
    exact ⟨((Subgroup.subgroupOfEquivOfLe hAmS).trans
      (A0.equivMapOfInjective data.embedding data.embedding_injective).symm).trans e⟩
  have hR : Nonempty (R ≃* Q8) := by
    obtain ⟨e⟩ := data.caseA.next_twoCore.2
    exact ⟨((Subgroup.subgroupOfEquivOfLe hRmS).trans
      (R0.equivMapOfInjective data.embedding data.embedding_injective).symm).trans e⟩
  obtain ⟨t, htQ, _, hinv, _⟩ := gTwo_card64_outside_inverter data hcard
  have htS : data.embedding t ∈ (S : Subgroup G) :=
    mapped_vertex_core data data.criticalPath.a hSPa ⟨t, htQ, rfl⟩
  let tS : S := ⟨data.embedding t, htS⟩
  have htInv : ∀ x ∈ A0.map data.embedding,
      (tS : G) * x * (tS : G)⁻¹ = x⁻¹ := by
    rintro x ⟨y, hy, rfl⟩
    change data.embedding t * data.embedding y * (data.embedding t)⁻¹ = _
    rw [← map_inv, ← map_mul, ← map_mul, hinv y hy, map_inv]
  refine ⟨tS, ⟨t, htQ, rfl⟩, ?_, htInv⟩
  have hUeq : gTwoCard64TransferSubgroup data = A ⊔ R :=
    Subgroup.subgroupOf_sup hAmS hRmS
  rw [hUeq]
  exact Subgroup.inverter_not_mem_c4_square_sup_quaternion A R hA hR tS
    (fun x hx => Subtype.ext (htInv x hx))

end Stellmacher.Recognition
