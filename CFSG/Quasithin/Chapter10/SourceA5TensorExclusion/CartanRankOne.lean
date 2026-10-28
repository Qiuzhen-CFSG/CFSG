module

public import CFSG.Quasithin.Chapter10.SourceA5TensorExclusion.CartanNormalization
public import CFSG.Quasithin.Chapter10.SourceA5TensorExclusion.OldCartanOrbit
public import CFSG.Quasithin.Chapter10.SourceA5TensorExclusion.OldComponentLocal
public import Theory.SpecificGroups.PSL2.PrimeCartanNormalizer

/-!
# Rank-one Cartan containers for the original tensor line

Retain the original H-star member, its old residual K = O²(H), and the
literal singular tensor line. A containing C-component J in its normalizer
is normalized by the elementary cubic Cartan: SQTK gives orbit size at most
two. Its two-core lies in T, so normalizes K. The three-rank-one action
bound then proves Cartan normalization of K whenever J/O₂(J) is centerless
with two-group outer automorphisms.

The tensor model supplies a nontrivial H-fixed involution in the line, so
cubic irreducibility makes K centralize the entire line. The final consumers
apply this conclusion to the actual overgroup residual and component product.
The prime-field PSL₂ row supplies the model inputs from existing coverage.

Source: Aschbacher–Smith 9.3.1 and 9.3.5, printed pp.732–733.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter10.SourceA5TensorModel
open Chapter3.Section02
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  {D : FundamentalSetup KnownSimple.IsKnownSimple T L}
  {e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5)}
  (m : SourceA5TensorModel D e)

private theorem cubic_normalizes_cComponent
    {X : Type*} [Group X] [Finite X]
    (hX : IsSQTK KnownSimple.IsKnownSimple X) (A J : Subgroup X)
    (hA : IsPGroup 3 A) (hJ : J.IsCComponent) : A ≤ normalizer (J : Set X) := by
  rcases Chapter1.Section02.component_normal_or_index_two_source hX hJ with hn | hi
  · let := hn
    exact le_normalizer_of_normal
  · let N := normalizer (J : Set X)
    let : N.Normal := normal_of_index_eq_two hi
    let q := QuotientGroup.mk' N
    have hp : IsPGroup 2 (X ⧸ N) := IsPGroup.of_card (n := 1) (by
      change N.index = 2 ^ 1
      simpa only [pow_one] using hi)
    have hb : A.map q = ⊥ := disjoint_self.mp
      ((hA.map q).disjoint_of_coprime (hp.to_subgroup _) (by decide))
    simpa only [q,QuotientGroup.ker_mk'] using (Subgroup.map_eq_bot_iff A).mp hb

/-- Source rank-one normalization uses the original residual and the actual
line normalizer; normalization of the containing component is derived. -/
theorem cartan_normalizes_old_residual_of_rank_one
    {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G) D.maximalLocal)
    (eK : ((pResidual 2 H).map H.subtype ⧸
      pCore 2 ((pResidual 2 H).map H.subtype)) ≃* alternatingGroup (Fin 5))
    (A B J : Subgroup G) [IsElementaryAbelian 3 A]
    (hJU : J ≤ normalizer (m.tensorLine : Set G))
    (hJ : (J.subgroupOf (normalizer (m.tensorLine : Set G))).IsCComponent)
    (hKJ : (pResidual 2 H).map H.subtype ≤ J)
    (hBA : B ≤ A) (hBK : B ≤ (pResidual 2 H).map H.subtype) (hB : Nat.card B = 3)
    (hAU : A ≤ normalizer (m.tensorLine : Set G))
    (hr : primeRank 3 J ≤ 1) (hz : center (J ⧸ pCore 2 J) = ⊥)
    (hout : IsPGroup 2 (MulAut.Outer (J ⧸ pCore 2 J))) :
    A ≤ normalizer ((pResidual 2 H).map H.subtype : Set G) := by
  let K := (pResidual 2 H).map H.subtype
  let N := normalizer (m.tensorLine : Set G)
  let := Chapter1.mem_L_isPerfect (source_hstar_residual_mem_local_of_a5 hH eK)
  have hN := D.simpleQTKE.twoLocal_sqtk (show IsTwoLocal N from
    ⟨m.tensorLine,m.tensorLine_ne_bot,IsPGroup.of_card (n := 2) m.card_tensorLine,rfl⟩)
  have hnJ := cubic_normalizes_cComponent hN (A.subgroupOf N) (J.subgroupOf N)
    (IsElementaryAbelian.isPGroup 3 A).comap_subtype hJ
  rw [←subgroupOf_normalizer_eq hJU] at hnJ
  have hAJ : A ≤ normalizer (J : Set G) := fun a ha =>
    hnJ (show (⟨a,hAU ha⟩ : N) ∈ A.subgroupOf N from ha)
  have hQN : J.pCoreIn 2 ≤ N.pCoreIn 2 := by
    have hh := map_mono (f := N.subtype) (pCoreIn_le_of_subnormal 2 hJ.subnormal)
    rw [map_pCoreIn_of_injective 2 _ N.subtype N.subtype_injective,
      map_subgroupOf_eq_of_le hJU] at hh
    exact hh
  have hQT : J.pCoreIn 2 ≤ (T : Subgroup G) :=
    hQN.trans ((pCoreIn_le_sylow N (T.subtype m.tensorLine_normalized)).trans_eq
      (map_subgroupOf_eq_of_le m.tensorLine_normalized))
  exact CubicCoreQuotientNormalizer.normalizes_of_rank_one K J A B hKJ hAJ hBA hBK
    (hQT.trans (hH.1.1.2.trans (le_normalizer_embedded_pResidual 2 H))) hB hz hout hr

/-- The original H-fixed involution and actual cubic orbit discharge the
fixed-vector and irreducibility inputs in source 9.3.1. -/
theorem cartan_rank_one_normalizes_and_centralizes_tensorLine
    {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G) D.maximalLocal)
    (eK : ((pResidual 2 H).map H.subtype ⧸
      pCore 2 ((pResidual 2 H).map H.subtype)) ≃* alternatingGroup (Fin 5))
    (A B J : Subgroup G) [IsElementaryAbelian 3 A]
    (hJU : J ≤ normalizer (m.tensorLine : Set G))
    (hJ : (J.subgroupOf (normalizer (m.tensorLine : Set G))).IsCComponent)
    (hKJ : (pResidual 2 H).map H.subtype ≤ J)
    (hBA : B ≤ A) (hBK : B ≤ (pResidual 2 H).map H.subtype) (hB : Nat.card B = 3)
    (hAU : A ≤ normalizer (m.tensorLine : Set G))
    (hr : primeRank 3 J ≤ 1) (hz : center (J ⧸ pCore 2 J) = ⊥)
    (hout : IsPGroup 2 (MulAut.Outer (J ⧸ pCore 2 J)))
    (d : G) (hdA : d ∈ A) (hd3 : d ^ 3 = 1)
    (hdC : d ∉ centralizer (m.tensorLine : Set G)) :
    A ≤ normalizer ((pResidual 2 H).map H.subtype : Set G) ∧
      (pResidual 2 H).map H.subtype ≤ centralizer (m.tensorLine : Set G) := by
  have hn := m.cartan_normalizes_old_residual_of_rank_one hH eK A B J
    hJU hJ hKJ hBA hBK hB hAU hr hz hout
  obtain ⟨z,hz2,hzU,hzT⟩ := m.exists_central_involution_tensorLine
  have hzOmega : z ∈ Stellmacher.omegaOneCenterAmbient (T : Subgroup G) :=
    (Stellmacher.mem_omegaOneCenterAmbient_iff _ _).mpr
      ⟨m.tensorLine_le_sylow hzU,hz2 ▸ pow_orderOf_eq_one z,hzT⟩
  refine ⟨hn,source_hstar_residual_centralizes_irreducible_line H m.tensorLine A hAU
    (m.tensorLine_cartan_irreducible A hAU d hdA hd3 hdC) hn z ?_ hzU ?_⟩
  · intro he
    simp [he] at hz2
  · intro h hh
    exact ((m.hstar_centralizes_sylowOmega hH) hh z hzOmega).symm

/-- The rank-one row supplies the actual component-product consumer.
Tensor geometry also discharges core centralization and the fixed seed. -/
theorem cartan_rank_one_tensor_pair_component_product
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G) D.maximalLocal)
    (eK : ((pResidual 2 H).map H.subtype ⧸
      pCore 2 ((pResidual 2 H).map H.subtype)) ≃* alternatingGroup (Fin 5))
    (A B J : Subgroup G) [IsElementaryAbelian 3 A]
    (hJU : J ≤ normalizer (m.tensorLine : Set G))
    (hJ : (J.subgroupOf (normalizer (m.tensorLine : Set G))).IsCComponent)
    (hKJ : (pResidual 2 H).map H.subtype ≤ J)
    (hBA : B ≤ A) (hBK : B ≤ (pResidual 2 H).map H.subtype) (hB : Nat.card B = 3)
    (hAU : A ≤ normalizer (m.tensorLine : Set G))
    (hr : primeRank 3 J ≤ 1) (hz : center (J ⧸ pCore 2 J) = ⊥)
    (hout : IsPGroup 2 (MulAut.Outer (J ⧸ pCore 2 J)))
    (d : G) (hdA : d ∈ A) (hd3 : d ^ 3 = 1)
    (hdC : d ∉ centralizer (m.tensorLine : Set G))
    (hSyl : Chapter1.IsSylowIn 2 ((T : Subgroup G) ⊓ normalizer (L : Set G))
      ((pResidual 2 H).map H.subtype ⊔ ((T : Subgroup G) ⊓ normalizer (L : Set G))))
    (E : Subgroup G) (hcore : pCore 2 E ≠ ⊥)
    (hgen : E = (L ⊔ (pResidual 2 H).map H.subtype) ⊔
      ((T : Subgroup G) ⊓ normalizer (L : Set G)))
    (hmove : ¬ (pResidual 2 H).map H.subtype ≤ centralizer (m.tensorPlane : Set G)) :
    (pResidual 2 E).IsCComponent ∧
      L.subgroupOf E ≤ pResidual 2 E ∧
      ((pResidual 2 H).map H.subtype).subgroupOf E ≤ pResidual 2 E ∧
      ∀ g : E, ∃ k ∈ pResidual 2 E,
        ∃ r ∈ (((T : Subgroup G) ⊓ normalizer (L : Set G)).subgroupOf E), k * r = g := by
  have hc := (m.cartan_rank_one_normalizes_and_centralizes_tensorLine hH eK A B J
    hJU hJ hKJ hBA hBK hB hAU hr hz hout d hdA hd3 hdC).2
  have hl := m.old_residual_mem_local_at_stabilizer hn hH eK hSyl
  have hEout : ¬ E ≤ D.maximalLocal := by
    intro he
    exact source_hstar_residual_not_le (le_normalizer_componentOrbit L T) hH
      ((hgen ▸ le_sup_of_le_left le_sup_right).trans he)
  exact source_a5_tensor_pair_component_product D e hn E ((pResidual 2 H).map H.subtype)
    m.tensorLine hcore hgen hEout hl m.component_core_centralizes_tensorPlane hc hmove

/-- The proved odd prime-field PSL₂ automorphism theorem discharges the
center and outer-group premises for the original rank-one container. -/
theorem cartan_primePSL2_normalizes_and_centralizes_tensorLine
    {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G) D.maximalLocal)
    (eK : ((pResidual 2 H).map H.subtype ⧸
      pCore 2 ((pResidual 2 H).map H.subtype)) ≃* alternatingGroup (Fin 5))
    (A B J : Subgroup G) [IsElementaryAbelian 3 A]
    (hJU : J ≤ normalizer (m.tensorLine : Set G))
    (hJ : (J.subgroupOf (normalizer (m.tensorLine : Set G))).IsCComponent)
    (hKJ : (pResidual 2 H).map H.subtype ≤ J)
    (hBA : B ≤ A) (hBK : B ≤ (pResidual 2 H).map H.subtype) (hB : Nat.card B = 3)
    (hAU : A ≤ normalizer (m.tensorLine : Set G)) (hr : primeRank 3 J ≤ 1)
    {F : Type*} [Field F] [Finite F] {p : ℕ}
    (hp : p.Prime) (ho : Odd p) (hF : Nat.card F = p)
    (eJ : (J ⧸ pCore 2 J) ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) F)
    (d : G) (hdA : d ∈ A) (hd3 : d ^ 3 = 1)
    (hdC : d ∉ centralizer (m.tensorLine : Set G)) :
    A ≤ normalizer ((pResidual 2 H).map H.subtype : Set G) ∧
      (pResidual 2 H).map H.subtype ≤ centralizer (m.tensorLine : Set G) := by
  obtain ⟨hz,hout⟩ := Theory.PSL2.primeField_center_outer_of_equiv hp ho hF eJ
  exact m.cartan_rank_one_normalizes_and_centralizes_tensorLine hH eK A B J
    hJU hJ hKJ hBA hBK hB hAU hr hz hout d hdA hd3 hdC

/-- The odd prime-field PSL₂ row applied to the literal new overgroup. -/
theorem cartan_primePSL2_tensor_pair_component_product
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G) D.maximalLocal)
    (eK : ((pResidual 2 H).map H.subtype ⧸
      pCore 2 ((pResidual 2 H).map H.subtype)) ≃* alternatingGroup (Fin 5))
    (A B J : Subgroup G) [IsElementaryAbelian 3 A]
    (hJU : J ≤ normalizer (m.tensorLine : Set G))
    (hJ : (J.subgroupOf (normalizer (m.tensorLine : Set G))).IsCComponent)
    (hKJ : (pResidual 2 H).map H.subtype ≤ J)
    (hBA : B ≤ A) (hBK : B ≤ (pResidual 2 H).map H.subtype) (hB : Nat.card B = 3)
    (hAU : A ≤ normalizer (m.tensorLine : Set G)) (hr : primeRank 3 J ≤ 1)
    {F : Type*} [Field F] [Finite F] {p : ℕ}
    (hp : p.Prime) (ho : Odd p) (hF : Nat.card F = p)
    (eJ : (J ⧸ pCore 2 J) ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) F)
    (d : G) (hdA : d ∈ A) (hd3 : d ^ 3 = 1)
    (hdC : d ∉ centralizer (m.tensorLine : Set G))
    (hSyl : Chapter1.IsSylowIn 2 ((T : Subgroup G) ⊓ normalizer (L : Set G))
      ((pResidual 2 H).map H.subtype ⊔ ((T : Subgroup G) ⊓ normalizer (L : Set G))))
    (E : Subgroup G) (hcore : pCore 2 E ≠ ⊥)
    (hgen : E = (L ⊔ (pResidual 2 H).map H.subtype) ⊔
      ((T : Subgroup G) ⊓ normalizer (L : Set G)))
    (hmove : ¬ (pResidual 2 H).map H.subtype ≤ centralizer (m.tensorPlane : Set G)) :
    (pResidual 2 E).IsCComponent ∧
      L.subgroupOf E ≤ pResidual 2 E ∧
      ((pResidual 2 H).map H.subtype).subgroupOf E ≤ pResidual 2 E ∧
      ∀ g : E, ∃ k ∈ pResidual 2 E,
        ∃ r ∈ (((T : Subgroup G) ⊓ normalizer (L : Set G)).subgroupOf E), k * r = g := by
  obtain ⟨hz,hout⟩ := Theory.PSL2.primeField_center_outer_of_equiv hp ho hF eJ
  exact m.cartan_rank_one_tensor_pair_component_product hn hH eK A B J
    hJU hJ hKJ hBA hBK hB hAU hr hz hout d hdA hd3 hdC hSyl E hcore hgen hmove

end CFSG.Quasithin.Chapter10.SourceA5TensorModel
