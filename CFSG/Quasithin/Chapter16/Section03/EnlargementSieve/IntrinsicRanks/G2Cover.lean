module

public import CFSG.Quasithin.Chapter16.Section03.EnlargementSieve.Contracts
public import CFSG.Quasithin.Chapter16.Section03.EnlargementSieve.Geometry
public import CFSG.Quasithin.Chapter16.Section03.EnlargementSieve.Rank
public import CFSG.Quasithin.Chapter16.Section03.EnlargementSieve.IntrinsicRanks.Bounds
public import Theory.AtlasPort.LinearGroups.G2.LongRootPlaneLift
public import Theory.AtlasPort.LinearGroups.G2.ShortRootFieldWitness
public import Theory.GroupTheory.DoubleCoverCentralizer.Basic
public import Theory.GroupTheory.PerfectNormalizerLift
public import Theory.GroupAction.PerfectCentralQuotient.ComponentNormalizer
public import Theory.GroupTheory.GeneralizedFitting.QuasisimpleCore

/-!
# The double-G₂(4) enlargement

The actual quotient of the enlargement is identified with the split-octonion
G₂(4) model. Its long-root plane has order sixteen and consists of
two-central involutions away from the identity. The earlier I.2.2(5a)
lifting statement therefore gives rank five in the enlargement.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
16.3.9, printed pp.1180–1181. For the actual field action on K/Z(K),
C(1) is a fixed non-two-central short-root involution. I.2.2(5b) supplies
its order-four lift. The component's quotient image is the fixed perfect
residual, and perfect-subgroup normalizer transport makes the lift normalize
L itself. The supplied ambient center identity then identifies its square
with t.

The earlier lifting clauses I.2.2(5a,b), the compatible field action and
L/O₂(L) identification of 16.1.7(3a), and the exact O² fixed-subgroup
identification of 16.1.4(4) remain explicit source inputs. The latter is
not confused with O₂ or the solvable residual. Quasisimplicity of the
binary derived model is inherited from the actual component quotient;
no independent simplicity or automorphism-rank bound is assumed.
-/

public section

namespace CFSG.Quasithin.Chapter16.EnlargementSieve.IntrinsicRanks.G2Cover
open Subgroup Theory.GroupTheory
variable {G : Type*} [Group G] [Finite G]
variable {F : Type*} [Field F] [Finite F] [CharP F 2]

theorem enlargement_rank_ge_five (t : G) (L : Subgroup G)
    (e : (enlargement t L ⧸ center (enlargement t L)) ≃* Atlas.G2.Model F)
    (hF : Nat.card F = 4) (hZ : Nat.card (center (enlargement t L)) = 2)
    (hlift : Atlas.G2.LongRootPlaneLift.CentralInvolutionLifting (enlargement t L)) :
    5 ≤ primeRank 2 (enlargement t L) :=
  Atlas.G2.LongRootPlaneLift.rank_ge_five e hF hZ hlift

end CFSG.Quasithin.Chapter16.EnlargementSieve.IntrinsicRanks.G2Cover

namespace CFSG.Quasithin.Chapter16.EnlargementSieve.IntrinsicRanks.G2Cover
open Subgroup Theory.GroupTheory
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
private theorem component_in_fixed (K L : Subgroup G) (z : G)
    (hz : z ∈ normalizer K)
    (hL : ComponentTransfer.IsComponentIn L (ComponentTransfer.centralizerIn K z)) :
    Theory.GroupTheory.IsComponentIn (L.subgroupOf K)
      (K.normalizerMonoidHom ⟨z,hz⟩).fixedSubgroup := by
  let C := ComponentTransfer.centralizerIn K z
  have hCK : C ≤ K := inf_le_left
  have he : (K.normalizerMonoidHom ⟨z,hz⟩).fixedSubgroup = C.subgroupOf K := by
    ext x
    rw [MulAut.mem_fixedSubgroup]
    change (K.normalizerMonoidHom ⟨z,hz⟩) x = x ↔ (x : G) ∈ C
    rw [Subtype.ext_iff]
    change z * (x : G) * z⁻¹ = x ↔ _
    change _ ↔ (x : G) ∈ K ∧ x.val ∈ involutionCentralizer z
    rw [and_iff_right x.property, mem_centralizer_singleton_iff]
    exact ⟨fun h => (mul_inv_eq_iff_eq_mul.mp h).symm,
      fun h => mul_inv_eq_iff_eq_mul.mpr h.symm⟩
  rw [he]
  have hLC : L.subgroupOf K ≤ C.subgroupOf K := fun _ hx => hL.1 hx
  refine ⟨hLC, ?_, ?_⟩
  · have hsub := hL.2.1.comap (subgroupOfEquivOfLe hCK).toMonoidHom
    exact hsub
  · let := hL.quasisimple
    let : IsQuasisimple (L.subgroupOf K) :=
      IsQuasisimple.of_mulEquiv (subgroupOfEquivOfLe (hL.1.trans hCK)).symm
    exact IsQuasisimple.of_mulEquiv (subgroupOfEquivOfLe hLC).symm

private theorem square_eq_of_order_four (K : Subgroup G) (t : G)
    (ht : orderOf t = 2) (hZ : (center K).map K.subtype = zpowers t)
    (u : K) (hu : orderOf u = 4) (hsq : u ^ 2 ∈ center K) : (u : G) ^ 2 = t := by
  classical
  have hm : (u : G) ^ 2 ∈ zpowers t := hZ ▸ mem_map_of_mem K.subtype hsq
  have hn : (u : G) ^ 2 ≠ 1 := by
    intro he
    have hh : u ^ 2 = 1 := Subtype.ext he
    have hd := orderOf_dvd_of_pow_eq_one hh
    rw [hu] at hd
    norm_num at hd
  rw [mem_zpowers_iff_mem_range_orderOf, ht] at hm
  obtain ⟨n,hn',he⟩ := Finset.mem_image.mp hm
  have hlt : n < 2 := Finset.mem_range.mp hn'
  interval_cases n
  · exact (hn (by simpa using he.symm)).elim
  · simpa using he.symm

private theorem sylowCentral_of_twoCentral {H : Type*} [Group H]
    {v : H} (hv : orderOf v = 2) (hc : DoubleCoverCentralizer.TwoCentral v) :
    IsSylowCentralInvolution v := by
  obtain ⟨S,hvS,hc⟩ := hc
  refine ⟨hv,S,hvS,?_⟩
  intro y hy
  apply mem_centralizer_singleton_iff.mpr
  exact congrArg Subtype.val (mem_center_iff.mp hc (⟨y,hy⟩ : S))

variable {F : Type*} [Field F] [Finite F] [CharP F 2]

/-- The short-root lift normalizes the actual component, once the earlier
field-centralizer residual has been identified as quasisimple. -/
theorem normalizerSquareWitness_of_field_residual
    (K L : Subgroup G) (z t : G) (hz : z ∈ normalizer K)
    (hL : ComponentTransfer.IsComponentIn L (ComponentTransfer.centralizerIn K z))
    (e : K ⧸ center K ≃* Atlas.G2.Model F) (σ : F ≃+* F)
    (ha : MulAut.centralQuotientAction e (K.normalizerMonoidHom ⟨z,hz⟩) =
      Atlas.G2.LieAutomorphismExtensions.fieldAction σ)
    [IsQuasisimple (MulAut.fixedPerfectResidual
      (Atlas.G2.LieAutomorphismExtensions.fieldAction σ))]
    (hlift : DoubleCoverCentralizer.NonTwoCentralInvolutionLifting K)
    (ht : orderOf t = 2) (hZ : (center K).map K.subtype = zpowers t) :
    NormalizerSquareWitness L t := by
  let v := Atlas.G2.rootC (1 : F)
  have hv : orderOf v = 2 := Atlas.G2.ShortRootProducts.shortRoot_order
    ⟨1,one_ne_zero,1,by simp [v]⟩
  have hvq : orderOf (e.symm v) = 2 := (e.symm.orderOf_eq v).trans hv
  have hmark : ¬ DoubleCoverCentralizer.TwoCentral (e.symm v) := by
    intro hc
    have hh := (sylowCentral_of_twoCentral hvq hc).map e
    rw [e.apply_symm_apply] at hh
    exact Atlas.G2.ShortRootFieldWitness.rootC_one_not_twoCentral hh
  obtain ⟨u,hu,hu4⟩ := hlift _ hvq hmark
  have hcomp := component_in_fixed K L z hz hL
  let : IsQuasisimple (MulAut.fixedPerfectResidual
      (MulAut.centralQuotientAction e (K.normalizerMonoidHom ⟨z,hz⟩))) := by
    rw [ha]
    infer_instance
  have hfix : e (QuotientGroup.mk' (center K) u) ∈
      (MulAut.centralQuotientAction e (K.normalizerMonoidHom ⟨z,hz⟩)).fixedSubgroup := by
    rw [hu,e.apply_symm_apply,ha]
    exact Atlas.G2.ShortRootFieldWitness.rootC_one_fixed σ
  have hn := MulAut.fixed_quotient_normalizes_component e
    (K.normalizerMonoidHom ⟨z,hz⟩) (L.subgroupOf K) hcomp u hfix
  have hLK : L ≤ K := hL.1.trans inf_le_left
  have hnG : (u : G) ∈ normalizer L := by
    have hh := (L.subgroupOf K).le_normalizer_map K.subtype
      (mem_map_of_mem K.subtype hn)
    rwa [map_subgroupOf_eq_of_le hLK] at hh
  have hsq : u ^ 2 ∈ center K := by
    apply (QuotientGroup.eq_one_iff _).mp
    change QuotientGroup.mk' (center K) (u ^ 2) = 1
    rw [map_pow,hu,← hvq,pow_orderOf_eq_one]
  exact ⟨u,(orderOf_injective K.subtype K.subtype_injective u).trans hu4,
    hnG,square_eq_of_order_four K t ht hZ u hu4 hsq⟩

end CFSG.Quasithin.Chapter16.EnlargementSieve.IntrinsicRanks.G2Cover

namespace CFSG.Quasithin.Chapter16.EnlargementSieve.IntrinsicRanks.G2Cover
open Subgroup Theory.GroupTheory
variable {G : Type*} [Group G] [Finite G]
variable {F : Type*} [Field F] [Finite F] [CharP F 2]

/-- The actual field case of 16.1.7(3a), with its earlier 16.1.4(4)
fixed-two-residual identification, supplies the square witness. The two
source identifications concern the full indicated quotients; neither
assumes normalization of the chosen lift. -/
theorem normalizerSquareWitness_of_field_case
    (K L : Subgroup G) (z t : G) (hz : z ∈ normalizer K)
    (hL : ComponentTransfer.IsComponentIn L (ComponentTransfer.centralizerIn K z))
    (e : K ⧸ center K ≃* Atlas.G2.Model F) (σ : F ≃+* F)
    (ha : MulAut.centralQuotientAction e (K.normalizerMonoidHom ⟨z,hz⟩) =
      Atlas.G2.LieAutomorphismExtensions.fieldAction σ)
    (eL : (L ⧸ pCore 2 L) ≃* commutator (Atlas.G2.Model (ZMod 2)))
    (eFixed : pResidual 2 (Atlas.G2.LieAutomorphismExtensions.fieldAction σ).fixedSubgroup ≃*
      commutator (Atlas.G2.Model (ZMod 2)))
    (hlift : DoubleCoverCentralizer.NonTwoCentralInvolutionLifting K)
    (ht : orderOf t = 2) (hZ : (center K).map K.subtype = zpowers t) :
    NormalizerSquareWitness L t := by
  let := hL.quasisimple
  let : IsSimpleGroup (L ⧸ center L) := IsQuasisimple.simple
  let : Nontrivial L := (QuotientGroup.mk'_surjective (center L)).nontrivial
  have hpc : pCore 2 L ≠ ⊤ := by
    intro he
    have hc : center L = ⊤ := top_unique (he ▸ IsQuasisimple.pCore_le_center 2)
    exact Group.IsPerfect.not_isMulCommutative L (center_eq_top_iff.mp hc)
  let : Nontrivial (L ⧸ pCore 2 L) := (QuotientGroup.nontrivial_iff).mpr hpc
  let : IsQuasisimple (L ⧸ pCore 2 L) :=
    IsQuasisimple.of_surjective (QuotientGroup.mk' (pCore 2 L))
      (QuotientGroup.mk'_surjective _)
  let : IsQuasisimple (commutator (Atlas.G2.Model (ZMod 2))) :=
    IsQuasisimple.of_mulEquiv eL
  let : IsQuasisimple
      (pResidual 2 (Atlas.G2.LieAutomorphismExtensions.fieldAction σ).fixedSubgroup) :=
    IsQuasisimple.of_mulEquiv eFixed.symm
  let := MulAut.fixedPerfectResidual_quasisimple_of_twoResidual
    (Atlas.G2.LieAutomorphismExtensions.fieldAction σ)
  exact normalizerSquareWitness_of_field_residual K L z t hz hL e σ ha hlift ht hZ

end CFSG.Quasithin.Chapter16.EnlargementSieve.IntrinsicRanks.G2Cover
