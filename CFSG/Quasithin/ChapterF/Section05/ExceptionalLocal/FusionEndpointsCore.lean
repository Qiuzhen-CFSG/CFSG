module
public import CFSG.Quasithin.ChapterF.Section05.ExceptionalLocal.FusionEndpointsTransport
public import CFSG.Quasithin.ChapterF.Section05.ExceptionalLocal.FusionEndpointsRoots
public import Theory.GroupTheory.PCoreProduct
public import Theory.GroupTheory.SymmetricFourModelCoreData
public import Theory.GroupTheory.SpecificGroups.SymmetricFourElementaryCentralizer
public import Theory.ElementaryAbelian.Injective
/-!
# The actual exceptional endpoint two-cores

The proved E₄ × S₄ identifications give elementary two-cores of order sixteen.
Their literal embeddings lie in the common graph-fixed Sylow subgroup.
Together with the root and graph involution in each core, this puts every
ambient centralizer in E₁; the elementary-sixteen calculation there proves
the self-centralizer statement without a FusionFacts premise.

The fixed-image identity for Dᵢ retains the ordinary endpoint range for the
source amalgam intersections. These are the endpoint inputs to F.5.3 and
the first normalizer conclusion of F.5.4 (Aschbacher--Smith, pp.300–301).
-/
noncomputable section
namespace CFSG.Quasithin.ChapterF.Section05.ExceptionalLocal
open Subgroup
open scoped IsMulCommutative
open GreenBook.LieModels.UnitaryFour
local notation "hn" => Nat.le_refl 1
local notation "C2" => Multiplicative (ZMod 2)
local notation "S4" => Equiv.Perm (Fin 4)
local notation "K4" => C2 × C2
local notation "Model" => K4 × S4

private instance binaryFour_elementary : IsElementaryAbelian 2 K4 where
  is_comm.comm := mul_comm
  exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr (by decide +kernel)
private theorem binaryFour_core : pCore 2 K4 = ⊤ := by
  apply top_unique
  exact le_sSup ⟨inferInstance, (IsElementaryAbelian.isPGroup 2 K4).of_equiv Subgroup.topEquiv.symm⟩
private theorem symmetricFour_core_data :
    IsElementaryAbelian 2 (pCore 2 S4) ∧ Nat.card (pCore 2 S4) = 4 := by
  obtain ⟨he,hc⟩ := symmetric_four_model_twoCore_data (Or.inl ⟨MulEquiv.refl S4⟩)
  refine ⟨he, ?_⟩
  rcases hc with hc | hc
  · exact hc.1
  · have : Nat.card S4 = 24 := by norm_num [Nat.card_eq_fintype_card,Fintype.card_perm,Nat.factorial]
    omega
private instance modelProduct_elementary : IsElementaryAbelian 2 (K4 × pCore 2 S4) where
  is_comm := by
    let := symmetricFour_core_data.1
    infer_instance
  exponent_dvd_p := by
    let := symmetricFour_core_data.1
    apply Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr
    intro a
    apply Prod.ext
    · exact Monoid.exponent_dvd_iff_forall_pow_eq_one.mp (IsElementaryAbelian.exponent_dvd_p 2 K4) a.1
    · exact Monoid.exponent_dvd_iff_forall_pow_eq_one.mp (IsElementaryAbelian.exponent_dvd_p 2 (pCore 2 S4)) a.2
private def modelCoreEquiv : pCore 2 Model ≃* K4 × pCore 2 S4 :=
  (MulEquiv.subgroupCongr ((pCore_prod 2).trans (by rw [binaryFour_core]))).trans
    (((⊤ : Subgroup K4).prodEquiv (pCore 2 S4)).trans
      (MulEquiv.prodCongr Subgroup.topEquiv (MulEquiv.refl _)))
private theorem model_core_data :
    IsElementaryAbelian 2 (pCore 2 Model) ∧ Nat.card (pCore 2 Model) = 16 := by
  refine ⟨IsElementaryAbelian.of_injective modelCoreEquiv.toMonoidHom modelCoreEquiv.injective, ?_⟩
  rw [Nat.card_congr modelCoreEquiv.toEquiv,Nat.card_prod,symmetricFour_core_data.2]
  norm_num [Nat.card_prod,Nat.card_eq_fintype_card]

variable {G G0 : Type*} [Group G] [Group G0]
variable (c : Theory.GroupTheory.RankTwoAmalgam.FaithfulCompletion
    (Extension.amalgam 1 hn) (G := G0)) (i : G0 →* G)
private def sourceACoreEquiv (hi : Function.Injective i) (b : Bool) :
    A c i b ≃* pCore 2 Model :=
  ((pCore 2 (E c i b)).equivMapOfInjective (E c i b).subtype (E c i b).subtype_injective).symm.trans
    (((source_E_equiv c i hi b).subgroupMap (pCore 2 (E c i b))).trans
      (MulEquiv.subgroupCongr (pCore_map_iso 2 (source_E_equiv c i hi b))))

public theorem source_A_elementary (hi : Function.Injective i) (b : Bool) :
    IsElementaryAbelian 2 (A c i b) := by
  let := model_core_data.1
  exact IsElementaryAbelian.of_injective (sourceACoreEquiv c i hi b).toMonoidHom
    (sourceACoreEquiv c i hi b).injective
public theorem source_A_card (hi : Function.Injective i) (b : Bool) : Nat.card (A c i b) = 16 :=
  (Nat.card_congr (sourceACoreEquiv c i hi b).toEquiv).trans model_core_data.2

public theorem Dendpoint_eq_range_inf_C (hi : Function.Injective i) (b : Bool) :
    Dendpoint c i b = (ordinaryMap c i b).range ⊓ C c i := by
  apply le_antisymm
  · rintro x ⟨a,ha,rfl⟩
    exact ⟨⟨a,rfl⟩,(Dendpoint_le_E c i b ⟨a,ha,rfl⟩).2⟩
  · rintro x ⟨⟨a,rfl⟩,ha⟩
    refine ⟨a, ?_, rfl⟩
    change ordinaryInclusion b a ∈ centralizer ({modelGraph b} : Set (modelEndpoint b))
    rw [mem_centralizer_singleton_iff]
    apply endpointMap_injective c i hi b
    rw [map_mul,map_mul,endpointMap_graph]
    exact mem_centralizer_singleton_iff.mp ha

/-- Both literal endpoint cores lie in the common graph-fixed Sylow subgroup. -/
public theorem source_A_le_TfImage (hi : Function.Injective i) (b : Bool) :
    A c i b ≤ TfImage c i := by
  obtain ⟨S,hS⟩ := source_Tf_sylow_of_endpoint_equiv c i hi b (source_E_equiv c i hi b)
  rw [← hS]
  exact pCoreIn_le_sylow _ S

variable [Finite G] (z : pointParabolic 1 hn) (h : Source.Hypotheses c i z)
include h
public theorem source_A_self_centralizer (b : Bool) :
    centralizer (A c i b : Set G) = A c i b := by
  let := source_A_elementary c i h.embedding_injective b
  have hAE : A c i b ≤ E c i false :=
    (source_A_le_TfImage c i h.embedding_injective b).trans (TfImage_le_E c i false)
  let J := (A c i b).subgroupOf (E c i false)
  let : IsElementaryAbelian 2 J := IsElementaryAbelian.subgroupOf hAE
  let e := source_E_equiv c i h.embedding_injective false
  let K := J.map e.toMonoidHom
  let : IsElementaryAbelian 2 K := IsElementaryAbelian.map _
  have hcard : Nat.card K = 16 := by
    rw [card_map_of_injective e.injective]
    exact (Nat.card_congr (subgroupOfEquivOfLe hAE).toEquiv).trans (source_A_card c i h.embedding_injective b)
  have hcentral : centralizer (K : Set Model) = K :=
    SymmetricFourElementary.centralizer_eq_of_elementary_card_sixteen K hcard
  apply le_antisymm _ (le_centralizer_iff_isMulCommutative.mpr inferInstance)
  intro x hx
  have hxE : x ∈ E c i false := source_centralizer_A_le_E_point c i z h b hx
  let y : E c i false := ⟨x,hxE⟩
  have hy : e y ∈ centralizer (K : Set Model) := by
    rintro _ ⟨a,ha,rfl⟩
    change e a * e y = e y * e a
    rw [←map_mul,←map_mul]
    apply congrArg e
    apply Subtype.ext
    exact mem_centralizer_iff.mp hx a.val ha
  rw [hcentral] at hy
  obtain ⟨a,ha,he⟩ := hy
  have heq : a = y := e.injective he
  change y ∈ J
  exact heq ▸ ha
end CFSG.Quasithin.ChapterF.Section05.ExceptionalLocal
