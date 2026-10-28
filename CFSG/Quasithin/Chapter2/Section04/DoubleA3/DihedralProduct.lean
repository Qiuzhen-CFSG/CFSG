module
public import CFSG.Quasithin.Chapter2.Section04.DoubleA3.PairFrattini
public import Theory.GroupTheory.SpecificGroups.DihedralEightRecognition
public import Theory.GroupTheory.MarkedInternalProduct
public import Theory.GroupTheory.NormalizedSupCard

/-!
# The actual dihedral factors in the paired-cubic Thompson subgroup

Each noncommuting pair of elementary four-groups generates a group of order
eight, hence D8. The four-module action makes the two factors commute;
cubic faithfulness and the factor center calculation make their product
disjoint from the elementary central factor. The resulting direct product
retains the original centralizer D and gives the order formula used in 2.4.36.

Source: Aschbacher–Smith, 2.4.30(4), printed p.547.
-/

@[expose] public section
open Subgroup Stellmacher
open scoped Pointwise
namespace CFSG.Quasithin.Chapter2.DoubleA3
open ChapterC.Section05.BlockAnalysis ChapterC.Section05.ConjugateSource
variable {G : Type*} [Group G] [Finite G] {M : Subgroup G}

private theorem dihedral_factor (U V : Subgroup G)
    [IsElementaryAbelian 2 U] [IsElementaryAbelian 2 V]
    (hU : Nat.card U = 4) (hV : Nat.card V = 4) (hI : Nat.card (U ⊓ V : Subgroup G) = 2)
    (hn : V ≤ normalizer (U : Set G)) (hnc : ¬ V ≤ centralizer (U : Set G)) :
    Nonempty ((U ⊔ V : Subgroup G) ≃* DihedralGroup 4) := by
  have hcard : Nat.card (U ⊔ V : Subgroup G) = 8 := by
    have hh := card_mul_eq_card_inf_mul_card_sup_of_normalizes U V hn
    rw [hU,hV,hI] at hh
    omega
  let U₀ := U.subgroupOf (U ⊔ V)
  let : IsElementaryAbelian 2 U₀ := IsElementaryAbelian.subgroupOf le_sup_left
  have hU₀ : Nat.card U₀ = 4 := (Nat.card_congr (subgroupOfEquivOfLe (show U ≤ U ⊔ V from le_sup_left)).toEquiv).trans hU
  apply dihedral_eight_of_noncentral_elementary_four hcard U₀ hU₀
  intro hc
  apply hnc
  intro v hv u hu
  have hh := hc (show (⟨u,mem_sup_left hu⟩ : (U ⊔ V : Subgroup G)) ∈ U₀ from hu)
  exact (congrArg Subtype.val ((mem_center_iff.mp hh) ⟨v,mem_sup_right hv⟩)).symm

namespace SourcePairCoordinates
variable {d : MinimalBlockSetup M} {T : Sylow 2 G} (c : SourcePairCoordinates d T)

 theorem factors_dihedral :
    Nonempty ((c.U₁ ⊔ c.V₁ : Subgroup G) ≃* DihedralGroup 4) ∧
      Nonempty ((c.U₂ ⊔ c.V₂ : Subgroup G) ≃* DihedralGroup 4) := by
  let : IsElementaryAbelian 2 c.U₁ := c.first.elementary
  let : IsElementaryAbelian 2 c.U₂ := c.second.elementary
  let : IsElementaryAbelian 2 c.V₁ := IsElementaryAbelian.map (MulAut.conj c.x⁻¹).toMonoidHom
  let : IsElementaryAbelian 2 c.V₂ := IsElementaryAbelian.map (MulAut.conj c.x⁻¹).toMonoidHom
  have hU₁ := c.first.cubic_module_card c.cubic_first
  have hU₂ := c.second.cubic_module_card c.cubic_second
  have hV₁ : Nat.card c.V₁ = 4 := by
    rw [V₁,card_map_of_injective (MulAut.conj c.x⁻¹).injective]
    exact hU₁
  have hV₂ : Nat.card c.V₂ = 4 := by
    rw [V₂,card_map_of_injective (MulAut.conj c.x⁻¹).injective]
    exact hU₂
  have hI₁ : Nat.card (c.U₁ ⊓ c.V₁ : Subgroup G) = 2 := c.first_fixed_line.2.1 ▸ c.first_fixed_line.1
  have hI₂ : Nat.card (c.U₂ ⊓ c.V₂ : Subgroup G) = 2 := c.second_fixed_line.2.1 ▸ c.second_fixed_line.1
  exact ⟨dihedral_factor _ _ hU₁ hV₁ hI₁
    ((c.first.conjugate_le (c.original.R_normal c.x_mem)).trans c.first.coordinates.normalizes) c.noncommuting,
    dihedral_factor _ _ hU₂ hV₂ hI₂
    ((c.second.conjugate_le (c.original.R_normal c.x_mem)).trans c.second.coordinates.normalizes)
    (RankOne.second_noncommuting c.orbit)⟩

 theorem factor_product :
    Disjoint (c.U₁ ⊔ c.V₁) (c.U₂ ⊔ c.V₂) ∧
      (c.U₁ ⊔ c.V₁) ≤ centralizer ((c.U₂ ⊔ c.V₂ : Subgroup G) : Set G) ∧
      Disjoint ((c.U₁ ⊔ c.V₁) ⊔ (c.U₂ ⊔ c.V₂)) c.D := by
  let F₁ := c.U₁ ⊔ c.V₁
  let F₂ := c.U₂ ⊔ c.V₂
  have hFC : F₁ ≤ centralizer (F₂ : Set G) :=
    commutator_eq_bot_iff_le_centralizer.mp (FourModuleOrbit.conjugate_factors_commute c.orbit.toInputs)
  have hZ₁ : F₁ ⊓ centralizer (F₁ : Set G) ≤ c.U₁ :=
    (c.first.conjugate_factor_structure (c.original.R_normal c.x_mem) c.noncommuting).2.2.2.2
  have hZ₂ : F₂ ⊓ centralizer (F₂ : Set G) ≤ c.U₂ :=
    (c.second.conjugate_factor_structure (c.original.R_normal c.x_mem)
      (RankOne.second_noncommuting c.orbit)).2.2.2.2
  have hdU : Disjoint c.U₁ c.U₂ := RankOne.cubic_module_disjoint c.cubic_first _
    ((map_subtype_le _).trans c.commute)
  have hdF : Disjoint F₁ F₂ := by
    apply disjoint_def.mpr
    intro z hz₁ hz₂
    exact disjoint_def.mp hdU (hZ₁ ⟨hz₁,(le_centralizer_iff.mp hFC) hz₂⟩)
      (hZ₂ ⟨hz₂,hFC hz₁⟩)
  refine ⟨hdF,hFC,disjoint_def.mpr ?_⟩
  intro z hz hzD
  have hm : z ∈ (F₁ : Set G) * (F₂ : Set G) := by
    rw [←coe_mul_of_left_le_normalizer_right F₁ F₂ (hFC.trans (Subgroup.centralizer_le_normalizer _))]
    exact hz
  obtain ⟨a,ha,b,hb,rfl⟩ := hm
  have hF₁R : F₁ ≤ sourceR d := c.product.2.1 ▸ (le_sup_left.trans le_sup_left)
  have hF₂R : F₂ ≤ sourceR d := c.product.2.1 ▸ (le_sup_right.trans le_sup_left)
  have habC := c.product.2.2.1 hzD
  have haC : a ∈ centralizer (F₁ : Set G) := by
    have hh := (centralizer (F₁ : Set G)).mul_mem
      ((centralizer_le hF₁R) habC) ((centralizer (F₁ : Set G)).inv_mem ((le_centralizer_iff.mp hFC) hb))
    simpa only [mul_inv_cancel_right] using hh
  have hbC : b ∈ centralizer (F₂ : Set G) := by
    have hh := (centralizer (F₂ : Set G)).mul_mem
      ((centralizer (F₂ : Set G)).inv_mem (hFC ha)) ((centralizer_le hF₂R) habC)
    simpa only [inv_mul_cancel_left] using hh
  exact disjoint_def.mp c.module_join_disjoint_residual_centralizer
    (mul_mem_sup (hZ₁ ⟨ha,haC⟩) (hZ₂ ⟨hb,hbC⟩)) hzD.2

 theorem thompson_dihedral_product : Nonempty (sourceR d ≃* c.D × (DihedralGroup 4 × DihedralGroup 4)) := by
  obtain ⟨e₁⟩ := c.factors_dihedral.1
  obtain ⟨e₂⟩ := c.factors_dihedral.2
  obtain ⟨eF,_,_⟩ := Theory.GroupTheory.exists_marked_internalProductEquiv
    ((c.U₁ ⊔ c.V₁) ⊔ (c.U₂ ⊔ c.V₂)) (c.U₁ ⊔ c.V₁) (c.U₂ ⊔ c.V₂)
    rfl c.factor_product.1 c.factor_product.2.1
  have hFR : ((c.U₁ ⊔ c.V₁) ⊔ (c.U₂ ⊔ c.V₂)) ≤ sourceR d := c.product.2.1 ▸ le_sup_left
  obtain ⟨eR,_,_⟩ := Theory.GroupTheory.exists_marked_internalProductEquiv
    (sourceR d) c.D ((c.U₁ ⊔ c.V₁) ⊔ (c.U₂ ⊔ c.V₂))
    ((sup_comm _ _).trans c.product.2.1.symm) c.factor_product.2.2.symm
    (c.product.2.2.1.trans (centralizer_le hFR))
  exact ⟨eR.trans ((MulEquiv.refl c.D).prodCongr (eF.trans (e₁.prodCongr e₂)))⟩

 theorem thompson_card : Nat.card (sourceR d) = Nat.card c.D * 64 := by
  obtain ⟨e⟩ := c.thompson_dihedral_product
  rw [Nat.card_congr e.toEquiv,Nat.card_prod,Nat.card_prod,DihedralGroup.nat_card]

end SourcePairCoordinates
end CFSG.Quasithin.Chapter2.DoubleA3
