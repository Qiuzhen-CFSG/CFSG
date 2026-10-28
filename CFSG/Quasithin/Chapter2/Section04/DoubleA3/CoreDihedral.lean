module
public import CFSG.Quasithin.Chapter2.Section04.DoubleA3.DihedralProduct
public import Theory.GroupTheory.PrimeRankElementary
public import Theory.ElementaryAbelian.Join

/-!
# Core and centralizer products for the paired cubic blocks

The actual elementary core splits as D times its two natural four-groups.
Comparing the two commuting complements to the first dihedral factor gives
C_R(L) isomorphic to D times D8, retaining the literal original centralizer.
The order formula forces D to vanish when the ambient Sylow two-rank is at
most four, supplying the rank specialization in the proof of 2.4.34.

Source: Aschbacher–Smith, 2.4.30, 2.4.34 and 2.4.36, printed pp.547–549.
-/

@[expose] public section
open Subgroup Stellmacher
open scoped Pointwise
namespace CFSG.Quasithin.Chapter2.DoubleA3
open ChapterC.Section05.BlockAnalysis ChapterC.Section05.ConjugateSource
variable {G : Type*} [Group G] [Finite G] {M : Subgroup G}

private theorem commuting_complements_equiv (R A B C : Subgroup G)
    (hAB : A ⊔ B = R) (hAC : A ⊔ C = R)
    (hdAB : Disjoint A B) (hdAC : Disjoint A C)
    (hcAB : A ≤ centralizer (B : Set G)) (hcAC : A ≤ centralizer (C : Set G)) :
    Nonempty (C ≃* B) := by
  obtain ⟨e,hAm,_⟩ := Theory.GroupTheory.exists_marked_internalProductEquiv R A B hAB hdAB hcAB
  obtain ⟨e',_,_⟩ := Theory.GroupTheory.exists_marked_internalProductEquiv R A C hAC hdAC hcAC
  have hCR : C ≤ R := hAC ▸ le_sup_right
  let f : C →* B := (MonoidHom.snd A B).comp (e.toMonoidHom.comp (inclusion hCR))
  have hi : Function.Injective f := by
    apply (MonoidHom.ker_eq_bot_iff f).mp
    apply bot_unique
    intro v hv
    have he : (e (inclusion hCR v)).2 = 1 := hv
    have hev : e (inclusion hCR v) ∈ (A.subgroupOf R).map e.toMonoidHom := by
      rw [hAm]
      exact ⟨mem_top _,he⟩
    obtain ⟨a,ha,hea⟩ := hev
    have haeq : a = inclusion hCR v := e.injective hea
    have hvA : (v : G) ∈ A := by
      have hha := haeq ▸ ha
      exact hha
    exact Subtype.ext (disjoint_def.mp hdAC hvA v.property)
  have hcard : Nat.card C = Nat.card B := by
    have h1 := Nat.card_congr e.toEquiv
    have h2 := Nat.card_congr e'.toEquiv
    rw [Nat.card_prod] at h1 h2
    exact Nat.eq_of_mul_eq_mul_left (Nat.card_pos (α := A)) (h2.symm.trans h1)
  exact ⟨MulEquiv.ofBijective f ((Nat.bijective_iff_injective_and_card f).mpr ⟨hi,hcard⟩)⟩

namespace SourcePairCoordinates
variable {d : MinimalBlockSetup M} {T : Sylow 2 G} (c : SourcePairCoordinates d T)

 theorem core_direct_product : Nonempty (twoCore d.H ≃* c.D × (c.U₁ × c.U₂)) := by
  have hUC : c.U₁ ≤ centralizer (c.U₂ : Set G) :=
    le_centralizer_iff.mp ((map_subtype_le _).trans (c.commute.trans (centralizer_le (map_subtype_le _))))
  have hdU : Disjoint c.U₁ c.U₂ := RankOne.cubic_module_disjoint c.cubic_first _
    ((map_subtype_le _).trans c.commute)
  have hdD : Disjoint (c.U₁ ⊔ c.U₂) c.D := c.module_join_disjoint_residual_centralizer.mono_right inf_le_right
  obtain ⟨eU,_,_⟩ := Theory.GroupTheory.exists_marked_internalProductEquiv
    (c.U₁ ⊔ c.U₂) c.U₁ c.U₂ rfl hdU hUC
  have hUR : c.U₁ ⊔ c.U₂ ≤ sourceR d :=
    sup_le (c.baumann ▸ c.first.module_le) (c.baumann ▸ c.second.module_le)
  obtain ⟨eQ,_,_⟩ := Theory.GroupTheory.exists_marked_internalProductEquiv
    (twoCore d.H) c.D (c.U₁ ⊔ c.U₂) ((sup_comm _ _).trans c.product.1.symm)
    hdD.symm (c.product.2.2.1.trans (centralizer_le hUR))
  exact ⟨eQ.trans ((MulEquiv.refl _).prodCongr eU)⟩

 theorem core_card : Nat.card (twoCore d.H) = Nat.card c.D * 16 := by
  obtain ⟨e⟩ := c.core_direct_product
  have hU₁ : Nat.card c.U₁ = 4 := c.first.cubic_module_card c.cubic_first
  have hU₂ : Nat.card c.U₂ = 4 := c.second.cubic_module_card c.cubic_second
  rw [Nat.card_congr e.toEquiv,Nat.card_prod,Nat.card_prod,hU₁,hU₂]

include c in
 theorem core_index_thompson : (twoCore d.H).relIndex (sourceR d) = 4 := by
  have hQR : twoCore d.H ≤ sourceR d := by
    rw [c.product.1]
    exact sup_le (sup_le (c.baumann ▸ c.first.module_le) (c.baumann ▸ c.second.module_le))
      (c.product.2.1 ▸ le_sup_right)
  have hh := relIndex_mul_relIndex (⊥ : Subgroup G) (twoCore d.H) (sourceR d) bot_le hQR
  rw [relIndex_bot_left,relIndex_bot_left,c.core_card,c.thompson_card] at hh
  have hd : 0 < Nat.card c.D := Nat.card_pos
  nlinarith

 theorem first_block_centralizer_dihedral :
    Nonempty ((sourceR d ⊓ centralizer (d.block.map d.H.subtype : Set G) : Subgroup G) ≃* c.D × DihedralGroup 4) := by
  let F₁ := c.U₁ ⊔ c.V₁
  let F₂ := c.U₂ ⊔ c.V₂
  let B := F₂ ⊔ c.D
  let C := sourceR d ⊓ centralizer (d.block.map d.H.subtype : Set G)
  have hFR : F₁ ⊔ F₂ ≤ sourceR d := c.product.2.1 ▸ le_sup_left
  have hDC : c.D ≤ centralizer ((F₁ ⊔ F₂ : Subgroup G) : Set G) :=
    c.product.2.2.1.trans (centralizer_le hFR)
  have hF1B : F₁ ≤ centralizer (B : Set G) := by
    apply le_centralizer_iff.mpr
    exact sup_le (le_centralizer_iff.mp c.factor_product.2.1)
      (hDC.trans (centralizer_le (show F₁ ≤ F₁ ⊔ F₂ from le_sup_left)))
  have hdF1B : Disjoint F₁ B := by
    apply disjoint_def.mpr
    intro z hz₁ hzB
    have hm : z ∈ (F₂ : Set G) * (c.D : Set G) := by
      rw [←coe_mul_of_right_le_normalizer_left F₂ c.D
        ((hDC.trans (centralizer_le (show F₂ ≤ F₁ ⊔ F₂ from le_sup_right))).trans (Subgroup.centralizer_le_normalizer _))]
      exact hzB
    obtain ⟨a,ha,b,hb,rfl⟩ := hm
    have hbF : b ∈ F₁ ⊔ F₂ := by
      have hh := (F₁ ⊔ F₂).mul_mem ((F₁ ⊔ F₂).inv_mem (mem_sup_right ha)) (mem_sup_left hz₁)
      simpa only [inv_mul_cancel_left] using hh
    have hb1 := disjoint_def.mp c.factor_product.2.2 hbF hb
    simp only [hb1,mul_one] at hz₁ ⊢
    exact disjoint_def.mp c.factor_product.1 hz₁ ha
  have hAC : F₁ ⊔ C = sourceR d := by
    have hh := (c.first.conjugate_factor_structure (c.original.R_normal c.x_mem) c.noncommuting).1
    change ChapterB.baumann ((d.S : Subgroup d.H).map d.H.subtype) =
      F₁ ⊔ (ChapterB.baumann ((d.S : Subgroup d.H).map d.H.subtype) ⊓ centralizer (d.block.map d.H.subtype : Set G)) at hh
    rw [c.baumann] at hh
    exact hh.symm
  have hCFC : C ≤ centralizer (F₁ : Set G) := by
    have hh := (c.first.conjugate_factor_structure (c.original.R_normal c.x_mem) c.noncommuting).2.1
    change ChapterB.baumann ((d.S : Subgroup d.H).map d.H.subtype) ⊓
      centralizer (d.block.map d.H.subtype : Set G) ≤ centralizer (F₁ : Set G) at hh
    rwa [c.baumann] at hh
  have hdFC : Disjoint F₁ C := by
    apply disjoint_def.mpr
    intro z hz hzC
    have hh := (c.first.conjugate_factor_structure (c.original.R_normal c.x_mem) c.noncommuting).2.2.2.1
    change F₁ ⊓ (ChapterB.baumann ((d.S : Subgroup d.H).map d.H.subtype) ⊓
      centralizer (d.block.map d.H.subtype : Set G)) =
      c.U₁ ⊓ (ChapterB.baumann ((d.S : Subgroup d.H).map d.H.subtype) ⊓
      centralizer (d.block.map d.H.subtype : Set G)) at hh
    rw [c.baumann] at hh
    exact disjoint_def.mp (RankOne.cubic_module_disjoint c.cubic_first C inf_le_right)
      (hh.le ⟨hz,hzC⟩).1 hzC
  obtain ⟨eC⟩ := commuting_complements_equiv (sourceR d) F₁ B C
    ((sup_assoc _ _ _).symm.trans c.product.2.1.symm) hAC hdF1B hdFC hF1B (le_centralizer_iff.mp hCFC)
  obtain ⟨eB,_,_⟩ := Theory.GroupTheory.exists_marked_internalProductEquiv B c.D F₂
    (sup_comm _ _) (c.factor_product.2.2.mono_left le_sup_right).symm
    (hDC.trans (centralizer_le (show F₂ ≤ F₁ ⊔ F₂ from le_sup_right)))
  obtain ⟨e₂⟩ := c.factors_dihedral.2
  exact ⟨eC.trans (eB.trans ((MulEquiv.refl _).prodCongr e₂))⟩

 theorem residual_centralizer_eq_bot_of_rank_le_four
    (hrank : primeRank 2 (T : Subgroup G) ≤ 4) : c.D = ⊥ := by
  let : IsElementaryAbelian 2 c.U₁ := c.first.elementary
  let : IsElementaryAbelian 2 c.U₂ := c.second.elementary
  let : IsElementaryAbelian 2 c.D := c.product.2.2.2
  have hU₁R : c.U₁ ≤ sourceR d := c.baumann ▸ c.first.module_le
  have hU₂R : c.U₂ ≤ sourceR d := c.baumann ▸ c.second.module_le
  have hUC : c.U₂ ≤ centralizer (c.U₁ : Set G) :=
    (map_subtype_le _).trans (c.commute.trans (centralizer_le (map_subtype_le _)))
  let : IsElementaryAbelian 2 (c.U₁ ⊔ c.U₂ : Subgroup G) := IsElementaryAbelian.sup_of_le_centralizer hUC
  have hQD : IsElementaryAbelian 2 ((c.U₁ ⊔ c.U₂) ⊔ c.D : Subgroup G) :=
    IsElementaryAbelian.sup_of_le_centralizer (c.product.2.2.1.trans (centralizer_le (sup_le hU₁R hU₂R)))
  let : IsElementaryAbelian 2 (twoCore d.H) := c.product.1.symm ▸ hQD
  have hQT : twoCore d.H ≤ (T : Subgroup G) := (pCoreIn_le_sylow d.H d.S).trans c.original.T_le
  have hcard := (primeRank_le_iff_elementary_card_le (T : Subgroup G)).mp hrank
    ((twoCore d.H).subgroupOf T) (IsElementaryAbelian.subgroupOf hQT)
  have hle : Nat.card (twoCore d.H) ≤ 16 := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hQT).toEquiv] at hcard
    exact hcard
  rw [c.core_card] at hle
  have hdpos : 0 < Nat.card c.D := Nat.card_pos
  exact Subgroup.card_eq_one.mp (by omega)

 theorem rank_four_geometry (hrank : primeRank 2 (T : Subgroup G) ≤ 4) :
    c.D = ⊥ ∧ twoCore d.H = c.U₁ ⊔ c.U₂ ∧
      sourceR d = (c.U₁ ⊔ c.V₁) ⊔ (c.U₂ ⊔ c.V₂) ∧
      Nat.card (twoCore d.H) = 16 ∧ Nat.card (sourceR d) = 64 := by
  have hD := c.residual_centralizer_eq_bot_of_rank_le_four hrank
  refine ⟨hD,?_,?_,?_,?_⟩
  · simpa only [hD,sup_bot_eq] using c.product.1
  · simpa only [hD,sup_bot_eq] using c.product.2.1
  · simpa only [hD,Nat.card_unique,one_mul] using c.core_card
  · simpa only [hD,Nat.card_unique,one_mul] using c.thompson_card

end SourcePairCoordinates
end CFSG.Quasithin.Chapter2.DoubleA3
