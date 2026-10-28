module
public import CFSG.Quasithin.Chapter14.Section02.ProperComponent
public import Theory.GroupAction.ComponentRankAction.OuterTwo

/-!
# The later containing overgroup in the proper quasisimple branch

The original index-two Sylow argument applies to every maximal two-local
containing X=K₁YS. The canonical solvable residual L is a local C-component
at that same Sylow subgroup, so genuine 1.2.4 places it in a unique normal
C-component of the later overgroup. Local maximality identifies this component
with L. For centerless cubic-rank-two L with two-group outer automorphisms,
the actual component-action theorem then identifies O^{3′}(M₁) with L.

The final application uses the literal C_G(C_{Ω₁Z(S)}(L)) and original
subgroup maps expected by `ProperBinaryPairTerminal`. The equality LS=X,
local maximality from 1.2.8(4), and the model rank/outer facts remain explicit.
In particular this does not assert the five-row non-enlargement theorem, and
the outer-two deduction does not apply to triality(2).

Source: Aschbacher--Smith 14.2.15, pp.985--986; 1.2.4 and 1.2.8(4),
pp.505--507; A.3.18, pp.51--53.
-/

public section

open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter14.Section02
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
/-- The actual Sylow join centralizes its fixed central omega subgroup. -/
theorem proper_sylow_join_le_fixed_center_centralizer (L S : Subgroup G) :
    L ⊔ S ≤ centralizer ((omegaOneCenterAmbient S ⊓ centralizer (L : Set G)) : Set G) := by
  apply sup_le (le_centralizer_iff.mp inf_le_right)
  apply le_centralizer_iff.mp
  exact inf_le_left.trans (fun _ hz => ((mem_omegaOneCenterAmbient_iff _ _).mp hz).2.2)

/-- The original S is Sylow in each maximal two-local containing the completion. -/
theorem source_proper_completion_contained_sylow
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (H : Subgroup G) (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (K S : Subgroup G) (hST : S ≤ (T : Subgroup G))
    (hi : S.relIndex (T : Subgroup G) = 2)
    (hN : normalizer (omegaOneCenterAmbient S : Set G) ≤ Mc)
    (hplacement : ∀ P : Sylow 2 Mc, S ≤ (P : Subgroup Mc).map Mc.subtype →
      maximalTwoLocalOvergroups (K ⊔ (P : Subgroup Mc).map Mc.subtype) = {Mc})
    (M₁ : Subgroup G) (hM₁ : IsMaximalTwoLocal M₁)
    (hXM₁ : K ⊔ sourceResidual M Mc ⊔ S ≤ M₁) :
    Chapter1.IsSylowIn 2 S M₁ := by
  obtain ⟨_,_,_,_,_,_,hunique,_⟩ := source_lemma_14_1_18 hG T hempty hM hu hmany hcard e
  have hHMc : H ≤ Mc := ((source_lemma_14_2_3 hG T hempty hM hu hmany hcard e
    H hH.1.1 hH.1.2).2).trans (InitialSource.centralizer_le_partner T hu)
  exact proper_completion_sylow_in_maximal T M Mc H (sourceResidual M Mc) K S M₁
    hST hi (hH.1.1.2.trans hHMc) hHMc hH.1.2 hunique hN hplacement hM₁
    ((le_sup_left.trans le_sup_left).trans hXM₁)
    ((le_sup_right.trans le_sup_left).trans hXM₁) (le_sup_right.trans hXM₁)

/-- Literal ambient transport of the unique normal containing C-component in 1.2.4. -/
theorem proper_unique_normal_containing_component
    (M₁ L S : Subgroup G)
    (hQ : IsSQTK KnownSimple.IsKnownSimple (M₁ ⧸ pCore 2 M₁))
    (hs : Chapter1.IsSylowIn 2 S M₁)
    (hLM₁ : L ≤ M₁) (hL : L ∈ Chapter1.L G S)
    (hSN : S ≤ normalizer (L : Set G)) :
    ∃! D : Subgroup G, D ∈ Chapter1.cComponentsIn M₁ ∧ L ≤ D ∧
      M₁ ≤ normalizer (D : Set G) := by
  have hSM₁ := (Chapter1.isSylowIn_iff.mp hs).2.1
  obtain ⟨P,hP⟩ := hs
  have hPe : (P : Subgroup M₁) = S.subgroupOf M₁ := by
    apply map_injective M₁.subtype_injective
    rw [map_subgroupOf_eq_of_le hSM₁,hP]
  have hLP : L.subgroupOf M₁ ∈ Chapter1.L M₁ P := by
    rw [hPe]
    exact (Chapter1.mem_LIn_iff_subgroupOf hSM₁ hLM₁).mp ⟨hLM₁,hL⟩
  have hPN : (P : Subgroup M₁) ≤ normalizer (L.subgroupOf M₁ : Set M₁) := by
    rw [hPe,←subgroupOf_normalizer_eq hLM₁]
    exact comap_mono hSN
  obtain ⟨D,⟨hD,hLD,hn⟩,hu⟩ :=
    Chapter1.Section02.lemma_1_2_4_containment_normality_source hQ P hLP hPN
  let := hn
  have hd : (D.map M₁.subtype).subgroupOf M₁ = D :=
    comap_map_eq_self_of_injective M₁.subtype_injective _
  refine ⟨D.map M₁.subtype,⟨⟨map_subtype_le _,hd.symm ▸ hD⟩,?_,?_⟩,?_⟩
  · simpa only [map_subgroupOf_eq_of_le hLM₁] using map_mono (f := M₁.subtype) hLD
  · exact (normal_subgroupOf_iff_le_normalizer (map_subtype_le D)).mp (hd.symm ▸ hn)
  · intro E hE
    have hEN : (E.subgroupOf M₁).Normal :=
      (normal_subgroupOf_iff_le_normalizer hE.1.1).mpr hE.2.2
    have he := hu (E.subgroupOf M₁) ⟨hE.1.2,comap_mono hE.2.1,hEN⟩
    simpa only [map_subgroupOf_eq_of_le hE.1.1] using congrArg (map M₁.subtype) he

/-- The 1.2.8(4) maximality conclusion identifies the original subgroup as a component. -/
theorem proper_containing_component_of_local_maximal
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (M₁ L S : Subgroup G) (hM₁ : IsMaximalTwoLocal M₁)
    (hs : Chapter1.IsSylowIn 2 S M₁) (hLM₁ : L ≤ M₁)
    (hmax : L ∈ Chapter1.LStar G S)
    (hSN : S ≤ normalizer (L : Set G)) :
    L ∈ Chapter1.cComponentsIn M₁ ∧ M₁ ≤ normalizer (L : Set G) := by
  have hQ := ChapterE.Structure.sqtk_two_quotient (hG.twoLocal_sqtk hM₁.1)
    (pCore 2 M₁) pCore_isPGroup
  obtain ⟨D,⟨hD,hLD,hn⟩,_⟩ := proper_unique_normal_containing_component M₁ L S hQ hs hLM₁ hmax.1 hSN
  have hlocal := Chapter1.mem_L_of_cComponent (Chapter1.mem_H_of_isTwoLocal hM₁.1)
    hs hD.1 hD.2
  have he : D = L := hmax.2 D hlocal hLD
  exact he ▸ ⟨hD,hn⟩

/-- The canonical completion residual lies in a unique normal component of the later overgroup. -/
theorem source_proper_completion_containing_component
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (H : Subgroup G) (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (K S : Subgroup G) (hST : S ≤ (T : Subgroup G))
    (hi : S.relIndex (T : Subgroup G) = 2)
    (hN : normalizer (omegaOneCenterAmbient S : Set G) ≤ Mc)
    (hplacement : ∀ P : Sylow 2 Mc, S ≤ (P : Subgroup Mc).map Mc.subtype →
      maximalTwoLocalOvergroups (K ⊔ (P : Subgroup Mc).map Mc.subtype) = {Mc})
    (hK : K ∈ Chapter1.L G S) (hSN : S ≤ normalizer (K : Set G))
    (hcore : (K ⊔ sourceResidual M Mc ⊔ S).pCoreIn 2 ≠ ⊥)
    (M₁ : Subgroup G) (hM₁ : IsMaximalTwoLocal M₁)
    (hXM₁ : K ⊔ sourceResidual M Mc ⊔ S ≤ M₁) :
    let X := K ⊔ sourceResidual M Mc ⊔ S
    let L := (solvableResidual X).map X.subtype
    Chapter1.IsSylowIn 2 S M₁ ∧ L ∈ Chapter1.L G S ∧
      ∃! D : Subgroup G, D ∈ Chapter1.cComponentsIn M₁ ∧ L ≤ D ∧
        M₁ ≤ normalizer (D : Set G) := by
  let X := K ⊔ sourceResidual M Mc ⊔ S
  let L := (solvableResidual X).map X.subtype
  have hs := source_proper_completion_contained_sylow hG T hempty hM hu hmany hcard e H hH K S hST hi
    hN hplacement M₁ hM₁ hXM₁
  have hsX := hs.restrict (show S ≤ X from le_sup_right) hXM₁
  obtain ⟨hL,_,_⟩ := source_proper_completion_component hG T hempty hM hu hmany
    hcard e K S hST hK hSN hcore hsX
  have hlocal := Chapter1.mem_L_of_cComponent hcore hsX hL.1 hL.2
  have hLN : X ≤ normalizer (L : Set G) := by
    have hh := (solvableResidual X).le_normalizer_map X.subtype
    rwa [normalizer_eq_top,←MonoidHom.range_eq_map,range_subtype] at hh
  have hQ := ChapterE.Structure.sqtk_two_quotient (hG.twoLocal_sqtk hM₁.1)
    (pCore 2 M₁) pCore_isPGroup
  exact ⟨hs,hlocal,proper_unique_normal_containing_component M₁ L S hQ hs (hL.1.trans hXM₁) hlocal
    ((le_sup_right : S ≤ X).trans hLN)⟩

/-- A.3.18 for the original centerless full-rank component with two-group outer automorphisms. -/
theorem proper_containing_three_residual_of_outer_two
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (M₁ L S : Subgroup G) (hM₁ : IsMaximalTwoLocal M₁)
    (hs : Chapter1.IsSylowIn 2 S M₁) (hLM₁ : L ≤ M₁)
    (hmax : L ∈ Chapter1.LStar G S)
    (hSN : S ≤ normalizer (L : Set G))
    (hq : IsQuasisimple L) (hz : center L = ⊥) (hr : 2 ≤ primeRank 3 L)
    (ho : IsPGroup 2 (MulAut.Outer L)) :
    L ∈ Chapter1.cComponentsIn M₁ ∧ (primeToResidual 3 M₁).map M₁.subtype = L := by
  obtain ⟨hL,_⟩ := proper_containing_component_of_local_maximal hG M₁ L S hM₁ hs hLM₁ hmax hSN
  let B := L.subgroupOf M₁
  let eB : B ≃* L := subgroupOfEquivOfLe hLM₁
  let := hq
  let : IsQuasisimple B := IsQuasisimple.of_mulEquiv eB.symm
  have hc : center B = ⊥ := by
    apply eq_bot_iff.mpr
    intro b hb
    have hh : eB b ∈ center L := (centerCongr eB ⟨b,hb⟩).property
    rw [hz,mem_bot] at hh
    exact mem_bot.mpr (eB.map_eq_one_iff.mp hh)
  have hB : IsComponent M₁ B := ⟨hL.2.subnormal,inferInstance⟩
  have hrB : 2 ≤ primeRank 3 B := by rwa [primeRank_equiv 3 eB]
  have hbound := (hG.twoLocal_sqtk hM₁.1).stronglyQuasithin 3 Nat.prime_three (by decide)
  let e : (B ⧸ center B) ≃* L :=
    ((QuotientGroup.quotientMulEquivOfEq hc).trans QuotientGroup.quotientBot).trans eB
  have he := (Theory.GroupAction.ComponentRankAction.component_eq_primeClosure_and_residual_of_outer_twoGroup
    hB (by rw [hc]; simp) hrB hbound e (by decide) ho).2
  refine ⟨hL,?_⟩
  rw [←he,map_subgroupOf_eq_of_le hLM₁]

/-- The exact later residual identity consumed by the original binary-pair terminal. -/
theorem source_proper_containing_three_residual_of_maximal_outer_two
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (H : Subgroup G) (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (K S : Subgroup G) (hST : S ≤ (T : Subgroup G))
    (hi : S.relIndex (T : Subgroup G) = 2)
    (hN : normalizer (omegaOneCenterAmbient S : Set G) ≤ Mc)
    (hplacement : ∀ P : Sylow 2 Mc, S ≤ (P : Subgroup Mc).map Mc.subtype →
      maximalTwoLocalOvergroups (K ⊔ (P : Subgroup Mc).map Mc.subtype) = {Mc})
    (M₁ : Subgroup G) (hM₁ : IsMaximalTwoLocal M₁) :
    let X := K ⊔ sourceResidual M Mc ⊔ S
    let L := (solvableResidual X).map X.subtype
    L ⊔ S = X →
    centralizer ((omegaOneCenterAmbient S ⊓ centralizer (L : Set G)) : Set G) ≤ M₁ →
    L ∈ Chapter1.LStar G S →
    IsQuasisimple L → center L = ⊥ → 2 ≤ primeRank 3 L →
    IsPGroup 2 (MulAut.Outer L) →
    L ∈ Chapter1.cComponentsIn M₁ ∧ (primeToResidual 3 M₁).map M₁.subtype = L := by
  let X := K ⊔ sourceResidual M Mc ⊔ S
  let L := (solvableResidual X).map X.subtype
  dsimp only
  intro hLS hC hmax hq hz hr ho
  have hXM₁ : X ≤ M₁ := by
    change L ⊔ S = X at hLS
    rw [←hLS]
    exact (proper_sylow_join_le_fixed_center_centralizer L S).trans hC
  have hs := source_proper_completion_contained_sylow hG T hempty hM hu hmany hcard e H hH K S hST hi
    hN hplacement M₁ hM₁ hXM₁
  have hLN : X ≤ normalizer (L : Set G) := by
    have hh := (solvableResidual X).le_normalizer_map X.subtype
    rwa [normalizer_eq_top,←MonoidHom.range_eq_map,range_subtype] at hh
  exact proper_containing_three_residual_of_outer_two hG M₁ L S hM₁ hs
    ((map_subtype_le _).trans hXM₁) hmax ((le_sup_right : S ≤ X).trans hLN) hq hz hr ho

end CFSG.Quasithin.Chapter14.Section02
