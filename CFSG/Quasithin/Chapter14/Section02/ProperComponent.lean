module
public import CFSG.Quasithin.Chapter14.Section02.ProperSylow
public import CFSG.Quasithin.Chapter14.Section02.ComponentPlacement
public import CFSG.Quasithin.Chapter14.Section02.ResidualSylow
public import CFSG.Quasithin.Chapter1.Section02.ComponentDichotomy.NormalSupplement
public import Theory.GroupTheory.SymmetricThreeTwoCoreStructure

/-!
# The normal component in the proper-index completion

Original 1.2.4 selects a normal C-component containing K₁ when the actual
Sylow normalizes K₁. The plane quotient makes YT solvable. A solvable
supplement then identifies the selected component with the literal solvable
residual, giving both normality and solvability of its quotient. The original
H-core also supplies the nontrivial local core of K₁S. The selected local
component remains an explicit input; its normal overcomponent is constructed.

Source: Aschbacher--Smith 14.2.15, printed p.985, using 1.2.4 and 14.1.18.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter14.Section02
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
private theorem solvable_quotient_of_supplement (N C : Subgroup G)
    [N.Normal] [Group.IsSolvable C] (hgen : N ⊔ C = ⊤) :
    Group.IsSolvable (G ⧸ N) := by
  let q := QuotientGroup.mk' N
  let f : C →* G ⧸ N := q.comp C.subtype
  apply Group.isSolvable_of_surjective (f := f)
  intro y
  obtain ⟨g,rfl⟩ := QuotientGroup.mk'_surjective N y
  obtain ⟨n,hn,c,hc,he⟩ := mem_sup_of_normal_left.mp (show g ∈ N ⊔ C by rw [hgen]; trivial)
  have hqn : q n = 1 := (QuotientGroup.eq_one_iff n).mpr hn
  refine ⟨⟨c,hc⟩,?_⟩
  change q c = q g
  rw [←he,map_mul,hqn,one_mul]

/-- The normal local component is exactly the solvable residual of the completion. -/
theorem proper_completion_residual_component
    (hQ : IsSQTK KnownSimple.IsKnownSimple (G ⧸ pCore 2 G))
    (S : Sylow 2 G) (K Y : Subgroup G)
    (hK : K ∈ Chapter1.L G S) (hSN : (S : Subgroup G) ≤ normalizer (K : Set G))
    (hgen : K ⊔ Y ⊔ (S : Subgroup G) = ⊤)
    [Group.IsSolvable (Y ⊔ (S : Subgroup G) : Subgroup G)] :
    (solvableResidual G).IsCComponent ∧ K ≤ solvableResidual G ∧
      solvableResidual G ⊔ Y ⊔ (S : Subgroup G) = ⊤ := by
  obtain ⟨L,⟨hL,hKL,hn⟩,_⟩ := Chapter1.Section02.lemma_1_2_4_containment_normality_source hQ S hK hSN
  let := hn
  let := hL.perfect
  have hg : L ⊔ (Y ⊔ (S : Subgroup G)) = ⊤ := by
    rw [←sup_assoc]
    exact top_unique (hgen ▸ sup_le_sup_right (sup_le_sup_right hKL _) _)
  let : Group.IsSolvable (G ⧸ L) := solvable_quotient_of_supplement L _ hg
  have he : L = solvableResidual G := le_antisymm (le_solvableResidual_of_isPerfect _)
    (solvableResidual_le_of_solvable_quotient _)
  exact ⟨he ▸ hL,he ▸ hKL,by simpa only [sup_assoc,he] using hg⟩

omit [Finite G] in
/-- The original H-core supplies the nontrivial local core of K₁S. -/
theorem proper_selected_mem_local
    (H K S X : Subgroup G) (hKH : K ≤ H) (hSH : S ≤ H)
    (hKX : K ≤ X) (hSX : S ≤ X)
    (hs : Chapter1.IsSylowIn 2 S X)
    (hK : (K.subgroupOf (K ⊔ S)).IsCComponent)
    (hcore : H.pCoreIn 2 ≠ ⊥) (hQS : H.pCoreIn 2 ≤ S) :
    K ∈ Chapter1.L G S := by
  refine ⟨hK,hs.restrict le_sup_right (sup_le hKX hSX),?_⟩
  have hc : H.pCoreIn 2 ≤ (K ⊔ S).pCoreIn 2 := le_pCoreIn_of_normalizes
    (isPGroup_pCoreIn 2 H) (hQS.trans le_sup_right)
    ((sup_le hKH hSH).trans (H.le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image H (pCore 2 H))))
  exact fun he => hcore (bot_unique (he ▸ hc))

/-- The actual YT in the plane source is solvable. -/
theorem source_residualSylow_solvable
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3)) :
    Group.IsSolvable (sourceResidual M Mc ⊔ (T : Subgroup G) : Subgroup G) := by
  obtain ⟨_,⟨f⟩⟩ := source_residualSylow_quotient hG T hempty hM hu hmany hcard e
  exact SymmetricThreeTwoCore.solvable f

/-- The original proposed completion has a canonical normal C-component containing K₁. -/
theorem source_proper_completion_component
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (K S : Subgroup G) (hST : S ≤ (T : Subgroup G))
    (hK : K ∈ Chapter1.L G S) (hSN : S ≤ normalizer (K : Set G))
    (hcore : (K ⊔ sourceResidual M Mc ⊔ S).pCoreIn 2 ≠ ⊥)
    (hs : Chapter1.IsSylowIn 2 S (K ⊔ sourceResidual M Mc ⊔ S)) :
    let X := K ⊔ sourceResidual M Mc ⊔ S
    let L := (solvableResidual X).map X.subtype
    L ∈ Chapter1.cComponentsIn X ∧ K ≤ L ∧ L ⊔ sourceResidual M Mc ⊔ S = X := by
  let X := K ⊔ sourceResidual M Mc ⊔ S
  let Y := sourceResidual M Mc
  have hKX : K ≤ X := le_sup_left.trans le_sup_left
  have hYX : Y ≤ X := le_sup_right.trans le_sup_left
  have hSX : S ≤ X := le_sup_right
  have hXN : X ≤ normalizer (X.pCoreIn 2 : Set G) :=
    X.le_normalizer.trans (normalizer_le_normalizer_characteristic_image X (pCore 2 X))
  have hsN := hG.twoLocal_sqtk
    (show IsTwoLocal (normalizer (X.pCoreIn 2 : Set G)) from ⟨X.pCoreIn 2,hcore,isPGroup_pCoreIn 2 X,rfl⟩)
  have hsX : IsSQTK KnownSimple.IsKnownSimple X :=
    ⟨hsN.stronglyQuasithin.of_injective (inclusion hXN) (inclusion_injective hXN),
      hsN.isKGroup.of_injective (inclusion hXN) (inclusion_injective hXN)⟩
  have hsQ := ChapterE.Structure.sqtk_two_quotient hsX (pCore 2 X) pCore_isPGroup
  change Chapter1.IsSylowIn 2 S X at hs
  obtain ⟨P,hP⟩ := hs
  have hPe : (P : Subgroup X) = S.subgroupOf X := by
    apply map_injective X.subtype_injective
    rw [map_subgroupOf_eq_of_le hSX,hP]
  have hKP : K.subgroupOf X ∈ Chapter1.L X P := by
    rw [hPe]
    exact (Chapter1.mem_LIn_iff_subgroupOf hSX hKX).mp ⟨hKX,hK⟩
  have hPN : (P : Subgroup X) ≤ normalizer (K.subgroupOf X : Set X) := by
    rw [hPe,←subgroupOf_normalizer_eq hKX]
    exact comap_mono hSN
  have hgen : K.subgroupOf X ⊔ Y.subgroupOf X ⊔ (P : Subgroup X) = ⊤ := by
    apply map_injective X.subtype_injective
    rw [Subgroup.map_sup,Subgroup.map_sup,map_subgroupOf_eq_of_le hKX,
      map_subgroupOf_eq_of_le hYX,hP,←MonoidHom.range_eq_map,range_subtype]
  let : Group.IsSolvable (Y ⊔ (T : Subgroup G) : Subgroup G) :=
    source_residualSylow_solvable hG T hempty hM hu hmany hcard e
  let : Group.IsSolvable (Y ⊔ S : Subgroup G) := Group.isSolvable_of_isSolvable_injective
    (inclusion_injective (sup_le_sup_left hST Y))
  have hYS : Y.subgroupOf X ⊔ (P : Subgroup X) = (Y ⊔ S).subgroupOf X := by
    rw [hPe,subgroupOf_sup hYX hSX]
  let : Group.IsSolvable (Y.subgroupOf X ⊔ (P : Subgroup X) : Subgroup X) := by
    rw [hYS]
    exact Group.isSolvable_of_isSolvable_injective
      (f := (subgroupOfEquivOfLe (sup_le hYX hSX)).toMonoidHom)
      (subgroupOfEquivOfLe (sup_le hYX hSX)).injective
  obtain ⟨hL,hKL,hgenL⟩ := proper_completion_residual_component hsQ P
    (K.subgroupOf X) (Y.subgroupOf X) hKP hPN hgen
  change (solvableResidual X).map X.subtype ∈ Chapter1.cComponentsIn X ∧
    K ≤ (solvableResidual X).map X.subtype ∧
    (solvableResidual X).map X.subtype ⊔ Y ⊔ S = X
  refine ⟨⟨map_subtype_le _,?_⟩,?_,?_⟩
  · simpa only [subgroupOf,comap_map_eq_self_of_injective X.subtype_injective] using hL
  · simpa only [map_subgroupOf_eq_of_le hKX] using map_mono (f := X.subtype) hKL
  · have hh := congrArg (Subgroup.map X.subtype) hgenL
    simpa only [Subgroup.map_sup,map_subgroupOf_eq_of_le hYX,hP,←MonoidHom.range_eq_map,range_subtype] using hh
end CFSG.Quasithin.Chapter14.Section02
