module
public import CFSG.Quasithin.Chapter14.Section02.ProperSpan
public import CFSG.Quasithin.Chapter14.Section02.ProperPushingUp
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.ChiZero

/-!
# Excluding the χ₀ outcome in the proper-index completion

The actual selected K₁ is a local C-component at the full Sylow S of the
completion. If the containing normal component L were a χ₀-block, the
proved A.3.12 non-enlargement theorem would force K₁=L. This contradicts
K₁≤H≤C_G(Z) and the source noncentrality of L. Combining this with the
literal C.1.29 application reduces the characteristic-two branch to proving
that R=O₂(YS) is Sylow in LR (and the original quasisimple core quotient).

Source: Aschbacher--Smith 14.2.15, printed p.986, using A.3.12 and C.1.29.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter14.Section02
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]

theorem source_proper_completion_not_chiZero
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (H : Subgroup G) (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (K S : Subgroup G) (hST : S ≤ (T : Subgroup G))
    (hgen : K ⊔ (T : Subgroup G) = H)
    (hK : K ∈ Chapter1.L G S) (hSN : S ≤ normalizer (K : Set G))
    (hcore : (K ⊔ sourceResidual M Mc ⊔ S).pCoreIn 2 ≠ ⊥)
    (hs : Chapter1.IsSylowIn 2 S (K ⊔ sourceResidual M Mc ⊔ S)) :
    let X := K ⊔ sourceResidual M Mc ⊔ S
    let L := (solvableResidual X).map X.subtype
    ¬ ChapterC.IsChiZeroBlock L := by
  let X := K ⊔ sourceResidual M Mc ⊔ S
  let L := (solvableResidual X).map X.subtype
  change ¬ ChapterC.IsChiZeroBlock L
  intro hc
  obtain ⟨hL,hKL,_⟩ := source_proper_completion_component hG T hempty hM hu hmany
    hcard e K S hST hK hSN hcore hs
  have hKX : K ≤ X := le_sup_left.trans le_sup_left
  have hSX : S ≤ X := le_sup_right
  obtain ⟨P,hP⟩ := hs
  have hPS : (P : Subgroup X) = S.subgroupOf X := by
    apply map_injective X.subtype_injective
    rw [hP,map_subgroupOf_eq_of_le hSX]
  have hlocal : K.subgroupOf X ∈ Chapter1.L X P := by
    rw [hPS]
    exact (Chapter1.mem_LIn_iff_subgroupOf hSX hKX).mp ⟨hKX,hK⟩
  have hc' : ChapterC.IsChiZeroBlock (L.subgroupOf X) :=
    hc.of_mulEquiv (subgroupOfEquivOfLe hL.1).symm
  have he := ChapterA.Section03.SourceEmbeddings.eq_of_chiZero_containing_component P
    hlocal.1 hL.2 (comap_mono hKL) hc'
  have he' : K = L := by
    have hh := congrArg (Subgroup.map X.subtype) he
    rwa [map_subgroupOf_eq_of_le hKX,map_subgroupOf_eq_of_le hL.1] at hh
  have hKC : K ≤ centralizer (centralInvolutions T : Set G) :=
    (le_sup_left.trans_eq hgen).trans
      (source_lemma_14_2_3 hG T hempty hM hu hmany hcard e H hH.1.1 hH.1.2).2
  exact source_proper_completion_component_noncentral hG T hempty hM hu hmany hcard e
    H hH K S hST hgen hK hSN hcore ⟨P,hP⟩ (he'.ge.trans hKC)

theorem source_proper_completion_sylow_core_false
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
    (hgen : K ⊔ (T : Subgroup G) = H)
    (hK : K ∈ Chapter1.L G S) (hSN : S ≤ normalizer (K : Set G))
    (hcore : (K ⊔ sourceResidual M Mc ⊔ S).pCoreIn 2 ≠ ⊥)
    (hs : Chapter1.IsSylowIn 2 S (K ⊔ sourceResidual M Mc ⊔ S)) :
    let X := K ⊔ sourceResidual M Mc ⊔ S
    let L := (solvableResidual X).map X.subtype
    let R := (sourceResidual M Mc ⊔ S).pCoreIn 2
    X ∈ Chapter1.He G → IsQuasisimple (L ⧸ pCore 2 L) →
      Chapter1.IsSylowIn 2 R (L ⊔ R) → False := by
  intro X L R hXe hq hsR
  exact source_proper_completion_not_chiZero hG T hempty hM hu hmany hcard e
    H hH K S hST hgen hK hSN hcore hs
    (source_proper_component_chiZero_of_sylow_core hG T hempty hM hu hmany hcard e
      H hH K S hST hi hgen hK hSN hcore hs hXe hq hsR)

end CFSG.Quasithin.Chapter14.Section02
