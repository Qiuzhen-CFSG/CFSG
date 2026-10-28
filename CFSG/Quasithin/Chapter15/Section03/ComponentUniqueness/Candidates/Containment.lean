module

public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.Candidates.Basic
public import Theory.GroupTheory.Commutator.PerfectLocalReduction

/-!
# Containment of invariant characteristic-two subgroups

For 15.3.33(1), put `J = L₁Y₊S`. The common Sylow subgroup gives
`O₂(I) ≤ O₂(J)`, so `J` has nontrivial two-core. If `J` is outside `M`,
15.3.11(8) gives `O(J) = 1`. As `L₁` is normal in `J` and `Y₊S` is
solvable, every component of `J` lies in `L₁`. Its characteristic-two
hypothesis excludes such components, giving `F*(J) = O₂(J)`. This is
the contradiction to 15.3.25.

The conclusion holds for every invariant `L₁ ≤ I`, hence in particular
for the source's `L₁ ≤ L₀`. Solvability of `Y₊S`, the common Sylow
property, 15.3.11(8), and 15.3.25 are explicit earlier inputs. Neither
characteristic two nor nontriviality of the two-core of `J` is assumed.

Source: Aschbacher--Smith, combined manuscript (1 March 2004),
15.3.33(1), printed p.1134.
-/

public section

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section03
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
private theorem solvable_quotient_of_supplement (N B : Subgroup G) [N.Normal]
    [Group.IsSolvable B] (hNB : N ⊔ B = ⊤) : Group.IsSolvable (G ⧸ N) := by
  let q := QuotientGroup.mk' N
  have hNq : N.map q = ⊥ := (map_eq_bot_iff N).mpr (QuotientGroup.ker_mk' N).symm.le
  have hBq : B.map q = ⊤ := by
    have he := congrArg (Subgroup.map q) hNB
    rwa [Subgroup.map_sup, hNq, bot_sup_eq,
      map_top_of_surjective q (QuotientGroup.mk'_surjective N)] at he
  let : Group.IsSolvable (B.map q) :=
    Group.isSolvable_of_surjective (q.subgroupMap_surjective B)
  let : Group.IsSolvable (⊤ : Subgroup (G ⧸ N)) := hBq ▸ inferInstance
  exact Group.isSolvable_of_surjective (f := (⊤ : Subgroup (G ⧸ N)).subtype)
    (by intro x; exact ⟨⟨x, mem_top x⟩, rfl⟩)


omit [Finite G] in
private theorem component_subgroupOfEquiv {I L₁ : Subgroup G} (hL : L₁ ≤ I)
    {K : Subgroup I} (hK : IsComponent I K)
    (hKN : K ≤ L₁.subgroupOf I) :
    IsComponent L₁ ((K.subgroupOf (L₁.subgroupOf I)).map
      (subgroupOfEquivOfLe hL).toMonoidHom) :=
  (hK.subgroupOf hKN).map_equiv (subgroupOfEquivOfLe hL)

/-- The whole extension has no components because its solvable quotient
forces each perfect component into L₁. -/
private theorem no_component_extension {L₁ B : Subgroup G}
    (hBN : B ≤ normalizer (L₁ : Set G)) [Group.IsSolvable B]
    (hL : generalizedFitting L₁ = pCore 2 L₁) :
    ¬ ∃ K : Subgroup (L₁ ⊔ B : Subgroup G), IsComponent (L₁ ⊔ B : Subgroup G) K := by
  let J := L₁ ⊔ B
  let N := L₁.subgroupOf J
  let D := B.subgroupOf J
  have hLJ : L₁ ≤ J := le_sup_left
  have hBJ : B ≤ J := le_sup_right
  let : N.Normal := (normal_subgroupOf_iff_le_normalizer hLJ).mpr
    (sup_le L₁.le_normalizer hBN)
  let : Group.IsSolvable D :=
    Group.isSolvable_of_isSolvable_injective
      (f := (subgroupOfEquivOfLe hBJ).toMonoidHom) (subgroupOfEquivOfLe hBJ).injective
  have hND : N ⊔ D = ⊤ := by
    rw [← subgroupOf_sup hLJ hBJ]
    exact subgroupOf_self J
  let : Group.IsSolvable (J ⧸ N) := solvable_quotient_of_supplement N D hND
  rintro ⟨K, hK⟩
  let := hK.2
  have hKN : K ≤ N := le_of_isPerfect_of_solvable_quotient K N
  let E := (K.subgroupOf N).map (subgroupOfEquivOfLe hLJ).toMonoidHom
  have hcomp : IsComponent L₁ E := component_subgroupOfEquiv hLJ hK hKN
  let := hcomp.2
  have hEcore : E ≤ pCore 2 L₁ := (component_le_generalizedFitting L₁ E hcomp).trans hL.le
  have hp : IsPGroup 2 E := pCore_isPGroup.to_le hEcore
  let := hp.isNilpotent
  let : IsSimpleGroup (E ⧸ center E) := IsQuasisimple.simple
  let : Nontrivial E := (QuotientGroup.mk'_surjective (center E)).nontrivial
  exact Group.IsPerfect.not_isSolvable E inferInstance

/-- Source 15.3.33(1), in the slightly stronger form L₁ ≤ I. -/
theorem lemma_15_3_33_1
    {Yplus S M I L₁ : Subgroup G}
    (hI : I ∈ outsideFamily Yplus S M)
    (hSylow : OutsideSylowControl Yplus S M)
    (h25 : ∀ J ∈ outsideFamily Yplus S M, generalizedFitting J ≠ pCore 2 J)
    (hodd : ∀ J ∈ outsideFamily Yplus S M, pPrimeCore 2 J = ⊥)
    [Group.IsSolvable (Yplus ⊔ S : Subgroup G)]
    (hL : L₁ ≤ I) (hLN : Yplus ⊔ S ≤ normalizer (L₁ : Set G))
    (hF : generalizedFitting L₁ = pCore 2 L₁) : L₁ ≤ M ⊓ I := by
  refine le_inf ?_ hL
  by_contra hn
  have hJ := component_extension_mem_outsideFamily hI hSylow hL hn
  have hJF : generalizedFitting (L₁ ⊔ (Yplus ⊔ S) : Subgroup G) =
      pCore 2 (L₁ ⊔ (Yplus ⊔ S) : Subgroup G) := by
    by_contra hne
    exact no_component_extension hLN hF
      (exists_ordinary_component_of_fstar_ne_twoCore (hodd _ hJ) hne)
  exact h25 _ hJ hJF

end CFSG.Quasithin.Chapter15.Section03
