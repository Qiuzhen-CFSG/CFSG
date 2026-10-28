module

public import CFSG.Quasithin.Chapter10.SourceA5NaturalGeneration.TerminalOvercomponent.CommonComponent
public import Theory.GroupTheory.CComponent.NonsolvableNormalIntersection
public import Theory.GroupTheory.CentralizingTorusRank

/-!
# The common component centralizes the opposite Borel

The centralizer of A is normal in its normalizer. A C-component containing
an actual nonsolvable subgroup of this centralizer therefore lies entirely
in it. For A = S D with faithful cubic D, strong quasithinness forces the
resulting component to have three-rank at most one. Thus the terminal source
step only needs to exclude three-rank one for the proper natural-block
containing component; its full identification would be a stronger input.

Source: Aschbacher--Smith 10.2.3(4), printed p.747, and A.3.3(1).
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter10
variable {G : Type*} [Group G] [Finite G]

/-- A nonsolvable original block already centralizing A forces its containing
C-component in N(A) to centralize A. -/
theorem source_borel_component_centralizes (A L C : Subgroup G)
    (hC : C ∈ Chapter1.cComponentsIn (normalizer (A : Set G)))
    (hLC : L ≤ C) (hL : ¬ Group.IsSolvable L)
    (hLA : L ≤ centralizer (A : Set G)) : C ≤ centralizer (A : Set G) := by
  let N := normalizer (A : Set G)
  have hLN : L ≤ N := hLC.trans hC.1
  have hCN : C ≤ N := hC.1
  have hcenN : centralizer (A : Set G) ≤ N := Subgroup.centralizer_le_normalizer _
  have hnon : ¬ Group.IsSolvable (L.subgroupOf N) := by
    intro hs
    let : Group.IsSolvable (L.subgroupOf N) := hs
    exact hL (Group.isSolvable_of_surjective
      (f := (subgroupOfEquivOfLe hLN).toMonoidHom)
      (subgroupOfEquivOfLe hLN).surjective)
  have hh : C.subgroupOf N ≤ (centralizer (A : Set G)).subgroupOf N :=
    hC.2.le_normal_of_nonsolvable_subgroup hnon (comap_mono hLC) (comap_mono hLA)
  have hm := map_mono (f := N.subtype) hh
  simpa only [map_subgroupOf_eq_of_le hCN,
    map_subgroupOf_eq_of_le hcenN] using hm

/-- At the actual faithful cubic Borel, every containing C-component as above
has three-rank at most one. No component model or core computation is assumed. -/
theorem source_borel_component_cubic_rank_le_one {κ : GroupClass}
    (S D L C : Subgroup G)
    (hI : IsSQTK κ (normalizer ((S ⊔ D : Subgroup G) : Set G)))
    (hfaithful : D ⊓ centralizer (S : Set G) = ⊥)
    (hD : Nat.card D = 3)
    (hC : C ∈ Chapter1.cComponentsIn (normalizer ((S ⊔ D : Subgroup G) : Set G)))
    (hLC : L ≤ C) (hL : ¬ Group.IsSolvable L)
    (hLA : L ≤ centralizer ((S ⊔ D : Subgroup G) : Set G)) :
    primeRank 3 C ≤ 1 := by
  have hCA := source_borel_component_centralizes (S ⊔ D) L C hC hLC hL hLA
  have hCS : C ≤ centralizer (S : Set G) := hCA.trans (centralizer_le (fun _ hx => mem_sup_left hx))
  have hDC : D ≤ centralizer (C : Set G) :=
    le_centralizer_iff.mp (hCA.trans (centralizer_le (fun _ hx => mem_sup_right hx)))
  by_contra hn
  have hlarge := three_le_primeRank_of_disjoint_commuting D C
    (disjoint_of_centralizes_faithful_subgroup D C S hfaithful hCS)
    hDC (by rw [hD] : 3 ∣ Nat.card D) (by omega : 2 ≤ primeRank 3 C)
  have hle := _root_.primeRank_le_of_injective 3
    (inclusion (sup_le (le_sup_right.trans (S ⊔ D).le_normalizer) hC.1))
    (inclusion_injective (sup_le (le_sup_right.trans (S ⊔ D).le_normalizer) hC.1))
  have hsmall := hI.stronglyQuasithin 3 (by decide) (by decide)
  omega

/-- Application to the two original blocks: their commutator movement selects
a common component inside the actual Borel centralizer. -/
theorem source_natural_pair_common_centralizing_component
    (A L K D : Subgroup G)
    (hQ : IsSQTK KnownSimple.IsKnownSimple
      ((normalizer (A : Set G)) ⧸ pCore 2 (normalizer (A : Set G))))
    (T : Sylow 2 (normalizer (A : Set G)))
    (hL : L.subgroupOf (normalizer (A : Set G)) ∈
      Chapter1.L (normalizer (A : Set G)) T)
    (hLA : L ≤ centralizer (A : Set G)) (hKN : K ≤ normalizer (A : Set G))
    (hDL : D ≤ L) (hmove : ⁅K, D⁆ = K) :
    ∃! C : Subgroup G,
      C ∈ Chapter1.cComponentsIn (normalizer (A : Set G)) ∧ L ≤ C ∧ K ≤ C ∧
        C ≤ centralizer (A : Set G) := by
  have hLN := hLA.trans (centralizer_le_normalizer (A : Set G))
  obtain ⟨C, ⟨hC, hLC, hKC⟩, hu⟩ :=
    source_borel_normalizer_common_component A L K D hQ T hL hLN hKN hDL hmove
  have hnon : ¬ Group.IsSolvable L := by
    intro hs
    let : Group.IsSolvable L := hs
    exact Chapter1.mem_L_not_isSolvable hL
      (Group.isSolvable_of_isSolvable_injective
        (f := (subgroupOfEquivOfLe hLN).toMonoidHom)
        (subgroupOfEquivOfLe hLN).injective)
  exact ⟨C, ⟨hC, hLC, hKC, source_borel_component_centralizes A L C hC hLC hnon hLA⟩,
    fun E hE => hu E ⟨hE.1, hE.2.1, hE.2.2.1⟩⟩

end CFSG.Quasithin.Chapter10
