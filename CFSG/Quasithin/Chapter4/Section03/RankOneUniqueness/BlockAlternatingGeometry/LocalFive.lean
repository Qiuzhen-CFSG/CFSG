module
public import CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.BlockAlternatingGeometry.LocalAction
public import Theory.SpecificGroups.Alternating.SevenFiveSection
public import Theory.SpecificGroups.Alternating.SevenFivePlacement
public import Theory.SpecificGroups.SL2.CardFourEquiv
public import Theory.GroupTheory.SylowNormalIntersection

/-!
# The original five-letter component inside the A₇ action

The two-core quotient PSL₂(4) identifies the image of the original L with
A₅. The full Sylow intersection normalizes L, so its A₇ image fixes two
letters. The image kernel is exactly O₂(L), retaining the original
quotient map for the ensuing section-centralizer calculation.

Source: Aschbacher--Smith C.4.1(1), C.4.6 and 4.3.7, pp.151--152,616.
The remaining local marking and final exclusion belong to
qt-d-1222-rankone-block-alternating.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

private theorem component_sylow_le (c : SourceConfiguration T L) :
    ∃ P : Sylow 2 (c.K.map c.H.subtype),
      (P : Subgroup (c.K.map c.H.subtype)).map (c.K.map c.H.subtype).subtype ≤
        (T : Subgroup G) := by
  obtain ⟨S,hS⟩ := c.sylow
  let : c.K.Normal := c.component_normal
  obtain ⟨P,hP⟩ := S.exists_subgroupOf_eq_of_normal c.K
  let e := c.K.equivMapOfInjective c.H.subtype c.H.subtype_injective
  refine ⟨P.mapSurjective (f := e.toMonoidHom) e.surjective,?_⟩
  rintro _ ⟨a,⟨k,hk,rfl⟩,rfl⟩
  have hkS : (k : c.H) ∈ (S : Subgroup c.H) := by
    change k ∈ (S : Subgroup c.H).subgroupOf c.K
    rwa [← hP]
  have hh := mem_map_of_mem c.H.subtype hkS
  rw [hS] at hh
  exact hh.1

/-- The original PSL₂(4) section has the literal five-letter image in every
compatible seven-letter action, and its restricted kernel is exactly O₂(L). -/
theorem SourceConfiguration.alternating_five_placement
    (c : SourceConfiguration T L) (D : Chapter12.Section02.ChosenModule T L V)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 4)
    (f : (c.K.map c.H.subtype ⊔ ((T : Subgroup G) ⊓ c.H) : Subgroup G) →*
      Equiv.Perm (Fin 7))
    (hk : f.ker = pCore 2
      (c.K.map c.H.subtype ⊔ ((T : Subgroup G) ⊓ c.H) : Subgroup G))
    (ha : ((c.K.map c.H.subtype).subgroupOf
      (c.K.map c.H.subtype ⊔ ((T : Subgroup G) ⊓ c.H))).map f =
        alternatingGroup (Fin 7)) :
    (f.comp (inclusion (c.le_component.trans le_sup_left))).ker = pCore 2 L ∧
    ∃ i j : Fin 7, i ≠ j ∧
      (L.subgroupOf (c.K.map c.H.subtype ⊔ ((T : Subgroup G) ⊓ c.H))).map f =
        (fixingSubgroup (alternatingGroup (Fin 7)) ({i,j} : Set (Fin 7))).map
          (alternatingGroup (Fin 7)).subtype := by
  let A := c.K.map c.H.subtype
  let J := A ⊔ ((T : Subgroup G) ⊓ c.H)
  let LA := L.subgroupOf A
  have hAJ : A ≤ J := le_sup_left
  let a := f.comp (inclusion hAJ)
  have hamem (x : A) : a x ∈ alternatingGroup (Fin 7) := by
    rw [← ha]
    exact mem_map_of_mem f x.property
  let q : A →* alternatingGroup (Fin 7) := a.codRestrict _ hamem
  have hq : Function.Surjective q := by
    intro b
    obtain ⟨x,hx,hxb⟩ := ha.ge b.property
    exact ⟨⟨x,hx⟩,Subtype.ext hxb⟩
  have hqker : IsPGroup 2 q.ker := by
    have hfk : IsPGroup 2 f.ker := hk ▸ pCore_isPGroup
    have heq : q.ker = f.ker.comap (inclusion hAJ) := by
      ext x
      change q x = 1 ↔ f (inclusion hAJ x) = 1
      exact Subtype.ext_iff
    rw [heq]
    exact hfk.comap_of_injective _ (inclusion_injective hAJ)
  have hLAker : IsPGroup 2 (q.subgroupMap LA).ker := by
    rw [Subgroup.ker_subgroupMap]
    exact hqker.comap_subtype
  obtain ⟨F,_,_,hF,⟨eF⟩⟩ := hpsl
  obtain ⟨e5⟩ := Matrix.ProjectiveSpecialLinearGroup.equiv_alternatingGroup_of_card_four
    (K := F) hF
  let eLA : LA ≃* L := subgroupOfEquivOfLe c.le_component
  let e : (LA ⧸ pCore 2 LA) ≃* alternatingGroup (Fin 5) :=
    (QuotientGroup.congr _ _ eLA (pCore_map_iso 2 eLA)).trans (eF.trans e5)
  have hker := (alternatingGroup.SevenFiveSection.image_twoCore_eq_bot_and_ker_eq
    q LA hLAker e).2
  let eimage := alternatingGroup.SevenFiveSection.imageFiveEquiv q LA hLAker e
  obtain ⟨P,hPT⟩ := component_sylow_le c
  have hPN : (P : Subgroup A) ≤ normalizer (LA : Set A) := by
    intro p hp l
    exact D.sylow_normalizes_component (hPT (mem_map_of_mem A.subtype hp)) (l : G)
  have hPN' : (P : Subgroup A).map q ≤ normalizer (LA.map q : Set (alternatingGroup (Fin 7))) :=
    (map_mono hPN).trans (LA.le_normalizer_map q)
  obtain ⟨i,j,hij,hpair⟩ := Theory.SpecificGroups.Alternating.SevenFivePlacement.exists_fixed_pair
    (LA.map q) eimage (P.mapSurjective hq) hPN'
  constructor
  · ext l
    have hl : eLA.symm l ∈ (q.subgroupMap LA).ker ↔ l ∈ pCore 2 L := by
      rw [hker,← pCore_map_iso 2 eLA]
      exact (mem_map_equiv).symm
    change f (inclusion (c.le_component.trans le_sup_left) l) = 1 ↔ _
    rw [← hl]
    change _ ↔ q.subgroupMap LA (eLA.symm l) = 1
    rw [Subtype.ext_iff, Subtype.ext_iff]
    rfl
  · refine ⟨i,j,hij,?_⟩
    rw [← hpair]
    ext g
    constructor
    · rintro ⟨l,hl,rfl⟩
      exact ⟨q ⟨l,c.le_component hl⟩,
        ⟨⟨l,c.le_component hl⟩,hl,rfl⟩,rfl⟩
    · rintro ⟨b,⟨l,hl,rfl⟩,rfl⟩
      exact ⟨inclusion hAJ l,hl,rfl⟩

end CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness
