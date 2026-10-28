module

public import CFSG.Quasithin.ChapterI.Section06To08.UniqueFixedOmega
public import BenderSuzuki.SE.ModelOuterSolvable
public import Theory.GroupTheory.SolvableSubgroupAutomorphisms
public import Theory.GroupTheory.PerfectCentralCoverOuter
public import Theory.GroupTheory.NormalCenterQuotient

/-!
# Lemma I.8.5

The structural theorem supplies the original quasisimple normal closure and
its Borel normalizer. The concrete simple Bender models have solvable outer
automorphism groups; faithful outer descent transfers this to the perfect
central cover. The automorphisms preserving V have solvable inner part, the
image of its Borel normalizer, and solvable outer quotient. Thus the actual
M/C_M(V) is solvable. If |V|=2, normality makes V central in M directly.

Both clauses now follow from the original unique-fixed-coset hypotheses.
There is no Shult, ZD, Bender recognition, omega-identification or
model-automorphism premise.

Source: Aschbacher--Smith, *The Classification of Quasithin Groups*, combined
1 March 2004 manuscript, Lemma I.8.5, printed p.430.
-/

noncomputable section
namespace CFSG.Quasithin.ChapterI.Section06To08
open Theory.GroupTheory BenderSuzuki Subgroup

variable {G : Type*} [Group G] [Finite G]

/-- I.8.5(2), on the literal actor quotient M/C_M(V). -/
public theorem lemma_I_8_5_automizer
    (V M : Subgroup G) [IsElementaryAbelian 2 V] [(V.subgroupOf M).Normal]
    (hVM : V ≤ M) (hVne : V ≠ ⊥) (hproper : M ≠ ⊤)
    (hfix : ∀ v : G, v ∈ V → v ≠ 1 → ∃! q : G ⧸ M, v • q = q) :
    Group.IsSolvable (M ⧸ centralizer (V.subgroupOf M : Set M)) := by
  rcases lemma_I_8_5_structure V M hVM hVne hproper hfix with
    ⟨hcard, _⟩ | ⟨hquasi, hmodel, hN, hB, _⟩
  · have hcardM : Nat.card (V.subgroupOf M) = 2 :=
      (Nat.card_congr (subgroupOfEquivOfLe hVM).toEquiv).trans hcard
    have hcent := central_of_normal_card_two (V.subgroupOf M) hcardM
    have hC : centralizer (V.subgroupOf M : Set M) = ⊤ :=
      centralizer_eq_top_iff_subset.mpr hcent
    let : Subsingleton (M ⧸ centralizer (V.subgroupOf M : Set M)) := by
      refine ⟨fun a b => ?_⟩
      obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective _ a
      obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective _ b
      apply QuotientGroup.eq.mpr
      rw [hC]
      exact mem_top _
    infer_instance
  · let L := normalClosure (V : Set G)
    let : IsQuasisimple L := hquasi
    let : Group.IsSolvable (MulAut.Outer (L ⧸ center L)) := hmodel.outer_isSolvable
    let : Group.IsSolvable (MulAut.Outer L) :=
      Group.isSolvable_of_isSolvable_injective
        (MulAut.centralQuotientOuter_injective (MulEquiv.refl (L ⧸ center L)))
    let : Group.IsSolvable (normalizer (V.subgroupOf L : Set L)) := hN ▸ hB.1
    exact MulAut.isSolvable_quotient_centralizer_of_normalizer L M V le_normalClosure
      ((normal_subgroupOf_iff_le_normalizer hVM).mp inferInstance)

/-- Both original clauses of I.8.5. The Bender alternative uses the actual
simple Bender central quotient of the quasisimple normal closure, and the
original subgroup and quotient maps throughout. -/
public theorem lemma_I_8_5
    (V M : Subgroup G) [IsElementaryAbelian 2 V] [(V.subgroupOf M).Normal]
    (hVM : V ≤ M) (hVne : V ≠ ⊥) (hproper : M ≠ ⊤)
    (hfix : ∀ v : G, v ∈ V → v ≠ 1 → ∃! q : G ⧸ M, v • q = q) :
    (let L := normalClosure (V : Set G)
     let N := M.comap L.subtype
     (Nat.card V = 2 ∧ pPrimeCore 2 L ⊔ V.subgroupOf L = ⊤) ∨
       (IsQuasisimple L ∧ BenderSuzuki.IsSimpleBenderGroup (L ⧸ center L) ∧
         N = normalizer (V.subgroupOf L : Set L) ∧ IsBorelSubgroup N ∧
         ∃ S : Sylow 2 L, (S : Subgroup L) ≤ N ∧
           V.subgroupOf L = (omega₁ S (p := 2)).map (S : Subgroup L).subtype)) ∧
      Group.IsSolvable (M ⧸ centralizer (V.subgroupOf M : Set M)) :=
  ⟨lemma_I_8_5_structure V M hVM hVne hproper hfix,
    lemma_I_8_5_automizer V M hVM hVne hproper hfix⟩

end CFSG.Quasithin.ChapterI.Section06To08
