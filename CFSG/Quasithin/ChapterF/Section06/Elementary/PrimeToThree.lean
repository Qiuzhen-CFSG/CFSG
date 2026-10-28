module

public import CFSG.Quasithin.ChapterF.Section06.Elementary.PrimeToThree.Reduction
public import CFSG.Quasithin.ChapterF.Section06.Elementary.PrimeToThree.CyclicObstruction

/-!
# The prime-to-three-core dichotomy for Goldschmidt triples

The prime-to-three core has the ambient two-core as a Sylow two-subgroup
and is solvable (`primeToThreeCore_structure`). Its intersection with each
local group is exactly that two-core, so the actual quotient images form
an amalgam compatibly isomorphic to the three quotients by the two-core.
The common Sylow image has index three in each local image. Thus either
the full intersection is preserved and the quotient is a Goldschmidt triple
with trivial two-core, or the images collapse to the whole symmetric-three
quotient. In the collapsed case, reduction modulo the two-core and the
cubic-residual obstruction prove that the core quotient cannot be cyclic.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*,
Lemma F.6.11, printed pp.306–307 (1 March 2004 manuscript).
-/

public section

open Subgroup Theory.GroupTheory
open scoped Pointwise
namespace CFSG.Quasithin.ChapterF
variable {G : Type*} [Group G] [Finite G] {G₁ G₂ : Subgroup G}

theorem IsGoldschmidtTriple.primeToThreeCore_collapsed_noncyclic
    (h : IsGoldschmidtTriple G₁ G₂)
    (he : G₁.map (QuotientGroup.mk' (pPrimeCore 3 G)) =
      G₂.map (QuotientGroup.mk' (pPrimeCore 3 G))) :
    ¬ IsCyclic ((pPrimeCore 3 G) ⧸ (pCore 2 G).subgroupOf (pPrimeCore 3 G)) := by
  intro hcyc
  let _ := hcyc
  let pi := QuotientGroup.mk' (pCore 2 G)
  let A := G₁.map pi
  let B := G₂.map pi
  let X := pPrimeCore 3 (G ⧸ pCore 2 G)
  have hbar : IsGoldschmidtTriple A B := h.quotient_twoCore
  have hzero : pCore 2 (G ⧸ pCore 2 G) = ⊥ := h.quotient_twoCore_eq_bot
  obtain ⟨hs₁, hs₂⟩ := h.primeToThreeCore_collapsed_sup he
  have hAX : A ⊔ X = ⊤ := h.primeToThreeCore_supplement_mod_twoCore hs₁
  have hBX : B ⊔ X = ⊤ := h.symm.primeToThreeCore_supplement_mod_twoCore hs₂
  obtain ⟨eA⟩ := hbar.left_equiv_symmetricThree_of_supplement hzero hAX
  obtain ⟨eB⟩ := hbar.symm.left_equiv_symmetricThree_of_supplement hzero hBX
  let eX := primeToThreeCoreQuotientTwoCoreEquiv (G := G)
  let _ : IsCyclic X := isCyclic_of_surjective eX.toMonoidHom eX.surjective
  exact cyclic_primeToThree_supplements_impossible hbar X pPrimeCore_coprime_card
    eA eB hAX (hbar.left_inf_primeToThreeCore.trans hzero)

/-- The exact two alternatives of F.6.11(2). The first carries the full
overlap, a genuine Goldschmidt triple with trivial two-core, and an amalgam
isomorphism whose two commuting squares use the original quotient maps.
The second includes a genuine S₃ isomorphism, the literal supplement
product, and noncyclicity of the intrinsic quotient of the prime-to-three core. -/
theorem IsGoldschmidtTriple.primeToThreeCore_dichotomy
    (h : IsGoldschmidtTriple G₁ G₂) :
    (G₁.map (QuotientGroup.mk' (pPrimeCore 3 G)) ⊓
        G₂.map (QuotientGroup.mk' (pPrimeCore 3 G)) =
        (G₁ ⊓ G₂).map (QuotientGroup.mk' (pPrimeCore 3 G)) ∧
      IsGoldschmidtTriple (G₁.map (QuotientGroup.mk' (pPrimeCore 3 G)))
        (G₂.map (QuotientGroup.mk' (pPrimeCore 3 G))) ∧
      pCore 2 (G ⧸ pPrimeCore 3 G) = ⊥ ∧
      Nonempty (RankTwoAmalgam.Iso
        (RankTwoAmalgam.ofSubgroupQuotients (QuotientGroup.mk' (pCore 2 G))
          G₁ (G₁ ⊓ G₂) G₂ inf_le_left inf_le_right)
        (RankTwoAmalgam.ofSubgroups
          (G₁.map (QuotientGroup.mk' (pPrimeCore 3 G)))
          ((G₁ ⊓ G₂).map (QuotientGroup.mk' (pPrimeCore 3 G)))
          (G₂.map (QuotientGroup.mk' (pPrimeCore 3 G)))
          (Subgroup.map_mono inf_le_left) (Subgroup.map_mono inf_le_right)))) ∨
    ((pCore 2 G₁).map G₁.subtype = pCore 2 G ∧
      (pCore 2 G₂).map G₂.subtype = pCore 2 G ∧
      Nonempty ((G ⧸ pPrimeCore 3 G) ≃* Equiv.Perm (Fin 3)) ∧
      (G₁ : Set G) * (pPrimeCore 3 G : Set G) = Set.univ ∧
      ¬ IsCyclic ((pPrimeCore 3 G) ⧸ (pCore 2 G).subgroupOf (pPrimeCore 3 G))) := by
  rcases h.primeToThreeCore_image_intersection_or_eq with hi | he
  · exact Or.inl ⟨hi, h.quotient_primeToThreeCore_of_intersection hi,
      h.primeToThreeCore_quotient_twoCore_eq_bot, ⟨h.primeToThreeCoreAmalgamIso⟩⟩
  · obtain ⟨h₁, h₂, e, hprod, _⟩ := h.primeToThreeCore_collapsed_structure he
    exact Or.inr ⟨h₁, h₂, e, hprod, h.primeToThreeCore_collapsed_noncyclic he⟩

end CFSG.Quasithin.ChapterF
