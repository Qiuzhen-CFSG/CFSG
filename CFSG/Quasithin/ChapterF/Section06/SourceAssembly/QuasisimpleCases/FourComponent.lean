module

public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.QuasisimpleCases.FourLocal
public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.ComponentSieve.OrderFour
public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.ComponentProduct.PrimeModel
public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.ComponentExclusions.SmallIntersection
public import Theory.ElementaryAbelian.Injective
/-!
# The prime-field component in the four-element Sylow branch

The compatible four-element amalgam gives an elementary common Sylow.
Its intersection with the actual component, followed by the literal central
projection, supplies the elementary Sylow input to the complete Theorem C
sieve. The original O₃′ quotient removes the central covering kernel.

If the two-residual is quasisimple, its Sylow subgroup has order greater
than two by transfer and therefore has all four elements of the common
Sylow. The residual supplement identity makes the whole group that component.
This proves the group-model part of F.6.18(4) from the earlier A/C inputs.

Source: Aschbacher–Smith F.6.18, fourth and fifth proof paragraphs, p.310.
-/

public section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterF.SourceAssembly
universe u
variable {G H : Type u} [Group G] [Finite G] [Group H] [Finite H]
    {κ : GroupClass.{u}} {G₁ G₂ K : Subgroup G}

theorem component_small_elementary_sylow_of_intersection_four
    (h : IsGoldschmidtTriple G₁ G₂) (hcore : pCore 2 G = ⊥)
    (hT : Nat.card (G₁ ⊓ G₂ : Subgroup G) = 4) (hK : IsComponent G K) :
    ∃ P : Sylow 2 K, IsElementaryAbelian 2 P ∧ Nat.card P ≤ 4 := by
  obtain ⟨hE, _, _⟩ := four_intersection_models h hcore hT
  let : IsElementaryAbelian 2 (G₁ ⊓ G₂ : Subgroup G) := hE
  obtain ⟨P, hP⟩ := h.subnormal_intersection_sylow K hK.1
  let f : P →* (G₁ ⊓ G₂ : Subgroup G) :=
    (K.subtype.comp (P : Subgroup K).subtype).codRestrict _ (fun x => by
      exact hP.le x.property)
  have hf : Function.Injective f := by
    intro x y hxy
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun z : (G₁ ⊓ G₂ : Subgroup G) => (z : G)) hxy
  exact ⟨P, IsElementaryAbelian.of_injective f hf,
    (Nat.card_le_card_of_injective f hf).trans_eq hT⟩

theorem component_prime_psl_of_intersection_four
    (hA : ChapterA.Section02.TheoremA κ H)
    (hC : ChapterA.Section02.TheoremC κ (K ⧸ center K))
    (hH : IsSQTK κ H) (e : G ≃* (H ⧸ pPrimeCore 3 H))
    (h : IsGoldschmidtTriple G₁ G₂) (hT : Nat.card (G₁ ⊓ G₂ : Subgroup G) = 4)
    (hK : IsComponent G K) :
    ∃ p : ℕ, p.Prime ∧ Odd p ∧ 3 < p ∧ (p % 8 = 3 ∨ p % 8 = 5) ∧
      center K = ⊥ ∧ Nonempty (K ≃* PSL(2, ZMod p)) := by
  have hcore : pCore 2 G = ⊥ := le_bot_iff.mp
    (twoCore_le_primeToThreeCore.trans (Noncyclic.primeToThreeCore_eq_bot_of_quotient e).le)
  obtain ⟨P, hP, hcard⟩ := component_small_elementary_sylow_of_intersection_four h hcore hT hK
  let : IsElementaryAbelian 2 P := hP
  let S := P.mapSurjective (QuotientGroup.mk'_surjective (center K))
  let : IsElementaryAbelian 2 S := IsElementaryAbelian.map (QuotientGroup.mk' (center K))
  have hS : Nat.card S ≤ 4 :=
    (Nat.le_of_dvd (Nat.card_pos (α := P))
      ((P : Subgroup K).card_map_dvd (QuotientGroup.mk' (center K)))).trans hcard
  let : IsQuasisimple K := hK.2
  let : IsSimpleGroup (K ⧸ center K) := IsQuasisimple.simple
  let : Group.IsPerfect (K ⧸ center K) :=
    Group.IsPerfect.ofSurjective (QuotientGroup.mk'_surjective (center K))
  have hm := component_central_quotient_model hA hC hH
    (e.symm.toMonoidHom.comp (QuotientGroup.mk' (pPrimeCore 3 H)))
    (e.symm.surjective.comp (QuotientGroup.mk'_surjective _)) hK
  obtain ⟨p, hp, ho, hr, hm⟩ := prime_psl2_of_theoremC_small_elementary_sylow
    S hS (Group.IsPerfect.not_isSolvable _) hm
  let : Fact p.Prime := ⟨hp⟩
  obtain ⟨hz, _, he⟩ := prime_psl_component_center_and_outer e hK ho hm
  exact ⟨p, hp, ho, prime_psl_component_prime_gt_three hK ho hm, hr, hz, he⟩


theorem quasisimple_residual_eq_top_of_intersection_four
    (h : IsGoldschmidtTriple G₁ G₂)
    (hT : Nat.card (G₁ ⊓ G₂ : Subgroup G) = 4)
    (hL : IsQuasisimple (pResidual 2 G)) : pResidual 2 G = ⊤ := by
  let K := pResidual 2 G
  let : IsQuasisimple K := hL
  let : IsSimpleGroup (K ⧸ center K) := IsQuasisimple.simple
  let : Nontrivial K := (QuotientGroup.mk'_surjective (center K)).nontrivial
  obtain ⟨P, hP⟩ := h.subnormal_intersection_sylow K
    (inferInstance : K.Normal).isSubnormal
  have heven : Even (Nat.card K) := by
    by_contra! hh
    exact Group.IsPerfect.not_isSolvable K (odd_order_theorem K (Nat.not_even_iff_odd.mp hh))
  have hp := perfect_sylow_two_card_gt_two P heven
  have himage : (P : Subgroup K).map K.subtype = (G₁ ⊓ G₂) ⊓ K := by
    rw [hP, subgroupOf_map_subtype]
  have hcard : Nat.card ((P : Subgroup K).map K.subtype) = Nat.card P :=
    card_map_of_injective K.subtype_injective
  have hd : Nat.card P ∣ 4 := by
    rw [← hT, ← hcard]
    exact card_dvd_of_le (himage.le.trans inf_le_left)
  have hp4 : Nat.card P = 4 := by
    have hh := (Nat.dvd_prime_pow Nat.prime_two).mp (show Nat.card P ∣ 2 ^ 2 from hd)
    obtain ⟨n, hn, he⟩ := hh
    interval_cases n
    · rw [he] at hp
      norm_num at hp
    · rw [he] at hp
      norm_num at hp
    · simpa using he
  have heq : (P : Subgroup K).map K.subtype = G₁ ⊓ G₂ :=
    eq_of_le_of_card_ge (himage.le.trans inf_le_left) (by rw [hcard, hp4, hT])
  have hTK : G₁ ⊓ G₂ ≤ K := by
    rw [← heq]
    exact map_subtype_le _
  obtain ⟨T, ht⟩ := h.intersection_sylow
  apply top_unique
  rw [← pResidual_sup_sylow_eq_top T]
  exact sup_le le_rfl (ht ▸ hTK)

theorem quasisimple_four_prime_model
    (hA : ChapterA.Section02.TheoremA κ H)
    (hC : ∀ (S : Type u) [Group S] [Finite S], ChapterA.Section02.TheoremC κ S)
    (hH : IsSQTK κ H) (e : G ≃* (H ⧸ pPrimeCore 3 H))
    (h : IsGoldschmidtTriple G₁ G₂) (hT : Nat.card (G₁ ⊓ G₂ : Subgroup G) = 4)
    (hL : pResidual 2 G = generalizedFitting G ∧ IsQuasisimple (pResidual 2 G)) :
    generalizedFitting G = ⊤ ∧ IsQuasisimple G ∧
      ∃ p : ℕ, p.Prime ∧ Odd p ∧ 3 < p ∧ (p % 8 = 3 ∨ p % 8 = 5) ∧
        Nonempty (G ≃* PSL(2, ZMod p)) := by
  have ht := quasisimple_residual_eq_top_of_intersection_four h hT hL.2
  have hK : IsComponent G (pResidual 2 G) :=
    ⟨(inferInstance : (pResidual 2 G).Normal).isSubnormal, hL.2⟩
  obtain ⟨p, hp, ho, hlarge, hr, _, he⟩ :=
    component_prime_psl_of_intersection_four hA (hC _) hH e h hT hK
  let f : pResidual 2 G ≃* G := (MulEquiv.subgroupCongr ht).trans topEquiv
  let : IsQuasisimple (pResidual 2 G) := hL.2
  exact ⟨hL.1.symm.trans ht, IsQuasisimple.of_mulEquiv f,
    p, hp, ho, hlarge, hr, he.map (fun j => f.symm.trans j)⟩
end CFSG.Quasithin.ChapterF.SourceAssembly
