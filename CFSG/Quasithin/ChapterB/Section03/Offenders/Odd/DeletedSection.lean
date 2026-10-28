module
public import Theory.Representation.BinaryConjugationSection.FiveNormalizer
public import CFSG.Quasithin.ChapterB.Section03.Offenders.Odd.ThompsonOrbits
public import CFSG.Quasithin.ChapterB.Section02.Baumann.FixedOrbit
public import Stellmacher.ElementaryAbelianMaxJFixedCenter
public import Stellmacher.ElementaryAbelianMaxJMap
public import Theory.GroupTheory.ElementaryThompsonFrattini

/-!
# Baumann fixed representatives in an original deleted A₅ section

The actual maximal elementary subgroups give a common transposition pair
image. Every deleted vector has an A₅ conjugate fixed by this image of J(S).
An elementary subgroup of S centralizing J(S) lies in Ω₁Z(J(S)), so the
Baumann subgroup fixes that representative as well. Conjugating back gives
the literal subgroup centralizer needed by the point Sylow argument.

Only the original section, a common normalizer containing J(S), and the
original surjective A₅ actor map are used; no full-module identification is
needed. Source: Aschbacher–Smith, 10.2.9(1), printed p.750, deleted case (2).
-/

public section
open Subgroup Representation Representation.BinaryOffender Stellmacher BinaryPermutation
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterB
noncomputable section
variable {G : Type*} [Group G] [Finite G]

theorem deleted_section_thompson_fixed_representative
    (S L W N : Subgroup G) [IsElementaryAbelian 2 W]
    (hS : IsPGroup 2 S) (hWS : W ≤ S) (hLN : L ≤ N)
    (hNW : N ≤ normalizer (W : Set G)) (hNL : N ≤ normalizer (L : Set G))
    (hJN : elementaryAbelianMaxJ S ≤ N)
    (q : L →* alternatingGroup (Fin 5)) (hq : Function.Surjective q)
    (c : BinaryConjugationSection L W ⊥ ((alternatingNaturalRepresentation (Fin 5)).comp q))
    (v : W) :
    ∃ l : L, (MulAut.conj (l : G)) (v : G) ∈
      W ⊓ centralizer (elementaryAbelianMaxJ S : Set G) := by
  have hWN : W ≤ N := c.section_le.trans hLN
  have hci : Function.Injective c.coordinates := by
    apply (MonoidHom.ker_eq_bot_iff _).mp
    rw [c.kernel_eq, bot_subgroupOf]
  obtain ⟨π, hπ, hmark⟩ := c.exists_five_normalizer_action L W N hLN hNW hNL q hq
  let U := W.subgroupOf N
  let R := S.subgroupOf N
  let : U.Normal := normal_subgroupOf_of_le_normalizer hNW
  let : IsElementaryAbelian 2 U := IsElementaryAbelian.subgroupOf hWN
  let eW : U ≃* W := subgroupOfEquivOfLe hWN
  let E : Additive U ≃ₗ[ZMod 2] natural (Fin 5) := LinearEquiv.ofBijective
    ((c.coordinates.comp eW.toMonoidHom).toAdditiveLeft.toZModLinearMap 2)
    ⟨hci.comp eW.injective, c.onto.comp eW.surjective⟩
  have hker : π.ker = centralizer (U : Set N) := by
    ext n
    constructor
    · intro hn w hw
      have hh := hπ n (eW ⟨w, hw⟩)
      rw [show π n = 1 from hn, map_one, Module.End.one_apply] at hh
      have he := hci (Multiplicative.toAdd.injective hh)
      have he' := congrArg Subtype.val he
      change (n : G) * (w : G) * (n : G)⁻¹ = (w : G) at he'
      apply Subtype.ext
      exact (mul_inv_eq_iff_eq_mul.mp he').symm
    · intro hn
      change π n = 1
      apply naturalMulAction_injective_of_odd (Fin 5) (by decide)
      apply MulEquiv.ext
      intro w
      obtain ⟨w, rfl⟩ := c.onto w
      apply Multiplicative.toAdd.injective
      have hc := congrArg N.subtype (hn ⟨w, hWN w.property⟩ w.property)
      change (w : G) * (n : G) = (n : G) * (w : G) at hc
      have he : (⟨(n : G) * w * (n : G)⁻¹,
          (mem_normalizer_iff.mp (hNW n.property) w).mp w.property⟩ : W) = w := by
        apply Subtype.ext
        change (n : G) * (w : G) * (n : G)⁻¹ = (w : G)
        rw [← hc, mul_inv_cancel_right]
      have hh := hπ n w
      rw [he] at hh
      change naturalRepresentation (Fin 5) (π n) (c.coordinates w).toAdd =
        naturalRepresentation (Fin 5) 1 (c.coordinates w).toAdd
      rw [map_one, Module.End.one_apply]
      exact hh.symm
  have he (n : N) (w : Additive U) : E (NoncentralChiefRefinement.normalRepresentation U n w) =
      naturalRepresentation (Fin 5) (π n) (E w) := hπ n (eW w.toMul)
  obtain ⟨a, ha⟩ := Offenders.thompson_image_le_pair U R
    (fun w hw => hWS hw) hS.comap_subtype π hker E he
  have hJmap : (elementaryAbelianMaxJ R).map N.subtype = elementaryAbelianMaxJ S := by
    rw [← elementaryAbelianMaxJ_map_injective N.subtype N.subtype_injective,
      subgroupOf_map_subtype]
    exact elementaryAbelianMaxJ_eq_of_intermediate S (S ⊓ N)
      (le_inf (sSup_le fun _ hA => hA.1) hJN) inf_le_left
  obtain ⟨g, hg⟩ := FivePairFixedSpaces.exists_even_moves_to_conjugate_pair_fixed_natural
    a (c.coordinates v).toAdd
  obtain ⟨l, hl⟩ := hq g
  let w : W := ⟨(l : G) * v * (l : G)⁻¹,
    (mem_normalizer_iff.mp (c.normalized l.property) v).mp v.property⟩
  have hwcoord : (c.coordinates w).toAdd = naturalRepresentation (Fin 5) g.val
      (c.coordinates v).toAdd := by
    have hh := c.equivariant l v
    change (c.coordinates w).toAdd = naturalRepresentation (Fin 5) (q l).val
      (c.coordinates v).toAdd at hh
    rwa [hl] at hh
  have hwJ : (w : G) ∈ centralizer (elementaryAbelianMaxJ S : Set G) := by
    intro j hj
    rw [← hJmap] at hj
    obtain ⟨j, hj, rfl⟩ := hj
    have hh := hπ j w
    rw [hwcoord, hg _ (ha (mem_map_of_mem π hj)), ← hwcoord] at hh
    have hh' := congrArg Subtype.val (hci (Multiplicative.toAdd.injective hh))
    exact mul_inv_eq_iff_eq_mul.mp hh'
  exact ⟨l, w.property, hwJ⟩

theorem deleted_section_baumann_conjugate_centralizes
    (S L W N : Subgroup G) [IsElementaryAbelian 2 W]
    (hS : IsPGroup 2 S) (hWS : W ≤ S) (hLN : L ≤ N)
    (hNW : N ≤ normalizer (W : Set G)) (hNL : N ≤ normalizer (L : Set G))
    (hJN : elementaryAbelianMaxJ S ≤ N)
    (q : L →* alternatingGroup (Fin 5)) (hq : Function.Surjective q)
    (c : BinaryConjugationSection L W ⊥ ((alternatingNaturalRepresentation (Fin 5)).comp q))
    (v : W) :
    ∃ l : L, (baumann S).map (MulAut.conj (l : G)⁻¹).toMonoidHom ≤
      centralizer ({(v : G)} : Set G) := by
  obtain ⟨l, hl⟩ := deleted_section_thompson_fixed_representative S L W N hS hWS hLN
    hNW hNL hJN q hq c v
  exact ⟨l, baumann_conjugate_centralizes_of_thompson_fixed_representative
    S W hWS v l hl⟩

end
end CFSG.Quasithin.ChapterB
