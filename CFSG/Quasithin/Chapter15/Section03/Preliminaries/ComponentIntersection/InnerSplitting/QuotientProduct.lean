module

public import CFSG.Quasithin.Chapter15.Section03.Preliminaries.ComponentIntersection.QuotientCoordinates
public import Theory.GroupTheory.PCoreImage
public import Theory.GroupTheory.SylowNormalRestriction
public import Theory.GroupTheory.SylowImageIntersection
public import Theory.GroupTheory.CoprimeQuotientSubgroups
public import Theory.GroupTheory.NormalizedSupCard
public import Theory.GroupTheory.DisjointCommutingProduct

/-!
# Quotient orders after the inner-action splitting

For normal factors with a two-group intersection, their images in an odd
two-core quotient are disjoint. This is proved by lifting both images into
a common Sylow three-subgroup, on which the quotient map is injective.
Their orders therefore multiply. If one factor has two-core quotient of
order three, the nonabelian order-27 alternative would have two abelian
commuting factors, a contradiction. The remaining quotient orders are
nine and three.

Source: Aschbacher–Smith, combined manuscript (1 March 2004),
15.3.12(2), printed p.1125 (PDF p.1142). The two numerical alternatives
here are consequences of 15.3.11(5i), supplied at the final assembly.
-/

public section

open Subgroup
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section03.ComponentIntersection.InnerSplitting

private theorem quotient_image_card {H : Type*} [Group H] [Finite H]
    (A : Subgroup H) [A.Normal] :
    Nat.card (A.map (QuotientGroup.mk' (pCore 2 H))) = Nat.card (A ⧸ pCore 2 A) := by
  let f := (QuotientGroup.mk' (pCore 2 H)).comp A.subtype
  have hk : f.ker = pCore 2 A := by
    apply le_antisymm
    · have hh : f.ker = (pCore 2 H).comap A.subtype := by
        ext a
        exact QuotientGroup.eq_one_iff _
      have hp : IsPGroup 2 f.ker := by
        rw [hh]
        exact pCore_isPGroup.comap_subtype
      exact le_sSup ⟨inferInstance, hp⟩
    · intro a ha
      have hle : (pCore 2 A).map A.subtype ≤ pCore 2 H :=
        le_sSup ⟨inferInstance, pCore_isPGroup.map A.subtype⟩
      exact (QuotientGroup.eq_one_iff _).mpr (hle ⟨a, ha, rfl⟩)
  have he : Nat.card (A ⧸ pCore 2 A) = Nat.card f.range := by
    rw [← hk]
    exact Nat.card_congr (QuotientGroup.quotientKerEquivRange f).toEquiv
  rw [MonoidHom.range_comp, range_subtype] at he
  exact he.symm

private theorem disjoint_images {H : Type*} [Group H] [Finite H]
    (A C : Subgroup H) [A.Normal] [C.Normal]
    (hInf : IsPGroup 2 (A ⊓ C : Subgroup H))
    (hq : IsPGroup 3 (H ⧸ pCore 2 H)) :
    Disjoint (A.map (QuotientGroup.mk' (pCore 2 H)))
      (C.map (QuotientGroup.mk' (pCore 2 H))) := by
  let q := QuotientGroup.mk' (pCore 2 H)
  let P : Sylow 3 H := Sylow.nonempty.some
  have hPq : (P : Subgroup H).map q = ⊤ := by
    exact top_unique ((hq.to_subgroup ⊤).le_sylow_of_normal
      (P.mapSurjective (QuotientGroup.mk'_surjective _)))
  have hcop : Nat.Coprime 3 (Nat.card q.ker) := by
    rw [QuotientGroup.ker_mk']
    obtain ⟨n, hn⟩ := (pCore_isPGroup (p := 2) (G := H)).exists_card_eq
    rw [hn]
    exact (by decide : Nat.Coprime 3 2).pow_right n
  have hqi := injective_comp_subtype_of_coprime_ker q hcop (P : Subgroup H) P.isPGroup'
  obtain ⟨PA, hPA⟩ := P.exists_sylow_map_eq_inf_of_normal A
  obtain ⟨PC, hPC⟩ := P.exists_sylow_map_eq_inf_of_normal C
  have hAq : ((P : Subgroup H) ⊓ A).map q = A.map q := by
    simpa only [hPq, top_inf_eq] using P.map_image_eq_inf A _ PA hPA inf_le_left q
  have hCq : ((P : Subgroup H) ⊓ C).map q = C.map q := by
    simpa only [hPq, top_inf_eq] using P.map_image_eq_inf C _ PC hPC inf_le_left q
  apply disjoint_def.mpr
  intro x hxA hxC
  rw [← hAq] at hxA
  rw [← hCq] at hxC
  obtain ⟨a, ha, rfl⟩ := hxA
  obtain ⟨c, hc, he⟩ := hxC
  have hac : a = c := congrArg Subtype.val (hqi (a₁ := ⟨a, ha.1⟩) (a₂ := ⟨c, hc.1⟩) he.symm)
  have hd := IsPGroup.disjoint_of_ne 3 2 (by decide) (P : Subgroup H) (A ⊓ C)
    P.isPGroup' hInf
  have ha1 : a = 1 := hd.le_bot ⟨ha.1, ha.2, hac.symm ▸ hc.2⟩
  exact ha1 ▸ q.map_one

/-- A split normal product with a two-group intersection cannot give the
nonabelian order-27 alternative of 15.3.11(5). -/
theorem quotient_orders_of_normal_product
    {H : Type*} [Group H] [Finite H]
    (A C : Subgroup H) [A.Normal] [C.Normal]
    (hgen : A ⊔ C = ⊤) (hInf : IsPGroup 2 (A ⊓ C : Subgroup H))
    (ha : Nat.card (A ⧸ pCore 2 A) = 3)
    (hq : IsPGroup 3 (H ⧸ pCore 2 H))
    (hshape : Nat.card (H ⧸ pCore 2 H) = 9 ∨
      (Nat.card (H ⧸ pCore 2 H) = 27 ∧ ¬ IsMulCommutative (H ⧸ pCore 2 H))) :
    Nat.card (H ⧸ pCore 2 H) = 9 ∧ Nat.card (C ⧸ pCore 2 C) = 3 := by
  let q := QuotientGroup.mk' (pCore 2 H)
  let B := A.map q
  let D := C.map q
  let : B.Normal := Subgroup.Normal.map inferInstance q (QuotientGroup.mk'_surjective _)
  let : D.Normal := Subgroup.Normal.map inferInstance q (QuotientGroup.mk'_surjective _)
  have hb : Nat.card B = 3 := (quotient_image_card A).trans ha
  have hd := quotient_image_card C
  have hdis : Disjoint B D := disjoint_images A C hInf hq
  have hsup : B ⊔ D = ⊤ := by
    rw [← Subgroup.map_sup, hgen, map_top_of_surjective q (QuotientGroup.mk'_surjective _)]
  have hsize : Nat.card (H ⧸ pCore 2 H) = 3 * Nat.card D := by
    have hh := card_sup_eq_mul_of_normalizes_of_disjoint B D le_normalizer_of_normal hdis
    simpa only [hsup, card_top, hb] using hh
  have h9 : Nat.card (H ⧸ pCore 2 H) = 9 := by
    rcases hshape with h9 | ⟨h27, hnoncomm⟩
    · exact h9
    · have hd9 : Nat.card D = 9 := by omega
      let : IsMulCommutative D := IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := 3) hd9
      let : IsCyclic B := isCyclic_of_prime_card hb
      have hcomm : B ≤ centralizer (D : Set (H ⧸ pCore 2 H)) := by
        apply commutator_eq_bot_iff_le_centralizer.mp
        exact eq_bot_iff.mpr ((commutator_le_inf B D).trans hdis.le_bot)
      obtain ⟨e, _⟩ := exists_mulEquiv_prod_sup_of_disjoint_of_commuting B D hdis hcomm
      let E : B × D ≃* (H ⧸ pCore 2 H) := e.trans ((MulEquiv.subgroupCongr hsup).trans topEquiv)
      have hc : IsMulCommutative (H ⧸ pCore 2 H) := ⟨⟨fun x y => by
        apply E.symm.injective
        simp only [map_mul]
        exact mul_comm' _ _⟩⟩
      exact (hnoncomm hc).elim
  refine ⟨h9, ?_⟩
  change Nat.card D = Nat.card (C ⧸ pCore 2 C) at hd
  rw [← hd]
  omega

end CFSG.Quasithin.Chapter15.Section03.ComponentIntersection.InnerSplitting

end
