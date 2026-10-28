module
public import CFSG.Quasithin.ChapterE.Section02.ThompsonAction.PairedFiveBaumann
public import CFSG.Quasithin.ChapterE.Section02.ThompsonAction.PairResidualImages
public import Theory.Representation.BinaryPermutation.FivePairFixedSpaces

/-!
# The Baumann normalizer inside the original paired actor

Each transposition four-group in S₅ has normalizer of order eight.
Their product therefore has two-group normalizer. Transport through the
same marked-product embedding as the Baumann image puts its normalizer
inside the offender subgroup in a two-group. The original two-residual
maps into that subgroup, so a two-group centralizer kernel lifts the
conclusion to its Baumann-normalizer intersection.

Source: Aschbacher–Smith, E.2.3(3) and 10.2.1, pp.216–217 and 743.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher Representation Representation.BinaryOffender
open scoped IsMulCommutative
set_option backward.isDefEq.respectTransparency false
namespace CFSG.Quasithin.ChapterE.ThompsonAction
open ChapterB ChapterB.SourceInduction BinaryPermutation FivePairFixedSpaces

private theorem D_eq_pairClosure : Offenders.D 5 = pairClosure := by
  apply congrArg Subgroup.closure
  ext a
  constructor
  · rintro ⟨i,_,rfl⟩
    fin_cases i <;> simp [Offenders.pairSwap,first,second]
  · intro ha
    rcases ha with rfl | ha
    · exact ⟨0,by decide,rfl⟩
    · exact ⟨1,by decide,ha⟩

private theorem conjugate_D_normalizer_card (a : Perm) :
    Nat.card (normalizer ((Offenders.D 5).map (MulAut.conj a).toMonoidHom : Set Perm)) = 8 := by
  rw [←map_equiv_normalizer_eq,card_map_of_injective (MulAut.conj a).injective,
    D_eq_pairClosure,card_pairNormalizer]

private theorem product_normalizer (A B : Subgroup Perm) :
    normalizer (A.prod B : Set (Perm × Perm)) =
      (normalizer (A : Set Perm)).prod (normalizer (B : Set Perm)) := by
  ext g
  simp only [Subgroup.mem_prod,Subgroup.mem_normalizer_iff]
  constructor
  · intro h
    exact ⟨fun x => by simpa using h (x,1),fun x => by simpa using h (1,x)⟩
  · rintro ⟨hA,hB⟩ ⟨x,y⟩
    exact (hA x).and (hB y)

private theorem product_D_normalizer_isTwoGroup (a b : Perm) :
    IsPGroup 2 (normalizer
      (((Offenders.D 5).map (MulAut.conj a).toMonoidHom).prod
        ((Offenders.D 5).map (MulAut.conj b).toMonoidHom) : Set (Perm × Perm))) := by
  apply IsPGroup.of_card (n := 6)
  rw [product_normalizer,Nat.card_congr (Subgroup.prodEquiv _ _).toEquiv,Nat.card_prod,
    conjugate_D_normalizer_card,conjugate_D_normalizer_card]
  norm_num

variable {G H : Type*} [Group G] [Finite G] [Group H] [Finite H]

/-- A normalizer intersection in the original residual is a two-group when
the same centralizer quotient has the marked paired Baumann image. -/
theorem paired_residual_baumann_normalizer_isTwoGroup
    (T : Sylow 2 G) (hP : IsMinimalParabolicOver T ⊤)
    (U : Subgroup G) [U.Normal] [IsElementaryAbelian 2 U] (hU : IsPReduced 2 U)
    (hJ : ¬ elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (U : Set G))
    (q : G →* H) (hq : Function.Surjective q)
    (hker : q.ker = centralizer (U : Set G)) (hk : IsPGroup 2 q.ker)
    (d : SourceTwoFactorCase ((NormalElementaryQuotient.representation U q hq hker).comp
      (offenderSubgroup (NormalElementaryQuotient.representation U q hq hker)).subtype))
    (c : d.MarkedProduct (naturalRepresentation (Fin 5)))
    (hexchange : letI := offenderSubgroup_normal (NormalElementaryQuotient.representation U q hq hker)
      ∃ t : T.mapSurjective hq,
        d.first.map (MulAut.conjNormal (t:H)).toMonoidHom = d.second ∧
        d.second.map (MulAut.conjNormal (t:H)).toMonoidHom = d.first) :
    IsPGroup 2 (pResidual 2 G ⊓ normalizer (baumann (T : Subgroup G) : Set G) : Subgroup G) := by
  let α := NormalElementaryQuotient.representation U q hq hker
  let Y := offenderSubgroup α
  let j := Y.subtype.comp c.action.groupEquiv.symm.toMonoidHom
  have hj : Function.Injective j := Y.subtype_injective.comp c.action.groupEquiv.symm.injective
  obtain ⟨_,a,b,hBaum⟩ := paired_thompson_baumann_of_symmetric_model T hP U hU hJ q hq hker d c hexchange
  let F := ((Offenders.D 5).map (MulAut.conj a).toMonoidHom).prod
    ((Offenders.D 5).map (MulAut.conj b).toMonoidHom)
  have hres : (pResidual 2 G).map q ≤ Y := by
    rw [←paired_residual_factors_generate T hP U hU hJ q hq hker d,Subgroup.map_sup,
      paired_symmetric_first_residual_image α q hq d c,
      paired_symmetric_second_residual_image α q hq d c]
    exact sup_le ((map_le_range _ _).trans (by intro x hx; obtain ⟨a,rfl⟩ := hx; exact (c.action.groupEquiv.symm a).property))
      ((map_le_range _ _).trans (by intro x hx; obtain ⟨a,rfl⟩ := hx; exact (c.action.groupEquiv.symm a).property))
  let N := pResidual 2 G ⊓ normalizer (baumann (T : Subgroup G) : Set G)
  have hN : N.map q ≤ (normalizer (F : Set (Perm × Perm))).map j := by
    rintro _ ⟨x,hx,rfl⟩
    have hxY := hres (mem_map_of_mem q hx.1)
    let y : Y := ⟨q x,hxY⟩
    let z := c.action.groupEquiv y
    have hz : j z = q x := congrArg Y.subtype (c.action.groupEquiv.symm_apply_apply y)
    refine ⟨z,?_,hz⟩
    have hn : q x ∈ normalizer (F.map j : Set H) := by
      rw [←hBaum]
      exact (baumann (T : Subgroup G)).le_normalizer_map q (mem_map_of_mem q hx.2)
    have hh := (F.map j).le_normalizer_comap j (hz.symm ▸ hn)
    change z ∈ normalizer ((F.map j).comap j : Set (Perm × Perm)) at hh
    rw [comap_map_eq_self_of_injective hj] at hh
    exact hh
  have hNp : IsPGroup 2 (N.map q) :=
    ((product_D_normalizer_isTwoGroup a b).map j).to_le hN
  exact (hNp.comap_of_ker_isPGroup q hk).to_le (le_comap_map q N)

end CFSG.Quasithin.ChapterE.ThompsonAction
