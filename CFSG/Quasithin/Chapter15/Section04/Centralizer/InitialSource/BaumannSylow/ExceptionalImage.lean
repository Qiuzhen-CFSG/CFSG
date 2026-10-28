module
public import CFSG.Quasithin.Chapter15.Section04.Centralizer.InitialSource.BaumannSylow.ExceptionalModule
public import CFSG.Quasithin.Chapter15.Section04.Centralizer.InitialSource.ThompsonGeneration
public import Theory.GroupTheory.PResidual.NormalSubgroup
public import Theory.GroupTheory.SolvableOuterQuotient

/-!
# The canonical moved action in the minimal-parabolic application

The full cubic preimage and the original Sylow subgroup generate the
minimal parabolic, by the preceding Thompson generation theorem. Their
images identify the actual two-residual with the full cubic product in
the star quotient. On the global Thompson preimage the moved action and
star map have exactly the same kernel. Consequently their residual and
Thompson image orders agree, and the full moved-action kernel is a
two-group.

Source: Aschbacher--Smith B.2.16, B.6.10 and15.4.11, pp.79,117 and1160.
-/

@[expose] public noncomputable section
open Subgroup Stellmacher
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section04.InitialSource.BaumannSylow
open Chapter1.RadicalNormalizers.ThompsonSource FamilySource.ThompsonFactors
variable {H : Type*} [Group H] [Finite H] {S : Sylow 2 H}
  [IsElementaryAbelian 2 (Chapter1.RadicalNormalizers.ThompsonSource.closure S)]

def cubicPreimage (d : Exceptional S) : Subgroup H :=
  (cubicProduct d Finset.univ).comap (starMap (closure S))

instance cubicPreimage_normal (d : Exceptional S) : (cubicPreimage d).Normal := by
  exact (cubicProduct_normal d).comap (starMap (closure S))

omit [Finite H] in
theorem cubicPreimage_image (d : Exceptional S) :
    (cubicPreimage d).map (starMap (closure S)) = cubicProduct d Finset.univ :=
  map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _) _

theorem cubicPreimage_sup_sylow (d : Exceptional S)
    (hc : d.count = 1 ∨ d.count = 2)
    (hker : centralizer (closure S : Set H) = pCore 2 H)
    (hunique : Order.HasUniqueMaximalOver (S : Subgroup H) ⊤) :
    cubicPreimage d ⊔ (S : Subgroup H) = ⊤ := by
  apply exceptional_sup_sylow_eq_top S d hker hunique
  rw [cubicPreimage_image]
  change thompsonImage ≤ _
  rw [←cubicProduct_sylow_sup d hc]
  apply sup_le le_sup_left
  exact (map_mono (sSup_le fun A hA => hA.1)).trans le_sup_right

private theorem three_isTwoPerfect {A : Type*} [Group A]
    (h : IsPGroup 3 A) : IsPPerfect 2 A := by
  intro K hK hk
  let := hK
  have hd := IsPGroup.disjoint_of_coprime
    ((h.to_quotient K).to_subgroup ⊤) (hk.to_subgroup ⊤)
    (by decide : Nat.Coprime 3 2)
  apply top_unique
  intro a _
  apply (QuotientGroup.eq_one_iff a).mp
  exact Subgroup.disjoint_def.mp hd (mem_top _) (mem_top _)

theorem residual_star_image (d : Exceptional S)
    (hc : d.count = 1 ∨ d.count = 2)
    (hker : centralizer (closure S : Set H) = pCore 2 H)
    (hunique : Order.HasUniqueMaximalOver (S : Subgroup H) ⊤) :
    (pResidual 2 H).map (starMap (closure S)) = cubicProduct d Finset.univ := by
  classical
  let := cubicProduct_normal d
  have hi : (Finset.univ : Finset (Fin d.count)).card = 1 ∨
      (Finset.univ : Finset (Fin d.count)).card = 2 := by simpa using hc
  let := cubicProduct_elementary d Finset.univ hi
  have hq : Function.Surjective (starMap (closure S)) := QuotientGroup.mk'_surjective _
  have hsup : cubicProduct d Finset.univ ⊔
      (S : Subgroup H).map (starMap (closure S)) = ⊤ := by
    have h := congrArg (Subgroup.map (starMap (closure S)))
      (cubicPreimage_sup_sylow d hc hker hunique)
    simpa only [Subgroup.map_sup,cubicPreimage_image,
      map_top_of_surjective _ hq] using h
  rw [map_pResidual_of_surjective 2 _ hq]
  exact pResidual_eq_of_isPPerfect_sup _ _
    (three_isTwoPerfect (IsElementaryAbelian.isPGroup 3 _)) (S.isPGroup'.map _) hsup

/-- The literal conjugation image on the moved group has the original
star image order for every subgroup in the global Thompson preimage. -/
theorem conjugation_image_card (d : Exceptional S) (B : Subgroup H)
    (hB : B.map (starMap (closure S)) ≤ thompsonImage (S := S)) :
    Nat.card (B.map (MulAut.conjNormal : H →* MulAut (moduleGroup d))) =
      Nat.card (B.map (starMap (closure S))) := by
  let f := (MulAut.conjNormal : H →* MulAut (moduleGroup d)).comp B.subtype
  let q := (starMap (closure S)).comp B.subtype
  have hk : f.ker = q.ker := by
    ext b
    constructor
    · intro hb
      have hcentral : (b : H) ∈ centralizer (moduleGroup d : Set H) := by
        rw [←MulAut.conjNormal_ker_eq_centralizer]
        exact hb
      exact centralizer_star_eq_one d b (hB (mem_map_of_mem _ b.property)) hcentral
    · intro hb
      have hcentral : (b : H) ∈ centralizer (closure S : Set H) :=
        (QuotientGroup.eq_one_iff (b : H)).mp hb
      have hw := (centralizer_le (moduleGroup_le d)) hcentral
      rw [←MulAut.conjNormal_ker_eq_centralizer] at hw
      exact hw
  have hf : f.range = B.map (MulAut.conjNormal : H →* MulAut (moduleGroup d)) := by
    rw [MonoidHom.range_comp,range_subtype]
  have hq : q.range = B.map (starMap (closure S)) := by
    rw [MonoidHom.range_comp,range_subtype]
  rw [←hf,←hq,←Nat.card_congr (QuotientGroup.quotientKerEquivRange f).toEquiv,
    hk,Nat.card_congr (QuotientGroup.quotientKerEquivRange q).toEquiv]

theorem moduleGroup_centralizer_two (d : Exceptional S)
    (hc : d.count = 1 ∨ d.count = 2)
    (hker : centralizer (closure S : Set H) = pCore 2 H)
    (hunique : Order.HasUniqueMaximalOver (S : Subgroup H) ⊤) :
    IsPGroup 2 (centralizer (moduleGroup d : Set H)) := by
  let X := cubicPreimage d
  let C := centralizer (moduleGroup d : Set H)
  have hquot : IsPGroup 2 (H ⧸ X) :=
    isPGroup_quotient_of_sup_eq_top X (S : Subgroup H) S.isPGroup'
      (cubicPreimage_sup_sylow d hc hker hunique)
  let q := (QuotientGroup.mk' X).comp C.subtype
  have hqker : IsPGroup 2 q.ker := by
    let f : q.ker →* pCore 2 H :=
      (C.subtype.comp q.ker.subtype).codRestrict _ (by
        intro x
        have hx : (x.val : H) ∈ X := (QuotientGroup.eq_one_iff _).mp x.property
        have hg := centralizer_star_eq_one d x.val
          (cubicProduct_le d Finset.univ hx) x.val.property
        rw [←hker]
        exact (QuotientGroup.eq_one_iff _).mp hg)
    exact pCore_isPGroup.of_injective f (by
      intro a b hab
      apply Subtype.ext
      apply Subtype.ext
      exact congrArg (fun z : pCore 2 H => (z : H)) hab)
  have ht := (hquot.to_subgroup ⊤).comap_of_ker_isPGroup q hqker
  rw [comap_top] at ht
  exact ht.of_equiv topEquiv

end CFSG.Quasithin.Chapter15.Section04.InitialSource.BaumannSylow
