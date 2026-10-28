module
public import Theory.GroupAction.BinaryA4Pair.SymmetricFourActors
public import Theory.GroupTheory.PResidual.FiniteImage
public import Mathlib.GroupTheory.Subgroup.Centralizer

/-!
# Literal normalizer actions of a pair of local groups

Two local groups normalize an elementary abelian group of order sixteen.
Their actual conjugation images are symmetric-four groups, and a common
subgroup has a two-group image of order eight. A fixed-free cubic in the
first image and a centralizer of order two for the second local residual
force the action of the join of the two local residuals to be A₆.

The shared image has index three in each actor and therefore supplies their
common Sylow two-subgroup. Surjectivity onto each action image transports
the two-residual. An explicit equivalence identifies the common fixed space
with the literal ambient centralizer intersection. The action of a join is
the join of the action images, allowing `recognition_of_symmetricFour_actors`
to identify the requested normalizer action without changing its maps.

This supplies the normalizer-actor transport in Aschbacher–Smith,
*The Classification of Quasithin Groups*, 14.3.19(4). The source consumer
discharges the local subgroup, action-image and centralizer hypotheses.
-/

namespace BinaryA4Pair
open Subgroup
local notation "S4" => Equiv.Perm (Fin 4)

private theorem sylow_of_shared_eight {H : Type*} [Group H]
    (X D : Subgroup H) (e : X ≃* S4) (hDX : D≤X)
    (hp : IsPGroup 2 D) (hD : Nat.card D=8) :
    ∃ S : Sylow 2 X, (S : Subgroup X).map X.subtype=D := by
  let : Finite X := Finite.of_injective e e.injective
  let P := D.subgroupOf X
  have hP : Nat.card P=8 := (Nat.card_congr (subgroupOfEquivOfLe hDX).toEquiv).trans hD
  have hX : Nat.card X=24 := by
    rw [Nat.card_congr e.toEquiv,Nat.card_eq_fintype_card,Fintype.card_perm]
    decide
  have hi : P.index=3 := by
    have h := P.index_mul_card
    rw [hP,hX] at h
    omega
  have hpP : IsPGroup 2 P := hp.comap_subtype
  refine ⟨hpP.toSylow (by rw [hi]; decide),?_⟩
  exact map_subgroupOf_eq_of_le hDX

private theorem normalizer_range_mono {G : Type*} [Group G]
    (A P Q : Subgroup G) (hPA : P≤normalizer (A : Set G))
    (hQA : Q≤normalizer (A : Set G)) (hPQ : P≤Q) :
    (A.normalizerMonoidHom.comp (inclusion hPA)).range ≤
      (A.normalizerMonoidHom.comp (inclusion hQA)).range := by
  rintro x ⟨p,rfl⟩
  exact ⟨⟨p.val,hPQ p.property⟩,rfl⟩

private theorem residual_action_image {G : Type*} [Group G] [Finite G]
    (A I L : Subgroup G) (hIA : I≤normalizer (A : Set G))
    (hLA : L≤normalizer (A : Set G)) (hL : L=(pResidual 2 I).map I.subtype) :
    (A.normalizerMonoidHom.comp (inclusion hLA)).range =
      (pResidual 2 (A.normalizerMonoidHom.comp (inclusion hIA)).range).map
        (A.normalizerMonoidHom.comp (inclusion hIA)).range.subtype := by
  let f := A.normalizerMonoidHom.comp (inclusion hIA)
  have hr : (A.normalizerMonoidHom.comp (inclusion hLA)).range =
      (pResidual 2 I).map f := by
    ext a
    constructor
    · rintro ⟨l,rfl⟩
      have hl : (l : G)∈(pResidual 2 I).map I.subtype :=
        Eq.mp (congrArg (fun T : Subgroup G => (l : G)∈T) hL) l.property
      obtain ⟨i,hi,he⟩ := hl
      refine ⟨i,hi,?_⟩
      apply MulEquiv.ext
      intro v
      apply Subtype.ext
      change i.val*v.val*i.val⁻¹=l.val*v.val*l.val⁻¹
      exact congrArg (fun g : G => g*v.val*g⁻¹) he
    · rintro ⟨i,hi,rfl⟩
      have hiL : i.val∈L := by rw [hL]; exact mem_map_of_mem _ hi
      exact ⟨⟨i.val,hiL⟩,rfl⟩
  rw [hr]
  calc
    _ = ((pResidual 2 I).map f.rangeRestrict).map f.range.subtype := by
      rw [map_map]
      rfl
    _ = _ := by rw [map_pResidual_of_surjective 2 f.rangeRestrict f.rangeRestrict_surjective]

private theorem normalizer_fixed_card {G : Type*} [Group G]
    (A Y : Subgroup G) (hYA : Y≤normalizer (A : Set G)) :
    Nat.card {a : A // ∀ f∈(A.normalizerMonoidHom.comp (inclusion hYA)).range, f a=a} =
      Nat.card (A ⊓ centralizer (Y : Set G) : Subgroup G) := by
  apply Nat.card_congr
  refine {
    toFun := fun a => ⟨a.val.val,a.val.property,?_⟩
    invFun := fun a => ⟨⟨a.val,a.property.1⟩,?_⟩
    left_inv := fun a => rfl
    right_inv := fun a => rfl }
  · intro y hy
    have h := congrArg Subtype.val (a.property
      ((A.normalizerMonoidHom.comp (inclusion hYA)) ⟨y,hy⟩) ⟨⟨y,hy⟩,rfl⟩)
    change y*a.val.val*y⁻¹=a.val.val at h
    exact mul_inv_eq_iff_eq_mul.mp h
  · rintro f ⟨y,rfl⟩
    apply Subtype.ext
    change y.val*a.val*y.val⁻¹=a.val
    exact mul_inv_eq_iff_eq_mul.mpr (a.property.2 y.val y.property)

private theorem normalizer_range_sup {G : Type*} [Group G]
    (A L Y : Subgroup G) (hLA : L≤normalizer (A : Set G))
    (hYA : Y≤normalizer (A : Set G)) :
    (A.normalizerMonoidHom.comp (inclusion (sup_le hLA hYA))).range =
      (A.normalizerMonoidHom.comp (inclusion hLA)).range ⊔
        (A.normalizerMonoidHom.comp (inclusion hYA)).range := by
  simp only [MonoidHom.range_comp,inclusion_range]
  rw [subgroupOf_sup hLA hYA,Subgroup.map_sup]

/-- Literal normalizer actions of two local groups recognize the action of
the join of their embedded residuals. -/
public theorem canonical_model_of_normalizer_actors
    {G : Type*} [Group G] [Finite G]
    (A I J S L Y : Subgroup G) [IsElementaryAbelian 2 A] (hA : Nat.card A=16)
    (hIA : I≤normalizer (A : Set G)) (hJA : J≤normalizer (A : Set G))
    (hSI : S≤I) (hSJ : S≤J)
    (eI : (A.normalizerMonoidHom.comp (inclusion hIA)).range ≃* S4)
    (eJ : (A.normalizerMonoidHom.comp (inclusion hJA)).range ≃* S4)
    (hS : Nat.card (A.normalizerMonoidHom.comp (inclusion (hSI.trans hIA))).range=8)
    (hpS : IsPGroup 2 S)
    (hL : L=(pResidual 2 I).map I.subtype)
    (hY : Y=(pResidual 2 J).map J.subtype)
    (ht : ∃ t : MulAut A, t∈(A.normalizerMonoidHom.comp (inclusion hIA)).range ∧
      t^3=1 ∧ ∀ a, t a=a → a=1)
    (hfixed : Nat.card (A ⊓ centralizer (Y : Set G) : Subgroup G)=2) :
    ∃ hK : L⊔Y≤normalizer (A : Set G),
      HasCanonicalModel (A.normalizerMonoidHom.comp (inclusion hK)).range := by
  let fI := A.normalizerMonoidHom.comp (inclusion hIA)
  let fJ := A.normalizerMonoidHom.comp (inclusion hJA)
  let fS := A.normalizerMonoidHom.comp (inclusion (hSI.trans hIA))
  have hDI : fS.range≤fI.range := normalizer_range_mono A S I _ _ hSI
  have hDJ : fS.range≤fJ.range := normalizer_range_mono A S J _ _ hSJ
  have hpD : IsPGroup 2 fS.range := hpS.of_surjective fS.rangeRestrict fS.rangeRestrict_surjective
  obtain ⟨SI,hSI'⟩ := sylow_of_shared_eight fI.range fS.range eI hDI hpD hS
  obtain ⟨SJ,hSJ'⟩ := sylow_of_shared_eight fJ.range fS.range eJ hDJ hpD hS
  have hLI : L≤I := by rw [hL]; exact map_subtype_le _
  have hYJ : Y≤J := by rw [hY]; exact map_subtype_le _
  have hLA := hLI.trans hIA
  have hYA := hYJ.trans hJA
  have hfixed' : Nat.card {a : A // ∀ f∈(pResidual 2 fJ.range).map fJ.range.subtype, f a=a}=2 := by
    rw [← residual_action_image A J Y hJA hYA hY,normalizer_fixed_card]
    exact hfixed
  obtain ⟨t,htI,ht3,htfree⟩ := ht
  have hc := canonical_model_of_symmetricFour_actors hA fI.range fJ.range eI eJ SI SJ
    (hSI'.trans hSJ'.symm) t htI ht3 htfree hfixed'
  refine ⟨sup_le hLA hYA,?_⟩
  have heq : (A.normalizerMonoidHom.comp (inclusion (sup_le hLA hYA))).range =
      (pResidual 2 fI.range).map fI.range.subtype ⊔
        (pResidual 2 fJ.range).map fJ.range.subtype := by
    rw [normalizer_range_sup A L Y hLA hYA,residual_action_image A I L hIA hLA hL,
      residual_action_image A J Y hJA hYA hY]
  rw [heq]
  exact hc

public theorem recognition_of_normalizer_actors
    {G : Type*} [Group G] [Finite G]
    (A I J S L Y : Subgroup G) [IsElementaryAbelian 2 A] (hA : Nat.card A=16)
    (hIA : I≤normalizer (A : Set G)) (hJA : J≤normalizer (A : Set G))
    (hSI : S≤I) (hSJ : S≤J)
    (eI : (A.normalizerMonoidHom.comp (inclusion hIA)).range ≃* S4)
    (eJ : (A.normalizerMonoidHom.comp (inclusion hJA)).range ≃* S4)
    (hS : Nat.card (A.normalizerMonoidHom.comp (inclusion (hSI.trans hIA))).range=8)
    (hpS : IsPGroup 2 S)
    (hL : L=(pResidual 2 I).map I.subtype)
    (hY : Y=(pResidual 2 J).map J.subtype)
    (ht : ∃ t : MulAut A, t∈(A.normalizerMonoidHom.comp (inclusion hIA)).range ∧
      t^3=1 ∧ ∀ a, t a=a → a=1)
    (hfixed : Nat.card (A ⊓ centralizer (Y : Set G) : Subgroup G)=2) :
    ∃ hK : L⊔Y≤normalizer (A : Set G),
      Nonempty ((A.normalizerMonoidHom.comp (inclusion hK)).range ≃*
        alternatingGroup (Fin 6)) := by
  obtain ⟨hK,hc⟩ := canonical_model_of_normalizer_actors A I J S L Y hA hIA hJA hSI hSJ
    eI eJ hS hpS hL hY ht hfixed
  exact ⟨hK,hc.recognition⟩

end BinaryA4Pair
