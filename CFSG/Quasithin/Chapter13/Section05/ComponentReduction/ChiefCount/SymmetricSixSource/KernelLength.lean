module
public import CFSG.Quasithin.Chapter13.Section05.ComponentReduction.Recognition.MarkedModule.AlternatingParabolics.SixGeneration
public import Theory.GroupTheory.NoncentralChiefRefinement.CubicComparison.FixedIndex
public import Theory.GroupTheory.NoncentralChiefRefinement.CubicComparison.SmallQuotients
public import Theory.GroupAction.NoncentralTwoChiefLength.BinaryRepresentation

/-!
# Cubic length through the original central quotient

The point line and the component-fixed kernel contribute zero to cubic fixed
length. Thus the actual conjugate closure has the cubic length of its marked
natural central quotient. When [Q_H,K]=U_H and U_H lies in L₁, the original
kernel Q_H∩L₁ has the same length. An A₄ star quotient then adds precisely one
noncentral binary chief factor. Every map here is induced by the original
inclusion and quotient, with no splitting assumption on U_H.
Source: Aschbacher–Smith 13.5.24, printed p.925.
-/

@[expose] public section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section05.ComponentReduction.ChiefCount.SymmetricSixSource
open Recognition Recognition.MarkedModule Recognition.MarkedModule.AlternatingParabolics
open NoncentralChiefRefinement.CubicComparison
open Section08.Source
variable {G : Type*} [Group G] [Finite G]
  (D : ChapterF.Section09.Setup G) (h : D.Hypothesis)
  [(D.V₁.subgroupOf D.UH).Normal] [IsElementaryAbelian 2 (Action.ModuleGroup D)]

def starActor (A : Subgroup G) (hAH : A ≤ D.H) : A →* Hstar D.H :=
  (QuotientGroup.mk' (pCore 2 D.H)).comp (inclusion hAH)

theorem closure_length_as_fixedIndex (A : Subgroup G) (hAH : A ≤ D.H)
    (hA : Nat.card A = 3) :
    conjugationCubicLength A D.UH = Nat.log 4
      (Representation.BinaryFixedPoints.fixedIndex
        ((Action.starRepresentation D h).comp (starActor D A hAH))) := by
  have hAU : A ≤ normalizer (D.UH : Set G) :=
    hAH.trans (le_normalizer_conjugateSpanBy D.Vplus D.H)
  have hAV : A ≤ normalizer (D.V₁ : Set G) :=
    (hAH.trans h.H_centralizes).trans (Subgroup.centralizer_le_normalizer _)
  have hVU : D.V₁ ≤ D.UH := h.point_lt.le.trans (le_conjugateSpanBy _ _)
  have hzero : conjugationCubicLength A D.V₁ = 0 := by
    have hv : D.V₁ ≤ centralizer (A : Set G) :=
      le_centralizer_iff.mp (hAH.trans h.H_centralizes)
    simp only [conjugationCubicLength, relIndex_eq_one.mpr hv, Nat.log_one_right]
  let := quotientConjugationAction A D.UH D.V₁ hAU hAV
  have hs := sectionCubicLength_eq_quotient_of_twoGroup A D.UH D.V₁
    (IsPGroup.of_card (n := 1) (by simpa using hA)) h.g2_hypothesis.U_isPGroup
    hVU hAU hAV
  rw [sectionCubicLength, hzero, Nat.sub_zero] at hs
  rw [hs]
  let e : Action.ModuleGroup D ≃* Multiplicative (Action.Space D) :=
    { toFun := fun x => Multiplicative.ofAdd (Additive.ofMul x)
      invFun := fun x => x.toAdd.toMul
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_mul' := fun _ _ => rfl }
  apply Representation.BinaryFixedPoints.cubicLength_eq_of_equivariant
    ((Action.starRepresentation D h).comp (starActor D A hAH))
    (MonoidHom.id A) Function.surjective_id e
  intro a w
  obtain ⟨u,rfl⟩ := QuotientGroup.mk'_surjective (D.V₁.subgroupOf D.UH) w
  change Multiplicative.ofAdd (Additive.ofMul (QuotientGroup.mk' _ _)) =
    Multiplicative.ofAdd (Action.starRepresentation D h
      (QuotientGroup.mk' (pCore 2 D.H) (inclusion hAH a))
        (Additive.ofMul (QuotientGroup.mk' _ u)))
  rw [Action.starRepresentation_apply]
  rfl

theorem closure_length_through_central_projection {K : Subgroup G}
    (A : Subgroup G) (hAK : A ≤ K) (hKH : K ≤ D.H)
    (hA : Nat.card A = 3)
    (f : (starImage D.H K ⊔ starImage D.H D.V : Subgroup (Hstar D.H)) ≃*
      Equiv.Perm (Fin 6))
    (fV : (Action.Space D ⧸ fixedSpace (Action.starRepresentation D h)
      (starImage D.H K)) ≃ₗ[ZMod 2] BinaryPermutation.natural (Fin 6))
    (hfV : ∀ b : (starImage D.H K ⊔ starImage D.H D.V : Subgroup (Hstar D.H)),
      ∀ u, centralProjection D h fV (Action.starRepresentation D h b.val u) =
        BinaryPermutation.naturalRepresentation (Fin 6) (f b)
          (centralProjection D h fV u))
    (a : A →* (starImage D.H K ⊔ starImage D.H D.V : Subgroup (Hstar D.H)))
    (ha : ∀ x, (a x).val = starActor D A (hAK.trans hKH) x) :
    conjugationCubicLength A D.UH = Nat.log 4
      (Representation.BinaryFixedPoints.fixedIndex
        ((BinaryPermutation.naturalRepresentation (Fin 6)).comp (f.toMonoidHom.comp a))) := by
  rw [closure_length_as_fixedIndex D h A (hAK.trans hKH) hA]
  congr 1
  let ρ := (Action.starRepresentation D h).comp (starActor D A (hAK.trans hKH))
  let σ := (BinaryPermutation.naturalRepresentation (Fin 6)).comp (f.toMonoidHom.comp a)
  let : IsCyclic A := isCyclic_of_prime_card hA
  obtain ⟨x,hx⟩ := IsCyclic.exists_generator (α := A)
  have hx3 : x ^ 3 = 1 := hA ▸ pow_card_eq_one' (x := x)
  apply Representation.BinaryFixedPoints.fixedIndex_eq_of_surjective_trivial_kernel ρ σ
    x hx hx3 (centralProjection D h fV) (fV.surjective.comp (Submodule.mkQ_surjective _))
  · intro y u
    change centralProjection D h fV (Action.starRepresentation D h
      (starActor D A (hAK.trans hKH) y) u) = _
    rw [←ha y]
    exact hfV (a y) u
  · intro u hu
    have hfix : u ∈ fixedSpace (Action.starRepresentation D h) (starImage D.H K) := by
      rw [← centralProjection_ker D h fV]
      exact hu
    exact hfix ⟨starActor D A (hAK.trans hKH) x, mem_map_of_mem _ (hAK x.property)⟩

omit [(D.V₁.subgroupOf D.UH).Normal] [IsElementaryAbelian 2 (Action.ModuleGroup D)] in
include h in
theorem kernel_length_eq_closure {K : Subgroup G}
    (A : Subgroup G) (hAL : A ≤ D.L₁) (hLK : D.L₁ ≤ K)
    (hA : Nat.card A = 3) (hUcore : D.UH = ⁅D.QH,K⁆)
    (hUL : D.UH ≤ D.L₁) :
    conjugationCubicLength A (D.QH ⊓ D.L₁) = conjugationCubicLength A D.UH := by
  have hAH : A ≤ D.H := hAL.trans (le_sup_left.trans h.local_le)
  have hAU : A ≤ normalizer (D.UH : Set G) :=
    hAH.trans (le_normalizer_conjugateSpanBy D.Vplus D.H)
  have hAQ : A ≤ normalizer (D.QH : Set G) :=
    hAH.trans (D.H.le_normalizer.trans (normalizer_le_normalizer_characteristic_image D.H (pCore 2 D.H)))
  have hAP : A ≤ normalizer ((D.QH ⊓ D.L₁ : Subgroup G) : Set G) :=
    (le_inf hAQ (hAL.trans D.L₁.le_normalizer)).trans inf_normalizer_le_normalizer_inf
  have hUP : D.UH ≤ D.QH ⊓ D.L₁ := le_inf h.UH_le_QH hUL
  let : (D.UH.subgroupOf (D.QH ⊓ D.L₁)).Normal := normal_subgroupOf_of_le_normalizer
    (inf_le_left.trans ((pCoreIn_le 2 D.H).trans (le_normalizer_conjugateSpanBy _ _)))
  symm
  apply length_eq_of_commutator_le A (D.QH ⊓ D.L₁) D.UH
    (IsPGroup.of_card (n := 1) (by simpa using hA))
    ((isPGroup_pCoreIn 2 D.H).to_le inf_le_left) hUP hAP hAU
  rw [hUcore]
  exact commutator_mono inf_le_left (hAL.trans hLK)

omit [(D.V₁.subgroupOf D.UH).Normal] [IsElementaryAbelian 2 (Action.ModuleGroup D)] in
def starMap (X : Subgroup G) (hXH : X ≤ D.H) : X →* starImage D.H X :=
  (starActor D X hXH).codRestrict _
    (fun x => ⟨inclusion hXH x, x.property, rfl⟩)

omit [Finite G] [(D.V₁.subgroupOf D.UH).Normal] [IsElementaryAbelian 2 (Action.ModuleGroup D)] in
theorem starMap_surjective (X : Subgroup G) (hXH : X ≤ D.H) :
    Function.Surjective (starMap D X hXH) := by
  rintro ⟨_,x,hx,rfl⟩
  exact ⟨⟨x,hx⟩,Subtype.ext rfl⟩

omit [Finite G] [(D.V₁.subgroupOf D.UH).Normal] [IsElementaryAbelian 2 (Action.ModuleGroup D)] in
theorem starMap_ker (X : Subgroup G) (hXH : X ≤ D.H) :
    (starMap D X hXH).ker = (D.QH ⊓ X).subgroupOf X := by
  ext x
  change (starMap D X hXH x = 1) ↔ x.val ∈ D.QH ∧ x.val ∈ X
  rw [←Subtype.coe_inj]
  change QuotientGroup.mk' (pCore 2 D.H) (inclusion hXH x) = 1 ↔ _
  rw [show (QuotientGroup.mk' (pCore 2 D.H) (inclusion hXH x) = 1) ↔ inclusion hXH x ∈ pCore 2 D.H from QuotientGroup.eq_one_iff _, and_iff_left x.property]
  change (inclusion hXH x ∈ pCore 2 D.H) ↔ x.val ∈ (pCore 2 D.H).map D.H.subtype
  exact (mem_map_iff_mem D.H.subtype_injective).symm

omit [Finite G] [(D.V₁.subgroupOf D.UH).Normal] [IsElementaryAbelian 2 (Action.ModuleGroup D)] in
theorem starMap_injective_cubic (A : Subgroup G) (hAH : A ≤ D.H)
    (hA : Nat.card A = 3) : Function.Injective (starMap D A hAH) := by
  apply (starMap D A hAH).ker_eq_bot_iff.mp
  rw [starMap_ker]
  have hd := IsPGroup.disjoint_of_ne 2 3 (by decide) D.QH A
    (isPGroup_pCoreIn 2 D.H) (IsPGroup.of_card (n := 1) (by simpa using hA))
  rw [hd.eq_bot]
  simp only [bot_subgroupOf]

omit [(D.V₁.subgroupOf D.UH).Normal] [IsElementaryAbelian 2 (Action.ModuleGroup D)] in
include h in
theorem count_eq_kernel_length_add_one
    (eL : starImage D.H D.L₁ ≃* alternatingGroup (Fin 4))
    (A : Subgroup G) (hAL : A ≤ D.L₁) (hA : Nat.card A = 3)
    (t : NoncentralChiefRefinement.ChiefSeries D.L₁)
    (h0 : t.head = ⊥) (h1 : t.last = ⊤) :
    t.noncentralTwoCount = conjugationCubicLength A (D.QH ⊓ D.L₁) + 1 := by
  let q := starMap D D.L₁ (le_sup_left.trans h.local_le)
  let f := eL.toMonoidHom.comp q
  have hf : Function.Surjective f := eL.surjective.comp (starMap_surjective D _ _)
  have hk : f.ker = (D.QH ⊓ D.L₁).subgroupOf D.L₁ := by
    change (eL.toMonoidHom.comp q).ker = _
    rw [MonoidHom.ker_comp_of_injective q eL.toMonoidHom eL.injective]
    exact starMap_ker D _ _
  have hp : IsPGroup 2 f.ker := by
    rw [hk]
    exact ((isPGroup_pCoreIn 2 D.H).to_le inf_le_left).comap_subtype
  have hA' : Nat.card (A.subgroupOf D.L₁) = 3 := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hAL).toEquiv,hA]
  have he := alternatingFour_count f hf hp (A.subgroupOf D.L₁) hA' t h0 h1
  rw [hk,length_subgroupOf A (D.QH ⊓ D.L₁) D.L₁ hAL inf_le_right] at he
  exact he

end CFSG.Quasithin.Chapter13.Section05.ComponentReduction.ChiefCount.SymmetricSixSource
