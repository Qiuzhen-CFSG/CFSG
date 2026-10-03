module

public import Stellmacher.Recognition.NormalEightNonnormalCoreReduction
public import Stellmacher.Recognition.NormalFourLargeCoreInvolutionFixed
public import Stellmacher.Recognition.SimpleInvolutionFusion
public import Theory.GroupTheory.PGroup.ExtraspecialIndexTwoElementaryCentralizer
public import Theory.GroupTheory.InvolutionSquareSubgroupFusion

/-!
# Local geometry in the normal-only index-two large-core case

For an extraspecial quotient two-core of order thirty-two and Sylow index
two, the original Sylow has order sixty-four. Once inside-core fusion of its
central involution is excluded, Z-star supplies an outside conjugate. Its
centralizer is elementary. Its intersection with the core is normal in the
Sylow and has order at least four, so the normal-only bound and uniqueness
identify it with the given normal four. The whole centralizer has order eight
and is self-centralizing in the Sylow.

An elementary eight is allowed here. The ambient normalizer argument and
inside-core fusion exclusion are separate from this local geometry.

Source: Janko–Thompson, Math. Z. 113 (1970), §4, printed p.389,
the paragraph beginning “Suppose |T:H|=2”. Both extraspecial types are covered.
-/

namespace Stellmacher.Recognition.NormalEightNonnormalImage

open Subgroup NormalFourCentralOmegaTwo
open scoped IsMulCommutative

variable {G : Type*} [Group G] [Finite G]

/-- The order of the original Sylow in the index-two order-32 case. -/
public theorem card_sylow_of_large_core_index_two
    (S : Sylow 2 G) (hH : Nat.card (pCore 2 (OmegaQuotient S)) = 32)
    (hindex : (omegaCorePreimage S).index = 2) : Nat.card S = 64 := by
  have h := (omegaCorePreimage S).card_mul_index
  rw [card_omegaCorePreimage, hH, hindex] at h
  exact h.symm

/-- Under the normal-only bound an elementary outside centralizer is the join
of the unique normal four and the outside involution, and has order eight. -/
public theorem large_core_index_two_elementary_centralizer_structure
    (S : Sylow 2 G)
    (hno : ¬ ∃ E : Subgroup S, E.Normal ∧ IsElementaryAbelian 2 E ∧ 8 ≤ Nat.card E)
    (W : Subgroup S)
    (hunique : ∀ F : Subgroup S, F.Normal → IsElementaryAbelian 2 F → Nat.card F = 4 → F = W)
    [IsExtraspecial 2 (pCore 2 (OmegaQuotient S))]
    (hH : Nat.card (pCore 2 (OmegaQuotient S)) = 32)
    (hindex : (omegaCorePreimage S).index = 2)
    (t : S) (ht : orderOf t = 2) (hout : t ∉ omegaCorePreimage S)
    [IsElementaryAbelian 2 (centralizer ({t} : Set S))] :
    omegaCorePreimage S ⊓ centralizer ({t} : Set S) = W ∧
      centralizer ({t} : Set S) = W ⊔ zpowers t ∧
      Nat.card (centralizer ({t} : Set S)) = 8 ∧
      centralizer (centralizer ({t} : Set S) : Set S) = centralizer ({t} : Set S) := by
  let H := omegaCorePreimage S
  let C := centralizer ({t} : Set S)
  let F := H ⊓ C
  let : IsExtraspecial 2 H :=
    IsExtraspecial.of_mulEquiv (omegaCorePreimageEquiv S).symm inferInstance
  have ht2 : t ^ 2 = 1 := by simpa only [ht] using pow_orderOf_eq_one t
  let : F.Normal := extraspecial_inf_centralizer_normal_of_index_two H hindex t ht2 hout
  let : IsElementaryAbelian 2 F := {
    toIsMulCommutative := isMulCommutative_iff.mpr (by
      intro a b
      exact Subtype.ext (congrArg (fun x : C => (x : S))
        (mul_comm (⟨a, a.property.2⟩ : C) (⟨b, b.property.2⟩ : C))))
    exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr (by
      intro a
      exact Subtype.ext (elemPow_eq_one_of_isElementaryAbelian (A := C) a a.property.2)) }
  obtain ⟨hF, hsplit, hC⟩ := extraspecial_index_two_elementary_centralizer_card
    hno H hindex t ht2 hout
    (omegaCorePreimage_large_core_involution_centralizer_card_ge_four S hH t ht)
  have heq : F = W := hunique F inferInstance inferInstance hF
  refine ⟨heq, ?_, hC, ?_⟩
  · change C = F ⊔ zpowers t at hsplit
    simpa only [heq] using hsplit
  · apply le_antisymm
    · intro x hx
      exact mem_centralizer_singleton_iff.mpr
        (hx t (mem_centralizer_singleton_iff.mpr (Commute.refl t))).symm
    · exact le_centralizer C

/-- Inside-core weak closure supplies an outside fused involution whose
centralizer is an elementary eight with core intersection equal to the normal four.
No rank bound on arbitrary elementary subgroups is used. -/
public theorem large_core_index_two_outside_centralizer_of_inside_fusion
    [IsSimpleGroup G] (hns : ¬ Group.IsSolvable G)
    (S : Sylow 2 G)
    (hno : ¬ ∃ E : Subgroup S, E.Normal ∧ IsElementaryAbelian 2 E ∧ 8 ≤ Nat.card E)
    (W : Subgroup S)
    (hunique : ∀ F : Subgroup S, F.Normal → IsElementaryAbelian 2 F → Nat.card F = 4 → F = W)
    [IsExtraspecial 2 (pCore 2 (OmegaQuotient S))]
    (hH : Nat.card (pCore 2 (OmegaQuotient S)) = 32)
    (hindex : (omegaCorePreimage S).index = 2)
    (hinside : ∀ z t : S, orderOf z = 2 → z ∈ center S →
      t ∈ omegaCorePreimage S → IsConj (z : G) (t : G) → t = z) :
    ∃ z t : S, orderOf z = 2 ∧ z ∈ center S ∧ z ∈ omegaCorePreimage S ∧
      orderOf t = 2 ∧ t ∉ omegaCorePreimage S ∧ IsConj (z : G) (t : G) ∧
      IsElementaryAbelian 2 (centralizer ({t} : Set S)) ∧
      omegaCorePreimage S ⊓ centralizer ({t} : Set S) = W ∧
      centralizer ({t} : Set S) = W ⊔ zpowers t ∧
      Nat.card (centralizer ({t} : Set S)) = 8 ∧
      centralizer (centralizer ({t} : Set S) : Set S) = centralizer ({t} : Set S) := by
  let H := omegaCorePreimage S
  let : IsExtraspecial 2 H :=
    IsExtraspecial.of_mulEquiv (omegaCorePreimageEquiv S).symm inferInstance
  let Z := (center H).map H.subtype
  let : Z.Normal := ConjAct.normal_of_characteristic_of_normal
  have hZcard : Nat.card Z = 2 :=
    (card_map_of_injective H.subtype_injective).trans (IsExtraspecial.center_order_p 2 H)
  have hZcentral := central_of_normal_card_two Z hZcard
  obtain ⟨w, hw⟩ := exists_prime_orderOf_dvd_card' (G := center H) 2
    (by rw [IsExtraspecial.center_order_p 2 H])
  let z : H := w
  have hz : orderOf z = 2 := (orderOf_coe w).trans hw
  have hzc : (z : S) ∈ center S := hZcentral (mem_map_of_mem H.subtype w.property)
  have hzS : orderOf (z : S) = 2 := (orderOf_coe z).trans hz
  obtain ⟨t, htz, hzt⟩ := exists_distinct_isConj_in_sylow hns S z hzS
  have ht : orderOf t = 2 := by
    obtain ⟨g, hg⟩ := isConj_iff.mp hzt
    rw [← orderOf_coe t, ← hg, ← MulAut.conj_apply]
    simpa using ((MulAut.conj g).orderOf_eq ((z : S) : G)).trans
      ((orderOf_coe (z : S)).trans hzS)
  have hout : t ∉ H := fun hin => htz (hinside z t hzS hzc hin hzt)
  let : IsElementaryAbelian 2 (centralizer ({t} : Set S)) :=
    S.elementary_centralizer_of_extraspecial_index_two_of_inside_fusion H hindex
      z hz hzc (fun u hu hzu => hinside z u hzS hzc hu hzu) t
      (by simpa only [ht] using pow_orderOf_eq_one t) hout hzt
  exact ⟨z, t, hzS, hzc, z.property, ht, hout, hzt, inferInstance,
    large_core_index_two_elementary_centralizer_structure S hno W hunique hH hindex t ht hout⟩


end Stellmacher.Recognition.NormalEightNonnormalImage
