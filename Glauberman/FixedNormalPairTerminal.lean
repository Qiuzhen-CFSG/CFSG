module
public import Glauberman.FixedNormalPairOmega

/-!
# The elementary terminal branch of a fixed-normal-free pair

When the next intersection contains no maximum abelian subgroup of S,
every maximum abelian subgroup of either new member lies outside the other.
Transport the original two-sided replacement theorem along the specified
isomorphism. Alternating these replacements gives central elementary
supplements of both new members over their intersection. Their embedded
Frattini subgroups coincide, and the inherited fixed-normal obstruction
forces the common subgroup to vanish. Hence the original intersection is
elementary abelian.

The final theorem retains only the original replacement families and the
strict maximum-order drop. The central supplements are proved internally.
Source: Niles, *Pushing-up in finite groups* (1979), Proposition4.4,
printedpp45–46, the strict maximum-order case.
-/

public section
open Subgroup Theory.GroupTheory.SubgroupTransport
open scoped Pointwise
namespace Glauberman
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
private theorem central_supplement_intersection
    (S R Q V : Subgroup G) (hQS : Q ≤ S) (hVQ : V ≤ Q)
    (hn : S ≤ normalizer (R : Set G)) (hgen : S = V ⊔ R) :
    Q = V ⊔ (R ⊓ Q) := by
  apply le_antisymm
  · intro x hx
    have hm : x ∈ (V : Set G) * (R : Set G) := by
      rw [←coe_mul_of_left_le_normalizer_right V R ((hVQ.trans hQS).trans hn),←hgen]
      exact hQS hx
    obtain ⟨v,hv,r,hr,he⟩ := hm
    have hrQ : r ∈ Q := by
      have h := Q.mul_mem (Q.inv_mem (hVQ hv)) hx
      rwa [←he,inv_mul_cancel_left] at h
    rw [←he]
    exact mul_mem_sup hv ⟨hr,hrQ⟩
  · exact sup_le hVQ inf_le_right

/-- Alternating maximum-abelian replacements give the two central
supplements used at the terminal branch of Niles4.4. -/
theorem central_supplements_of_cross_replacement
    (S R Q U V : Subgroup G) (hRS : R ≤ S) (hQS : Q ≤ S)
    (hUR : U ≤ R) (hVQ : V ≤ Q)
    (hRn : S ≤ normalizer (R : Set G)) (hQn : S ≤ normalizer (Q : Set G))
    (hRQ : ∀ A, A ∈ thompsonAbelianSubgroups R →
      A ⊔ Q = S ∧ A ⊓ Q ⊔ V ∈ thompsonAbelianSubgroups Q)
    (hQR : ∀ B, B ∈ thompsonAbelianSubgroups Q →
      B ⊔ R = S ∧ B ⊓ R ⊔ U ∈ thompsonAbelianSubgroups R) :
    R = U ⊔ (R ⊓ Q) ∧ Q = V ⊔ (R ⊓ Q) := by
  obtain ⟨A,hA⟩ := thompsonAbelianSubgroups_nonempty R
  obtain ⟨B,hB⟩ := thompsonAbelianSubgroups_nonempty Q
  have hAV : (A ⊓ Q ⊔ V) ⊔ R = S := (hQR _ (hRQ A hA).2).1
  have hBU : (B ⊓ R ⊔ U) ⊔ Q = S := (hRQ _ (hQR B hB).2).1
  have hSV : S = V ⊔ R := by
    apply le_antisymm
    · calc
        S = (A ⊓ Q ⊔ V) ⊔ R := hAV.symm
        _ ≤ V ⊔ R := sup_le (sup_le ((inf_le_left.trans hA.1).trans le_sup_right) le_sup_left) le_sup_right
    · exact sup_le (hVQ.trans hQS) hRS
  have hSU : S = U ⊔ Q := by
    apply le_antisymm
    · calc
        S = (B ⊓ R ⊔ U) ⊔ Q := hBU.symm
        _ ≤ U ⊔ Q := sup_le (sup_le ((inf_le_left.trans hB.1).trans le_sup_right) le_sup_left) le_sup_right
    · exact sup_le (hUR.trans hRS) hQS
  exact ⟨by simpa only [inf_comm] using central_supplement_intersection S Q R U hRS hUR hQn hSU,
    central_supplement_intersection S R Q V hQS hVQ hRn hSV⟩

/-- The elementary terminal case follows from the actual cross-replacement
families; neither central supplement is an additional conclusion assumption. -/
theorem elementary_of_cross_replacement
    (S T : Subgroup G) (φ : S ≃* T)
    (hno : ∀ A : Subgroup S, A.Normal →
      (A.map φ.toMonoidHom).map T.subtype = A.map S.subtype → A = ⊥)
    (R Q U V : Subgroup G) (hRS : R ≤ S) (hQS : Q ≤ S)
    (hUR : U ≤ R) (hVQ : V ≤ Q)
    (hRn : S ≤ normalizer (R : Set G)) (hQn : S ≤ normalizer (Q : Set G))
    (hmap : image φ R = Q) (hR : IsPGroup 2 R) (hQ : IsPGroup 2 Q)
    (hU : IsElementaryAbelian 2 U) (hV : IsElementaryAbelian 2 V)
    (hUc : U ≤ centralizer (R : Set G)) (hVc : V ≤ centralizer (Q : Set G))
    (hRQ : ∀ A, A ∈ thompsonAbelianSubgroups R →
      A ⊔ Q = S ∧ A ⊓ Q ⊔ V ∈ thompsonAbelianSubgroups Q)
    (hQR : ∀ B, B ∈ thompsonAbelianSubgroups Q →
      B ⊔ R = S ∧ B ⊓ R ⊔ U ∈ thompsonAbelianSubgroups R) : IsElementaryAbelian 2 Q := by
  obtain ⟨hRgen,hQgen⟩ := central_supplements_of_cross_replacement S R Q U V
    hRS hQS hUR hVQ hRn hQn hRQ hQR
  exact elementary_of_restricted_central_supplements φ hno R Q (R ⊓ Q) U V hRS hRn hmap
    hR hQ hU hV hUc hVc hRgen hQgen
omit [Finite G] in
/-- The strict maximum-order drop makes every maximum subgroup of each new
member lie outside the other. The old two-sided replacements then transport
to the cross-replacement families used in the elementary terminal case. -/
theorem cross_replacement_of_no_common_maximum
    (S T : Subgroup G) (φ : S ≃* T) (R : Subgroup G)
    (hRS : R ≤ S) (hRmap : image φ R = S ⊓ T)
    (hRpre : image φ.symm (S ⊓ T) = R)
    (hfamilyS : thompsonAbelianSubgroups (S ⊓ T) ⊆ thompsonAbelianSubgroups S)
    (hfamilyT : thompsonAbelianSubgroups (S ⊓ T) ⊆ thompsonAbelianSubgroups T)
    (hsmall : ∀ A, A ∈ thompsonAbelianSubgroups S → ¬ A ≤ R ⊓ (S ⊓ T))
    (hreplaceS : ∀ A, A ∈ thompsonAbelianSubgroups S → ¬ A ≤ S ⊓ T →
      A ⊔ (S ⊓ T) = S ∧
      A ⊓ (S ⊓ T) ⊔ omegaCenterIn (S ⊓ T) ∈ thompsonAbelianSubgroups (S ⊓ T))
    (hreplaceT : ∀ A, A ∈ thompsonAbelianSubgroups T → ¬ A ≤ S ⊓ T →
      A ⊔ (S ⊓ T) = T ∧
      A ⊓ (S ⊓ T) ⊔ omegaCenterIn (S ⊓ T) ∈ thompsonAbelianSubgroups (S ⊓ T)) :
    (∀ A, A ∈ thompsonAbelianSubgroups R →
      A ⊔ (S ⊓ T) = S ∧
      A ⊓ (S ⊓ T) ⊔ omegaCenterIn (S ⊓ T) ∈ thompsonAbelianSubgroups (S ⊓ T)) ∧
    (∀ B, B ∈ thompsonAbelianSubgroups (S ⊓ T) →
      B ⊔ R = S ∧ B ⊓ R ⊔ omegaCenterIn R ∈ thompsonAbelianSubgroups R) := by
  constructor
  · intro A hA
    have ha := maximum_abelian_image φ hRS hA
    rw [hRmap] at ha
    have hat := hfamilyT ha
    have hback := maximum_abelian_image φ.symm le_rfl hat
    rw [image_self,image_symm φ A (hA.1.trans hRS)] at hback
    exact hreplaceS A hback (fun hAQ => hsmall A hback (le_inf hA.1 hAQ))
  · intro B hB
    have hBS : B ≤ S := hB.1.trans inf_le_left
    have hbt := maximum_abelian_image φ le_rfl (hfamilyS hB)
    rw [image_self] at hbt
    have hout : ¬ image φ B ≤ S ⊓ T := by
      intro hle
      have hh := image_mono φ.symm hle
      rw [image_symm φ B hBS,hRpre] at hh
      exact hsmall B (hfamilyS hB) (le_inf hh hB.1)
    obtain ⟨hgen,hrep⟩ := hreplaceT (image φ B) hbt hout
    constructor
    · have hh := congrArg (image φ.symm) hgen
      rw [image_sup φ.symm _ _ (image_le φ B) inf_le_right,
        image_symm φ B hBS,hRpre,image_self] at hh
      exact hh
    · have hh := maximum_abelian_image φ.symm inf_le_right hrep
      rw [hRpre] at hh
      have hWQ : omegaCenterIn (S ⊓ T) ≤ S ⊓ T :=
        fun _ hx => ((mem_omegaCenterIn_iff _ _).mp hx).1
      rw [image_sup φ.symm _ _ (inf_le_left.trans (image_le φ B)) (hWQ.trans inf_le_right),
        image_inf,image_symm φ B hBS,hRpre,
        omegaCenter_image φ.symm (S ⊓ T) inf_le_right,hRpre] at hh
      exact hh


/-- The strict maximum-order-drop branch of Niles4.4, with the central
supplements derived from the original two-sided replacement theorem. -/
theorem elementary_intersection_of_no_common_maximum
    (S T : Subgroup G) (φ : S ≃* T) (R : Subgroup G)
    (hno : ∀ A : Subgroup S, A.Normal →
      (A.map φ.toMonoidHom).map T.subtype = A.map S.subtype → A = ⊥)
    (hSp : IsPGroup 2 S) (hRS : R ≤ S) (hRmap : image φ R = S ⊓ T)
    (hRpre : image φ.symm (S ⊓ T) = R)
    (hSn : S ≤ normalizer (S ⊓ T : Set G))
    (hTn : T ≤ normalizer (S ⊓ T : Set G))
    (hfamilyS : thompsonAbelianSubgroups (S ⊓ T) ⊆ thompsonAbelianSubgroups S)
    (hfamilyT : thompsonAbelianSubgroups (S ⊓ T) ⊆ thompsonAbelianSubgroups T)
    (hsmall : ∀ A, A ∈ thompsonAbelianSubgroups S → ¬ A ≤ R ⊓ (S ⊓ T))
    (hreplaceS : ∀ A, A ∈ thompsonAbelianSubgroups S → ¬ A ≤ S ⊓ T →
      A ⊔ (S ⊓ T) = S ∧
      A ⊓ (S ⊓ T) ⊔ omegaCenterIn (S ⊓ T) ∈ thompsonAbelianSubgroups (S ⊓ T))
    (hreplaceT : ∀ A, A ∈ thompsonAbelianSubgroups T → ¬ A ≤ S ⊓ T →
      A ⊔ (S ⊓ T) = T ∧
      A ⊓ (S ⊓ T) ⊔ omegaCenterIn (S ⊓ T) ∈ thompsonAbelianSubgroups (S ⊓ T)) :
    IsElementaryAbelian 2 ↥(S ⊓ T) := by
  obtain ⟨hRQ,hQR⟩ := cross_replacement_of_no_common_maximum S T φ R hRS hRmap hRpre
    hfamilyS hfamilyT hsmall hreplaceS hreplaceT
  have hRn : S ≤ normalizer (R : Set G) := by
    rw [←hRpre]
    exact normalizes_image φ.symm (S ⊓ T) inf_le_right hTn
  have hRp := hSp.of_injective (inclusion hRS) (inclusion_injective hRS)
  have hQp := hSp.of_injective (inclusion (inf_le_left : S ⊓ T ≤ S))
    (inclusion_injective inf_le_left)
  exact elementary_of_cross_replacement S T φ hno R (S ⊓ T)
    (omegaCenterIn R) (omegaCenterIn (S ⊓ T)) hRS inf_le_left
    (fun _ hx => ((mem_omegaCenterIn_iff _ _).mp hx).1)
    (fun _ hx => ((mem_omegaCenterIn_iff _ _).mp hx).1)
    hRn hSn hRmap hRp hQp inferInstance inferInstance
    (fun _ hx => ((mem_omegaCenterIn_iff _ _).mp hx).2.1)
    (fun _ hx => ((mem_omegaCenterIn_iff _ _).mp hx).2.1) hRQ hQR

end Glauberman
