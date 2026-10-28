module
public import Glauberman.FixedNormalPairRecursion
public import Glauberman.FixedNormalPairCenters
public import Theory.Frattini.OmegaProducts

/-!
# Intersection descent at the original field degree

The counting and replacement argument of Niles 4.3--4.5 depends on the
common index q, not on q=4. The literal restricted pair retains that
index, the uniform omega fixed-index bounds and the absence of a fixed
normal subgroup. Strict finite descent reaches an elementary intersection
of maximum abelian order in both original members.

Source: Niles, *Pushing-up in finite groups* (1979), pp.44--46.
The original SL2 quotient consumer is PushingUpSL2Degree.
-/

public section
open Subgroup Theory.GroupTheory.SubgroupTransport
namespace Glauberman
variable {G : Type*} [Group G] {q : ℕ}

structure NumericalPairAt (q : ℕ) (S T : Subgroup G) (φ : S ≃* T) : Prop where
  nontrivial_index : 1 < q
  two : IsPGroup 2 S
  no_fixed : ∀ A : Subgroup S, A.Normal →
    (A.map φ.toMonoidHom).map T.subtype = A.map S.subtype → A = ⊥
  normal_left : S ≤ normalizer (S ⊓ T : Set G)
  normal_right : T ≤ normalizer (S ⊓ T : Set G)
  index_left : (S ⊓ T).relIndex S = q
  index_right : (S ⊓ T).relIndex T = q
  lower_left : ∀ B : Subgroup G, B ≤ S → ¬ B ≤ S ⊓ T →
    q ≤ (omegaCenterIn (S ⊓ T) ⊓ centralizer (B : Set G)).relIndex (omegaCenterIn (S ⊓ T))
  lower_right : ∀ B : Subgroup G, B ≤ T → ¬ B ≤ S ⊓ T →
    q ≤ (omegaCenterIn (S ⊓ T) ⊓ centralizer (B : Set G)).relIndex (omegaCenterIn (S ⊓ T))

private theorem relative_index_of_normal_supplement {S Q R : Subgroup G}
    (hRS : R ≤ S) (hQS : Q ≤ S) (hn : S ≤ normalizer (Q : Set G))
    (hgen : R ⊔ Q = S) : (R ⊓ Q).relIndex R = Q.relIndex S := by
  let _ : (Q.subgroupOf S).Normal := normal_subgroupOf_of_le_normalizer hn
  have hh := relIndex_sup_right (R.subgroupOf S) (Q.subgroupOf S)
  rw [←subgroupOf_sup hRS hQS,relIndex_subgroupOf (sup_le hRS hQS),
    relIndex_subgroupOf hRS,hgen] at hh
  rw [inf_relIndex_left]
  exact hh.symm

private theorem relIndex_image {S T : Subgroup G} (φ : S ≃* T)
    (R Q : Subgroup G) (hQS : Q ≤ S) :
    (image φ R).relIndex (image φ Q) = R.relIndex Q := by
  rw [image,image,relIndex_map_map_of_injective _ _ (ambientHom_injective φ),
    relIndex_subgroupOf hQS]

private theorem next_no_fixed {S T : Subgroup G} (φ : S ≃* T)
    (hno : ∀ A : Subgroup S, A.Normal →
      (A.map φ.toMonoidHom).map T.subtype = A.map S.subtype → A = ⊥)
    (hgen : image φ.symm (S ⊓ T) ⊔ (S ⊓ T) = S)
    (A : Subgroup (image φ.symm (S ⊓ T))) (hA : A.Normal)
    (hfix : (A.map (nextPairEquiv φ).toMonoidHom).map (S ⊓ T).subtype =
      A.map (image φ.symm (S ⊓ T)).subtype) : A = ⊥ := by
  let _ := hA
  apply restricted_pair_no_fixed_normal φ hno _ (image_le φ.symm _)
    (by
      have hm : image φ (image φ.symm (S ⊓ T)) = S ⊓ T :=
        image_symm φ.symm (S ⊓ T) inf_le_right
      rw [hm]
      exact hgen) A
  rw [map_map] at hfix ⊢
  exact hfix

/-- One recursive step: either the old intersection is elementary abelian,
or the literal restricted pair satisfies the same numerical hypotheses. -/
theorem NumericalPairAt.recursion [Finite G] {S T : Subgroup G} {φ : S ≃* T}
    (h : NumericalPairAt q S T φ) :
    IsElementaryAbelian 2 ↥(S ⊓ T) ∨
      (NumericalPairAt q (image φ.symm (S ⊓ T)) (S ⊓ T) (nextPairEquiv φ) ∧
        image φ.symm (S ⊓ T) ⊔ (S ⊓ T) = S) := by
  by_cases hQ : S ⊓ T = ⊥
  · left
    rw [hQ]
    refine ⟨?_⟩
    exact Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr (fun _ => Subsingleton.elim _ _)
  have hS : S ≠ ⊥ := fun he => hQ (le_bot_iff.mp (inf_le_left.trans he.le))
  let Q := S ⊓ T
  let R := image φ.symm Q
  have hRS : R ≤ S := image_le φ.symm Q
  have hRmap : image φ R = Q := image_symm φ.symm Q inf_le_right
  have hRn : S ≤ normalizer (R : Set G) := normalizes_image φ.symm Q inf_le_right h.normal_right
  obtain ⟨_,_,hreplaceS,hreplaceT,hfamilyS,hfamilyT,_,_⟩ :=
    fixed_normal_pair_counting S T (omegaCenterIn Q) φ hS h.no_fixed
      h.normal_left h.normal_right
      (fun _ hx => ((mem_omegaCenterIn_iff Q _).mp hx).1) inferInstance
      (fun _ hx => ((mem_omegaCenterIn_iff Q _).mp hx).2.1)
      (fun B hB hBQ => by rw [h.index_left]; exact h.lower_left B hB.1 hBQ)
      (fun B hB hBQ => by rw [h.index_right]; exact h.lower_right B hB.1 hBQ)
  have hgen : R ⊔ Q = S := preimage_intersection_generates φ h.no_fixed hQ
    h.normal_right hfamilyT (fun B hB hBQ => (hreplaceS B hB hBQ).1)
  by_cases hcommon : ∃ A, A ∈ thompsonAbelianSubgroups S ∧ A ≤ R ⊓ Q
  · obtain ⟨A,hA,hAD⟩ := hcommon
    obtain ⟨hlowerR,hlowerQ⟩ := both_fixedIndex_lower_of_common_maximum S T φ R A
      hRS hRmap rfl hA hAD h.lower_left h.lower_right
    have hDn : S ≤ normalizer (R ⊓ Q : Set G) :=
      fun x hx => inf_normalizer_le_normalizer_inf ⟨hRn hx,h.normal_left hx⟩
    have hidxR : (R ⊓ Q).relIndex R = q :=
      (relative_index_of_normal_supplement hRS inf_le_left h.normal_left hgen).trans h.index_left
    have hidxQ : (R ⊓ Q).relIndex Q = q := by
      rw [inf_comm]
      rw [relative_index_of_normal_supplement inf_le_left hRS hRn ((sup_comm Q R).trans hgen)]
      have hh := relIndex_image φ R S le_rfl
      rw [hRmap,image_self] at hh
      exact hh.symm.trans h.index_right
    exact Or.inr ⟨⟨h.nontrivial_index,h.two.of_injective (inclusion hRS) (inclusion_injective hRS),
      next_no_fixed φ h.no_fixed hgen,hRS.trans hDn,inf_le_left.trans hDn,
      hidxR,hidxQ,hlowerR,hlowerQ⟩,hgen⟩
  · left
    exact elementary_intersection_of_no_common_maximum S T φ R h.no_fixed h.two
      hRS hRmap rfl h.normal_left h.normal_right hfamilyS hfamilyT
      (fun A hA hAD => hcommon ⟨A,hA,hAD⟩) hreplaceS hreplaceT

namespace IntersectionPair
/-- Every successful recursion strictly reduces the size of the left member. -/
theorem next_card_lt_at [Finite G] (P : IntersectionPair G)
    (h : NumericalPairAt q P.left P.right P.equiv) : Nat.card P.next.left < Nat.card P.left := by
  rw [next_card_left]
  apply lt_of_le_of_ne (card_le_of_le inf_le_left)
  intro he
  have hQ := eq_of_le_of_card_ge (inf_le_left : P.left ⊓ P.right ≤ P.left) he.ge
  have hi : (P.left ⊓ P.right).relIndex P.left = 1 := relIndex_eq_one.mpr hQ.ge
  have := h.index_left
  have := h.nontrivial_index
  omega

end IntersectionPair

variable [Finite G]
/-- Maximum abelian families of the current intersection remain maximum
in both members of the numerical pair. -/
theorem NumericalPairAt.maximum_families {S T : Subgroup G} {φ : S ≃* T}
    (h : NumericalPairAt q S T φ) :
    thompsonAbelianSubgroups (S ⊓ T) ⊆ thompsonAbelianSubgroups S ∧
    thompsonAbelianSubgroups (S ⊓ T) ⊆ thompsonAbelianSubgroups T := by
  have hS : S ≠ ⊥ := by
    intro he
    have hh := h.index_left
    rw [he,relIndex_bot_right] at hh
    have := h.nontrivial_index
    omega
  have hh := fixed_normal_pair_counting S T (omegaCenterIn (S ⊓ T)) φ hS h.no_fixed
    h.normal_left h.normal_right
    (fun _ hx => ((mem_omegaCenterIn_iff _ _).mp hx).1) inferInstance
    (fun _ hx => ((mem_omegaCenterIn_iff _ _).mp hx).2.1)
    (fun B hB hBQ => by rw [h.index_left]; exact h.lower_left B hB.1 hBQ)
    (fun B hB hBQ => by rw [h.index_right]; exact h.lower_right B hB.1 hBQ)
  exact ⟨hh.2.2.2.2.1,hh.2.2.2.2.2.1⟩

namespace IntersectionPair
/-- The terminal elementary intersection has the full maximum abelian order
of both original members. This retains the source4.6(b) conclusion along
the finite descent, rather than merely finding an arbitrary elementary subgroup. -/
theorem exists_elementary_maximum_row_at (P : IntersectionPair G)
    (h : NumericalPairAt q P.left P.right P.equiv) :
    ∃ n, let Q := (P.row n).left ⊓ (P.row n).right
      IsElementaryAbelian 2 Q ∧ Q ∈ thompsonAbelianSubgroups P.left ∧
        Q ∈ thompsonAbelianSubgroups P.right := by
  generalize he : Nat.card P.left = m
  induction m using Nat.strong_induction_on generalizing P with
  | h m ih =>
    obtain ⟨hfamilyS,hfamilyT⟩ := h.maximum_families
    rcases h.recursion with hE | ⟨hnext,_⟩
    · let _ := hE
      have hmax : P.left ⊓ P.right ∈ thompsonAbelianSubgroups (P.left ⊓ P.right) :=
        ⟨le_rfl,inferInstance,fun _ hle _ => card_le_of_le hle⟩
      exact ⟨0,hE,hfamilyS hmax,hfamilyT hmax⟩
    · obtain ⟨n,hEn,hmaxS,hmaxT⟩ := ih (Nat.card P.next.left)
        (he ▸ P.next_card_lt_at h) P.next hnext rfl
      exact ⟨n + 1,hEn,hfamilyS hmaxT,hfamilyT hmaxT⟩
end IntersectionPair

omit [Finite G] in
private theorem NumericalPairAt.intersection_ne_bot {S T : Subgroup G} {φ : S ≃* T}
    (h : NumericalPairAt q S T φ) : S ⊓ T ≠ ⊥ := by
  have hout : ¬ S ≤ S ⊓ T := by
    intro hle
    have hh := relIndex_eq_one.mpr hle
    rw [h.index_left] at hh
    have := h.nontrivial_index
    omega
  intro hb
  have hh := h.lower_left S le_rfl hout
  have hvle : omegaCenterIn (S ⊓ T) ≤ S ⊓ T :=
    fun _ hx => ((mem_omegaCenterIn_iff _ _).mp hx).1
  have hv : omegaCenterIn (S ⊓ T) = ⊥ := le_bot_iff.mp (hvle.trans hb.le)
  rw [hv,relIndex_bot_right] at hh
  have := h.nontrivial_index
  omega

/-- Both next members generate the preceding left member, including the
terminal elementary branch. -/
theorem NumericalPairAt.next_generates {S T : Subgroup G} {φ : S ≃* T}
    (h : NumericalPairAt q S T φ) : image φ.symm (S ⊓ T) ⊔ (S ⊓ T) = S := by
  apply preimage_intersection_generates φ h.no_fixed h.intersection_ne_bot h.normal_right
    h.maximum_families.2
  intro A hA hAQ
  have hh := maximum_abelian_replacement_of_fixedIndex hA inf_le_left
    (fun _ hx => ((mem_omegaCenterIn_iff _ _).mp hx).1) inferInstance
    (fun _ hx => ((mem_omegaCenterIn_iff _ _).mp hx).2.1) h.normal_left
    (by rw [h.index_left]; exact h.lower_left A hA.1 hAQ)
  exact hh.1

omit [Finite G] in
private theorem omega_image {S T : Subgroup G} (φ : S ≃* T)
    (R : Subgroup G) (hRS : R ≤ S) :
    image φ (omegaOneAmbient R) = omegaOneAmbient (image φ R) := by
  have hs : (omegaOneAmbient R).subgroupOf S = omegaOneAmbient (R.subgroupOf S) := by
    apply map_injective S.subtype_injective
    rw [map_subgroupOf_eq_of_le ((omegaOneAmbient_le R).trans hRS),
      map_omegaOneAmbient_injective _ S.subtype_injective,map_subgroupOf_eq_of_le hRS]
  rw [image,hs,map_omegaOneAmbient_injective _ (ambientHom_injective φ)]
  rfl

omit [Finite G] in
private theorem omega_generated_transport {S T : Subgroup G} (φ : S ≃* T)
    (hS : omegaOneAmbient S = S) : omegaOneAmbient T = T := by
  have hh := omega_image φ S le_rfl
  rw [hS,image_self] at hh
  exact hh.symm

private theorem IntersectionPair.omega_generated (P : IntersectionPair G)
    (h : NumericalPairAt q P.left P.right P.equiv) : omegaOneAmbient P.left = P.left := by
  generalize he : Nat.card P.left = m
  induction m using Nat.strong_induction_on generalizing P with
  | h m ih =>
    have hgen := h.next_generates
    have hRS : P.next.left ≤ P.left := P.next_left_le
    have hQS : P.next.right ≤ P.left := inf_le_left
    have hRgen : omegaOneAmbient P.next.left = P.next.left := by
      rcases h.recursion with hE | ⟨hnext,_⟩
      · let _ : IsElementaryAbelian 2 P.next.right := hE
        have heQ : omegaOneAmbient P.next.right = P.next.right := omegaOneAmbient_eq_self _
        exact omega_generated_transport (nextPairEquiv P.equiv).symm heQ
      · exact ih (Nat.card P.next.left) (he ▸ P.next_card_lt_at h) P.next hnext rfl
    have hQgen : omegaOneAmbient P.next.right = P.next.right :=
      omega_generated_transport (nextPairEquiv P.equiv) hRgen
    apply le_antisymm (omegaOneAmbient_le _)
    calc
      P.left = P.next.left ⊔ P.next.right := hgen.symm
      _ ≤ omegaOneAmbient P.left := sup_le
        (hRgen.symm.trans_le (omegaOneAmbient_mono hRS))
        (hQgen.symm.trans_le (omegaOneAmbient_mono hQS))

/-- The recursive pair is generated by involutions. This preserves the
source generation input needed for exponent four after the class-two bound. -/
theorem NumericalPairAt.omega_generated {S T : Subgroup G} {φ : S ≃* T}
    (h : NumericalPairAt q S T φ) : omegaOneAmbient S = S ∧ omegaOneAmbient T = T := by
  have hs := IntersectionPair.omega_generated (⟨S,T,φ⟩ : IntersectionPair G) h
  exact ⟨hs,omega_generated_transport φ hs⟩

/-- The original two centers and the center of their intersection are
already elementary. This uses the actual elementary maximum row furnished
by the numerical4.4/4.5 argument. -/
theorem NumericalPairAt.omegaCenters_eq_centers {S T : Subgroup G} {φ : S ≃* T}
    (h : NumericalPairAt q S T φ) :
    omegaCenterIn S = centerIn S ∧ omegaCenterIn T = centerIn T ∧
      omegaCenterIn (S ⊓ T) = centerIn (S ⊓ T) := by
  let P : IntersectionPair G := ⟨S,T,φ⟩
  obtain ⟨n,hE,hAS,hAT⟩ := P.exists_elementary_maximum_row_at h
  let A := (P.row n).left ⊓ (P.row n).right
  let _ : IsElementaryAbelian 2 A := hE
  have hAQ : A ∈ thompsonAbelianSubgroups (S ⊓ T) :=
    ⟨le_inf hAS.1 hAT.1,hAS.2.1,fun B hB hBc => hAS.2.2 B (hB.trans inf_le_left) hBc⟩
  exact ⟨omegaCenter_eq_center_of_elementary_maximum hAS,
    omegaCenter_eq_center_of_elementary_maximum hAT,
    omegaCenter_eq_center_of_elementary_maximum hAQ⟩

end Glauberman
