module
public import Glauberman.FixedNormalPairRestriction
public import Theory.GroupTheory.RankOneInvariantKernelOrbit

/-!
# Central omega and fixed-index inheritance in a subgroup pair

In the equal maximum-abelian-order branch of Niles4.4, a common maximum
abelian subgroup contains both old central omega subgroups. They therefore
embed in the central omega of the new intersection. Fixed-space index is
monotone under that embedding and is preserved by the literal subgroup
isomorphism. Thus the two uniform lower bounds supplied initially by the
natural module theorem pass to the new pair without any new recognition.

Source: Niles, *Pushing-up in finite groups* (1979), Proposition4.4,
printedp45, the equal maximum-order case.
-/

public section
open Subgroup Theory.GroupTheory.SubgroupTransport
namespace Glauberman
variable {G H : Type*} [Group G] [Group H]

private theorem omega_le_self (Q : Subgroup G) : omegaCenterIn Q ≤ Q :=
  fun _ hx => ((mem_omegaCenterIn_iff Q _).mp hx).1

private theorem omega_central (Q : Subgroup G) :
    omegaCenterIn Q ≤ centralizer (Q : Set G) :=
  fun _ hx => ((mem_omegaCenterIn_iff Q _).mp hx).2.1

/-- Central omega transports along the literal subgroup isomorphism. -/
theorem omegaCenter_image {S : Subgroup G} {T : Subgroup H} (φ : S ≃* T)
    (R : Subgroup G) (hRS : R ≤ S) :
    image φ (omegaCenterIn R) = omegaCenterIn (image φ R) := by
  have hs : (omegaCenterIn R).subgroupOf S = omegaCenterIn (R.subgroupOf S) := by
    apply map_injective S.subtype_injective
    rw [map_subgroupOf_eq_of_le ((omega_le_self R).trans hRS),
      NilesRankOneKernel.omegaCenterIn_map_injective _ S.subtype_injective,
      map_subgroupOf_eq_of_le hRS]
  rw [image,hs,NilesRankOneKernel.omegaCenterIn_map_injective _ (ambientHom_injective φ)]
  rfl

/-- Central omega of a larger subgroup embeds in that of a smaller subgroup
when it already lies in the smaller subgroup. -/
theorem omegaCenter_le_of_le_of_omega_le {D Q : Subgroup G}
    (hDQ : D ≤ Q) (hVD : omegaCenterIn Q ≤ D) : omegaCenterIn Q ≤ omegaCenterIn D := by
  intro x hx
  obtain ⟨_,hc,hp⟩ := (mem_omegaCenterIn_iff Q x).mp hx
  exact (mem_omegaCenterIn_iff D x).mpr ⟨hVD hx,centralizer_le hDQ hc,hp⟩

/-- Relative fixed-space index is monotone on the underlying invariant layers. -/
theorem fixedIndex_mono [Finite G] {V W A : Subgroup G} (hVW : V ≤ W) :
    (V ⊓ centralizer (A : Set G)).relIndex V ≤
      (W ⊓ centralizer (A : Set G)).relIndex W := by
  rw [inf_relIndex_left,inf_relIndex_left]
  exact relIndex_le_of_le_right hVW (show (centralizer (A : Set G)).relIndex W ≠ 0 from
    index_ne_zero_of_finite)

/-- In the equal maximum-order case of Niles4.4, both old central omega
subgroups lie in the central omega of the new intersection. -/
theorem omegaCenters_le_intersection_of_common_maximum [Finite G]
    {S R Q A : Subgroup G} (hRS : R ≤ S) (hQS : Q ≤ S)
    (hA : A ∈ thompsonAbelianSubgroups S) (hAD : A ≤ R ⊓ Q) :
    omegaCenterIn R ≤ omegaCenterIn (R ⊓ Q) ∧
    omegaCenterIn Q ≤ omegaCenterIn (R ⊓ Q) := by
  have hAR : A ∈ thompsonAbelianSubgroups R :=
    ⟨hAD.trans inf_le_left,hA.2.1,fun B hB hBc => hA.2.2 B (hB.trans hRS) hBc⟩
  have hAQ : A ∈ thompsonAbelianSubgroups Q :=
    ⟨hAD.trans inf_le_right,hA.2.1,fun B hB hBc => hA.2.2 B (hB.trans hQS) hBc⟩
  have hVR : omegaCenterIn R ≤ A := le_maximum_abelian_of_centralizes hAR (omega_le_self R)
    ((omega_central R).trans (centralizer_le hAR.1))
  have hVQ : omegaCenterIn Q ≤ A := le_maximum_abelian_of_centralizes hAQ (omega_le_self Q)
    ((omega_central Q).trans (centralizer_le hAQ.1))
  exact ⟨omegaCenter_le_of_le_of_omega_le inf_le_left (hVR.trans hAD),
    omegaCenter_le_of_le_of_omega_le inf_le_right (hVQ.trans hAD)⟩

/-- The first inherited numerical module condition at the next row. No
recognition of a new arbitrary module is assumed. -/
theorem fixedIndex_lower_of_common_maximum [Finite G]
    {S R Q A : Subgroup G} (hRS : R ≤ S) (hQS : Q ≤ S)
    (hA : A ∈ thompsonAbelianSubgroups S) (hAD : A ≤ R ⊓ Q)
    {n : ℕ}
    (hlower : ∀ B : Subgroup G, B ≤ S → ¬ B ≤ Q →
      n ≤ (omegaCenterIn Q ⊓ centralizer (B : Set G)).relIndex (omegaCenterIn Q)) :
    ∀ B : Subgroup G, B ≤ R → ¬ B ≤ R ⊓ Q →
      n ≤ (omegaCenterIn (R ⊓ Q) ⊓ centralizer (B : Set G)).relIndex (omegaCenterIn (R ⊓ Q)) := by
  intro B hBR hBD
  have hBQ : ¬ B ≤ Q := fun hBQ => hBD (le_inf hBR hBQ)
  exact (hlower B (hBR.trans hRS) hBQ).trans
    (fixedIndex_mono (omegaCenters_le_intersection_of_common_maximum hRS hQS hA hAD).2)

/-- The literal fixed-space index is preserved by subgroup-pair transport. -/
theorem fixedIndex_image {S : Subgroup G} {T : Subgroup H} (φ : S ≃* T)
    (W A : Subgroup G) (hWS : W ≤ S) (hAS : A ≤ S) :
    (image φ W ⊓ centralizer (image φ A : Set H)).relIndex (image φ W) =
      (W ⊓ centralizer (A : Set G)).relIndex W := by
  have he : image φ (W ⊓ centralizer (A : Set G)) =
      image φ W ⊓ centralizer (image φ A : Set H) := by
    apply le_antisymm
    · rintro x ⟨y,hy,rfl⟩
      exact ⟨(mem_image_iff φ W y).mpr hy.1,(centralizes_iff φ A hAS y).mp hy.2⟩
    · rintro x ⟨⟨y,hy,rfl⟩,hc⟩
      exact ⟨y,⟨hy,(centralizes_iff φ A hAS y).mpr hc⟩,rfl⟩
  rw [←he]
  have hi := relIndex_map_map_of_injective
    ((W ⊓ centralizer (A : Set G)).subgroupOf S) (W.subgroupOf S) (ambientHom_injective φ)
  rw [relIndex_subgroupOf hWS] at hi
  exact hi

/-- Both uniform lower-index conditions inherit in the equal maximum-order
case of the recursive source pair. -/
theorem both_fixedIndex_lower_of_common_maximum [Finite G]
    (S T : Subgroup G) (φ : S ≃* T) (R A : Subgroup G)
    (hRS : R ≤ S) (hRmap : image φ R = S ⊓ T)
    (hRpre : image φ.symm (S ⊓ T) = R)
    (hA : A ∈ thompsonAbelianSubgroups S) (hAD : A ≤ R ⊓ (S ⊓ T))
    {n : ℕ}
    (hlowerS : ∀ B : Subgroup G, B ≤ S → ¬ B ≤ S ⊓ T →
      n ≤ (omegaCenterIn (S ⊓ T) ⊓ centralizer (B : Set G)).relIndex (omegaCenterIn (S ⊓ T)))
    (hlowerT : ∀ B : Subgroup G, B ≤ T → ¬ B ≤ S ⊓ T →
      n ≤ (omegaCenterIn (S ⊓ T) ⊓ centralizer (B : Set G)).relIndex (omegaCenterIn (S ⊓ T))) :
    (∀ B : Subgroup G, B ≤ R → ¬ B ≤ R ⊓ (S ⊓ T) →
      n ≤ (omegaCenterIn (R ⊓ (S ⊓ T)) ⊓ centralizer (B : Set G)).relIndex
        (omegaCenterIn (R ⊓ (S ⊓ T)))) ∧
    (∀ B : Subgroup G, B ≤ S ⊓ T → ¬ B ≤ R ⊓ (S ⊓ T) →
      n ≤ (omegaCenterIn (R ⊓ (S ⊓ T)) ⊓ centralizer (B : Set G)).relIndex
        (omegaCenterIn (R ⊓ (S ⊓ T)))) := by
  refine ⟨fixedIndex_lower_of_common_maximum hRS inf_le_left hA hAD hlowerS,?_⟩
  intro B hBQ hBD
  have hBS := hBQ.trans inf_le_left
  have hout : ¬ image φ B ≤ S ⊓ T := by
    intro hle
    have hh := image_mono φ.symm hle
    rw [image_symm φ B hBS,hRpre] at hh
    exact hBD (le_inf hh hBQ)
  have hlow := hlowerT (image φ B) (image_le φ B) hout
  have he := fixedIndex_image φ (omegaCenterIn R) B ((omega_le_self R).trans hRS) hBS
  rw [omegaCenter_image φ R hRS,hRmap] at he
  rw [he] at hlow
  exact hlow.trans (fixedIndex_mono
    (omegaCenters_le_intersection_of_common_maximum hRS inf_le_left hA hAD).1)

end Glauberman
