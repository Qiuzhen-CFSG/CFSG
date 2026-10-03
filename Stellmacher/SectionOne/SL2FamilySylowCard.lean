module

public import Stellmacher.SectionOne.SL2ProductSylowCoordinates

/-!
# Sylow cardinality for an indexed SL2 product

A normal internal product of n distinct SL2(2) factors meets an ambient
Sylow two-subgroup in a group of order 2^n. This wrapper converts the
injective finite indexed family, together with relative normality of each
factor, into the finite-set product used by the Sylow-coordinate theorem.
Injectivity ensures that the image has exactly n factors.

The shared indexed factors arise in Stellmacher (2.2), journal page20,
refs/latex/stellmacher-n-group.tex. Its normality premise is supplied by the
separate weak-closure/Frattini argument; it is not inferred from an arbitrary
internal product inside the ambient group.
-/

namespace Stellmacher.SectionOne
universe u

public theorem sl2_family_sylow_inf_card
    {G : Type u} [Group G] [Finite G] (S : Sylow 2 G)
    (E : Subgroup G) (hEnormal : E.Normal) {n : ℕ} (D : Fin n → Subgroup G)
    (hinj : Function.Injective D) (hprod : IsInternalDirectProductFamily E D)
    (hD : ∀ i, IsSL2Two (D i)) (hnorm : ∀ i, ((D i).subgroupOf E).Normal) :
    Nat.card (↥((S : Subgroup G) ⊓ E)) = 2 ^ n := by
  classical
  let F := Finset.univ.image D
  have hmem (i : Fin n) : D i ∈ F := Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩
  have hgen : E = ⨆ K : {K : Subgroup G // K ∈ F}, K.val := by
    rw [hprod.1]
    apply le_antisymm
    · exact iSup_le fun i => le_iSup (fun K : {K : Subgroup G // K ∈ F} => K.val) ⟨D i, hmem i⟩
    · apply iSup_le
      intro K
      obtain ⟨i, hi, heq⟩ := Finset.mem_image.mp K.property
      rw [← heq]
      exact le_iSup D i
  have hFprod : IsInternalDirectProduct E F := by
    refine ⟨hgen, ?_, ?_, ?_⟩
    · intro K hK
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hK
      exact hnorm i
    · intro K hK L hL hne
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hK
      obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hL
      exact hprod.2.1 i j (fun hij => hne (congrArg D hij))
    · intro K hK L hL hne
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hK
      obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hL
      exact hprod.2.2 i j (fun hij => hne (congrArg D hij))
  have hF : ∀ K ∈ F, IsSL2Two K := by
    intro K hK
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hK
    exact hD i
  have hc := (sl2_product_sylow_coordinates S E hEnormal F hFprod hF).2.2.1
  have hFcard : F.card = n := by
    rw [Finset.card_image_of_injective _ hinj]
    simp
  simpa only [hFcard] using hc

end Stellmacher.SectionOne

