module

public import Theory.GroupTheory.SylowNormalIntersection

/-!
# Sylow intersections in preimages

If the image of a prescribed Sylow subgroup meets `I` in a Sylow subgroup
of `I`, then the prescribed Sylow meets the full preimage of `I` in a
Sylow subgroup. The homomorphism need not be surjective.

For a larger p-subgroup in the preimage, maximality downstairs identifies
its image. Maximality inside the normal kernel identifies its kernel
intersection. Cancelling lifts then proves equality upstairs.

Source application: Aschbacher--Smith, *The Classification of Quasithin
Groups*, E.1.10(7), printed p.211, the appeal to A.1.16.
-/

public section
open Subgroup
namespace Sylow
variable {G H : Type*} [Group G] [Group H] [Finite G]
variable {p : ℕ} [Fact p.Prime]

/-- A Sylow intersection downstairs lifts to a Sylow intersection in the full preimage. -/
theorem exists_subgroupOf_eq_comap (T : Sylow p G) (f : G →* H)
    (I : Subgroup H) (P : Sylow p I)
    (hP : (P : Subgroup I) = ((T : Subgroup G).map f).subgroupOf I) :
    ∃ S : Sylow p (I.comap f),
      (S : Subgroup (I.comap f)) = (T : Subgroup G).subgroupOf (I.comap f) := by
  let L := I.comap f
  let S := (T : Subgroup G).subgroupOf L
  have hpS : IsPGroup p S := T.isPGroup'.comap_subtype
  refine ⟨⟨S, hpS, ?_⟩, rfl⟩
  intro R hpR hSR
  apply le_antisymm ?_ hSR
  let B := R.map L.subtype
  have hpB : IsPGroup p B := hpR.map L.subtype
  have hSB : (T : Subgroup G) ⊓ L ≤ B := by
    rintro t ⟨ht, hl⟩
    exact ⟨⟨t, hl⟩, hSR ht, rfl⟩
  have hBP : (B.map f).subgroupOf I ≤ (P : Subgroup I) := by
    have hpC : IsPGroup p ((B.map f).subgroupOf I) := (hpB.map f).comap_subtype
    apply le_of_eq (P.is_maximal' hpC ?_)
    intro x hx
    rw [hP] at hx
    obtain ⟨t, ht, he⟩ := hx
    refine ⟨t, hSB ⟨ht, ?_⟩, he⟩
    change f t ∈ I
    rw [he]
    exact x.property
  obtain ⟨V, hV⟩ := T.exists_subgroupOf_eq_of_normal f.ker
  have hBT : B.subgroupOf f.ker ≤ (T : Subgroup G).subgroupOf f.ker := by
    rw [← hV]
    apply le_of_eq (V.is_maximal' hpB.comap_subtype ?_)
    intro z hz
    rw [hV] at hz
    apply hSB
    refine ⟨hz, ?_⟩
    change f z ∈ I
    rw [show f z = 1 from z.property]
    exact I.one_mem
  intro r hr
  have hrB : (r : G) ∈ B := ⟨r, hr, rfl⟩
  have him : (⟨f r, r.property⟩ : I) ∈ (B.map f).subgroupOf I :=
    mem_map_of_mem f hrB
  have hrt : f r ∈ (T : Subgroup G).map f := by
    have hh := hBP him
    rwa [hP] at hh
  obtain ⟨t, ht, he⟩ := hrt
  have htL : t ∈ L := by
    change f t ∈ I
    rw [he]
    exact r.property
  have hkt : (r : G) * t⁻¹ ∈ (T : Subgroup G) := by
    have hk : (r : G) * t⁻¹ ∈ f.ker := by
      simp only [MonoidHom.mem_ker, map_mul, map_inv, he, mul_inv_cancel]
    exact hBT (show (⟨(r : G) * t⁻¹, hk⟩ : f.ker) ∈ B.subgroupOf f.ker from
      B.mul_mem hrB (B.inv_mem (hSB ⟨ht, htL⟩)))
  have hh := (T : Subgroup G).mul_mem hkt ht
  change (r : G) ∈ (T : Subgroup G)
  simpa only [inv_mul_cancel_right] using hh

end Sylow
