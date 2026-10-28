module
public import Theory.GroupTheory.CComponent.TwoComponent.CoreQuotient

/-!
# Intersections and simple images of two-components

Radicals intersect subnormal subgroups in their intrinsic radicals.
Consequently a two-component's intrinsic O_{2',2} is its intersection
with the ambient solvable radical. More generally every surjection of
a two-component onto a simple group has this same kernel: the image is
perfect, its radical is trivial, and the proper kernel is solvable.
The resulting quotient equivalence retains the original homomorphism.
This latter argument needs no subnormality in any larger image ambient,
which is essential when the component comes from a centralizer.

Source: GLS II, Chapter B, Lemma 4.8; the intrinsic quotient identification
in Aschbacher–Smith I.3.2, printed p.415 (1 March 2004 manuscript).
-/

@[expose] public section
open Subgroup Theory.GroupTheory
namespace Subgroup
variable {G S : Type*} [Group G] [Group S] [Finite G]

/-- The radical intersects subnormal subgroups in their intrinsic radical. -/
theorem solvableRadical_subgroupOf_of_isSubnormal {L : Subgroup G}
    (hL : L.IsSubnormal) :
    (solvableRadical G).subgroupOf L = solvableRadical L := by
  apply le_antisymm
  · let f := L.subtype.subgroupComap (solvableRadical G)
    let : Group.IsSolvable ((solvableRadical G).subgroupOf L) :=
      Group.isSolvable_of_isSolvable_injective (f := f)
        (fun a b h => Subtype.ext (Subtype.ext
          (congrArg (fun r : solvableRadical G => (r : G)) h)))
    exact le_solvableRadical _ inferInstance inferInstance
  · exact map_le_iff_le_comap.mp (map_solvableRadical_subtype_le_of_isSubnormal hL)

namespace IsTwoComponent
variable {L : Subgroup G} (hL : L.IsTwoComponent)
include hL

/-- The unique maximal proper subnormal subgroup is the source O_{2',2}. -/
theorem oddTwoCore_eq_solvableRadical [Group.IsSolvable (pPrimeCore 2 L)] :
    oddTwoCore L = solvableRadical L := by
  let := hL.2
  exact oddTwoCore_eq_solvableRadical_of_quasisimple

/-- Intrinsic source core as the intersection with the ambient radical. -/
theorem oddTwoCore_eq_radical_intersection [Group.IsSolvable (pPrimeCore 2 L)] :
    oddTwoCore L = (solvableRadical G).subgroupOf L :=
  hL.oddTwoCore_eq_solvableRadical.trans
    (solvableRadical_subgroupOf_of_isSubnormal hL.1.subnormal).symm

/-- If the ambient source core is its radical, its intersection is the intrinsic core. -/
theorem oddTwoCore_subgroupOf_eq [Group.IsSolvable (pPrimeCore 2 L)]
    (hG : oddTwoCore G = solvableRadical G) :
    (oddTwoCore G).subgroupOf L = oddTwoCore L := by
  rw [hG, ← hL.oddTwoCore_eq_radical_intersection]

/-- Any simple surjective image of a two-component has precisely its intrinsic core as kernel.
No subnormality in the image's original ambient group is required. -/
theorem ker_eq_oddTwoCore_of_surjective_simple [Group.IsSolvable (pPrimeCore 2 L)]
    [IsSimpleGroup S] (f : L →* S) (hf : Function.Surjective f) :
    f.ker = oddTwoCore L := by
  let : Finite S := Finite.of_surjective f hf
  let : Group.IsPerfect L := hL.1.perfect
  let : Group.IsPerfect S := Group.IsPerfect.ofSurjective hf
  have hR : solvableRadical S = ⊥ := by
    rcases (inferInstance : (solvableRadical S).Normal).eq_bot_or_eq_top with h | h
    · exact h
    · let : Group.IsSolvable (⊤ : Subgroup S) := h ▸ inferInstanceAs
        (Group.IsSolvable (solvableRadical S))
      let : Group.IsSolvable S := Group.isSolvable_of_surjective
        (f := (topEquiv : (⊤ : Subgroup S) ≃* S).toMonoidHom) topEquiv.surjective
      exact (Group.IsPerfect.not_isSolvable S inferInstance).elim
  have hk : f.ker ≠ ⊤ := by
    intro ht
    obtain ⟨s, hs⟩ := exists_ne (1 : S)
    obtain ⟨l, rfl⟩ := hf s
    exact hs (show f l = 1 from (ht ▸ mem_top l : l ∈ f.ker))
  let : Group.IsSolvable f.ker := hL.1.isSolvable_of_subnormal_lt_top
    (inferInstance : f.ker.Normal).isSubnormal hk
  have he := comap_solvableRadical_eq_of_solvable_ker f hf
  rw [hR] at he
  change f.ker = solvableRadical L at he
  exact he.trans hL.oddTwoCore_eq_solvableRadical.symm

/-- The simple image is canonically the source quotient, using the supplied homomorphism. -/
noncomputable def quotientOddTwoCoreEquivOfSurjectiveSimple
    [Group.IsSolvable (pPrimeCore 2 L)] [IsSimpleGroup S]
    (f : L →* S) (hf : Function.Surjective f) :
    (L ⧸ oddTwoCore L) ≃* S :=
  QuotientGroup.liftEquiv _ hf (hL.ker_eq_oddTwoCore_of_surjective_simple f hf).symm

theorem quotientOddTwoCoreEquivOfSurjectiveSimple_mk
    [Group.IsSolvable (pPrimeCore 2 L)] [IsSimpleGroup S]
    (f : L →* S) (hf : Function.Surjective f) (x : L) :
    hL.quotientOddTwoCoreEquivOfSurjectiveSimple f hf
      (QuotientGroup.mk' (oddTwoCore L) x) = f x := rfl

end IsTwoComponent
end Subgroup
