module

public import Theory.GroupTheory.GeneralizedFitting.QuasisimpleThompsonNormalizer

/-!
# Normalizers of two-subgroup images through an odd central layer

A surjection whose kernel lies in a two-subgroup maps its normalizer onto
its image normalizer. The same holds for a subsequent odd kernel by Sylow
conjugacy. Consequently every normalizer of the two-subgroup image normalizes
the image of its elementary Thompson subgroup, even when that image is not
the elementary Thompson subgroup of the quotient.

This is the normalizer transport used for the inner-action branch of
Aschbacher--Smith C.2.7, printed pp.146--147. The kernel need not itself
be a two-group.
-/

public section
open Subgroup Stellmacher
namespace Theory.GroupTheory.QuasisimpleThompson
variable {G H D : Type*} [Group G] [Finite G] [Group H] [Group D]

theorem normalizer_map_two_stage (R : Subgroup G) (hR : IsPGroup 2 R)
    (q : G →* H) (hq : Function.Surjective q) (hk : q.ker ≤ R)
    (f : H →* D) (hf : Function.Surjective f)
    (hcop : Nat.Coprime 2 (Nat.card f.ker)) :
    (normalizer (R : Set G)).map (f.comp q) =
      normalizer (R.map (f.comp q) : Set D) := by
  let : Finite H := Finite.of_surjective q hq
  let : Fact (IsPGroup 2 (R.map q)) := ⟨hR.map q⟩
  have hqN : (normalizer (R : Set G)).map q = normalizer (R.map q : Set H) := by
    have he : (normalizer (R.map q : Set H)).comap q = normalizer (R : Set G) := by
      rw [comap_normalizer_eq_of_surjective _ hq, comap_map_eq_self hk]
    rw [←he, map_comap_eq_self_of_surjective hq]
  rw [←map_map, ←map_map, hqN, normalizer_map_eq_of_coprime_kernel 2 _ f hf hcop]

theorem normalizer_image_le_normalizer_maxJ_of_odd_core_kernel
    (R : Subgroup G) (hR : IsPGroup 2 R)
    (f : G →* H) (hf : Function.Surjective f)
    (P : Subgroup G) [P.Normal] (hPR : P ≤ R) (hPk : P ≤ f.ker)
    (hcop : Nat.Coprime 2 (Nat.card (f.ker.map (QuotientGroup.mk' P)))) :
    normalizer (R.map f : Set H) ≤
      normalizer ((elementaryAbelianMaxJ R).map f : Set H) := by
  let q := QuotientGroup.mk' P
  let f' := QuotientGroup.lift P f hPk
  have he : f'.comp q = f := by ext; rfl
  have hc : Nat.Coprime 2 (Nat.card f'.ker) := by
    simpa only [f', QuotientGroup.ker_lift] using hcop
  have hqR : q.ker ≤ R := by simpa only [q, QuotientGroup.ker_mk'] using hPR
  have hf' := QuotientGroup.lift_surjective_of_surjective P f hf hPk
  rw [←he, ←normalizer_map_two_stage R hR q (QuotientGroup.mk'_surjective P)
    hqR f' hf' hc, ←normalizer_maxJ_two_stage R hR q
      (QuotientGroup.mk'_surjective P) hqR f' hf' hc]
  exact map_mono (normalizer_le_normalizer_elementaryAbelianMaxJ R)

end Theory.GroupTheory.QuasisimpleThompson
