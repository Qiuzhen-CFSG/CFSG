module
public import Theory.SpecificGroups.Alternating.SixFiveImage
public import Theory.SpecificGroups.Alternating.SixSylowNormalizer

/-!
# A Sylow subgroup cannot normalize an alternating-five section above A₆

A perfect subgroup with two-core quotient A₅ maps onto an actual A₅ under
any map to A₆ with solvable kernel. A surjection carries the original Sylow
to a full Sylow of A₆, contradicting the self-normalizing A₅ calculation.
This retains central covers of A₆ instead of identifying their carriers.

Source application: Aschbacher--Smith 14.7.68(2), pp.1071--1072,
comparing the fixed-component models supplied by C.2.7, pp.145--147.
-/

public noncomputable section
open Subgroup Theory.GroupTheory

namespace Theory.SpecificGroups.Alternating.SixSylowNormalizer
theorem no_sylow_normalizes_perfect_five_section
    {D : Type*} [Group D] [Finite D] (P : Sylow 2 D)
    (B : Subgroup D) [Group.IsPerfect B]
    (e : (B ⧸ pCore 2 B) ≃* alternatingGroup (Fin 5))
    (hPB : (P : Subgroup D) ≤ normalizer (B : Set D))
    (q : D →* alternatingGroup (Fin 6)) (hq : Function.Surjective q)
    [Group.IsSolvable q.ker] : False := by
  let j : (q.subgroupMap B).ker →* q.ker :=
    { toFun := fun x => ⟨x.val.val, congrArg Subtype.val x.property⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  have hj : Function.Injective j := by
    intro x y hh
    exact Subtype.ext (Subtype.ext (congrArg (fun z : q.ker => z.val) hh))
  let : Group.IsSolvable (q.subgroupMap B).ker :=
    Group.isSolvable_of_isSolvable_injective hj
  exact no_sylow_normalizes_five (P.mapSurjective hq) (B.map q)
    (SixFiveImage.imageEquiv q B e)
    ((map_mono hPB).trans (B.le_normalizer_map q))
end Theory.SpecificGroups.Alternating.SixSylowNormalizer
