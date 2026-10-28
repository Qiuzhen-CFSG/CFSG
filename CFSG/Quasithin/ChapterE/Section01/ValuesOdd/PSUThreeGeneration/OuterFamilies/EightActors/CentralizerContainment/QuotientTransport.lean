module
public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSUThreeGeneration.OuterFamilies.EightActors.Reduction
public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSUThreeGeneration.OuterFamilies.EightActors.FamilyTransport
public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSUThreeGeneration.InnerFamilies.Reduction
public import Theory.GroupTheory.NormalizedSupConsequences
/-!
# Lifting generation for the actual centralizer family

We retain precisely the restriction of the obstruction family, then its image
under the literal radical quotient map. Quotient E-members lift by E.1.10(7),
and the weak-closure normalizer lifts by Sylow conjugacy. The remaining
solvable kernel lies in a solvable Sylow overgroup, which is already trapped.
Finally the same minimal-supplement argument recovers the full centralizer
from its residual supplement. No unrestricted generation hypothesis is used.

Source: Aschbacher--Smith E.1.8, E.1.10(7), E.1.13, pp.210--214;
application to E.1.14(7), citing Aschbacher (1982), Lemma 4.11.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterE.ValuesOdd.PSUThreeGeneration.OuterFamilies.EightActors
variable {G : Type*} [Group G] [Finite G]

/-- Generation for the image of the original restricted family suffices through
a solvable kernel. Every quotient and inclusion is the literal one. -/
theorem quotient_family_generated_sylow_overgroup_le {T : Sylow 2 G}
    (d : LargeFamilyObstruction T) (H : Subgroup G) (hTH : (T : Subgroup G) ≤ H)
    (Y : Subgroup H) [Y.Normal] [Group.IsSolvable Y]
    (hgen : eFamilySubgroup 1
        (((T : Subgroup G).subgroupOf H).map (QuotientGroup.mk' Y))
        (Subgroup.map (QuotientGroup.mk' Y) '' ChiefOrbit.restrictedFamily H d.family) ⊔
      normalizer (weakClosure
        (((T : Subgroup G).subgroupOf H).map (QuotientGroup.mk' Y))
        (Subgroup.map (QuotientGroup.mk' Y) '' ChiefOrbit.restrictedFamily H d.family) :
        Set (H ⧸ Y)) = ⊤) : H ≤ d.overgroup := by
  let S := T.subtype hTH
  let Ω := ChiefOrbit.restrictedFamily H d.family
  have hΩ : IsElementaryFamily Ω := ChiefOrbit.restrictedFamily_elementary H d.elementary
  let q := QuotientGroup.mk' Y
  let M := ChiefOrbit.generationTarget 1 S Ω
  have hmap : M.map q = ⊤ := by
    apply top_unique
    rw [← hgen]
    apply sup_le
    · exact (quotient_eFamilySubgroup_le_map_sup_sylow S hΩ Y).trans
        (map_mono (sup_le le_sup_left
          ((sylow_le_weakClosure_normalizer S hΩ).trans le_sup_right)))
    · change normalizer (weakClosure ((S : Subgroup H).map q)
          (Subgroup.map q '' Ω) : Set (H ⧸ Y)) ≤ _
      rw [← map_weakClosure_surjective S hΩ q,
        ← map_weakClosure_normalizer_surjective S hΩ q (QuotientGroup.mk'_surjective Y)]
      exact map_mono le_sup_right
  have hMY : M ⊔ Y = ⊤ := by
    have hm := congrArg (comap q) hmap
    simpa only [comap_map_eq, q, QuotientGroup.ker_mk', comap_top] using hm
  let : Group.IsNilpotent S := S.isPGroup'.isNilpotent
  let : Group.IsSolvable (Y ⊔ (S : Subgroup H) : Subgroup H) :=
    Group.isSolvable_sup_of_normal_left _ _
  have hYM : Y ≤ M := le_sup_left.trans
    (ChiefOrbit.solvable_overgroup_le_generationTarget (by decide) S
      (Y ⊔ (S : Subgroup H)) le_sup_right hΩ)
  rw [sup_eq_left.mpr hYM] at hMY
  exact family_generated_sylow_overgroup_le d H hTH hMY

/-- Concrete centralizer consumer: lift from the radical quotient of C^∞T,
then recover C using its solvable quotient. The quotient generation is explicit. -/
theorem centralizer_le_of_residual_quotient_family_generation {T : Sylow 2 G}
    (d : LargeFamilyObstruction T) {z : G}
    (hTz : (T : Subgroup G) ≤ centralizer ({z} : Set G))
    (hgen : let K := centralizerResidualOvergroup T z
      let q := QuotientGroup.mk' (solvableRadical K)
      eFamilySubgroup 1 (((T : Subgroup G).subgroupOf K).map q)
          (Subgroup.map q '' ChiefOrbit.restrictedFamily K d.family) ⊔
        normalizer (weakClosure (((T : Subgroup G).subgroupOf K).map q)
          (Subgroup.map q '' ChiefOrbit.restrictedFamily K d.family) :
          Set (K ⧸ solvableRadical K)) = ⊤) :
    centralizer ({z} : Set G) ≤ d.overgroup := by
  have hKM := quotient_family_generated_sylow_overgroup_le d
    (centralizerResidualOvergroup T z) le_sup_right (solvableRadical _) hgen
  exact sylow_overgroup_le_of_solvable_quotient d (centralizer ({z} : Set G)) hTz
    (solvableResidual _) (le_sup_left.trans hKM)
end CFSG.Quasithin.ChapterE.ValuesOdd.PSUThreeGeneration.OuterFamilies.EightActors
