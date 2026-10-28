module

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.LinearTwo.AlternatingFive.Permutation
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.LinearTwo.Local
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.Quotient
public import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple

/-!
# Excluding the alternating-five block in 15.3.30

The alternating block model identifies the genuine quotient L/O₂(L) with
A₅. Simplicity and relative component normality identify this quotient with
the star image through the original action map. The marked Borel therefore
makes the actual image of M ∩ L a Sylow two-normalizer in the same A₅ that
acts on the block module.

The local plane construction and the concrete permutation-module obstruction
then contradict one another. The conditional exclusion uses only `Earlier`,
the common Sylow subgroup, and `BorelIdentification`. In particular it needs
no additional conclusion of C.1.13 and no pushing-up premise.

Source: Aschbacher–Smith, combined manuscript (1 March 2004),
15.3.30, printed p.1131, and Definition C.1.12, printed p.124.
-/

@[expose] public section
open Subgroup
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.LinearTwo.AlternatingFive
variable {G : Type*} [Group G] {d : LocalData G} {I : Subgroup G}
  {c : ComponentWitness d I} {n : ℕ} {F : Type*} [Field F] [Finite F] [CharP F 2]

private theorem intersection_componentMap :
    (d.M.subgroupOf c.L).map (SmallExtension.componentMap d c) =
      (d.starImage I (d.M ⊓ c.L)).subgroupOf (d.starImage I c.L) := by
  apply le_antisymm
  · rintro _ ⟨l, hl, rfl⟩
    exact ⟨⟨l, component_le c l.property⟩, ⟨hl, l.property⟩, rfl⟩
  · rintro ⟨x, hx⟩ ⟨l, hl, he⟩
    exact ⟨⟨l, hl.2⟩, hl.1, Subtype.ext he⟩

/-- The actual intersection image, under any core-quotient identification
with A₅, is a Sylow two-normalizer. The comparison with the marked matrix
Borel commutes with the original quotient maps on every element of L. -/
theorem marked_actor_normalizer (b : BorelIdentification d I c n F)
    (h : Earlier d I c) (P : Sylow 2 I)
    (hP : (P : Subgroup I).map I.subtype = d.S)
    (e : (c.L ⧸ pCore 2 c.L) ≃* alternatingGroup (Fin 5)) :
    ∃ Q : Sylow 2 (alternatingGroup (Fin 5)),
      (d.M.subgroupOf c.L).map
        (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 c.L))) =
          normalizer (Q : Set (alternatingGroup (Fin 5))) := by
  let : IsSimpleGroup (c.L ⧸ pCore 2 c.L) :=
    (MulEquiv.isSimpleGroup_congr e).mpr (alternatingGroup.isSimpleGroup (by simp))
  let k := SmallExtension.coreQuotientEquivStar d c h.component_normal P hP
  let f := e.symm.trans (k.trans b.linear)
  let H := (d.M.subgroupOf c.L).map
    (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 c.L)))
  have hmap : H.map f.toMonoidHom = Matrix.SpecialLinearGroup.rankOneBorel F := by
    rw [map_map]
    have he : f.toMonoidHom.comp
        (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 c.L))) =
        b.linear.toMonoidHom.comp (SmallExtension.componentMap d c) := by
      apply MonoidHom.ext
      intro l
      change b.linear (k (e.symm (e (QuotientGroup.mk' (pCore 2 c.L) l)))) = _
      rw [e.symm_apply_apply]
      rfl
    rw [he, ← map_map, intersection_componentMap]
    exact b.linear_borel
  let Q := (Matrix.SpecialLinearGroup.upperUnipotentSylow F 2).mapSurjective
    (f := f.symm.toMonoidHom) f.symm.surjective
  refine ⟨Q, ?_⟩
  change H = _
  calc
    H = (Matrix.SpecialLinearGroup.rankOneBorel F).map f.symm.toMonoidHom :=
      ((map_symm_eq_iff_map_eq H (e := f)).mpr hmap).symm
    _ = normalizer (Q : Set (alternatingGroup (Fin 5))) :=
      map_equiv_normalizer_eq (Matrix.SpecialLinearGroup.upperUnipotent F) f.symm

/-- The A₅ branch of 15.3.30 is impossible: the actual intersection preserves
an order-four subgroup, whereas its marked Borel image is a Sylow normalizer
in the actual natural permutation module. -/
theorem not_isAlternatingBlock [Finite G] (b : BorelIdentification d I c n F)
    (h : Earlier d I c) (P : Sylow 2 I)
    (hP : (P : Subgroup I).map I.subtype = d.S) :
    ¬ ChapterC.IsAlternatingBlock c.L 5 := by
  rintro ⟨_, _, rho, ⟨model⟩, haction⟩
  have hSI : d.S ≤ I := hP ▸ map_subtype_le (P : Subgroup I)
  obtain ⟨Q, hQ⟩ := marked_actor_normalizer b h P hP model.quotientIso
  obtain ⟨W, hW, hInv⟩ := h.blockModel_plane d hSI model
  rw [hQ] at hInv
  apply Permutation.no_four_natural_normalizer Q W hW
  intro a ha v hv
  have hm := hInv a ha v hv
  change Multiplicative.ofAdd
    (((BinaryPermutation.naturalRepresentation (Fin 5)).comp
      (alternatingGroup (Fin 5)).subtype) a v.toAdd) ∈ W
  rw [← haction a v]
  exact hm

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.LinearTwo.AlternatingFive
end
