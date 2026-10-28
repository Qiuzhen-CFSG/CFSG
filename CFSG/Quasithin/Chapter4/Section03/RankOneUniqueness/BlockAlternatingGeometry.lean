module
public import CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.BlockAlternatingSetup
public import CFSG.Quasithin.ChapterC.Section01.BlockTypes.AlternatingSevenFixed
public import CFSG.Quasithin.ChapterC.Section01.RankOne.Solvable.Source.Transport
public import Theory.SpecificGroups.Alternating.SevenComponent.Extension
public import Theory.GroupTheory.PResidual.SylowSupplement

/-!
# The actual residual and quotient action of the ordinary A₇ block

Transport the given block along its literal inclusion into G. Since S normalizes
K and is a two-group, O²(KS)=K. Conjugation on the normal A₇ quotient then
constructs a seven-letter action of KS whose kernel is exactly O₂(KS), and whose
K-image is A₇. A transposition in the image of the original R makes this action
surjective, yielding an isomorphism on the literal core quotient.

The final constructor supplies the residual, quotient and structural C.6 inputs.
The transposition marking, T=SΛ, and Levi normalization remain explicit source
premises; they are not asserted here. The vanishing fixed layer is also
transported to the actual ambient block for the whole-module coordinate proof.

Source: Aschbacher--Smith, original C.4.1(1), C.6.2--4 and 4.3.7,
printed pp.151,166--169,616.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}

theorem SourceConfiguration.ambient_alternating_block (c : SourceConfiguration T L)
    (ha : ChapterC.IsAlternatingBlock c.K 7) :
    ChapterC.IsAlternatingBlock (c.K.map c.H.subtype) 7 :=
  ChapterC.RankOne.Solvable.isAlternatingBlock_of_equiv
    (c.K.equivMapOfInjective c.H.subtype c.H.subtype_injective) ha

theorem SourceConfiguration.alternating_join_residual (c : SourceConfiguration T L)
    (ha : ChapterC.IsAlternatingBlock c.K 7) :
    (pResidual 2 (c.K.map c.H.subtype ⊔ ((T : Subgroup G) ⊓ c.H) : Subgroup G)).map
      (c.K.map c.H.subtype ⊔ ((T : Subgroup G) ⊓ c.H)).subtype = c.K.map c.H.subtype := by
  apply embedded_pResidual_join_pGroup _ _ (c.ambient_alternating_block ha).2.1.twoPerfect
    (T.isPGroup'.to_le inf_le_left)
  exact inf_le_right.trans c.normalizer_component.le

theorem SourceConfiguration.alternating_fixed_eq_bot (c : SourceConfiguration T L)
    (ha : ChapterC.IsAlternatingBlock c.K 7) :
    ChapterC.blockFixed (c.K.map c.H.subtype) = ⊥ :=
  (c.ambient_alternating_block ha).seven_fixed_eq_bot

theorem SourceConfiguration.exists_alternating_join_action (c : SourceConfiguration T L)
    (ha : ChapterC.IsAlternatingBlock c.K 7) :
    ∃ (f : (c.K.map c.H.subtype ⊔ ((T : Subgroup G) ⊓ c.H) : Subgroup G) →*
        Equiv.Perm (Fin 7)),
      f.ker = pCore 2 (c.K.map c.H.subtype ⊔ ((T : Subgroup G) ⊓ c.H) : Subgroup G) ∧
      ((c.K.map c.H.subtype).subgroupOf
        (c.K.map c.H.subtype ⊔ ((T : Subgroup G) ⊓ c.H))).map f =
          alternatingGroup (Fin 7) := by
  let A := c.K.map c.H.subtype
  let S := (T : Subgroup G) ⊓ c.H
  let J := A ⊔ S
  let B := A.subgroupOf J
  have hAJ : A ≤ J := le_sup_left
  have hSJ : S ≤ J := le_sup_right
  have hn : J ≤ normalizer (A : Set G) :=
    sup_le A.le_normalizer (inf_le_right.trans c.normalizer_component.le)
  let : B.Normal := normal_subgroupOf_of_le_normalizer hn
  have hB : ChapterC.IsAlternatingBlock B 7 :=
    ChapterC.RankOne.Solvable.isAlternatingBlock_of_equiv
      (subgroupOfEquivOfLe hAJ).symm (c.ambient_alternating_block ha)
  obtain ⟨ρ, ⟨m⟩, hρ⟩ := hB.2.2
  have hgen : B ⊔ S.subgroupOf J = ⊤ := by
    apply map_injective J.subtype_injective
    rw [Subgroup.map_sup, map_subgroupOf_eq_of_le hAJ,
      map_subgroupOf_eq_of_le hSJ, ← MonoidHom.range_eq_map, range_subtype]
  have hp : IsPGroup 2 (J ⧸ B) := isPGroup_quotient_of_sup_eq_top B
    (S.subgroupOf J) (T.isPGroup'.to_le inf_le_left).comap_subtype hgen
  obtain ⟨f, hf⟩ := alternatingGroup.SevenComponent.exists_extension B m.quotientIso
  refine ⟨f, alternatingGroup.SevenComponent.extension_kernel_eq_twoCore
    B m.quotientIso hp f hf, ?_⟩
  apply le_antisymm
  · rintro _ ⟨b, hb, rfl⟩
    rw [hf ⟨b,hb⟩]
    exact (m.quotientIso (QuotientGroup.mk' (pCore 2 B) ⟨b,hb⟩)).property
  · intro a ha
    obtain ⟨q, hq⟩ := m.quotientIso.surjective ⟨a,ha⟩
    obtain ⟨b, rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 B) q
    exact mem_map.mpr ⟨b.val,b.property,(hf b).trans (congrArg Subtype.val hq)⟩

private theorem surjective_of_alternating_and_swap {J : Type*} [Group J]
    (f : J →* Equiv.Perm (Fin 7))
    (ha : alternatingGroup (Fin 7) ≤ f.range)
    (ht : Equiv.swap (0 : Fin 7) 1 ∈ f.range) : Function.Surjective f := by
  have htodd : Equiv.swap (0 : Fin 7) 1 ∉ alternatingGroup (Fin 7) := by
    rw [Equiv.Perm.mem_alternatingGroup, Equiv.Perm.sign_swap (by decide)]
    decide
  apply MonoidHom.range_eq_top.mp
  apply top_unique
  intro g _
  by_cases hg : g ∈ alternatingGroup (Fin 7)
  · exact ha hg
  · have hgt : g * Equiv.swap (0 : Fin 7) 1 ∈ alternatingGroup (Fin 7) :=
      (mul_mem_iff_of_index_two (alternatingGroup.index_eq_two)).mpr
        (iff_of_false hg htodd)
    have hh := f.range.mul_mem (ha hgt) ht
    simpa only [mul_assoc, Equiv.swap_mul_self, mul_one] using hh

omit [Finite G] in
theorem SourceConfiguration.alternating_quotient_of_transposition
    (c : SourceConfiguration T L)
    (f : (c.K.map c.H.subtype ⊔ ((T : Subgroup G) ⊓ c.H) : Subgroup G) →*
      Equiv.Perm (Fin 7))
    (hk : f.ker = pCore 2 (c.K.map c.H.subtype ⊔ ((T : Subgroup G) ⊓ c.H) : Subgroup G))
    (ha : ((c.K.map c.H.subtype).subgroupOf
      (c.K.map c.H.subtype ⊔ ((T : Subgroup G) ⊓ c.H))).map f = alternatingGroup (Fin 7))
    (hr : ((c.I.pCoreIn 2).subgroupOf
      (c.K.map c.H.subtype ⊔ ((T : Subgroup G) ⊓ c.H))).map f =
        zpowers (Equiv.swap (0 : Fin 7) 1)) :
    ∃ e : ((c.K.map c.H.subtype ⊔ ((T : Subgroup G) ⊓ c.H) : Subgroup G) ⧸
      pCore 2 (c.K.map c.H.subtype ⊔ ((T : Subgroup G) ⊓ c.H) : Subgroup G)) ≃*
        Equiv.Perm (Fin 7),
      e.toMonoidHom.comp (QuotientGroup.mk' _) = f := by
  have hsurj : Function.Surjective f := surjective_of_alternating_and_swap f
    (ha ▸ map_le_range f _) (by
      apply map_le_range f ((c.I.pCoreIn 2).subgroupOf
        (c.K.map c.H.subtype ⊔ ((T : Subgroup G) ⊓ c.H)))
      rw [hr]
      exact mem_zpowers _)
  let e := (QuotientGroup.quotientMulEquivOfEq hk.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective f hsurj)
  exact ⟨e, rfl⟩

theorem SourceConfiguration.alternating_pushingUp_input_of_action
    (c : SourceConfiguration T L) (ha : ChapterC.IsAlternatingBlock c.K 7)
    (hfactor : (T : Subgroup G) = ((T : Subgroup G) ⊓ c.H) ⊔
      (L ⊔ (T : Subgroup G)).pCoreIn 2)
    (f : (c.K.map c.H.subtype ⊔ ((T : Subgroup G) ⊓ c.H) : Subgroup G) →*
      Equiv.Perm (Fin 7))
    (hk : f.ker = pCore 2 (c.K.map c.H.subtype ⊔ ((T : Subgroup G) ⊓ c.H) : Subgroup G))
    (hA : ((c.K.map c.H.subtype).subgroupOf
      (c.K.map c.H.subtype ⊔ ((T : Subgroup G) ⊓ c.H))).map f = alternatingGroup (Fin 7))
    (hr : ((c.I.pCoreIn 2).subgroupOf
      (c.K.map c.H.subtype ⊔ ((T : Subgroup G) ⊓ c.H))).map f =
        zpowers (Equiv.swap (0 : Fin 7) 1))
    (hlevi : (pResidual 2 (c.K.map c.H.subtype ⊓ normalizer (c.I.pCoreIn 2 : Set G) : Subgroup G)).map
      (c.K.map c.H.subtype ⊓ normalizer (c.I.pCoreIn 2 : Set G)).subtype ≤
        normalizer ((L ⊔ (T : Subgroup G)).pCoreIn 2 : Set G)) :
    Nonempty (ChapterC.Section06.AlternatingCentralVector.Input
      (c.K.map c.H.subtype) (c.I.pCoreIn 2) ((T : Subgroup G) ⊓ c.H)
      ((L ⊔ (T : Subgroup G)).pCoreIn 2)) := by
  obtain ⟨e, he⟩ := c.alternating_quotient_of_transposition f hk hA hr
  exact ⟨c.alternating_pushingUp_input (c.ambient_alternating_block ha) hfactor
    (c.alternating_join_residual ha) e (by rw [he]; exact hr) hlevi⟩

end CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness
