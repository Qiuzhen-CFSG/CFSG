module
public import Theory.SpecificGroups.SymmetricSix.Parabolics.TwoCores.Duad.Calculation
public import Theory.SpecificGroups.PSL2.SylowFixedQuotients.Five
public import Mathlib.Logic.Equiv.Fin.Basic

/-!
# The normalizer of the original alternating Sylow four-group

A Sylow two-subgroup of A5, embedded in S5 by the literal alternating
inclusion, has normalizer isomorphic to S4. Its two-core is exactly that
same four-group, and its quotient is S3. The marking is transported by
Sylow conjugacy from the four-point permutation group; the finite checks
use only individual permutations and two double transpositions.

This is the finite quotient calculation for the actual point-line
intersection in Aschbacher--Segev, *The uniqueness of groups of type J4*,
Invent. Math. 105 (1991), (4.7), printed p.598, DOI 10.1007/BF01232280.
The source application is in ThreeSpace.PointLine.
-/

@[expose] public section
open Subgroup
namespace Theory.GroupTheory.Recognition.JankoFour.SourceRecognition.AlternatingSylowNormalizer
abbrev S5 := Equiv.Perm (Fin 5)
abbrev S4 := Equiv.Perm (Fin 4)
open Theory.SpecificGroups.SymmetricSix.DuadCalculation
private def embed : S4 →* S5 := Equiv.Perm.extendDomainHom (finSuccAboveEquiv (4 : Fin 5))
private theorem embed_injective : Function.Injective embed := Equiv.Perm.extendDomainHom_injective _
private def four : Subgroup S5 := core.map embed
private theorem four_card : Nat.card four = 4 := (card_map_of_injective embed_injective).trans core_card
private theorem four_even : four ≤ alternatingGroup (Fin 5) := by
  have hc : ∀ t : S4, t ∈ core → (embed t).sign = 1 := by decide +kernel
  rintro _ ⟨t,ht,rfl⟩
  exact Equiv.Perm.mem_alternatingGroup.mpr (hc t ht)
private def a : S4 := Equiv.swap 0 1 * Equiv.swap 2 3
private def b : S4 := Equiv.swap 0 2 * Equiv.swap 1 3
private theorem normalizer_four : normalizer (four : Set S5) = embed.range := by
  have hc : ∀ s : S5,
      (∃ t : S4, t ∈ core ∧ embed t = s*embed a*s⁻¹) →
      (∃ t : S4, t ∈ core ∧ embed t = s*embed b*s⁻¹) →
      ∃ t : S4, embed t = s := by decide +kernel
  apply le_antisymm
  · intro s hs
    apply hc s
    · exact (mem_normalizer_iff.mp hs (embed a)).mp (mem_map_of_mem embed (by decide +kernel : a ∈ core))
    · exact (mem_normalizer_iff.mp hs (embed b)).mp (mem_map_of_mem embed (by decide +kernel : b ∈ core))
  · have hh := core.le_normalizer_map embed
    rw [normalizer_eq_top,←MonoidHom.range_eq_map] at hh
    exact hh
private noncomputable def standard : Sylow 2 (alternatingGroup (Fin 5)) :=
  Sylow.ofCard (four.subgroupOf (alternatingGroup (Fin 5))) (by
    rw [Nat.card_congr (subgroupOfEquivOfLe four_even).toEquiv,four_card,nat_card_alternatingGroup]
    norm_num [Nat.factorial]
    decide +kernel)

def image (P : Sylow 2 (alternatingGroup (Fin 5))) : Subgroup S5 :=
  (P : Subgroup (alternatingGroup (Fin 5))).map (alternatingGroup (Fin 5)).subtype

private theorem exists_conj (P : Sylow 2 (alternatingGroup (Fin 5))) :
    ∃ g : S5, (image P).map (MulAut.conj g).toMonoidHom = four := by
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq (alternatingGroup (Fin 5)) P standard
  have he := congrArg (fun Q : Sylow 2 (alternatingGroup (Fin 5)) => (Q : Subgroup (alternatingGroup (Fin 5)))) hg
  rw [Sylow.coe_subgroup_smul,Subgroup.pointwise_smul_def] at he
  have hh := congrArg (Subgroup.map (alternatingGroup (Fin 5)).subtype) he
  change ((P : Subgroup (alternatingGroup (Fin 5))).map (MulAut.conj g).toMonoidHom).map
    (alternatingGroup (Fin 5)).subtype = (four.subgroupOf (alternatingGroup (Fin 5))).map
      (alternatingGroup (Fin 5)).subtype at hh
  rw [map_map,map_subgroupOf_eq_of_le four_even] at hh
  change ((P : Subgroup (alternatingGroup (Fin 5))).map
    ((alternatingGroup (Fin 5)).subtype.comp (MulAut.conj g).toMonoidHom)) = four at hh
  refine ⟨g.val,?_⟩
  rw [image,map_map]
  exact hh

/-- The normalizer of the original alternating Sylow four-group is an actual S4. -/
theorem normalizer_equiv (P : Sylow 2 (alternatingGroup (Fin 5))) :
    Nonempty (normalizer (image P : Set S5) ≃* S4) := by
  obtain ⟨g,hg⟩ := exists_conj P
  exact ⟨((MulAut.conj g).subgroupMap (normalizer (image P : Set S5))).trans
    ((MulEquiv.subgroupCongr (by
        change (normalizer (image P : Set S5)).map (MulAut.conj g).toMonoidHom = _
        rw [map_equiv_normalizer_eq,hg,normalizer_four])).trans
      (MonoidHom.ofInjective embed_injective).symm)⟩

noncomputable def equiv (P : Sylow 2 (alternatingGroup (Fin 5))) :
    normalizer (image P : Set S5) ≃* S4 := (normalizer_equiv P).some

theorem card (P : Sylow 2 (alternatingGroup (Fin 5))) :
    Nat.card (normalizer (image P : Set S5)) = 24 := by
  rw [Nat.card_congr (equiv P).toEquiv,Nat.card_perm,Nat.card_fin]
  rfl

theorem index (P : Sylow 2 (alternatingGroup (Fin 5))) :
    (normalizer (image P : Set S5)).index = 5 := by
  have hh := (normalizer (image P : Set S5)).card_mul_index
  rw [card,Nat.card_perm,Nat.card_fin] at hh
  norm_num at hh
  omega

/-- The action of this S4 on its three double transpositions. -/
noncomputable def projection (P : Sylow 2 (alternatingGroup (Fin 5))) :
    normalizer (image P : Set S5) →* Equiv.Perm (Fin 3) :=
  quotientHom.comp (equiv P).toMonoidHom

theorem projection_surjective (P : Sylow 2 (alternatingGroup (Fin 5))) :
    Function.Surjective (projection P) := quotientHom_surjective.comp (equiv P).surjective

theorem projection_ker_card (P : Sylow 2 (alternatingGroup (Fin 5))) :
    Nat.card (projection P).ker = 4 := by
  have hh := (projection P).ker.card_mul_index
  rw [index_ker,MonoidHom.range_eq_top_of_surjective _ (projection_surjective P),
    card_top,card,Nat.card_perm,Nat.card_fin] at hh
  change Nat.card (projection P).ker * 6 = 24 at hh
  omega

theorem image_card (P : Sylow 2 (alternatingGroup (Fin 5))) : Nat.card (image P) = 4 :=
  (card_map_of_injective (alternatingGroup (Fin 5)).subtype_injective).trans
    (Theory.PSL2.SylowFixedQuotients.alternating_sylow_card P)

/-- The kernel is exactly the given four-group, with its original embedding. -/
theorem projection_ker (P : Sylow 2 (alternatingGroup (Fin 5))) :
    (projection P).ker = (image P).subgroupOf (normalizer (image P : Set S5)) := by
  have he : (projection P).ker = pCore 2 (normalizer (image P : Set S5)) :=
    ker_eq_twoCore_of_surjective_perm_three _ (projection_surjective P)
      (IsPGroup.of_card (n := 2) (projection_ker_card P))
  have hp : IsPGroup 2 (image P) := P.isPGroup'.map (alternatingGroup (Fin 5)).subtype
  have hl : (image P).subgroupOf (normalizer (image P : Set S5)) ≤ (projection P).ker := by
    rw [he]
    exact le_sSup ⟨inferInstance,hp.comap_subtype⟩
  apply Eq.symm
  apply eq_of_le_of_card_ge hl
  rw [Nat.card_congr (subgroupOfEquivOfLe (image P).le_normalizer).toEquiv,
    image_card,projection_ker_card]

theorem twoCore (P : Sylow 2 (alternatingGroup (Fin 5))) :
    pCore 2 (normalizer (image P : Set S5)) =
      (image P).subgroupOf (normalizer (image P : Set S5)) :=
  (ker_eq_twoCore_of_surjective_perm_three _ (projection_surjective P)
    (IsPGroup.of_card (n := 2) (projection_ker_card P))).symm.trans (projection_ker P)

theorem twoCore_card (P : Sylow 2 (alternatingGroup (Fin 5))) :
    Nat.card (pCore 2 (normalizer (image P : Set S5))) = 4 := by
  rw [twoCore,Nat.card_congr (subgroupOfEquivOfLe (image P).le_normalizer).toEquiv,image_card]

/-- The actual normalizer modulo the original Sylow four-group is S3. -/
noncomputable def quotientEquiv (P : Sylow 2 (alternatingGroup (Fin 5))) :
    (normalizer (image P : Set S5) ⧸ (image P).subgroupOf (normalizer (image P : Set S5))) ≃*
      Equiv.Perm (Fin 3) :=
  (QuotientGroup.quotientMulEquivOfEq (projection_ker P).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective _ (projection_surjective P))

end Theory.GroupTheory.Recognition.JankoFour.SourceRecognition.AlternatingSylowNormalizer
