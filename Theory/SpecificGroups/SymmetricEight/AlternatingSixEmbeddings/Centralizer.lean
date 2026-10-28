module
public import Theory.SpecificGroups.SymmetricEight.AlternatingSixEmbeddings.TwoKernel
public import Theory.SpecificGroups.SymmetricEight.EvenPairCentralizer

/-!
# Centralizers of alternating-six sections in symmetric degree eight

Conjugate the actual A6 image to the even pointwise stabilizer of a pair.
Its full S8 centralizer has order at most two. For a perfect subgroup above
a two-group kernel with A6 two-core quotient, the image is exactly A6:
the factor five excludes a nontrivial two-core in its even image.

These bounds identify the literal local quotient centralizer in the
contrary branch of Aschbacher--Smith 12.6.17, printed p.827.
-/

public section
open Subgroup
namespace Theory.SpecificGroups.SymmetricEight.AlternatingSixEmbeddings

theorem six_centralizer_card_le_two (A : Subgroup (alternatingGroup (Fin 8)))
    (e : A ≃* alternatingGroup (Fin 6)) :
    Nat.card (centralizer (A.map (alternatingGroup (Fin 8)).subtype : Set (Equiv.Perm (Fin 8)))) ≤ 2 := by
  let f := A.subtype.comp e.symm.toMonoidHom
  have hf : Function.Injective f := A.subtype_injective.comp e.symm.injective
  have hr : f.range = A := by
    rw [MonoidHom.range_comp,MonoidHom.range_eq_top.mpr e.symm.surjective,
      ←MonoidHom.range_eq_map,range_subtype]
  obtain ⟨a,b,hab,hh⟩ := range_eq_pairFixer f hf
  rw [hr] at hh
  obtain ⟨p,hp⟩ := pairFixer_conjugate a b 0 1 hab (by decide)
  rw [←hh] at hp
  let c := (MulAut.conj (p : Equiv.Perm (Fin 8))).toMonoidHom
  let B := A.map (alternatingGroup (Fin 8)).subtype
  have heven : (pairFixer 0 1).map (alternatingGroup (Fin 8)).subtype =
      EvenPairCentralizer.evenPair := by
    ext x
    constructor
    · rintro ⟨y,hy,rfl⟩
      exact ⟨y.property,hy⟩
    · rintro ⟨hx,hfix⟩
      exact ⟨⟨x,hx⟩,hfix,rfl⟩
  have hBc : B.map c = EvenPairCentralizer.evenPair := by
    have hm := congrArg (Subgroup.map (alternatingGroup (Fin 8)).subtype) hp
    rw [heven,map_map] at hm
    change (A.map _).map c = _
    rw [map_map]
    exact hm
  have hc : (centralizer (B : Set (Equiv.Perm (Fin 8)))).map c ≤
      centralizer (EvenPairCentralizer.evenPair : Set (Equiv.Perm (Fin 8))) := by
    rw [←hBc]
    exact map_centralizer_le_centralizer_image _ _
  have hcard := (card_le_of_le hc).trans EvenPairCentralizer.centralizer_card_le_two
  rwa [card_map_of_injective (MulAut.conj (p : Equiv.Perm (Fin 8))).injective] at hcard


theorem six_subgroup_centralizer_card_le_two (A : Subgroup (Equiv.Perm (Fin 8)))
    (e : A ≃* alternatingGroup (Fin 6)) :
    Nat.card (centralizer (A : Set (Equiv.Perm (Fin 8)))) ≤ 2 := by
  let : Group.IsPerfect (alternatingGroup (Fin 6)) :=
    ⟨commutator_alternatingGroup_eq_top (by simp)⟩
  let : Group.IsPerfect A := Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective
  have hA : A ≤ alternatingGroup (Fin 8) := by
    intro x hx
    exact Abelianization.commutator_subset_ker (Equiv.Perm.sign.comp A.subtype)
      (show (⟨x,hx⟩ : A) ∈ commutator A from Group.IsPerfect.mem_commutator)
  have hh := six_centralizer_card_le_two (A.subgroupOf (alternatingGroup (Fin 8)))
    ((subgroupOfEquivOfLe hA).trans e)
  rwa [map_subgroupOf_eq_of_le hA] at hh


theorem symmetric_six_section_image {G : Type*} [Group G] [Finite G]
    (f : G →* Equiv.Perm (Fin 8)) (hk : IsPGroup 2 f.ker) (A : Subgroup G)
    [Group.IsPerfect A] (e : (A ⧸ pCore 2 A) ≃* alternatingGroup (Fin 6)) :
    pCore 2 (A.map f) = ⊥ ∧ Nonempty (A.map f ≃* alternatingGroup (Fin 6)) := by
  have hkA : IsPGroup 2 (f.subgroupMap A).ker := by
    rw [Subgroup.ker_subgroupMap]
    exact hk.comap_subtype
  let a := (f.subgroupMap A).pCoreQuotientEquiv (f.subgroupMap_surjective A) hkA
  let b := a.symm.trans e
  have h5 : 5 ∣ Nat.card (A.map f) := by
    apply dvd_trans _ (card_quotient_dvd_card (pCore 2 (A.map f)))
    rw [Nat.card_congr b.toEquiv,nat_card_alternatingGroup,Nat.card_fin]
    decide
  have hA : A.map f ≤ alternatingGroup (Fin 8) := by
    rintro _ ⟨x,hx,rfl⟩
    exact Abelianization.commutator_subset_ker ((Equiv.Perm.sign.comp f).comp A.subtype)
      (show (⟨x,hx⟩ : A) ∈ commutator A from Group.IsPerfect.mem_commutator)
  have hc := Theory.SpecificGroups.Alternating.EightSectionExtension.twoCore_eq_bot_of_five
    (alternatingGroup (Fin 8)) (A.map f) (MulEquiv.refl _) hA h5
  exact ⟨hc,⟨QuotientGroup.quotientBot.symm.trans
    ((QuotientGroup.quotientMulEquivOfEq hc).symm.trans b)⟩⟩
end Theory.SpecificGroups.SymmetricEight.AlternatingSixEmbeddings
