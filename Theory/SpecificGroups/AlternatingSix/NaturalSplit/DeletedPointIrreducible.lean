module
public import Theory.SpecificGroups.AlternatingSix.NaturalSplit.DeletedPointAmbient
public import Theory.Representation.BinaryPermutation.SixFiveRestriction
public import Theory.Representation.BinaryPermutation.GroupIrreducible
public import Theory.GroupTheory.AbelianConjugateSpan

/-!
# Irreducibility of the marked deleted-point block

The fixed subgroup of the sixth-coordinate automorphism restricts the natural
six-letter module to the five-letter even core. Its invariant translation
subgroups are therefore trivial or the whole sixteen-group. The ambient
versions preserve the supplied block marking and the original normalizing
involution. They give both generation by each nonzero factor element and a
trivial factor centralizer.

Source: Aschbacher--Smith, 14.3.20, printed pp.997--998, using B.3.1.
-/

@[expose] public noncomputable section

open Subgroup SemidirectProduct
namespace BinaryPermutation.SixNaturalSplit
open Theory.SpecificGroups.SymmetricSix.BinaryFlags

noncomputable def pointActorFiveEquiv : pointActor ≃* FivePair.five where
  toFun k := ⟨k.val.val, k.property, k.val.property⟩
  invFun k := ⟨⟨k.val,k.property.2⟩,k.property.1⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

theorem pointActor_invariant_subgroup (N : Subgroup Vector)
    (hn : ∀ k : pointActor, ∀ v ∈ N, action k.val v ∈ N) : N = ⊥ ∨ N = ⊤ := by
  let e := SixFiveRestriction.naturalSixEquivCoreFive.toAddEquiv.toMultiplicative
  let E := N.map e.toMonoidHom
  have he (k : pointActor) (v : Vector) :
      e (action k.val v) = Multiplicative.ofAdd
        (coreRepresentation (Fin 5) (FivePair.fiveEquiv (pointActorFiveEquiv k)).val
          (e v).toAdd) := by
    apply Multiplicative.toAdd.injective
    exact SixFiveRestriction.naturalSixEquivCoreFive_equivariant
      (pointActorFiveEquiv k) v.toAdd
  have hi : ∀ g : alternatingGroup (Fin 5), ∀ v ∈ E,
      Multiplicative.ofAdd (coreRepresentation (Fin 5) g.val v.toAdd) ∈ E := by
    intro g v hv
    obtain ⟨k,rfl⟩ := (pointActorFiveEquiv.trans FivePair.fiveEquiv).surjective g
    obtain ⟨w,hw,rfl⟩ := hv
    change Multiplicative.ofAdd (coreRepresentation (Fin 5)
      (FivePair.fiveEquiv (pointActorFiveEquiv k)).val (e w).toAdd) ∈ E
    rw [← he]
    exact mem_map_of_mem _ (hn k w hw)
  rcases fiveCore_invariant_subgroup E hi with hb | ht
  · left
    exact (map_eq_bot_iff_of_injective N e.injective).mp hb
  · right
    apply (map_injective e.injective)
    rw [← MonoidHom.range_eq_map, MonoidHom.range_eq_top.mpr e.surjective]
    exact ht

theorem pointFixed_invariant_translation (N : Subgroup Model)
    (hN : N ≤ translations)
    (hn : pointAutomorphism.fixedSubgroup ≤ normalizer (N : Set Model)) :
    N = ⊥ ∨ N = translations := by
  let W := N.comap (inl : Vector →* Model)
  have hw : ∀ k : pointActor, ∀ v ∈ W, action k.val v ∈ W := by
    intro k v hv
    have hk : inr k.val ∈ pointAutomorphism.fixedSubgroup :=
      (pointAutomorphism_fixed_iff _).mpr k.property
    have hh := (mem_normalizer_iff.mp (hn hk) (inl v)).mp hv
    change (inr k.val : Model) * inl v * (inr k.val : Model)⁻¹ ∈ N at hh
    change inl (action k.val v) ∈ N
    simpa only [inl_aut,map_inv] using hh
  have hmap : W.map (inl : Vector →* Model) = N :=
    map_comap_eq_self hN
  rcases pointActor_invariant_subgroup W hw with hb | ht
  · left
    rw [hb,Subgroup.map_bot] at hmap
    exact hmap.symm
  · right
    rw [ht,← MonoidHom.range_eq_map] at hmap
    exact hmap.symm

theorem pointBlock_invariant_factor {G : Type*} [Group G]
    (K A N : Subgroup G) (f : K ≃* Model)
    (hA : (A.subgroupOf K).map f.toMonoidHom = translations)
    (hAK : A ≤ K) (d : normalizer (K : Set G))
    (hd : MulAut.congr f (K.normalizerMonoidHom d) = pointAutomorphism)
    (hNA : N ≤ A)
    (hn : K ⊓ centralizer ({(d:G)} : Set G) ≤ normalizer (N : Set G)) :
    N = ⊥ ∨ N = A := by
  let D := K ⊓ centralizer ({(d:G)} : Set G)
  let E := (N.subgroupOf K).map f.toMonoidHom
  have hE : E ≤ translations := hA ▸ map_mono (subgroupOf_mono K hNA)
  have hnE : pointAutomorphism.fixedSubgroup ≤ normalizer (E : Set Model) := by
    apply le_normalizer_iff.mpr
    intro k hk v hv
    obtain ⟨a,ha⟩ := (pointBlockCentralizerEquiv K f d hd).surjective ⟨k,hk⟩
    let aK : K := ⟨a,(show D ≤ K from inf_le_left) a.property⟩
    have haf : f aK = k := by
      simpa only [pointBlockCentralizerEquiv_apply] using congrArg Subtype.val ha
    obtain ⟨w,hw,rfl⟩ := hv
    refine ⟨aK*w*aK⁻¹, ?_, ?_⟩
    · exact le_normalizer_iff.mp hn a a.property w hw
    · change f (aK*w*aK⁻¹) = k * f w * k⁻¹
      rw [map_mul,map_mul,map_inv,haf]
  have hNK : N ≤ K := hNA.trans hAK
  rcases pointFixed_invariant_translation E hE hnE with hb | ht
  · left
    have hn0 : N.subgroupOf K = ⊥ := (map_eq_bot_iff_of_injective (N.subgroupOf K) f.injective).mp hb
    have hh := congrArg (map K.subtype) hn0
    simpa only [map_subgroupOf_eq_of_le hNK,Subgroup.map_bot] using hh
  · right
    have hh := (map_injective f.injective) (ht.trans hA.symm)
    simpa only [map_subgroupOf_eq_of_le hNK,map_subgroupOf_eq_of_le hAK]
      using congrArg (map K.subtype) hh

theorem pointBlock_nonzero_span {G : Type*} [Group G]
    (K A : Subgroup G) (f : K ≃* Model)
    (hA : (A.subgroupOf K).map f.toMonoidHom = translations)
    (hAK : A ≤ K) (d : normalizer (K : Set G))
    (hd : MulAut.congr f (K.normalizerMonoidHom d) = pointAutomorphism)
    (hAN : K ⊓ centralizer ({(d:G)} : Set G) ≤ normalizer (A : Set G))
    (a : G) (ha : a ∈ A) (hne : a ≠ 1) :
    conjugateSpanBy (zpowers a) (K ⊓ centralizer ({(d:G)} : Set G)) = A := by
  let N := conjugateSpanBy (zpowers a) (K ⊓ centralizer ({(d:G)} : Set G))
  rcases pointBlock_invariant_factor K A N f hA hAK d hd
    (conjugateSpanBy_le (zpowers_le.mpr ha) hAN)
    (le_normalizer_conjugateSpanBy _ _) with hb | he
  · exact False.elim (hne (show a ∈ (⊥ : Subgroup G) from
      hb ▸ le_conjugateSpanBy _ _ (mem_zpowers a)))
  · exact he

theorem pointBlock_factor_centralizer {G : Type*} [Group G]
    (K A : Subgroup G) [IsElementaryAbelian 2 A] (hcard : Nat.card A = 16)
    (f : K ≃* Model)
    (hA : (A.subgroupOf K).map f.toMonoidHom = translations)
    (hAK : A ≤ K) (d : normalizer (K : Set G))
    (hd : MulAut.congr f (K.normalizerMonoidHom d) = pointAutomorphism) :
    A ⊓ centralizer (K ⊓ centralizer ({(d:G)} : Set G) : Set G) = ⊥ := by
  apply le_antisymm _ bot_le
  intro a ha
  by_contra hne
  have hn : K ⊓ centralizer ({(d:G)} : Set G) ≤ normalizer (zpowers a : Set G) :=
    (le_centralizer_iff.mp (zpowers_le.mpr ha.2)).trans
      (Subgroup.centralizer_le_normalizer _)
  rcases pointBlock_invariant_factor K A (zpowers a) f hA hAK d hd
    (zpowers_le.mpr ha.1) hn with hb | he
  · exact hne (hb ▸ mem_zpowers a)
  · have htwo : orderOf a = 2 :=
      orderOf_eq_prime (elemPow_eq_one_of_isElementaryAbelian (p := 2) a ha.1) hne
    have hh := congrArg (fun B : Subgroup G => Nat.card B) he
    rw [Nat.card_zpowers, htwo, hcard] at hh
    omega

end BinaryPermutation.SixNaturalSplit
