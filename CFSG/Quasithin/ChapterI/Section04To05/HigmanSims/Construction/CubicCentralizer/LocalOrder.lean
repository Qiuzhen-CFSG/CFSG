module

public import CFSG.Quasithin.ChapterI.Section04To05.HigmanSims.Construction.CubicCentralizer.FixedCore
public import CFSG.Quasithin.ChapterI.Section04To05.HigmanSims.Construction.OverlapCores
public import Theory.GroupTheory.CoprimeSubgroupCentralizer
public import Theory.GroupTheory.PrimeOrderLift
public import Theory.SpecificGroups.SymmetricFive.ThreeCentralizer

/-!
# The original point-centralizer's cubic centralizer has order24

Coprime centralizer lifting preserves the actual five-point quotient.
The kernel on the cubic centralizer is its original cyclic-four fixed
point core. Its full image is the six-element centralizer of the original
cubic image in S₅, so the original centralizer has order24.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.HigmanSims
variable {G : Type*} [Group G] [Finite G] {z : G} {V : Subgroup G}

omit [Finite G] in
private theorem centralizer_powers {J : Type*} [Group J] (x : J) :
    centralizer (zpowers x : Set J) = centralizer ({x} : Set J) := by
  rw [zpowers_eq_closure, centralizer_closure]

/-- The actual cubic centralizer in the original marked involution
centralizer has order24 and maps onto the literal six-element centralizer
of its original five-point quotient image. -/
theorem TypeAt.cubic_point_centralizer_order (h : TypeAt z V) (t : G)
    (ht : t ∈ involutionCentralizer z) (ht3 : orderOf t = 3) :
    Nat.card (involutionCentralizer z ⊓ centralizer ({t} : Set G) : Subgroup G) = 24 ∧
    ∃ f : involutionCentralizer z →* Equiv.Perm (Fin 5), Function.Surjective f ∧
      f.ker = pCore 2 (involutionCentralizer z) ∧ orderOf (f ⟨t, ht⟩) = 3 ∧
      (centralizer ({(⟨t, ht⟩ : involutionCentralizer z)} : Set (involutionCentralizer z))).map f =
        centralizer ({f ⟨t, ht⟩} : Set (Equiv.Perm (Fin 5))) ∧
      Nat.card (centralizer ({f ⟨t, ht⟩} : Set (Equiv.Perm (Fin 5)))) = 6 := by
  let H := involutionCentralizer z
  let tH : H := ⟨t, ht⟩
  let C := centralizer ({tH} : Set H)
  obtain ⟨f, _, hf, hk, _⟩ := h.exists_overlap_five_marking
  have htH : orderOf tH = 3 := (orderOf_coe tH).symm.trans ht3
  have hkp : IsPGroup 2 f.ker := hk ▸ pCore_isPGroup
  have hft : orderOf (f tH) = 3 :=
    (f.orderOf_map_eq_of_coprime_of_isPGroup_ker hkp tH (by rw [htH]; decide)).trans htH
  have hk64 : Nat.card f.ker = 64 := by
    rw [hk, ← h.centralizer_fitting]
    exact h.centralizer_core_card
  have himage : C.map f = centralizer ({f tH} : Set (Equiv.Perm (Fin 5))) := by
    have hp : IsPGroup 3 (zpowers tH) := IsPGroup.of_card (n := 1)
      (by rw [Nat.card_zpowers, htH, pow_one])
    have hh := map_centralizer_eq_of_isPGroup_of_surjective_coprime 3 (zpowers tH) hp f hf
      (by rw [hk64]; decide)
    rw [MonoidHom.map_zpowers, centralizer_powers, centralizer_powers] at hh
    exact hh
  have himage6 : Nat.card (C.map f) = 6 := by
    rw [himage]
    exact Theory.SpecificGroups.SymmetricFive.centralizer_three_card _ hft
  let k : C →* Equiv.Perm (Fin 5) := f.comp C.subtype
  let j : C →* G := H.subtype.comp C.subtype
  have hj : Function.Injective j := H.subtype_injective.comp C.subtype_injective
  have hker : k.ker.map j = H.pCoreIn 2 ⊓ centralizer ({t} : Set G) := by
    ext x
    constructor
    · rintro ⟨q, hq, rfl⟩
      have hqk : (q : H) ∈ pCore 2 H := hk ▸ (show (q : H) ∈ f.ker from hq)
      refine ⟨⟨q, hqk, rfl⟩, mem_centralizer_singleton_iff.mpr ?_⟩
      exact congrArg Subtype.val (mem_centralizer_singleton_iff.mp q.property)
    · rintro ⟨⟨q, hq, he⟩, hxC⟩
      have hqC : q ∈ C := mem_centralizer_singleton_iff.mpr (Subtype.ext (by
        change (q : G) * t = t * (q : G)
        rw [show (q : G) = x from he]
        exact mem_centralizer_singleton_iff.mp hxC))
      refine ⟨⟨q, hqC⟩, ?_, he⟩
      change q ∈ f.ker
      rwa [hk]
  have hk4 : Nat.card k.ker = 4 := by
    obtain ⟨c, hc4, _, _, hc⟩ := h.cubic_point_core_fixed t ht ht3
    rw [← card_map_of_injective hj, hker, hc, Nat.card_zpowers, hc4]
  have hC24 : Nat.card C = 24 := by
    have hh := k.ker.card_mul_index
    rw [hk4, index_ker] at hh
    have hr : k.range = C.map f := by
      rw [MonoidHom.range_comp, range_subtype]
    rw [hr, himage6] at hh
    omega
  have hCmap : C.map H.subtype = H ⊓ centralizer ({t} : Set G) := by
    ext x
    constructor
    · rintro ⟨q, hq, rfl⟩
      exact ⟨q.property, mem_centralizer_singleton_iff.mpr
        (congrArg Subtype.val (mem_centralizer_singleton_iff.mp hq))⟩
    · rintro ⟨hxH, hxC⟩
      exact ⟨⟨x, hxH⟩, mem_centralizer_singleton_iff.mpr
        (Subtype.ext (mem_centralizer_singleton_iff.mp hxC)), rfl⟩
  refine ⟨?_, f, hf, hk, hft, himage, ?_⟩
  · rw [← hCmap, card_map_of_injective H.subtype_injective, hC24]
  · exact Theory.SpecificGroups.SymmetricFive.centralizer_three_card _ hft

end CFSG.Quasithin.HigmanSims
