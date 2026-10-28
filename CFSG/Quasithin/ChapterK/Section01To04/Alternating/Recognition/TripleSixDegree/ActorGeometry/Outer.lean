module

public import CFSG.Quasithin.ChapterK.Section01To04.Alternating.Recognition.TripleSixDegree.Reduction
public import Theory.Alternating.TripleSixActorInversion
public import Theory.Representation.BinaryOffender.InnerInvolutions

/-!
# Outer elementary actors for the triple-A₆ degree bound

A normalizing involution inducing an inner automorphism belongs to the
irreducibly acting component: divide an inner representative by a central
square root and apply the binary Schur lemma. Hence an involution outside
the component induces a non-inner involution of the actual hexacode cover.
Both natural and exceptional quotient normal forms invert its cubic center.

Source: Aschbacher–Smith K.1–K.1.3, printed pp.452–453; GLS3 5.2.7.
This uses faithful binary irreducibility directly, without needing the
general finite-group self-centralization theorem.
-/

public section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory Atlas.Codes

namespace CFSG.Quasithin.ChapterK.Alternating.TripleSixReduction

variable {G V : Type*} [Group G] [Finite G] [AddCommGroup V] [Module (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V) {L : Subgroup G} [L.Normal]
  [IsIrreducible (ρ.comp L.subtype)]

/-- An actual involution outside the component inverts its marked cubic center. -/
theorem centralElement_inverted_of_not_mem (hf : Function.Injective ρ)
    (e : L ≃* HexEvenAutomorphisms) (t : G) (ht2 : t ^ 2 = 1) (htL : t ∉ L) :
    t * centralElement e * t⁻¹ = (centralElement e)⁻¹ := by
  let tN : normalizer (L : Set G) := ⟨t, by rw [normalizer_eq_top]; trivial⟩
  let α := L.normalizerMonoidHom tN
  let x := MulAut.congr e α
  have hx2 : x ^ 2 = 1 := by
    have htN : tN ^ 2 = 1 := Subtype.ext ht2
    change (MulAut.congr e (L.normalizerMonoidHom tN)) ^ 2 = 1
    rw [← map_pow, ← map_pow, htN, map_one, map_one]
  have hout : ∀ a : HexEvenAutomorphisms, x ≠ MulAut.conj a := by
    intro a ha
    apply htL
    apply involution_mem_of_inner ρ L hf tN ht2
    exact (MulAut.congr_inner_iff e α).mp ⟨a, ha⟩
  have hz : hexEvenZ ∈ center HexEvenAutomorphisms := by
    rw [← Hexacode.even_kernel_eq_center, hexEvenCoordinate_kernel]
    exact mem_zpowers _
  have hinv := GLS3.Chapter5.TripleSixActorInversion.hexEven_center_inverted x hx2 hout
    hexEvenZ hz
  have he : α (e.symm hexEvenZ) = (e.symm hexEvenZ)⁻¹ := by
    apply e.injective
    rw [map_inv, e.apply_symm_apply]
    exact hinv
  exact congrArg (fun a : L => (a : G)) he

/-- An elementary actor not contained in L contains an actual cubic inverter. -/
theorem actorGeometry_of_not_le (hf : Function.Injective ρ)
    (e : L ≃* HexEvenAutomorphisms) {A : Subgroup G}
    (hA : IsElementaryTwo A) (hAL : ¬ A ≤ L) : ActorGeometry e A := by
  classical
  obtain ⟨t, htA, htL⟩ := Set.not_subset.mp hAL
  let := hA.2
  refine ⟨t, htA, (fun ht => htL (ht.symm ▸ L.one_mem)), Or.inr ?_⟩
  exact centralElement_inverted_of_not_mem ρ hf e t
    (elemPow_eq_one_of_isElementaryAbelian t htA) htL

end CFSG.Quasithin.ChapterK.Alternating.TripleSixReduction
