module

public import GorensteinWalter.A5
public import GorensteinWalter.PGL2InnerAction
public import GorensteinWalter.LinearRingEquiv
public import Theory.SpecificGroups.Alternating.FiveExtensionAction

/-!
# The five-point action of PGL₂ over a field of order five

The concrete A₅ ≃ PSL₂(5) comparison and faithful conjugation on PSL₂
embed PGL₂(K) in Aut(A₅) ≃ S₅. Both groups have order 120, making this
actual homomorphism an isomorphism. The literal PSL₂ range maps to A₅
because it has index two. No recognition from group order alone is used.

This is the smaller-group comparison used in the characteristic-five
subfield-centralizer calculation for Aschbacher--Smith E.1.14(6), printed
p.214. The automorphism comparison is GLS3, Theorem 5.2.1; the concrete
PSL₂ comparison is proved in `GorensteinWalter.A5`.
-/

public section
noncomputable section
open Subgroup GorensteinWalter Matrix
namespace Theory.PSL2

/-- The actual five-point comparison is induced by the faithful conjugation
on PSL2, the concrete A5 isomorphism, and Aut(A5)=S5. -/
theorem exists_pgl2_five_equiv (K : Type*) [Field K] [Finite K]
    (hK : Nat.card K = 5) : Nonempty (PGL2 K ≃* Equiv.Perm (Fin 5)) := by
  let : Fintype K := Fintype.ofFinite K
  let eK : ZMod 5 ≃+* K := ZMod.ringEquivOfPrime K (by decide)
    (by simpa only [Nat.card_eq_fintype_card] using hK)
  let eA : PSL2 K ≃* alternatingGroup (Fin 5) :=
    (psl2RingEquiv eK).symm.trans alternatingGroupFive_equiv_PSL2.some.symm
  have ho : IsOddPrimePower (Nat.card K) :=
    ⟨5, 1, by decide, by decide, le_rfl, by simpa using hK⟩
  have hc : 3 < Nat.card K := by omega
  let eS := Theory.SpecificGroups.Alternating.FiveExtensionAction.symmetricAutEquiv
  let f : PGL2 K →* Equiv.Perm (Fin 5) := eS.symm.toMonoidHom.comp
    ((MulAut.congr eA).toMonoidHom.comp (pgl2InnerAutPSL2 K ho hc))
  have hf : Function.Injective f := eS.symm.injective.comp
    ((MulAut.congr eA).injective.comp (pgl2InnerAutPSL2_injective K ho hc))
  have hcard : Nat.card (PGL2 K) = Nat.card (Equiv.Perm (Fin 5)) := by
    rw [pgl2_card_formula, hK, Nat.card_perm]
    norm_num [Nat.card_eq_fintype_card, Nat.factorial]
  exact ⟨MulEquiv.ofBijective f ((Nat.bijective_iff_injective_and_card f).mpr ⟨hf, hcard⟩)⟩

/-- Any actual five-point comparison marks the PSL2 layer automatically,
since A5 is the unique subgroup of index two in S5. -/
theorem pgl2_five_equiv_maps_psl (K : Type*) [Field K] [Finite K]
    (hK : Nat.card K = 5) (e : PGL2 K ≃* Equiv.Perm (Fin 5)) :
    (ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := K)).range.map
      e.toMonoidHom = alternatingGroup (Fin 5) := by
  apply Equiv.Perm.eq_alternatingGroup_of_index_eq_two
  rw [Subgroup.index_map_of_bijective e.bijective]
  exact pgl2_psl2Range_index_eq_two K
    ⟨5, 1, by decide, by decide, le_rfl, by simpa using hK⟩

end Theory.PSL2
