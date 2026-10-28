module
public import Theory.SpecificGroups.SymmetricSix.Parabolics.Actions
public import Theory.SpecificGroups.SymmetricSix.BinaryFlags.NaturalGeometry

/-!
# Six-letter polar coordinates and the binary natural module

The four polar basis vectors correspond to the duad classes 35, 02, 45 and
01 in the even-weight permutation module modulo constants. Their linear map
carries every polar duad vector to the class of that same duad. Nonzero duad
classes prove injectivity, and the equal dimensions give an equivalence.
The established duad actions then prove equivariance for every permutation.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, §B.3
and I.5.4–9. This identifies the polar model with the literal quotient model
used in the definition of an alternating block.
-/

namespace Theory.SpecificGroups.SymmetricSix
namespace PolarNatural
open BinaryPermutation
open BinaryFlags.NaturalGeometry (pairVector pairVector_ne_zero pairVector_map pairVector_eq_iff)
private def pairs : Duad → Letter × Letter :=
  ![(0,1),(0,2),(0,3),(0,4),(0,5),(1,2),(1,3),(1,4),(1,5),
    (2,3),(2,4),(2,5),(3,4),(3,5),(4,5)]
private theorem pairs_ne (d : Duad) : (pairs d).1 ≠ (pairs d).2 := by
  fin_cases d <;> decide
private theorem pairs_set (d : Duad) : duadSet d = pair (pairs d).1 (pairs d).2 := by
  fin_cases d <;> rfl
private def pairFull (i j : Letter) : Full Letter := Pi.single i 1 + Pi.single j 1
private def fullMap (v : NaturalModule) : Full Letter :=
  v (.inl 0) • pairFull 3 5 + v (.inl 1) • pairFull 0 2 +
    v (.inr 0) • pairFull 4 5 + v (.inr 1) • pairFull 0 1
private theorem fullMap_polar : ∀ d : Duad,
    fullMap (polarVector d).val - pairFull (pairs d).1 (pairs d).2 =
      (fullMap (polarVector d).val 5 - pairFull (pairs d).1 (pairs d).2 5) • allOne Letter := by
  decide +kernel

private def toNatural : NaturalModule →ₗ[ZMod 2] natural Letter where
  toFun v := v (.inl 0) • pairVector 3 5 + v (.inl 1) • pairVector 0 2 +
    v (.inr 0) • pairVector 4 5 + v (.inr 1) • pairVector 0 1
  map_add' v w := by simp only [Pi.add_apply,add_smul]; abel
  map_smul' c v := by simp only [Pi.smul_apply,smul_add,smul_smul,RingHom.id_apply,smul_eq_mul]

private theorem toNatural_polar (d : Duad) :
    toNatural (polarVector d).val = pairVector (pairs d).1 (pairs d).2 := by
  apply Subtype.ext
  change (constants Letter).mkQ (fullMap (polarVector d).val) =
    (constants Letter).mkQ (pairFull (pairs d).1 (pairs d).2)
  apply (Submodule.Quotient.eq _).mpr
  rw [fullMap_polar]
  exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_singleton _))

private theorem toNatural_injective : Function.Injective toNatural := by
  apply LinearMap.ker_eq_bot.mp
  apply le_bot_iff.mp
  intro v hv
  change toNatural v = 0 at hv
  change v = 0
  by_contra hne
  obtain ⟨d,hd⟩ := polarVector_bijective.2 ⟨v,hne⟩
  have hd' : (polarVector d).val = v := congrArg Subtype.val hd
  rw [← hd',toNatural_polar] at hv
  exact pairVector_ne_zero (pairs_ne d) hv

public noncomputable def equiv : NaturalModule ≃ₗ[ZMod 2] natural Letter :=
  LinearEquiv.ofBijective toNatural ⟨toNatural_injective,
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (by
      rw [naturalModule_finrank,finrank_natural_even Letter (by decide)]
      rfl)).mp toNatural_injective⟩

public theorem equiv_action (g : S6) (v : NaturalModule) :
    equiv (polarAction g v) = naturalRepresentation Letter g (equiv v) := by
  by_cases hv : v=0
  · subst v
    simp only [polarAction_zero,map_zero]
  obtain ⟨d,hd⟩ := polarVector_bijective.2 ⟨v,hv⟩
  have hd' : (polarVector d).val = v := congrArg Subtype.val hd
  rw [← hd',polarAction_vector]
  change toNatural (polarVector (g • d)).val = naturalRepresentation Letter g (toNatural (polarVector d).val)
  rw [toNatural_polar,toNatural_polar,pairVector_map]
  apply (pairVector_eq_iff (pairs_ne (g • d)) (g.injective.ne (pairs_ne d))).mpr
  rw [← pairs_set,duadSet_smul,pairs_set]
  simp [pair]
end PolarNatural
end Theory.SpecificGroups.SymmetricSix
