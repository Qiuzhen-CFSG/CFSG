module

public import Stellmacher.Recognition.OddCoreComponentNormalizer
public import Theory.GroupTheory.ElementaryCommutingCoprime

/-!
# Solvable overgroups of an involution odd-core closure

If a solvable subgroup M contains both the elementary binary actor A and
its ambient odd-core closure R, then R lies in the ambient image of
O₂′(M). Each defining value is normal in its full element centralizer;
restricting that normality to C_M(a) and applying solvable centralizer
control puts the value in O₂′(M).

For a rank-three actor in an N₂ group, every A-invariant odd subgroup
normalizes R. Coprime fixed-point generation places such a subgroup in the
stabilizer of A's elementary commuting component, on which R is constant.

These are the solvable centralizer-control and component-stabilizer inputs
to the uniqueness argument in GLS2, Chapter F, §§19 and 21–22; the local
control theorem is Feit–Thompson background Proposition 1.15(b), and the
component argument uses GLS2 Lemma 22.2 and Proposition 21.8.
-/

namespace Stellmacher.Recognition

universe u

/-- If an overgroup contains an actor and its entire ambient odd-core closure,
solvability of the overgroup puts that closure in its own odd core. -/
public theorem oddCoreClosure_le_oddCore_of_solvable_overgroup
    {G : Type u} [Group G] [Finite G]
    (A M : Subgroup G) [IsElementaryAbelian 2 A]
    (hM : Group.IsSolvable M) (hAM : A ≤ M)
    (hRM : involutionOddCoreClosure A ≤ M) :
    involutionOddCoreClosure A ≤ (pPrimeCore 2 M).map M.subtype := by
  refine iSup₂_le fun a ha => ?_
  let C := Subgroup.centralizer ({(a : G)} : Set G)
  let aM : M := ⟨a, hAM a.property⟩
  let Q := Subgroup.zpowers aM
  let D := Subgroup.centralizer (Q : Set M)
  have horder : orderOf aM = 2 := by
    have ho : orderOf (a : G) = 2 := by
      rw [Subgroup.orderOf_coe]
      exact orderOf_eq_prime_iff.mpr ⟨Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
        (IsElementaryAbelian.exponent_dvd_p 2 A) a, ha⟩
    exact (Subgroup.orderOf_coe aM).symm.trans ho
  have hQ : IsPGroup 2 Q := IsPGroup.of_card (n := 1) (by
    simpa only [Q, Nat.card_zpowers, pow_one] using horder)
  have hDmem (d : M) : d ∈ D ↔ d * aM = aM * d := by
    change d ∈ Subgroup.centralizer (Subgroup.zpowers aM : Set M) ↔ _
    rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure,
      Subgroup.mem_centralizer_singleton_iff]
  let f : D →* C :=
    { toFun := fun d => ⟨d.val.val, Subgroup.mem_centralizer_singleton_iff.mpr
        (congrArg (fun x : M => (x : G)) ((hDmem d.val).mp d.property))⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  have hf : Function.Injective f := by
    intro x y hxy
    exact Subtype.ext (Subtype.ext (congrArg (fun c : C => (c : G)) hxy))
  let K := (pPrimeCore 2 C).comap f
  have hK : K ≤ pPrimeCore 2 D := le_sSup ⟨inferInstance,
    (pPrimeCore_coprime_card (p := 2) (G := C)).of_dvd_right
      (Subgroup.card_comap_dvd_of_injective _ f hf)⟩
  have hcontrol := pPrimeCore_map_centralizer_le_pPrimeCore_of_solvable hM 2 Q hQ
  have hcoreR : involutionOddCore (a : G) ≤ involutionOddCoreClosure A :=
    le_iSup_of_le a (le_iSup_of_le ha le_rfl)
  have hcoreM : involutionOddCore (a : G) ≤ M := hcoreR.trans hRM
  rintro x ⟨c, hc, rfl⟩
  have hcM : (c : G) ∈ M := hcoreM ⟨c, hc, rfl⟩
  let cM : M := ⟨c, hcM⟩
  have hcD : cM ∈ D := (hDmem cM).mpr (Subtype.ext
    (Subgroup.mem_centralizer_singleton_iff.mp c.property))
  have hcK : (⟨cM, hcD⟩ : D) ∈ K := hc
  exact ⟨cM, hcontrol ⟨⟨cM, hcD⟩, hK hcK, rfl⟩, rfl⟩

/-- Every odd subgroup normalized by the actor normalizes its closure. -/
public theorem odd_le_normalizer_oddCoreClosure_of_normalized
    {G : Type u} [Group G] [Finite G] (hN : IsNTwoGroup G)
    (A K : Subgroup G) [IsElementaryAbelian 2 A]
    (hA : 8 ≤ Nat.card A) (hK : Odd (Nat.card K))
    (hAK : A ≤ Subgroup.normalizer (K : Set G)) :
    K ≤ Subgroup.normalizer (involutionOddCoreClosure A : Set G) := by
  intro g hg
  apply Subgroup.mem_normalizer_iff_map_conj_eq.mpr
  change (involutionOddCoreClosure A).map (MulAut.conj g).toMonoidHom = _
  rw [involutionOddCoreClosure_map]
  exact (oddCoreClosure_eq_of_connected hN
    (Subgroup.elementaryCommutingConnected_conj_of_mem_normalized_odd
      A K hA hK hAK hg)).symm


end Stellmacher.Recognition

