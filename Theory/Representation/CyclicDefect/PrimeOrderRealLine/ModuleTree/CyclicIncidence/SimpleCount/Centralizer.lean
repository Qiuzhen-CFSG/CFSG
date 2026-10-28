module

public import Theory.Representation.CyclicDefect.PrimeOrderRealLine.ModuleTree.CyclicIncidence.SimpleCount.Classes
public import Theory.Representation.CyclicDefect.PrimeOrderRealLine.ModuleTree.CyclicIncidence.SimpleCount.LocalBlock
public import Theory.Representation.TwoDimensionalOddOrder
public import Theory.Representation.Quotient

/-!
# The unique simple module in the Sylow-centralizer block

A primitive central idempotent with augmentation one acts inside the averaging
idempotent of every normal subgroup of order prime to the characteristic.
Thus any representation selected by this block kills the normal subgroup.
When the quotient is a p-group, a nonzero fixed vector and irreducibility
identify each selected simple with the one-dimensional trivial module.

A cyclic Sylow subgroup lies in the center of its centralizer. Burnside
transfer supplies a normal prime complement there, so the result applies to
the literal local Brauer image in `PrimeOrderInput`. The trivial module itself
is selected because the image has augmentation one. This gives a complete
singleton family and the class count one.

Source: Feit, *The Representation Theory of Finite Groups*, V.4.6, VII.1.2,
and the standing hypothesis of VII.3 (printed p.281). For a defect group of
prime order there is just this one centralizer. The fixed-vector intertwiner
argument also appears for two-groups in `ModularBlock.PGroupCartan`.
-/

public section
open scoped BigOperators Classical
open ModularBlock
noncomputable section
attribute [local instance] Fintype.ofFinite
namespace Representation.CyclicDefect.PrimeOrderRealLine.ModuleTree.CyclicIncidence.SimpleCount
variable {K G : Type*} [Field K] [Group G] [Finite G]

private def normalAverage (N : Subgroup G) : MonoidAlgebra K G :=
  (Nat.card N : K)⁻¹ • ∑ x : N, MonoidAlgebra.single (x : G) 1

private theorem normalAverage_left (N : Subgroup G) (x : N) :
    MonoidAlgebra.single (x : G) (1 : K) * normalAverage N = normalAverage N := by
  classical
  simp only [normalAverage, Algebra.mul_smul_comm, Finset.mul_sum,
    MonoidAlgebra.single_mul_single, one_mul]
  congr 1
  exact (Equiv.sum_comp (Equiv.mulLeft x)
    (fun y : N => MonoidAlgebra.single (y : G) (1 : K)))

private theorem normalAverage_idempotent (N : Subgroup G)
    (hc : (Nat.card N : K) ≠ 0) : IsIdempotentElem (normalAverage (K := K) N) := by
  change normalAverage N * normalAverage N = normalAverage (K := K) N
  conv_lhs => lhs; unfold normalAverage
  rw [Algebra.smul_mul_assoc, Finset.sum_mul]
  simp only [normalAverage_left, Finset.sum_const, Finset.card_univ,
    ← Nat.cast_smul_eq_nsmul K, smul_smul, ← Nat.card_eq_fintype_card]
  rw [inv_mul_cancel₀ hc, one_smul]

private theorem normalAverage_center (N : Subgroup G) [N.Normal] :
    normalAverage (K := K) N ∈ Set.center (MonoidAlgebra K G) := by
  classical
  apply Semigroup.mem_center_iff.mpr
  intro a
  induction a using MonoidAlgebra.induction_linear with
  | zero => simp
  | add a b ha hb => simp [add_mul, mul_add, ha, hb]
  | single g c =>
    simp only [normalAverage, Algebra.mul_smul_comm, Algebra.smul_mul_assoc,
      Finset.mul_sum, Finset.sum_mul, MonoidAlgebra.single_mul_single, mul_one, one_mul]
    congr 1
    have h := Equiv.sum_comp (MulAut.conjNormal g : MulAut N).toEquiv
      (fun x : N => MonoidAlgebra.single ((x : G) * g) c)
    simpa only [MulEquiv.toEquiv_eq_coe, EquivLike.coe_coe,
      MulAut.conjNormal_apply, inv_mul_cancel_right] using h

private theorem normalAverage_augmentation (N : Subgroup G)
    (hc : (Nat.card N : K) ≠ 0) :
    groupAlgebraAugmentation K G (normalAverage N) = 1 := by
  rw [normalAverage, map_smul, map_sum]
  simp only [groupAlgebraAugmentation_single, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul, mul_one, smul_eq_mul, ← Nat.card_eq_fintype_card]
  exact inv_mul_cancel₀ hc

private theorem primitive_mul_normalAverage (N : Subgroup G) [N.Normal]
    (hc : (Nat.card N : K) ≠ 0) (e : MonoidAlgebra K G)
    (he : IsCentrallyPrimitive e) (haug : groupAlgebraAugmentation K G e = 1) :
    e * normalAverage N = e := by
  have hcmt : Commute e (normalAverage (K := K) N) :=
    (Semigroup.mem_center_iff.mp he.1 _).symm
  apply he.2.2.2 _ (Set.mul_mem_center he.1 (normalAverage_center N))
    (he.2.1.mul_of_commute hcmt (normalAverage_idempotent N hc))
  · rw [mul_assoc, ← hcmt.eq, ← mul_assoc, he.2.1.eq]
  · intro hz
    have hz' := congrArg (groupAlgebraAugmentation K G) hz
    rw [map_mul, haug, normalAverage_augmentation N hc, one_mul, map_zero] at hz'
    exact one_ne_zero hz'

/-- A normal subgroup of order prime to the characteristic acts trivially
on every representation selected by a primitive augmentation-one block. -/
theorem normalCoprime_le_ker_of_primitive_augmentation {p : ℕ} [Fact p.Prime] [CharP K p]
    {V : Type*} [AddCommGroup V] [Module K V]
    (e : MonoidAlgebra K G) (he : IsCentrallyPrimitive e)
    (haug : groupAlgebraAugmentation K G e = 1)
    (ρ : Representation K G V) (hin : ρ.asAlgebraHom e = 1)
    (N : Subgroup G) [N.Normal] (hN : Nat.Coprime p (Nat.card N)) : N ≤ ρ.ker := by
  have hc : (Nat.card N : K) ≠ 0 := by
    rw [Ne, CharP.cast_eq_zero_iff K p]
    exact (Nat.Prime.coprime_iff_not_dvd (Fact.out : p.Prime)).mp hN
  have ha : ρ.asAlgebraHom (normalAverage N) = 1 := by
    have h := congrArg ρ.asAlgebraHom (primitive_mul_normalAverage N hc e he haug)
    simpa only [map_mul, hin, one_mul] using h
  intro g hg
  have h := congrArg ρ.asAlgebraHom (normalAverage_left N ⟨g, hg⟩)
  change ρ g = 1
  simpa only [map_mul, Representation.asAlgebraHom_single_one, ha, mul_one] using h


/-- A normal prime complement leaves only the trivial simple module in
any primitive augmentation-one block. -/
theorem simple_equiv_trivial_of_normalComplement
    {p : ℕ} [Fact p.Prime] [CharP K p]
    {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (e : MonoidAlgebra K G) (he : IsCentrallyPrimitive e)
    (haug : groupAlgebraAugmentation K G e = 1)
    (ρ : Representation K G V) [Representation.IsIrreducible ρ]
    (hin : ρ.asAlgebraHom e = 1) (hcomp : HasNormalPComplement p G) :
    Nonempty (ρ.Equiv (Representation.trivial K G (Fin 1 → K))) := by
  obtain ⟨N, hnormal, hcoprime, hquot⟩ := hcomp
  let := hnormal
  have hker := normalCoprime_le_ker_of_primitive_augmentation e he haug ρ hin N hcoprime
  let σ := Representation.quotientOfLEKer ρ N hker
  let : Nontrivial V := Subrepresentation.irreducible_module_nontrivial ρ
  have hchar : ringChar K = p := ringChar.eq K p
  obtain ⟨v, hv, hfix⟩ := Representation.pGroup_fix_nonzero_vector
    (hchar ▸ (Fact.out : p.Prime).ne_zero) (hchar.symm ▸ hquot) σ
  have hfixed (g : G) : ρ g v = v := hfix (QuotientGroup.mk' N g)
  let f : Representation.IntertwiningMap (Representation.trivial K G (Fin 1 → K)) ρ :=
    { toLinearMap :=
        { toFun := fun x => x 0 • v
          map_add' := by intros; simp [add_smul]
          map_smul' := by intros; simp [smul_smul] }
      isIntertwining' := by
        intro g
        apply LinearMap.ext
        intro x
        change x 0 • v = ρ g (x 0 • v)
        rw [map_smul, hfixed] }
  have hf : f ≠ 0 := by
    intro h
    have hz := congrArg (fun q : Representation.IntertwiningMap
      (Representation.trivial K G (Fin 1 → K)) ρ => q (fun _ => 1)) h
    exact hv (by simpa [f] using hz)
  have hinj : Function.Injective f := by
    intro x y hxy
    have hh : x 0 = y 0 := (smul_left_injective K hv) hxy
    ext j
    have hj : j = 0 := Subsingleton.elim _ _
    simpa [hj] using hh
  have hsurj := (Representation.IsIrreducible.surjective_or_eq_zero f).resolve_right hf
  exact ⟨(f.ofBijective ⟨hinj, hsurj⟩).symm⟩

/-- The centralizer of an abelian Sylow subgroup has a normal prime complement. -/
theorem centralizer_normalComplement {p : ℕ} [Fact p.Prime]
    (P : Sylow p G) [IsCyclic P] :
    HasNormalPComplement p (Subgroup.centralizer (P : Set G)) := by
  let : CommGroup P := IsCyclic.commGroup
  let C := Subgroup.centralizer (P : Set G)
  have hPC : (P : Subgroup G) ≤ C := by
    intro x hx y hy
    exact congrArg Subtype.val (mul_comm (⟨y, hy⟩ : P) ⟨x, hx⟩)
  let S := P.subtype hPC
  have hSC : (S : Subgroup C) ≤ Subgroup.center C := by
    intro x hx
    apply Subgroup.mem_center_iff.mpr
    intro y
    apply Subtype.ext
    exact (y.property (x : G) hx).symm
  apply exists_normal_coprime_subgroup_and_pgroup_quotient_of_sylow_le_center_normalizer p S
  intro x hx
  refine ⟨S.le_normalizer hx, ?_⟩
  intro y _
  exact Subgroup.mem_center_iff.mp (hSC hx) y

open ModularBlock.PrimeBlockConstruction

/-- The unique simple module in the actual Sylow-centralizer principal block
is trivial. This discharges the standing hypothesis of Feit VII.3 for prime defect. -/
theorem centralizer_simple_equiv_trivial {p m : ℕ} [Fact p.Prime] [CharP K p]
    (d : PrimeCongruenceBlockData p G)
    (residue : Localization.AtPrime d.primeIdeal →+* K) (P : Sylow p G)
    (h : PrimeOrderInput d residue m P)
    (k : ℕ) (ρ : Representation K (Subgroup.centralizer (P : Set G)) (Fin k → K))
    (hirr : Representation.IsIrreducible ρ)
    (hin : ρ.asAlgebraHom (DefectSupport.subgroupCentralizerRestriction K
      (P : Subgroup G) (reducedPrincipal d residue)) = 1) :
    Nonempty (ρ.Equiv (Representation.trivial K _ (Fin 1 → K))) := by
  let := hirr
  let := h.cyclic
  apply simple_equiv_trivial_of_normalComplement _ h.local_primitive _ ρ hin
    (centralizer_normalComplement P)
  exact (SubgroupBrauerMap.augmentation_subgroupCentralizerRestriction
    (P : Subgroup G) P.isPGroup' _ (reducedPrincipal_mem_center d residue)).trans
      (reducedPrincipal_augmentation d residue)


private theorem trivial_irreducible (H : Type*) [Group H] :
    Representation.IsIrreducible (Representation.trivial K H (Fin 1 → K)) := by
  rw [Representation.irreducible_iff_isSimpleModule_asModule, isSimpleModule_iff]
  apply is_simple_module_of_finrank_eq_one (K := K)
  change Module.finrank K (Fin 1 → K) = 1
  simp

private theorem trivial_inBlock (H : Type*) [Group H]
    (e : MonoidAlgebra K H) (haug : groupAlgebraAugmentation K H e = 1) :
    (Representation.trivial K H (Fin 1 → K)).asAlgebraHom e = 1 := by
  have h (a : MonoidAlgebra K H) :
      (Representation.trivial K H (Fin 1 → K)).asAlgebraHom a =
        groupAlgebraAugmentation K H a • (1 : Module.End K (Fin 1 → K)) := by
    induction a using MonoidAlgebra.induction_on with
    | of g => simp [MonoidAlgebra.of_apply, Representation.asAlgebraHom_single,
        groupAlgebraAugmentation_single, Representation.trivial]
    | add a b ha hb => simp [map_add, ha, hb, add_smul]
    | smul c a ha => simp [map_smul, ha, smul_smul]
  rw [h, haug, one_smul]

/-- There is exactly one local centralizer simple class. -/
def centralizerSimpleClassEquiv {p m : ℕ} [Fact p.Prime] [CharP K p]
    (d : PrimeCongruenceBlockData p G)
    (residue : Localization.AtPrime d.primeIdeal →+* K) (P : Sylow p G)
    (h : PrimeOrderInput d residue m P) :
    Fin 1 ≃ SimpleClass (DefectSupport.subgroupCentralizerRestriction K
      (P : Subgroup G) (reducedPrincipal d residue)) := by
  apply simpleClassEquivOfFamily _ (fun _ => 1)
    (fun _ => Representation.trivial K _ (Fin 1 → K))
  · intro _
    exact trivial_irreducible _
  · intro _
    apply trivial_inBlock
    exact (SubgroupBrauerMap.augmentation_subgroupCentralizerRestriction
      (P : Subgroup G) P.isPGroup' _ (reducedPrincipal_mem_center d residue)).trans
        (reducedPrincipal_augmentation d residue)
  · intro i j hij
    exact (hij (Subsingleton.elim i j)).elim
  · intro k ρ hirr hin
    exact ⟨0, centralizer_simple_equiv_trivial d residue P h k ρ hirr hin⟩

/-- The local centralizer count, for the literal Brauer image in the source input. -/
theorem card_centralizerSimpleClass {p m : ℕ} [Fact p.Prime] [CharP K p]
    (d : PrimeCongruenceBlockData p G)
    (residue : Localization.AtPrime d.primeIdeal →+* K) (P : Sylow p G)
    (h : PrimeOrderInput d residue m P) :
    Nat.card (SimpleClass (DefectSupport.subgroupCentralizerRestriction K
      (P : Subgroup G) (reducedPrincipal d residue))) = 1 := by
  simpa only [Nat.card_fin] using
    Nat.card_congr (centralizerSimpleClassEquiv d residue P h).symm

end Representation.CyclicDefect.PrimeOrderRealLine.ModuleTree.CyclicIncidence.SimpleCount
