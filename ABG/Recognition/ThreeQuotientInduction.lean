module

public import ABG.Recognition.ThreeQuotientCharacters
public import ABG.Recognition.ThreeCharacterDecomposition
public import Theory.Character.Inflation
public import Theory.GroupTheory.OddKernelCyclicRoots

/-!
# Wong's induced characters above an odd local core

For an involution whose centralizer modulo its odd core is GL₂(3), inflate
Wong's five supported generalized characters and induce them to the ambient
group. Oddness of the kernel preserves cyclic roots and ensures that the
involution maps to the central involution of GL₂(3). Inflation and root
induction preserve scalar products, so Wong's Gram matrix produces seven
actual distinct nontrivial irreducibles with the signs and five identities.

Source: W. J. Wong, On finite groups whose 2-Sylow subgroups have cyclic
subgroups of index 2 (1964), Table 1, equation (3), and Appendix, as in
`ThreeCharacterTable` and `ThreeCharacterDecomposition`.
-/

namespace ABG
open Matrix Matrix.GeneralLinearGroup BenderGlauberman
noncomputable section
attribute [local instance] Fintype.ofFinite
attribute [local instance] Classical.propDecidable

variable {G : Type*} [Group G] [Finite G] (t : G)
local notation "C" => Subgroup.centralizer (Set.singleton t)

private theorem quotient_root_iff (ht : orderOf t = 2) (a : C) :
    QuotientGroup.mk' (pPrimeCore 2 C)
        ⟨t, Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩ ∈
      Subgroup.zpowers (QuotientGroup.mk' (pPrimeCore 2 C) a) ↔
        t ∈ Subgroup.zpowers (a : G) := by
  let z : C := ⟨t, Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩
  have hz : z ^ 2 = 1 := Subtype.ext (ht ▸ pow_orderOf_eq_one t)
  have hza : Commute z a := by
    apply Subtype.ext
    exact (Subgroup.mem_centralizer_singleton_iff.mp a.property).symm
  rw [QuotientGroup.involution_mem_zpowers_iff _
    (Nat.coprime_two_left.mp pPrimeCore_coprime_card) z a hz hza]
  constructor
  · rintro ⟨n, hn⟩
    exact ⟨n, congrArg Subtype.val hn⟩
  · rintro ⟨n, hn⟩
    exact ⟨n, Subtype.ext hn⟩

/-- The quotient image of the distinguished involution is the central
involution in the concrete GL₂(3) table. -/
public theorem threeOddCoreQuotientMap_involution (ht : orderOf t = 2)
    (e : (C ⧸ pPrimeCore 2 C) ≃* GL2 3 1) :
    threeOddCoreQuotientMap e
      ⟨t, Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩ = threeCentral := by
  let z : C := ⟨t, Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩
  let f := threeOddCoreQuotientMap e
  have hz : z ^ 2 = 1 := Subtype.ext (ht ▸ pow_orderOf_eq_one t)
  have hn : f z ≠ 1 := by
    intro h
    have hq : QuotientGroup.mk' (pPrimeCore 2 C) z = 1 :=
      (e.trans glTwoThreeFieldEquiv).injective (h.trans (map_one _).symm)
    have hr := (quotient_root_iff t ht (1 : C)).mp (by
      change QuotientGroup.mk' (pPrimeCore 2 C) z ∈
        Subgroup.zpowers (QuotientGroup.mk' (pPrimeCore 2 C) 1)
      rw [hq, map_one]
      exact Subgroup.one_mem _)
    have ht1 : t = 1 := by simpa using hr
    rw [ht1, orderOf_one] at ht
    norm_num at ht
  have ho : orderOf (f z) = 2 :=
    orderOf_eq_prime (by rw [← map_pow, hz, map_one]) hn
  have hc (g : GL (Fin 2) (ZMod 3)) : g * f z = f z * g := by
    obtain ⟨a, rfl⟩ := threeOddCoreQuotientMap_surjective e g
    rw [← map_mul, ← map_mul]
    apply congrArg f
    apply Subtype.ext
    exact Subgroup.mem_centralizer_singleton_iff.mp a.property
  obtain ⟨i, hi, _⟩ := three_conjugacy_data.1 (f z)
  obtain ⟨g, hg⟩ := isConj_iff.mp hi
  have he : f z = threeClassRepr i := by
    simpa only [hc g, mul_assoc, mul_inv_cancel, mul_one] using hg
  rw [he, three_conjugacy_data.2.1] at ho
  have hnc : threeUnipotent * threeReflection ≠ threeReflection * threeUnipotent := by
    decide +kernel
  fin_cases i <;> norm_num at ho
  · exact he
  · exact (hnc (by simpa [he, threeClassRepr] using hc threeUnipotent)).elim

/-- Inflation through the odd core preserves exactly the cyclic-root support. -/
public theorem threeOddCoreQuotientMap_root_iff (ht : orderOf t = 2)
    (e : (C ⧸ pPrimeCore 2 C) ≃* GL2 3 1) (a : C) :
    threeOddCoreQuotientMap e a ∈ glTwoThreeRootSupport ↔
      t ∈ Subgroup.zpowers (a : G) := by
  change threeCentral ∈ Subgroup.zpowers (threeOddCoreQuotientMap e a) ↔ _
  rw [← threeOddCoreQuotientMap_involution t ht e, ← quotient_root_iff t ht a]
  constructor
  · rintro ⟨n, hn⟩
    refine ⟨n, (e.trans glTwoThreeFieldEquiv).injective ?_⟩
    exact (map_zpow (e.trans glTwoThreeFieldEquiv) _ n).trans hn
  · rintro ⟨n, hn⟩
    refine ⟨n, ?_⟩
    exact (map_zpow (e.trans glTwoThreeFieldEquiv) _ n).symm.trans
      (congrArg (e.trans glTwoThreeFieldEquiv) hn)

/-- Wong's five supported local functions inflated through the odd core. -/
@[expose] public def threeQuotientGenerator
    (e : (C ⧸ pPrimeCore 2 C) ≃* GL2 3 1) (k : Fin 5) : ClassFunction C :=
  fun a => glTwoThreeSupportedGenerator k (threeOddCoreQuotientMap e a)

omit [Finite G] in
public theorem threeQuotientGenerator_generalized
    (e : (C ⧸ pPrimeCore 2 C) ≃* GL2 3 1) (k : Fin 5) :
    IsGeneralizedCharacter (threeQuotientGenerator t e k) :=
  isGeneralizedCharacter_comp_hom (threeOddCoreQuotientMap e)
    (glTwoThreeSupportedGenerator_generalized k)

omit [Finite G] in
public theorem threeQuotientGenerator_class
    (e : (C ⧸ pPrimeCore 2 C) ≃* GL2 3 1) (k : Fin 5) :
    IsClassFunction (threeQuotientGenerator t e k) :=
  isClassFunction_of_isGeneralizedCharacter (threeQuotientGenerator_generalized t e k)

public theorem threeQuotientGenerator_supported (ht : orderOf t = 2)
    (e : (C ⧸ pPrimeCore 2 C) ≃* GL2 3 1) (k : Fin 5) (a : C)
    (ha : t ∉ Subgroup.zpowers (a : G)) : threeQuotientGenerator t e k a = 0 :=
  glTwoThreeSupportedGenerator_supported k _
    (fun h => ha ((threeOddCoreQuotientMap_root_iff t ht e a).mp h))

public theorem threeQuotientGenerator_gram
    (e : (C ⧸ pPrimeCore 2 C) ≃* GL2 3 1) (k l : Fin 5) :
    scalarProduct C (threeQuotientGenerator t e k) (threeQuotientGenerator t e l) =
      ![![3,1,0,-1,1], ![1,2,-1,0,1], ![0,-1,2,0,0],
        ![-1,0,0,3,1], ![1,1,0,1,3]] k l :=
  (scalarProduct_comp_surjective (threeOddCoreQuotientMap e)
    (threeOddCoreQuotientMap_surjective e)
    (glTwoThreeSupportedGenerator k) (glTwoThreeSupportedGenerator l)).trans
      (glTwoThreeSupportedGenerator_gram k l)

/-- The five ambient induced functions, without a core-free assumption. -/
@[expose] public def threeQuotientInducedGenerator
    (e : (C ⧸ pPrimeCore 2 C) ≃* GL2 3 1) (k : Fin 5) : ClassFunction G :=
  inducedClassFunction C (threeQuotientGenerator t e k)

public theorem threeQuotientInducedGenerator_generalized
    (e : (C ⧸ pPrimeCore 2 C) ≃* GL2 3 1) (k : Fin 5) :
    IsGeneralizedCharacter (threeQuotientInducedGenerator t e k) :=
  isGeneralizedCharacter_induced C (threeQuotientGenerator_generalized t e k)

public theorem threeQuotientInducedGenerator_gram (ht : orderOf t = 2)
    (e : (C ⧸ pPrimeCore 2 C) ≃* GL2 3 1) (k l : Fin 5) :
    scalarProduct G (threeQuotientInducedGenerator t e k)
      (threeQuotientInducedGenerator t e l) =
      ![![3,1,0,-1,1], ![1,2,-1,0,1], ![0,-1,2,0,0],
        ![-1,0,0,3,1], ![1,1,0,1,3]] k l :=
  (scalarProduct_inducedClassFunction_involutionRoots t ht
    _ _ (threeQuotientGenerator_class t e l)
    (threeQuotientGenerator_supported t ht e k)
    (threeQuotientGenerator_supported t ht e l)).trans
      (threeQuotientGenerator_gram t e k l)

public theorem threeQuotientInducedGenerator_apply_root (ht : orderOf t = 2)
    (e : (C ⧸ pPrimeCore 2 C) ≃* GL2 3 1) (k : Fin 5) (a : C)
    (ha : t ∈ Subgroup.zpowers (a : G)) :
    threeQuotientInducedGenerator t e k a = threeQuotientGenerator t e k a :=
  inducedClassFunction_involutionRoots_apply t ht _ (threeQuotientGenerator_class t e k)
    (threeQuotientGenerator_supported t ht e k) a ha

/-- Away from conjugates of cyclic roots, the induced functions vanish. -/
public theorem threeQuotientInducedGenerator_eq_zero (ht : orderOf t = 2)
    (e : (C ⧸ pPrimeCore 2 C) ≃* GL2 3 1) (k : Fin 5) (a : G)
    (ha : ∀ g : G, t ∉ Subgroup.zpowers (g⁻¹ * a * g)) :
    threeQuotientInducedGenerator t e k a = 0 :=
  inducedClassFunction_involutionRoots_eq_zero t _
    (threeQuotientGenerator_supported t ht e k) a ha

public theorem threeQuotientInducedGenerator_one (ht : orderOf t = 2)
    (e : (C ⧸ pPrimeCore 2 C) ≃* GL2 3 1) (k : Fin 5) :
    threeQuotientInducedGenerator t e k 1 = 0 := by
  apply threeQuotientInducedGenerator_eq_zero t ht e k
  intro g
  simp only [mul_one, inv_mul_cancel, Subgroup.zpowers_one_eq_bot, Subgroup.mem_bot]
  intro h
  rw [h, orderOf_one] at ht
  norm_num at ht

public theorem threeQuotientInducedGenerator_trivial_coefficient
    (e : (C ⧸ pPrimeCore 2 C) ≃* GL2 3 1) (k : Fin 5) :
    scalarProduct G (threeQuotientInducedGenerator t e k) 1 =
      if k = 0 then 1 else 0 := by
  rw [threeQuotientInducedGenerator, scalarProduct_inducedClassFunction C _
    (irreducibleCharacter_isClassFunction isLinearCharacter_one.1)]
  change scalarProduct C
    (fun a => glTwoThreeSupportedGenerator k (threeOddCoreQuotientMap e a))
    (fun a => (1 : ClassFunction (GL (Fin 2) (ZMod 3)))
      (threeOddCoreQuotientMap e a)) = _
  rw [scalarProduct_comp_surjective (threeOddCoreQuotientMap e)
    (threeOddCoreQuotientMap_surjective e) (glTwoThreeSupportedGenerator k) 1]
  change scalarProduct _ (glTwoThreeSupportedGenerator k) (glTwoThreeCharacter 0) = _
  fin_cases k <;>
    simp [glTwoThreeSupportedGenerator, scalarProduct_add_left, _root_.scalarProduct_sub_left,
      glTwoThreeCharacter_orthonormal]

/-- The shared seven-character catalog, including four signs and all five
induction identities, above a possibly nontrivial local odd core. -/
public theorem exists_threeQuotientCharacterDecomposition (ht : orderOf t = 2)
    (e : (C ⧸ pPrimeCore 2 C) ≃* GL2 3 1) :
    Nonempty (ThreeCharacterDecomposition (threeQuotientInducedGenerator t e)) :=
  exists_threeCharacterDecomposition _
    (threeQuotientInducedGenerator_generalized t e)
    (threeQuotientInducedGenerator_one t ht e)
    (threeQuotientInducedGenerator_trivial_coefficient t e)
    (threeQuotientInducedGenerator_gram t ht e)

end
end ABG
