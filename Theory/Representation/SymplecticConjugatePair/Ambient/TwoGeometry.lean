module

public import Theory.Representation.SymplecticConjugatePair.Ambient.TwoGeometry.Operators
public import Theory.Representation.SymplecticConjugatePair.Ambient.TwoGeometry.StandardCoefficients

/-!
# Two-subgroup transports for the standard symplectic enlargement

The full paired symplectic image embeds in the actual generated binary operator
group. Pulling a subgroup back through this embedding preserves its rank,
elementary-abelian property and fixed space. Thus native full-group estimates
apply to every subgroup of that image, including over the two-element field.
The genuine derived image is not identified with this full image.

The swapping offender reduction uses the proved summand-permutation theorem
and retains the centralizer rank estimate as an explicit pending calculation.
These are reductions toward Aschbacher–Smith H.7, printed pp.388–389 of
`refs/quasithin.pdf`, not the unproved ambient rank bounds themselves.
-/

@[expose] public section

open Representation BinaryOffender Theory.SpecificGroups.SymplecticFour
open SymplecticConjugatePair
namespace SymplecticConjugatePair.Ambient
lemma elementary_preimage {G D : Type*} [Group G] [Group D]
    (f : G →* D) (hf : Function.Injective f) {A : Subgroup D}
    (hA : IsElementaryTwo A) (hAL : A ≤ f.range) :
    IsElementaryTwo (A.comap f) := by
  have hmap : (A.comap f).map f = A := Subgroup.map_comap_eq_self hAL
  let _ : IsElementaryAbelian 2 A := hA.2
  refine ⟨?_, ?_⟩
  · intro h
    apply hA.1
    rw [← hmap, h, Subgroup.map_bot]
  · refine { toIsMulCommutative := A.comap_injective_isMulCommutative hf
             exponent_dvd_p := ?_ }
    apply Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr
    intro x
    apply Subtype.ext
    apply hf
    change f ((x : G)^2) = f 1
    rw [map_pow, map_one]
    exact elemPow_eq_one_of_isElementaryAbelian (f x.val) x.property

variable {F : Type*} [Field F] [Algebra (ZMod 2) F] [Finite F] [CharP F 2]

lemma standardAction_comp_fullHom :
    (standardAction (F := F)).comp fullHom = graphPair := rfl

lemma full_fixedSpace (B : Subgroup (Sp F)) :
    fixedSpace standardAction (B.map fullHom) = fixedSpace (graphPair (F := F)) B := by
  rw [← fixedSpace_comp_map, standardAction_comp_fullHom]

lemma full_fixedCodim (B : Subgroup (Sp F)) :
    fixedCodim standardAction (B.map fullHom) = fixedCodim (graphPair (F := F)) B := by
  unfold fixedCodim
  rw [full_fixedSpace]

lemma full_preimage_elementary {A : Subgroup (standardAmbient (F := F))}
    (hA : IsElementaryTwo A) (hAL : A ≤ fullHom.range) :
    IsElementaryTwo (A.comap fullHom) :=
  elementary_preimage fullHom fullHom_injective hA hAL

lemma full_preimage_rank {A : Subgroup (standardAmbient (F := F))}
    (hAL : A ≤ fullHom.range) : rank (A.comap fullHom) = rank A := by
  have h := rank_map_injective fullHom fullHom_injective (A.comap fullHom)
  rw [Subgroup.map_comap_eq_self hAL] at h
  exact h.symm

lemma full_involution_bound {n : ℕ}
    (hi : ∀ x : Sp F, orderOf x = 2 → 3*n ≤ fixedCodim graphPair (Subgroup.zpowers x))
    (s : standardAmbient (F := F)) (hs : s ∈ fullHom.range) (ho : orderOf s = 2) :
    3*n ≤ fixedCodim standardAction (Subgroup.zpowers s) := by
  obtain ⟨x, rfl⟩ := hs
  rw [← MonoidHom.map_zpowers, full_fixedCodim]
  apply hi
  rwa [← orderOf_injective fullHom fullHom_injective x]

lemma full_not_offender
    (hi : ∀ B : Subgroup (Sp F), IsElementaryTwo B → rank B + 1 < fixedCodim graphPair B)
    {A : Subgroup (standardAmbient (F := F))} (hA : IsElementaryTwo A)
    (hAL : A ≤ fullHom.range) : rank A + 1 < fixedCodim standardAction A := by
  have h := hi (A.comap fullHom) (full_preimage_elementary hA hAL)
  rw [full_preimage_rank hAL, ← full_fixedCodim, Subgroup.map_comap_eq_self hAL] at h
  exact h

lemma standard_offender_le_stabilizer {n : ℕ} (hF : Nat.card F = 2^n) (hn : 0 < n)
    (hc : ∀ s : standardAmbient (F := F), orderOf s = 2 → SwapsSummands standardAction s →
      primeRank 2 (Subgroup.centralizer ({s} : Set (standardAmbient (F := F)))) ≤ n+1)
    {A : Subgroup (standardAmbient (F := F))} (hA : IsElementaryTwo A)
    (hoff : fixedCodim standardAction A ≤ rank A + 1) :
    A ≤ summandStabilizer standardAction := by
  by_contra hAN
  obtain ⟨s, hsA, hsN⟩ := SetLike.not_le_iff_exists.mp hAN
  have hswap := swaps_of_not_mem_stabilizer standardAction standardAction_permutesSummands hsN
  have hne : s ≠ 1 := fun he => hsN (he ▸ (summandStabilizer standardAction).one_mem)
  let _ : IsElementaryAbelian 2 A := hA.2
  have hs : orderOf s = 2 := orderOf_eq_prime
    (elemPow_eq_one_of_isElementaryAbelian s hsA) hne
  exact (not_offender_of_swapping standardAction hF hn hA hsA hswap (hc s hs hswap)).not_ge hoff

lemma standard_outer_involution_calculation_of_kernel
    (hker : ∀ g : standardPreserving (F := F), g^2 = 1 → standardCoefficient g = 1 → g.val ∈ fullHom.range)
    {n : ℕ} (hF : Nat.card F = 2^n)
    (s : standardAmbient (F := F)) (hs : s^2 = 1) (hout : s ∉ fullHom.range) :
    fixedSpace standardAction (Subgroup.zpowers s) =
        LinearMap.range (standardAction s - LinearMap.id) ∧
      fixedCodim standardAction (Subgroup.zpowers s) = 4*n := by
  by_cases hN : s ∈ standardPreserving
  · let t : standardPreserving (F := F) := ⟨s, hN⟩
    have ht : t^2 = 1 := Subtype.ext hs
    have hσ := SemilinearCoefficients.coefficient_involutive standardCoefficient ht
    have hne : standardCoefficient t ≠ RingEquiv.refl F := fun he => hout (hker t ht he)
    exact ⟨semilinear_involution_fixedSpace standardAction s hs (standardCoefficient t) hσ hne (standardCoefficient_smul t),
      semilinear_pair_involution_codim standardAction hF s hs (standardCoefficient t) hσ hne (standardCoefficient_smul t)⟩
  · have hswap := swaps_of_not_mem_stabilizer standardAction standardAction_permutesSummands hN
    exact ⟨swapping_fixedSpace standardAction s hs hswap,
      swapping_codim standardAction hF s hs hswap⟩

lemma standard_involution_bound_of_kernel
    (hker : ∀ g : standardPreserving (F := F), g^2 = 1 → standardCoefficient g = 1 → g.val ∈ fullHom.range)
    {n : ℕ} (hF : Nat.card F = 2^n)
    (hnative : ∀ x : Sp F, orderOf x = 2 → 3*n ≤ fixedCodim graphPair (Subgroup.zpowers x))
    (s : standardAmbient (F := F)) (hs : orderOf s = 2) :
    3*n ≤ fixedCodim standardAction (Subgroup.zpowers s) := by
  by_cases hinner : s ∈ fullHom.range
  · exact full_involution_bound hnative s hinner hs
  · have hs2 : s^2 = 1 := by simpa only [hs] using pow_orderOf_eq_one s
    rw [(standard_outer_involution_calculation_of_kernel hker hF s hs2 hinner).2]
    omega

end SymplecticConjugatePair.Ambient
