module

public import Theory.AlgebraicGroup.Bor1.SeparatingBorel.AvoidWeights
public import Theory.AlgebraicGroup.Tori.RegularCentralizer

/-!
# Choosing a semiregular cocharacter before orienting characters

Finite avoidance chooses a cocharacter and a point whose values distinguish
all weights of a faithful representation. The regular-centralizer theorem then
identifies the centralizer of its full one-parameter image with that of the
torus. This requires no prior choice of oriented rank-one characters.

Source: Borel, *Linear Algebraic Groups*, IV, 13.2--13.3 and 13.11.
-/

public section
namespace Theory.AlgebraicGroup.Bor1.SeparatingBorel
open scoped BigOperators
variable {k : Type*} [Field k] [IsAlgClosed k]
variable {G : Variety k} [AlgebraicGroup G]

private theorem cocharacter_avoiding_point (T : ClosedSubgroup G)
    (c : ClosedSubgroupTorusCocharacter T) (s : Finset (TorusWeight T))
    (hc : ∀ χ ∈ s, characterCocharacterPairing T c (Additive.ofMul χ) ≠ 0) :
    ∃ t : Variety.Point (KMult k),
      ∀ χ ∈ s, χ.pointCharacter (c.onPoints t) ≠ 1 := by
  let m (χ : TorusWeight T) := characterCocharacterPairing T c (Additive.ofMul χ)
  let N : ℤ := ∏ χ ∈ s, m χ
  have hN : N ≠ 0 := Finset.prod_ne_zero_iff.mpr hc
  obtain ⟨a, ha⟩ := exists_unit_zpow_ne_one (k := k) (z := N) hN
  let t : Variety.Point (KMult k) := (dPointEquiv 1).symm (fun _ => a)
  refine ⟨t, ?_⟩
  intro χ hχ hbad
  have he := characterCocharacterPairing_spec T χ c t
  change χ.pointCharacter (c.onPoints t) = (dPointEquiv 1 t 0 : k) ^ m χ at he
  have he' : (dPointEquiv 1 t 0 : k) = (a : k) := by
    exact congrArg (fun z : Fin 1 → kˣ => (z 0 : k)) ((dPointEquiv 1).apply_symm_apply _)
  rw [he', hbad] at he
  have hd : m χ ∣ N := Finset.dvd_prod_of_mem m hχ
  obtain ⟨z, hz⟩ := hd
  apply ha
  have hu : a ^ m χ = 1 := Units.ext (by
    simpa only [Units.val_zpow_eq_zpow_val, Units.val_one] using he.symm)
  rw [hz, zpow_mul, hu, one_zpow]

omit [IsAlgClosed k] in
private theorem pointCharacter_ratio_eq_one (T : ClosedSubgroup G)
    (χ ψ : TorusWeight T) (x : Variety.Point T.carrierVariety)
    (he : χ.pointCharacter x = ψ.pointCharacter x) :
    (χ * ψ⁻¹).pointCharacter x = 1 := by
  let f := torusPointEval T.carrierVariety x
  have hf : f χ = f ψ := Units.ext he
  change (f (χ * ψ⁻¹) : k) = 1
  rw [map_mul, map_inv, hf, mul_inv_cancel]
  rfl

variable {V : Type*} [AddCommGroup V] [Module k V] [FiniteDimensional k V]

theorem exists_cocharacter_with_regular_point
    (ρ : RationalRepresentation G V) (T : ClosedSubgroup G) (hT : IsSubtorus T)
    :
    ∃ c : ClosedSubgroupTorusCocharacter T,
      ∃ t : Variety.Point (KMult k),
        ∀ χ ψ : TorusWeight T,
          χ ∈ representationWeights ρ T → ψ ∈ representationWeights ρ T →
          χ ≠ ψ → χ.pointCharacter (c.onPoints t) ≠ ψ.pointCharacter (c.onPoints t) := by
  classical
  let W := (representationWeights_finite ρ T).toFinset
  let P := (W.product W).filter (fun p => p.1 ≠ p.2)
  let s := P.image (fun p => p.1 * p.2⁻¹)
  have hs : ∀ χ ∈ s, χ ≠ 1 := by
    intro χ hχ
    obtain ⟨⟨a, b⟩, hab, rfl⟩ := Finset.mem_image.mp hχ
    exact fun he => (Finset.mem_filter.mp hab).2 (mul_inv_eq_one.mp he)
  obtain ⟨c, hc⟩ := exists_cocharacter_avoiding_weights T hT s hs
  obtain ⟨t, ht⟩ := cocharacter_avoiding_point T c s hc
  refine ⟨c, t, ?_⟩
  intro χ ψ hχ hψ hne he
  have hm : χ * ψ⁻¹ ∈ s := by
    apply Finset.mem_image.mpr
    refine ⟨(χ, ψ), Finset.mem_filter.mpr ⟨?_, hne⟩, rfl⟩
    exact Finset.mem_product.mpr
      ⟨(representationWeights_finite ρ T).mem_toFinset.mpr hχ,
        (representationWeights_finite ρ T).mem_toFinset.mpr hψ⟩
  exact ht _ hm (pointCharacter_ratio_eq_one T χ ψ _ he)

theorem exists_semiregular_cocharacter
    (T : ClosedSubgroup G) (hT : IsSubtorus T) :
    ∃ c : ClosedSubgroupTorusCocharacter T,
      (T.inclusion.comp c).imageClosedSubgroup.centralizer = T.centralizer := by
  let ρ := coordinateTranslationRationalRepresentation G
  let V := coordinateTranslationSubmodule G
  let : Module.Finite k V := coordinateTranslationSubmodule_finite G
  have hTop : (⨆ χ : TorusWeight T, weightSpace ρ T χ) = ⊤ :=
    closedSubtorusRepresentation_weightSpace_iSup_eq_top ρ
      (coordinateTranslationRationalRepresentation_isRational G) T hT
  obtain ⟨c, t, hsep⟩ :=
    exists_cocharacter_with_regular_point ρ T hT
  have he : semisimpleCommutatorPointCentralizer (T.includePoint (c.onPoints t)) =
      T.centralizer := regularTorus_centralizer_eq ρ
        (coordinateTranslationRepresentation_injective G) T hTop _ hsep
  refine ⟨c, SetLike.coe_injective ?_⟩
  ext x
  constructor
  · intro hx
    rw [← he]
    change x ∈ Subgroup.centralizer ({T.includePoint (c.onPoints t)} : Set (Variety.Point G))
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    rcases Set.mem_singleton_iff.mp hy with rfl
    exact (Subgroup.mem_centralizer_iff.mp hx) _ ⟨t, rfl⟩
  · intro hx
    change x ∈ Subgroup.centralizer
      ((T.inclusion.comp c).imageClosedSubgroup.toSubgroup : Set (Variety.Point G))
    rw [Subgroup.mem_centralizer_iff]
    rintro y ⟨t, rfl⟩
    exact (Subgroup.mem_centralizer_iff.mp hx) _ (T.pointEquiv (c.onPoints t)).property

end Theory.AlgebraicGroup.Bor1.SeparatingBorel
