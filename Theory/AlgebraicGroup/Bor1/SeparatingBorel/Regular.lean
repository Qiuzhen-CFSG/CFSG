module

public import Theory.AlgebraicGroup.Bor1.SeparatingBorel.Subtori
public import Theory.AlgebraicGroup.Tori.RegularCentralizer

/-!
# Semiregular separating cocharacters

The cocharacter from the integral separation argument can avoid all differences
of weights in a faithful representation. Choose a point on its image at which
these finitely many nonzero powers are nontrivial. Its eigenspaces are exactly
the torus weight spaces, so its full centralizer equals the torus centralizer.
Consequently the cocharacter image has that same centralizer.

The final theorem applies this construction to the literal distinct
codimension-one subtori in Bor1 13.12. The characters trivial on those subtori
are supplied by the preceding geometric statement 13.11(3); this module proves
the complete lattice and semiregularity step and does not assume or assert a
separating Borel witness.

Source: Borel, *Linear Algebraic Groups*, Chapter IV, 13.2 and the proof of
13.12, `refs/KGroup/Bor1/Chapter4.tex`.
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

theorem exists_separating_cocharacter_with_regular_point
    (ρ : RationalRepresentation G V) (T : ClosedSubgroup G) (hT : IsSubtorus T)
    (α β : TorusWeight T)
    (hi : LinearIndependent ℤ ![Additive.ofMul α, Additive.ofMul β]) :
    ∃ c : ClosedSubgroupTorusCocharacter T,
      0 < characterCocharacterPairing T c (Additive.ofMul α) ∧
      characterCocharacterPairing T c (Additive.ofMul β) < 0 ∧
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
  obtain ⟨c, hα, hβ, hc⟩ := exists_cocharacter_separating_weights T hT α β hi s hs
  obtain ⟨t, ht⟩ := cocharacter_avoiding_point T c s hc
  refine ⟨c, hα, hβ, t, ?_⟩
  intro χ ψ hχ hψ hne he
  have hm : χ * ψ⁻¹ ∈ s := by
    apply Finset.mem_image.mpr
    refine ⟨(χ, ψ), Finset.mem_filter.mpr ⟨?_, hne⟩, rfl⟩
    exact Finset.mem_product.mpr
      ⟨(representationWeights_finite ρ T).mem_toFinset.mpr hχ,
        (representationWeights_finite ρ T).mem_toFinset.mpr hψ⟩
  exact ht _ hm (pointCharacter_ratio_eq_one T χ ψ _ he)

theorem exists_separating_semiregular_cocharacter
    (T : ClosedSubgroup G) (hT : IsSubtorus T) (α β : TorusWeight T)
    (hi : LinearIndependent ℤ ![Additive.ofMul α, Additive.ofMul β]) :
    ∃ c : ClosedSubgroupTorusCocharacter T,
      0 < characterCocharacterPairing T c (Additive.ofMul α) ∧
      characterCocharacterPairing T c (Additive.ofMul β) < 0 ∧
      (T.inclusion.comp c).imageClosedSubgroup.centralizer = T.centralizer := by
  let ρ := coordinateTranslationRationalRepresentation G
  let V := coordinateTranslationSubmodule G
  let : Module.Finite k V := coordinateTranslationSubmodule_finite G
  have hTop : (⨆ χ : TorusWeight T, weightSpace ρ T χ) = ⊤ :=
    closedSubtorusRepresentation_weightSpace_iSup_eq_top ρ
      (coordinateTranslationRationalRepresentation_isRational G) T hT
  obtain ⟨c, hα, hβ, t, hsep⟩ :=
    exists_separating_cocharacter_with_regular_point ρ T hT α β hi
  have he : semisimpleCommutatorPointCentralizer (T.includePoint (c.onPoints t)) =
      T.centralizer := regularTorus_centralizer_eq ρ
        (coordinateTranslationRepresentation_injective G) T hTop _ hsep
  refine ⟨c, hα, hβ, SetLike.coe_injective ?_⟩
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

/-- The semiregular cocharacter used in Bor1 13.12, with the source's literal
codimension-one subtori and characters trivial on them. -/
theorem exists_semiregular_cocharacter_separating_codimension_one_subtori
    (T S Q : ClosedSubgroup G) (hT : IsSubtorus T)
    (hS : IsSubtorus S) (hQ : IsSubtorus Q) (hST : S ≤ T) (hQT : Q ≤ T)
    (hScodim : Variety.dimension S.carrierVariety + 1 = Variety.dimension T.carrierVariety)
    (hQcodim : Variety.dimension Q.carrierVariety + 1 = Variety.dimension T.carrierVariety)
    (hSQ : S ≠ Q) (α β : TorusWeight T) (hα : α ≠ 1) (hβ : β ≠ 1)
    (hαS : ∀ x : Variety.Point T.carrierVariety,
      T.inclusion.onPoints x ∈ S → α.onPoints x = 1)
    (hβQ : ∀ x : Variety.Point T.carrierVariety,
      T.inclusion.onPoints x ∈ Q → β.onPoints x = 1) :
    ∃ c : ClosedSubgroupTorusCocharacter T,
      0 < characterCocharacterPairing T c (Additive.ofMul α) ∧
      characterCocharacterPairing T c (Additive.ofMul β) < 0 ∧
      (T.inclusion.comp c).imageClosedSubgroup.centralizer = T.centralizer := by
  have hSker := ambientConnectedKernel_eq_of_codimension_one
    T S hT hS hST hScodim α hα hαS
  have hQker := ambientConnectedKernel_eq_of_codimension_one
    T Q hT hQ hQT hQcodim β hβ hβQ
  have hi : LinearIndependent ℤ ![Additive.ofMul α, Additive.ofMul β] := by
    apply characters_independent_of_connectedKernel_ne hT.isConnected α β hα hβ
    intro he
    apply hSQ
    rw [← hSker, ← hQker]
    unfold TorusCharacter.ambientConnectedKernel
    rw [he]
  exact exists_separating_semiregular_cocharacter T hT α β hi

end Theory.AlgebraicGroup.Bor1.SeparatingBorel
