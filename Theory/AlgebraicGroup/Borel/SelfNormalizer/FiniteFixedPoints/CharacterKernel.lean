module

public import Theory.AlgebraicGroup.Borel.SelfNormalizer.TorusCommutator
public import Theory.AlgebraicGroup.Representations.Algebraic.HighestWeight
public import Theory.AlgebraicGroup.Unipotent.SolvableTorusDecomposition

/-!
# The normalizer character in the finite fixed-torus case

A rational character of a Borel normalizer kills the maximal torus because
its points are commutators with the given normalizer element. It kills the
unipotent radical because the multiplicative group has no nonidentity
unipotent points. The proved solvable torus decomposition then puts the
whole Borel in its kernel. Applied to an invariant line, the actual regular
character construction makes that line pointwise fixed by the Borel.

Source: Borel, *Linear Algebraic Groups*, Theorem 11.16(iii),
`refs/KGroup/Bor1/Chapter4.tex`, line 229. No reductivity or characteristic
assumption is used.
-/

universe u v
namespace Theory.AlgebraicGroup.BorelSelfNormalizer
variable {k : Type u} [Field k] [IsAlgClosed k]
variable {G : Variety k} [AlgebraicGroup G]

/-- A character kills the torus in the finite-fixed-point case. -/
public theorem character_eq_one_on_torus_of_finite_fixedPoints
    (T N : ClosedSubgroup G) (hT : IsSubtorus T) (hTN : T ≤ N)
    (n : Variety.Point G) (hnT : n ∈ T.normalizer.toSubgroup)
    (hnN : n ∈ N.toSubgroup) (hfixed : (fixedTorusPoints T n).Finite)
    (χ : TorusCharacter N.carrierVariety)
    (t : Variety.Point N.carrierVariety) (ht : N.inclusion.onPoints t ∈ T.toSubgroup) :
    χ.pointCharacter t = 1 := by
  obtain ⟨s, hs, hst⟩ :=
    exists_torus_commutator_of_finite_fixedPoints T hT n hnT hfixed _ ht
  let nN := N.pointEquiv.symm ⟨n, hnN⟩
  let sN := N.pointEquiv.symm ⟨s, hTN hs⟩
  have hn : N.inclusion.onPoints nN = n :=
    congrArg Subtype.val (N.pointEquiv.apply_symm_apply _)
  have hs' : N.inclusion.onPoints sN = s :=
    congrArg Subtype.val (N.pointEquiv.apply_symm_apply _)
  have ht' : nN * sN * nN⁻¹ * sN⁻¹ = t := by
    apply N.inclusion_injective
    simpa only [map_mul, map_inv, hn, hs'] using hst
  rw [← ht', map_mul, map_mul, map_mul]
  calc
    χ.pointCharacter nN * χ.pointCharacter sN * χ.pointCharacter nN⁻¹ *
        χ.pointCharacter sN⁻¹ =
      (χ.pointCharacter nN * χ.pointCharacter nN⁻¹) *
        (χ.pointCharacter sN * χ.pointCharacter sN⁻¹) := by ring
    _ = 1 := by rw [← map_mul, ← map_mul]; simp

/-- A rational character is trivial on a contained unipotent subgroup. -/
public theorem character_eq_one_on_unipotent
    (N U : ClosedSubgroup G) (hUN : U ≤ N)
    (hU : IsUnipotentAlgebraicGroup U.carrierVariety)
    (χ : TorusCharacter N.carrierVariety)
    (t : Variety.Point N.carrierVariety) (ht : N.inclusion.onPoints t ∈ U.toSubgroup) :
    χ.pointCharacter t = 1 := by
  let j := U.inclusion.codRestrictClosedSubgroup N (fun x => hUN (U.pointEquiv x).property)
  let x := U.pointEquiv.symm ⟨N.inclusion.onPoints t, ht⟩
  have hj : j.onPoints x = t := by
    apply N.inclusion_injective
    rw [Morphism.codRestrictClosedSubgroup_inclusion_apply]
    exact congrArg Subtype.val (U.pointEquiv.apply_symm_apply _)
  have hu := morphism_preserves_unipotentElement (χ.comp j) x (hU x)
  have hone := semisimple_unipotent_eq_one ((χ.comp j).onPoints x)
    (dVariety_all_semisimple 1 _) hu
  have htone : χ.onPoints t = 1 := by
    change χ.onPoints (j.onPoints x) = 1 at hone
    rwa [hj] at hone
  change (dPointEquiv 1 (χ.onPoints t) 0 : k) = 1
  rw [htone, dPointEquiv_one]
  rfl

/-- The source character calculation: the torus and unipotent radical, and
therefore the Borel, lie in the kernel of the character of its normalizer. -/
public theorem character_eq_one_on_borel_of_finite_fixedPoints
    (B T : ClosedSubgroup G) (hB : IsBorelSubgroup B)
    (hT : IsMaximalTorus T) (hTB : T ≤ B)
    (n : Variety.Point G) (hnB : n ∈ B.normalizer.toSubgroup)
    (hnT : n ∈ T.normalizer.toSubgroup) (hfixed : (fixedTorusPoints T n).Finite)
    (χ : TorusCharacter B.normalizer.carrierVariety)
    (b : Variety.Point B.normalizer.carrierVariety)
    (hb : B.normalizer.inclusion.onPoints b ∈ B.toSubgroup) :
    χ.pointCharacter b = 1 := by
  obtain ⟨U, hU, _⟩ := exists_unipotentRadical_of_connected_solvable B hB.connected hB.solvable
  obtain ⟨t, u, ht, hu, htu⟩ :=
    (maximalTorus_unipotentRadical_decomposition_of_connected_solvable
      hB.connected hB.solvable hU hT hTB).1 _ hb
  have hBN : B ≤ B.normalizer := Subgroup.le_normalizer
  let tN := B.normalizer.pointEquiv.symm ⟨t, hBN (hTB ht)⟩
  let uN := B.normalizer.pointEquiv.symm ⟨u, hBN (hU.1 hu)⟩
  have htN : B.normalizer.inclusion.onPoints tN = t :=
    congrArg Subtype.val (B.normalizer.pointEquiv.apply_symm_apply _)
  have huN : B.normalizer.inclusion.onPoints uN = u :=
    congrArg Subtype.val (B.normalizer.pointEquiv.apply_symm_apply _)
  have hbN : b = tN * uN := by
    apply B.normalizer.inclusion_injective
    simpa only [map_mul, htN, huN] using htu
  rw [hbN, map_mul,
    character_eq_one_on_torus_of_finite_fixedPoints T B.normalizer hT.1
      (fun _ hx => hBN (hTB hx)) n hnT hnB hfixed χ tN (htN.symm ▸ ht),
    character_eq_one_on_unipotent B.normalizer U (fun _ hx => hBN (hU.1 hx))
      hU.2.1 χ uN (huN.symm ▸ hu), one_mul]

/-- Every normalizer-invariant line is fixed pointwise by the Borel in source case (iii). -/
public theorem borel_fixes_invariantLine_of_finite_fixedPoints
    (B T : ClosedSubgroup G) (hB : IsBorelSubgroup B)
    (hT : IsMaximalTorus T) (hTB : T ≤ B)
    (n : Variety.Point G) (hnB : n ∈ B.normalizer.toSubgroup)
    (hnT : n ∈ T.normalizer.toSubgroup) (hfixed : (fixedTorusPoints T n).Finite)
    {V : Type v} [AddCommGroup V] [Module k V]
    (ρ : RationalRepresentation G V) (hρ : IsRationalRepresentation ρ)
    (d : V) (hd : GeneratesInvariantLine ρ B.normalizer d) :
    ∀ b : Variety.Point G, b ∈ B.toSubgroup → (ρ.action b).1 d = d := by
  obtain ⟨χ, hχ, _⟩ := invariantLine_torusWeight_existsUnique_public ρ hρ B.normalizer d hd
  intro b hb
  let bN := B.normalizer.pointEquiv.symm ⟨b, Subgroup.le_normalizer hb⟩
  have hbN : B.normalizer.inclusion.onPoints bN = b :=
    congrArg Subtype.val (B.normalizer.pointEquiv.apply_symm_apply _)
  have hweight := hχ.2 bN
  change (ρ.action (B.normalizer.inclusion.onPoints bN)).1 d = χ.pointCharacter bN • d at hweight
  rw [hbN, character_eq_one_on_borel_of_finite_fixedPoints
    B T hB hT hTB n hnB hnT hfixed χ bN (hbN.symm ▸ hb), one_smul] at hweight
  exact hweight
end Theory.AlgebraicGroup.BorelSelfNormalizer
