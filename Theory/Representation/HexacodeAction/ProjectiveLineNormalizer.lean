module

public import Theory.Representation.HexacodeAction.SixDimensionalRecognition.EvenImage.Operators
public import Theory.SpecificGroups.Alternating.SmallInvolutionCentralizers
public import Theory.GroupTheory.CentralCoprimeCardLift
public import Theory.Representation.BinaryOffender.CommutatorRank
public import Theory.Representation.BinaryOffender.EquivariantStabilizer
public import Theory.Representation.BinaryOffender.EquivariantOffender

/-!
# No invariant binary two-space for a hexacode projective-line normalizer

Every involution of the even hexacode cover is conjugate to the square of
`generatorA`: its image is a double transposition in A₆, and involution lifts
are unique through the central kernel of order three. The fixed plane of
this square has field coordinates `x₀ = x₂` and binary dimension four.

The elements `A` and `BAABAABB` stabilize that plane. The only field point
invariant under `A` is the diagonal point, which the second word moves.
Small kernel-checked calculations establish these statements using the
proved coordinate formulas for the actual monomial generators. The cubic
scalar turns every invariant binary two-space into a field point.

A four-group whose fixed space has binary dimension four has the same
fixed space as any of its involutions. Conjugation therefore transports
the calculation to every four-group in the theorem. No classification of
four-subgroups or list of all 1080 group elements is needed.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, combined
manuscript of 1 March 2004, 13.6.22, printed p.932 (PDF p.949), and the
field realization in K.1.3, printed p.453. The actual code, monomial lifts
and coordinate formulas come from the attributed ATLAS ports by Gerald
Höhn and contributors; see `LICENSES/ATLAS.txt`. This module retains their
carriers and uses the proved formulas in `EvenImage.Operators`.
-/

public section

open Atlas.Codes Subgroup Representation.BinaryOffender
namespace Representation.Hexacode.ProjectiveLineNormalizer
open SixDimensional.EvenImage

private abbrev t : HexEvenAutomorphisms := generatorA ^ 2

private theorem t_sq : t ^ 2 = 1 := by
  rw [t, ← pow_mul]
  exact generatorA_four

private theorem image_ne_one {x : HexEvenAutomorphisms}
    (hx : x ^ 2 = 1) (hne : x ≠ 1) : hexEvenCoordinate x ≠ 1 := by
  intro he
  apply hne
  exact hexEvenCoordinate.eq_of_map_eq_of_pow_eq_one_of_central_coprime_ker
    (le_of_eq even_kernel_eq_center) (by rw [hexEven_kernel_card]; decide)
    (he.trans (map_one _).symm) hx (one_pow _)

private theorem involution_conjugate {x : HexEvenAutomorphisms}
    (hx : x ^ 2 = 1) (hne : x ≠ 1) : IsConj x t := by
  have ho (y : HexEvenAutomorphisms) (hy : y ^ 2 = 1) (hyne : y ≠ 1) :
      orderOf (hexEvenCoordinate y) = 2 :=
    orderOf_eq_prime (by rw [← map_pow, hy, map_one]) (image_ne_one hy hyne)
  have hxct := alternatingGroup.involution_cycleType_of_degree_le_six (by decide)
    (hexEvenCoordinate x) (ho x hx hne)
  have htct := alternatingGroup.involution_cycleType_of_degree_le_six (by decide)
    (hexEvenCoordinate t) (ho t t_sq generatorA_sq_ne_one)
  have hc : IsConj (hexEvenCoordinate x) (hexEvenCoordinate t) := by
    apply alternatingGroup.isConj_of
      (Equiv.Perm.isConj_iff_cycleType_eq.mpr (hxct.trans htct.symm))
    rw [← Equiv.Perm.sum_cycleType, hxct]
    decide
  obtain ⟨c, hc⟩ := isConj_iff.mp hc
  obtain ⟨g, rfl⟩ := hexEvenCoordinate_surjective c
  apply isConj_iff.mpr
  refine ⟨g, ?_⟩
  apply hexEvenCoordinate.eq_of_map_eq_of_pow_eq_one_of_central_coprime_ker
    (le_of_eq even_kernel_eq_center) (by rw [hexEven_kernel_card]; decide) _ _ t_sq
  · simpa only [map_mul, map_inv] using hc
  · rw [conj_pow, hx, mul_one, mul_inv_cancel]

private def opA (v : Fin 3 → F) : Fin 3 → F := ![v 0 + v 1 + v 2, v 0, v 1]
private def opB (v : Fin 3 → F) : Fin 3 → F := ![v 2, omega * v 0, omega ^ 2 * v 1]
private def word : HexEvenAutomorphisms :=
  generatorB * (generatorA * (generatorA * (generatorB *
    (generatorA * (generatorA * (generatorB * generatorB))))))
private def opWord (v : Fin 3 → F) : Fin 3 → F :=
  opB (opA (opA (opB (opA (opA (opB (opB v)))))))

private theorem coord_A (v : hexacode) :
    fieldCoordinates (evenAction generatorA v) = opA (fieldCoordinates v) :=
  generatorA_coordinates v
private theorem coord_B (v : hexacode) :
    fieldCoordinates (evenAction generatorB v) = opB (fieldCoordinates v) :=
  generatorB_coordinates v
private theorem coord_word (v : hexacode) :
    fieldCoordinates (evenAction word v) = opWord (fieldCoordinates v) := by
  simp only [word, map_mul, Module.End.mul_apply, coord_A, coord_B, opWord]

private theorem fixed_t_coordinates (v : hexacode) :
    v ∈ fixedSpace evenAction (zpowers t) ↔ fieldCoordinates v 0 = fieldCoordinates v 2 := by
  rw [mem_fixedSpace_zpowers_iff]
  have hc : evenAction t v = v ↔
      fieldCoordinates (evenAction t v) = fieldCoordinates v :=
    fieldCoordinates.injective.eq_iff.symm
  rw [hc, show t = generatorA * generatorA from pow_two _,
    map_mul, Module.End.mul_apply, coord_A, coord_A]
  have h : ∀ v : Fin 3 → F, opA (opA v) = v ↔ v 0 = v 2 := by decide +kernel
  exact h _

private noncomputable def planeEquiv : fixedSpace evenAction (zpowers t) ≃ₗ[Bit] (F × F) where
  toFun v := (fieldCoordinates v.val 0, fieldCoordinates v.val 1)
  invFun u := ⟨fieldCoordinates.symm ![u.1, u.2, u.1], by
    rw [fixed_t_coordinates, fieldCoordinates.apply_symm_apply]
    rfl⟩
  left_inv v := by
    apply Subtype.ext
    apply fieldCoordinates.injective
    rw [fieldCoordinates.apply_symm_apply]
    have h := (fixed_t_coordinates v.val).mp v.property
    funext i
    fin_cases i <;> simp_all
  right_inv u := by simp
  map_add' u v := by simp
  map_smul' r v := by
    exact Prod.ext (congrFun (binaryCoordinates.map_smul r v.val) 0)
      (congrFun (binaryCoordinates.map_smul r v.val) 1)

private theorem plane_finrank : Module.finrank Bit (fixedSpace evenAction (zpowers t)) = 4 := by
  rw [planeEquiv.finrank_eq, Module.finrank_prod]
  have h : Module.finrank Bit F = 2 := QuadraticAlgebra.finrank_eq_two _ _
  rw [h]

private theorem A_stabilizes : generatorA ∈ subspaceStabilizer evenAction
    (fixedSpace evenAction (zpowers t)) := by
  intro v
  rw [fixed_t_coordinates, fixed_t_coordinates, coord_A]
  have h : ∀ v : Fin 3 → F, opA v 0 = opA v 2 ↔ v 0 = v 2 := by decide +kernel
  exact h _

private theorem word_stabilizes : word ∈ subspaceStabilizer evenAction
    (fixedSpace evenAction (zpowers t)) := by
  intro v
  rw [fixed_t_coordinates, fixed_t_coordinates, coord_word]
  have h : ∀ v : Fin 3 → F, opWord v 0 = opWord v 2 ↔ v 0 = v 2 := by decide +kernel
  exact h _

private theorem eigenvector_A : ∀ (v : Fin 3 → F) (r : F),
    opA v = r • v → v = ![v 0, v 0, v 0] := by decide +kernel

private theorem word_on_diagonal : ∀ u : F,
    opWord ![u, u, u] = ![omega ^ 2 * u, 0, omega ^ 2 * u] := by decide +kernel

private theorem diagonal_word (u s : F)
    (h : opWord ![u, u, u] = s • ![u, u, u]) : u = 0 := by
  rw [word_on_diagonal] at h
  have h0 : omega ^ 2 * u = s * u := congrFun h 0
  have h1 : 0 = s * u := congrFun h 1
  exact (mul_eq_zero.mp (h0.trans h1.symm)).resolve_left
    (pow_ne_zero 2 (by decide : omega ≠ 0))

private theorem no_eigenvector (v : Fin 3 → F) (r s : F)
    (hA : opA v = r • v) (hW : opWord v = s • v) : v = 0 := by
  have he := eigenvector_A v r hA
  have hw : opWord ![v 0, v 0, v 0] = s • ![v 0, v 0, v 0] :=
    (congrArg opWord he).symm.trans (hW.trans (congrArg (fun u => s • u) he))
  have hz := diagonal_word (v 0) s hw
  calc
    v = ![v 0, v 0, v 0] := he
    _ = 0 := by rw [hz]; funext i; fin_cases i <;> rfl

/-- The central cubic scalar preserves the fixed space of every even subgroup. -/
theorem scalar_mem_fixedSpace (A : Subgroup HexEvenAutomorphisms) :
    hexZ ∈ subspaceStabilizer action (fixedSpace evenAction A) := by
  intro v
  constructor
  · intro hv a
    apply (hexAction hexZ).injective
    exact (action_commutes_scalar a.val.val a.val.property v).symm.trans (hv a)
  · intro hv a
    exact (action_commutes_scalar a.val.val a.val.property v).trans
      (congrArg (action hexZ) (hv a))

/-- A binary four-dimensional fixed space is a projective line: vector dimension two over F₄. -/
theorem fixedSpace_field_finrank (A : Subgroup HexEvenAutomorphisms)
    (hd : Module.finrank Bit (fixedSpace evenAction A) = 4) :
    Module.finrank F (scalarSubmodule (fixedSpace evenAction A) (scalar_mem_fixedSpace A)) = 2 := by
  have h := scalarSubmodule_finrank (fixedSpace evenAction A) (scalar_mem_fixedSpace A)
  omega

private theorem base_no_invariant_two (Q : Submodule Bit hexacode)
    (hQ : Module.finrank Bit Q = 2)
    (hN : subspaceStabilizer evenAction (fixedSpace evenAction (zpowers t)) ≤
      subspaceStabilizer evenAction Q) : False := by
  have hZ : hexEvenZ ∈ subspaceStabilizer evenAction
      (fixedSpace evenAction (zpowers t)) := scalar_mem_fixedSpace (zpowers t)
  have hz : hexZ ∈ subspaceStabilizer action Q := hN hZ
  let D := scalarSubmodule Q hz
  have hd : Module.finrank F D = 1 := by
    have h := scalarSubmodule_finrank Q hz
    change 2 * Module.finrank F D = _ at h
    omega
  have : Nontrivial D := Module.nontrivial_of_finrank_pos (by rw [hd]; decide)
  obtain ⟨v, hv⟩ := exists_ne (0 : D)
  have hAv : evenAction generatorA v.val ∈ D := (hN A_stabilizes v.val).mpr v.property
  have hWv : evenAction word v.val ∈ D := (hN word_stabilizes v.val).mpr v.property
  obtain ⟨r, hr⟩ := exists_smul_eq_of_finrank_eq_one hd hv (⟨_, hAv⟩ : D)
  obtain ⟨s, hs⟩ := exists_smul_eq_of_finrank_eq_one hd hv (⟨_, hWv⟩ : D)
  have hr' : opA (fieldCoordinates v.val) = r • fieldCoordinates v.val := by
    rw [← coord_A, ← fieldCoordinates.map_smul]
    exact congrArg fieldCoordinates (congrArg Subtype.val hr).symm
  have hs' : opWord (fieldCoordinates v.val) = s • fieldCoordinates v.val := by
    rw [← coord_word, ← fieldCoordinates.map_smul]
    exact congrArg fieldCoordinates (congrArg Subtype.val hs).symm
  apply hv
  apply Subtype.ext
  apply fieldCoordinates.injective
  change fieldCoordinates v.val = fieldCoordinates (0 : hexacode)
  simpa only [map_zero] using no_eigenvector (fieldCoordinates v.val) r s hr' hs'

private theorem action_intertwines (g a : HexEvenAutomorphisms) (v : hexacode) :
    hexAction g.val (evenAction a v) =
      evenAction (MulAut.conj g a) (hexAction g.val v) := by
  change evenAction g (evenAction a v) = evenAction (g * a * g⁻¹) (evenAction g v)
  simp only [← Module.End.mul_apply, ← map_mul, inv_mul_cancel_right]

/-- Every involution in the actual even hexacode cover fixes a binary four-space. -/
theorem involution_fixedSpace_finrank (x : HexEvenAutomorphisms)
    (hx : x ^ 2 = 1) (hne : x ≠ 1) :
    Module.finrank Bit (fixedSpace evenAction (zpowers x)) = 4 := by
  obtain ⟨g, hg⟩ := isConj_iff.mp (involution_conjugate hx hne)
  have he := (fixedSpaceConjEquiv evenAction (zpowers x) g).finrank_eq
  rw [MonoidHom.map_zpowers, show (MulAut.conj g).toMonoidHom x = t from hg] at he
  exact he.trans plane_finrank

/-- The full stabilizer of an involution fixed plane preserves no binary two-space. -/
theorem involution_no_invariant_two (x : HexEvenAutomorphisms)
    (hx : x ^ 2 = 1) (hne : x ≠ 1) (Q : Submodule Bit hexacode)
    (hQ : Module.finrank Bit Q = 2) :
    ¬ subspaceStabilizer evenAction (fixedSpace evenAction (zpowers x)) ≤
      subspaceStabilizer evenAction Q := by
  intro hN
  obtain ⟨g, hg⟩ := isConj_iff.mp (involution_conjugate hx hne)
  have hP := fixedSpace_map_equivariant evenAction evenAction (MulAut.conj g).toMonoidHom
    (hexAction g.val) (action_intertwines g) (zpowers x)
  rw [MonoidHom.map_zpowers, show (MulAut.conj g).toMonoidHom x = t from hg] at hP
  apply base_no_invariant_two (Q.map (hexAction g.val).toLinearMap)
    ((hexAction g.val).finrank_map_eq Q |>.trans hQ)
  have hmap := Subgroup.map_mono (f := (MulAut.conj g).toMonoidHom) hN
  rw [map_subspaceStabilizer_equivariant evenAction evenAction (MulAut.conj g)
    (hexAction g.val) (action_intertwines g),
    map_subspaceStabilizer_equivariant evenAction evenAction (MulAut.conj g)
    (hexAction g.val) (action_intertwines g), hP] at hmap
  exact hmap

/-- The full stabilizer of a four-group fixed four-space preserves no binary two-space. -/
theorem fourGroup_no_invariant_two (A : Subgroup HexEvenAutomorphisms)
    [IsElementaryAbelian 2 A] (hA : Nat.card A = 4)
    (hP : Module.finrank Bit (fixedSpace evenAction A) = 4)
    (Q : Submodule Bit hexacode) (hQ : Module.finrank Bit Q = 2) :
    ¬ subspaceStabilizer evenAction (fixedSpace evenAction A) ≤
      subspaceStabilizer evenAction Q := by
  have : Nontrivial A := (Finite.one_lt_card_iff_nontrivial).mp (by omega)
  obtain ⟨a, ha⟩ := exists_ne (1 : A)
  have hane : a.val ≠ 1 := fun he => ha (Subtype.ext he)
  have ha2 : a.val ^ 2 = 1 := elemPow_eq_one_of_isElementaryAbelian a.val a.property
  have he : fixedSpace evenAction A = fixedSpace evenAction (zpowers a.val) := by
    apply Submodule.eq_of_le_of_finrank_eq
    · intro v hv
      exact (mem_fixedSpace_zpowers_iff evenAction a.val v).mpr (hv a)
    · exact hP.trans (involution_fixedSpace_finrank a.val ha2 hane).symm
  rw [he]
  exact involution_no_invariant_two a.val ha2 hane Q hQ

/-- Equivalently, the full plane stabilizer preserves no additive subgroup of order four. -/
theorem fourGroup_no_invariant_addSubgroup (A : Subgroup HexEvenAutomorphisms)
    [IsElementaryAbelian 2 A] (hA : Nat.card A = 4)
    (hP : Module.finrank Bit (fixedSpace evenAction A) = 4)
    (Q : AddSubgroup hexacode) (hQ : Nat.card Q = 4) :
    ¬ ∀ g ∈ subspaceStabilizer evenAction (fixedSpace evenAction A),
      ∀ v ∈ Q, evenAction g v ∈ Q := by
  intro hi
  let D := AddSubgroup.toZModSubmodule 2 Q
  have hcard : Nat.card D = 4 := hQ
  have hd : Module.finrank Bit D = 2 := by
    rw [Module.natCard_eq_pow_finrank (K := Bit), Nat.card_zmod] at hcard
    exact Nat.pow_right_injective (by decide : 1 < 2) hcard
  apply fourGroup_no_invariant_two A hA hP D hd
  exact le_subspaceStabilizer evenAction D hi

end Representation.Hexacode.ProjectiveLineNormalizer
