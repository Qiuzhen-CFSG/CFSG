module

public import Theory.SpecificGroups.SymplecticFour.Sylow.DerivedNormalizerSolvable.Binary
public import Theory.SpecificGroups.SymplecticFour.Sylow.CentralRootGeometry.Coordinates
public import Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms.FieldFixedResidual.Descent

/-!
# Centralizers of binary derived Sylow subgroups under coefficient extension

The explicit dihedral generators of an A₆ Sylow subgroup have a four-element
centralizer in S₆. The polar equivalence transfers this bound to the actual
binary symplectic group. A containing Sylow subgroup has a four-element
center, parametrized by the two central roots, so equality places every
centralizing element in a conjugate of that root plane. Coefficient inclusion
extends the plane into the center of the larger standard unipotent Sylow.
The same conjugating matrix is retained throughout the extension.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, the binary
derived endpoint in 16.1.4(4), printed p.1171, and the symplectic Sylow root
geometry in 16.5.13, p.1202. This supplies the matrix calculation used in the
Sp₄(4) branch of E.6.23, p.254 (PDF p.265).
-/

public section

open Subgroup
open AlternatingSix.ShadowLocal
namespace Theory.SpecificGroups.SymplecticFour.Binary

private abbrev PairCentralizer := {g : Equiv.Perm (Fin 6) //
  g * (dihedralRotation : Equiv.Perm (Fin 6)) = dihedralRotation * g ∧
  g * (dihedralReflection : Equiv.Perm (Fin 6)) = dihedralReflection * g}

set_option maxRecDepth 100000 in
private theorem pairCentralizer_card : Nat.card PairCentralizer = 4 := by
  let : Fintype (Equiv.Perm (Fin 6)) := fintypePerm
  rw [Nat.card_eq_fintype_card]
  decide +kernel

private theorem permutation_centralizer_bound (P : Sylow 2 A6) :
    Nat.card (centralizer ((P : Subgroup A6).map A6.subtype : Set (Equiv.Perm (Fin 6)))) ≤ 4 := by
  have hp : IsPGroup 2 dihedralEmbedding.range := by
    apply IsPGroup.of_card (n := 3)
    rw [← Nat.card_congr (MonoidHom.ofInjective dihedralEmbedding_injective).toEquiv,
      DihedralGroup.nat_card]
    rfl
  obtain ⟨Q, hQ⟩ := hp.exists_le_sylow
  have hrot : dihedralRotation ∈ (Q : Subgroup A6) :=
    hQ ⟨DihedralGroup.r 1, by decide +kernel⟩
  have href : dihedralReflection ∈ (Q : Subgroup A6) :=
    hQ ⟨DihedralGroup.sr 0, by decide +kernel⟩
  obtain ⟨a, rfl⟩ := MulAction.exists_smul_eq A6 Q P
  let e := MulAut.conj (a : Equiv.Perm (Fin 6))
  have hmem (x : A6) (hx : x ∈ (Q : Subgroup A6)) :
      e (x : Equiv.Perm (Fin 6)) ∈
        ((a • Q : Sylow 2 A6) : Subgroup A6).map A6.subtype := by
    refine ⟨MulAut.conj a x, ?_, rfl⟩
    exact Subgroup.smul_mem_pointwise_smul x (MulAut.conj a) (Q : Subgroup A6) hx
  let f : centralizer (((a • Q : Sylow 2 A6) : Subgroup A6).map A6.subtype :
      Set (Equiv.Perm (Fin 6))) → PairCentralizer := fun g =>
    ⟨e.symm g, by
      have hh (x : A6) (hx : x ∈ (Q : Subgroup A6)) :
          e.symm g * (x : Equiv.Perm (Fin 6)) = x * e.symm g := by
        apply e.injective
        simpa only [map_mul, e.apply_symm_apply] using
          (mem_centralizer_iff.mp g.property _ (hmem x hx)).symm
      exact ⟨hh _ hrot, hh _ href⟩⟩
  calc
    _ ≤ Nat.card PairCentralizer := Nat.card_le_card_of_injective f (by
      intro x y h
      exact Subtype.ext (e.symm.injective (congrArg Subtype.val h)))
    _ = 4 := pairCentralizer_card

variable {F : Type*} [Field F] [Finite F] [CharP F 2]

omit [CharP F 2] in
private theorem centralizer_bound (hF : Nat.card F = 2)
    (P : Sylow 2 (commutator (Sp F))) :
    Nat.card (centralizer ((P : Subgroup (commutator (Sp F))).map
      (commutator (Sp F)).subtype : Set (Sp F))) ≤ 4 := by
  let e := (fieldEquivSp (fieldEquivZModTwo F hF)).trans symmetricSixEquiv.symm
  let d := derivedEquivAlternatingSix hF
  let Q := P.mapSurjective (f := d.toMonoidHom) d.surjective
  let f : centralizer ((P : Subgroup (commutator (Sp F))).map
      (commutator (Sp F)).subtype : Set (Sp F)) →
      centralizer ((Q : Subgroup A6).map A6.subtype : Set (Equiv.Perm (Fin 6))) :=
    fun g => ⟨e g, by
      apply mem_centralizer_iff.mpr
      rintro _ ⟨_, ⟨x, hx, rfl⟩, rfl⟩
      change (derivedEquivAlternatingSix hF x : Equiv.Perm (Fin 6)) * e g =
        e g * (derivedEquivAlternatingSix hF x : Equiv.Perm (Fin 6))
      rw [derivedEquivAlternatingSix_coe]
      have hh : (x : Sp F) * (g : Sp F) = (g : Sp F) * (x : Sp F) :=
        mem_centralizer_iff.mp g.property _ ⟨x, hx, rfl⟩
      exact (map_mul e _ _).symm.trans ((congrArg e hh).trans (map_mul e _ _))⟩
  exact (Nat.card_le_card_of_injective f (by
    intro x y h
    exact Subtype.ext (e.injective (congrArg Subtype.val h)))).trans
      (permutation_centralizer_bound Q)

open CentralRootGeometry

/-- The centralizer of a binary derived Sylow lies in a conjugate two-root plane. -/
theorem exists_conjugate_theta_of_centralizes_derived_sylow
    (hF : Nat.card F = 2) (P : Sylow 2 (commutator (Sp F))) (g : Sp F)
    (hg : ∀ x ∈ (P : Subgroup (commutator (Sp F))),
      (x : Sp F) * g = g * (x : Sp F)) :
    ∃ a : Sp F, ∃ s t : F, g = MulAut.conj a (theta s t : Sp F) := by
  let D := (P : Subgroup (commutator (Sp F))).map (commutator (Sp F)).subtype
  let C := centralizer (D : Set (Sp F))
  have hgc : g ∈ C := by
    apply mem_centralizer_iff.mpr
    rintro _ ⟨x, hx, rfl⟩
    exact hg x hx
  obtain ⟨R, hR⟩ := (P.isPGroup'.map (commutator (Sp F)).subtype).exists_le_sylow
  let U := unipotentSylow (by simpa using hF : Nat.card F = 2 ^ 1) (by decide)
  obtain ⟨a, ha⟩ := MulAction.exists_smul_eq (Sp F) U R
  let e : unipotent (F := F) ≃* R :=
    (U.equivSMul a).trans (MulEquiv.subgroupCongr (congrArg Sylow.toSubgroup ha))
  have he (x : unipotent (F := F)) : (e x : Sp F) = MulAut.conj a x := rfl
  let Z := (center R).map (R : Subgroup (Sp F)).subtype
  have hZ : Z ≤ C := by
    rintro _ ⟨z, hz, rfl⟩
    apply mem_centralizer_iff.mpr
    intro x hx
    exact congrArg Subtype.val (mem_center_iff.mp hz ⟨x, hR hx⟩)
  have hc : Nat.card Z = 4 := by
    rw [Subgroup.card_map_of_injective Subtype.val_injective,
      ← Nat.card_congr (centerCongr e).toEquiv,
      ← Nat.card_congr (centerEquiv (F := F)).toEquiv]
    simp only [Nat.card_prod, Nat.card_congr (Multiplicative.toAdd : Multiplicative F ≃ F), hF]
  have hCZ : Z = C := Subgroup.eq_of_le_of_card_ge hZ (by
    rw [hc]
    exact centralizer_bound hF P)
  obtain ⟨z, hz, hzg⟩ := hCZ ▸ hgc
  have hze : e.symm z ∈ center (unipotent (F := F)) :=
    (centerCongr e.symm ⟨z, hz⟩).property
  rw [← theta_range] at hze
  obtain ⟨⟨s,t⟩, hst⟩ := hze
  refine ⟨a, s.toAdd, t.toAdd, ?_⟩
  change theta s.toAdd t.toAdd = e.symm z at hst
  rw [hst, ← he, e.apply_symm_apply]
  exact hzg.symm

open DiagramAutomorphisms.FieldFixedResidual

omit [Finite F] in
/-- The central root plane extends through the literal coefficient inclusion. -/
theorem coefficientInclusion_theta (K : Subfield F) (s t : K) :
    coefficientInclusion K (theta s t : Sp K) = (theta (s : F) (t : F) : Sp F) := by
  apply Subtype.ext
  ext i j
  rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;>
    simp [coefficientInclusion_apply, theta, element_matrix, Matrix.fromBlocks]

/-- A centralizer of a derived binary Sylow fixes a Sylow after extension of coefficients. -/
theorem exists_sylow_fixed_by_inclusion {n : ℕ}
    (hF : Nat.card F = 2 ^ n) (hn : 1 ≤ n) (K : Subfield F) (hK : Nat.card K = 2)
    (P : Sylow 2 (commutator (Sp K))) (g : Sp K)
    (hg : ∀ x ∈ (P : Subgroup (commutator (Sp K))),
      (x : Sp K) * g = g * (x : Sp K)) :
    ∃ Q : Sylow 2 (Sp F), ∀ x ∈ (Q : Subgroup (Sp F)),
      MulAut.conj (coefficientInclusion K g) x = x := by
  obtain ⟨a, s, t, ha⟩ := exists_conjugate_theta_of_centralizes_derived_sylow hK P g hg
  let e := MulAut.conj (coefficientInclusion K a)
  have hge : coefficientInclusion K g = e (theta (s : F) (t : F) : Sp F) := by
    rw [ha]
    simp only [MulAut.conj_apply, map_mul, map_inv, coefficientInclusion_theta, e]
  let U := unipotentSylow hF hn
  refine ⟨U.mapSurjective (f := e.toMonoidHom) e.surjective, ?_⟩
  rintro _ ⟨x, hx, rfl⟩
  rw [MulAut.conj_apply, mul_inv_eq_iff_eq_mul, hge]
  have hcomm : (theta (s : F) (t : F) : Sp F) * x =
      x * (theta (s : F) (t : F) : Sp F) :=
    (congrArg Subtype.val (mem_center_iff.mp (theta_mem_center (s : F) (t : F))
      ⟨x, hx⟩)).symm
  exact (map_mul e _ _).symm.trans ((congrArg e hcomm).trans (map_mul e _ _))

end Theory.SpecificGroups.SymplecticFour.Binary
