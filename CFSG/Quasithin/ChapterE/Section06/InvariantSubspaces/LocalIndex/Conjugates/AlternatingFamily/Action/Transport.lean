module

public import CFSG.Quasithin.ChapterE.Section06.InvariantSubspaces.LocalIndex.Conjugates.AlternatingFamily.Coordinates
public import CFSG.Quasithin.ChapterE.Section06.InvariantSubspaces.LocalIndex.Baumann.AlternatingFive.Transport

/-!
# Transport of the genuine alternating-five action to core coordinates

Conjugating the permutation labels also conjugates the natural-module
coordinates. This marks a given conjugate of the disjoint-transposition
four-group as the literal group D without changing its actual action.
The odd-degree equivalence between the even-weight core and natural module
then gives an injective, equivariant homomorphism onto the actual U(L).

Every result retains the full NaturalActionModel as an explicit input.
Its construction, including removal of C_U(L), is a separate obligation;
no identification of U with its defining quotient is assumed implicitly.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), C.1.13(c),
printed pp.124–125, C.5.4(3), p.155, and B.3.1–2, pp.82–84.
-/

public section
namespace CFSG.Quasithin.ChapterE.Section06.InvariantSubspaces.LocalIndex.Conjugates.AlternatingFamily.Action
open Subgroup Baumann.AlternatingFive

universe u
variable {G : Type u} [Group G] {H L : Subgroup G}

/-- Relabel the permutation and module actions by the same permutation. -/
noncomputable def relabel (m : NaturalActionModel H L) (p : Perm) :
    NaturalActionModel H L where
  quotient := (MulAut.conj p).toMonoidHom.comp m.quotient
  kernel := by
    ext x
    change p * m.quotient x * p⁻¹ = 1 ↔ x ∈ pCore 2 H
    rw [mul_inv_eq_one, mul_eq_left, ← MonoidHom.mem_ker, m.kernel]
  block_image := by
    rw [← map_map, m.block_image]
    exact Normal.map_conj_eq _ p
  moduleEquiv := m.moduleEquiv.trans
    (LinearEquiv.ofBijective (BinaryPermutation.naturalRepresentation (Fin 5) p)
      ((BinaryPermutation.naturalRepresentation (Fin 5)).apply_bijective p)).toAddEquiv.toMultiplicative
  intertwining := by
    intro x v
    dsimp only [MulEquiv.symm_trans_apply]
    have he : (BinaryPermutation.naturalRepresentation (Fin 5) (p * m.quotient x * p⁻¹))
        (BinaryPermutation.naturalRepresentation (Fin 5) p (m.moduleEquiv v).toAdd) =
        BinaryPermutation.naturalRepresentation (Fin 5) p
          (BinaryPermutation.naturalRepresentation (Fin 5) (m.quotient x)
            (m.moduleEquiv v).toAdd) := by
      simp only [map_mul, Module.End.mul_apply, Representation.inv_self_apply]
    change ((m.moduleEquiv.symm
      ((LinearEquiv.ofBijective (BinaryPermutation.naturalRepresentation (Fin 5) p)
        ((BinaryPermutation.naturalRepresentation (Fin 5)).apply_bijective p)).toAddEquiv.toMultiplicative.symm
          (Multiplicative.ofAdd
            (BinaryPermutation.naturalRepresentation (Fin 5) (p * m.quotient x * p⁻¹)
              (BinaryPermutation.naturalRepresentation (Fin 5) p (m.moduleEquiv v).toAdd))))) : G) = _
    rw [he]
    change ((m.moduleEquiv.symm
      ((LinearEquiv.ofBijective (BinaryPermutation.naturalRepresentation (Fin 5) p)
        ((BinaryPermutation.naturalRepresentation (Fin 5)).apply_bijective p)).toAddEquiv.toMultiplicative.symm
          ((LinearEquiv.ofBijective (BinaryPermutation.naturalRepresentation (Fin 5) p)
            ((BinaryPermutation.naturalRepresentation (Fin 5)).apply_bijective p)).toAddEquiv.toMultiplicative
            (Multiplicative.ofAdd _)))) : G) = _
    rw [MulEquiv.symm_apply_apply]
    exact m.intertwining x v

/-- Relabeling transports every actual subgroup image by conjugation. -/
theorem relabel_image (m : NaturalActionModel H L) (p : Perm) (B : Subgroup H) :
    B.map (relabel m p).quotient = (B.map m.quotient).map (MulAut.conj p).toMonoidHom :=
  (map_map _ _ _).symm

/-- Choose labels placing the specified actual image at D. -/
theorem exists_marked (m : NaturalActionModel H L) (B : Subgroup H)
    (hB : CFSG.Quasithin.ChapterB.Offenders.IsConjugateTo
      (B.map m.quotient) (CFSG.Quasithin.ChapterB.Offenders.D 5)) :
    ∃ m' : NaturalActionModel H L,
      B.map m'.quotient = CFSG.Quasithin.ChapterB.Offenders.D 5 := by
  obtain ⟨p, hp⟩ := hB
  refine ⟨relabel m p⁻¹, ?_⟩
  rw [relabel_image, hp, map_map]
  have he : (MulAut.conj p⁻¹).toMonoidHom.comp (MulAut.conj p).toMonoidHom =
      MonoidHom.id _ := by
    ext x
    simp [MulAut.conj_apply, mul_assoc]
  rw [he, map_id]

/-- The even-weight core identifies with U through the full action model. -/
noncomputable def coreEquiv (m : NaturalActionModel H L) : Multiplicative Vector ≃* U L :=
  (BinaryPermutation.coreEquivNatural (Fin 5) (by decide)).toAddEquiv.toMultiplicative.trans
    m.moduleEquiv.symm

/-- The literal embedding of the core into the ambient group. -/
noncomputable def coreMap (m : NaturalActionModel H L) : Multiplicative Vector →* G :=
  (U L).subtype.comp (coreEquiv m).toMonoidHom

/-- The core embedding is injective. -/
theorem coreMap_injective (m : NaturalActionModel H L) : Function.Injective (coreMap m) :=
  Subtype.val_injective.comp (coreEquiv m).injective

/-- The range is the actual commutator subgroup U(L). -/
theorem coreMap_range (m : NaturalActionModel H L) : (coreMap m).range = U L := by
  rw [coreMap, MonoidHom.range_comp, MonoidHom.range_eq_top.mpr (coreEquiv m).surjective,
    ← MonoidHom.range_eq_map, range_subtype]

/-- Core coordinates intertwine with literal ambient conjugation. -/
theorem coreMap_equivariant (m : NaturalActionModel H L) (x : H) (v : Multiplicative Vector) :
    (x : G) * coreMap m v * (x : G)⁻¹ =
      coreMap m (Multiplicative.ofAdd
        (BinaryPermutation.coreRepresentation (Fin 5) (m.quotient x) v.toAdd)) := by
  have he := m.intertwining x (coreEquiv m v)
  change _ = ((m.moduleEquiv.symm (Multiplicative.ofAdd
    (BinaryPermutation.coreEquivNatural (Fin 5) (by decide)
      (BinaryPermutation.coreRepresentation (Fin 5) (m.quotient x) v.toAdd)))) : G)
  rw [BinaryPermutation.coreEquivNatural_equivariant]
  simp only [coreEquiv, MulEquiv.trans_apply, MulEquiv.apply_symm_apply] at he
  exact he.symm

end CFSG.Quasithin.ChapterE.Section06.InvariantSubspaces.LocalIndex.Conjugates.AlternatingFamily.Action

end
