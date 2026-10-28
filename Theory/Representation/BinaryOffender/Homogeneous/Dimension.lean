module

public import Theory.Representation.BinaryOffender.Homogeneous.DoubleCoordinates

/-!
# A homogeneous module below three constituent degrees

Properness supplies a second simple copy. If the two copies do not span,
homogeneity supplies a third copy outside their sum. Simplicity makes this
third copy disjoint from the sum, contradicting the strict dimension bound.
The resulting double-degree bound feeds the actual intertwining coordinates
in `DoubleCoordinates` through the A₆ Schur recognition consumer.

Source: the homogeneous multiplicity argument in Aschbacher--Smith G.11.7,
printed p.366.
-/

public noncomputable section

open Representation Module
namespace Representation.BinaryOffender.Homogeneous
variable {D V : Type*} [Group D] [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V] {ρ : Representation (ZMod 2) D V}

/-- Two copies of a proper homogeneous constituent fill the whole module
if its degree is strictly less than three constituent degrees. -/
theorem degree_le_double_of_lt_triple (I : Subrepresentation ρ)
    (hi : IsIrreducible I.toRepresentation)
    (hh : homogeneousPart I ⊤ = ⊤) (hp : I.toSubmodule ≠ ⊤)
    (hd : finrank (ZMod 2) V < 3 * finrank (ZMod 2) I.toSubmodule) :
    finrank (ZMod 2) V ≤ 2 * finrank (ZMod 2) I.toSubmodule := by
  classical
  have hex (N : Subrepresentation ρ) (hN : N.toSubmodule ≠ ⊤) :
      ∃ J : Subrepresentation ρ, SameModule I J ∧ ¬ J ≤ N := by
    by_contra! h
    apply hN
    apply top_unique
    rw [← hh]
    exact iSup_le fun J => iSup_le fun hJ => h J hJ.2
  obtain ⟨J,hJ,hJI⟩ := hex I hp
  have hj := hJ.irreducible hi
  have hdis : Disjoint J.toSubmodule I.toSubmodule := by
    rw [disjoint_iff]
    exact congrArg Subrepresentation.toSubmodule
      ((((Subrepresentation.irreducible_iff_isAtom J).mp hj).not_le_iff_disjoint.mp hJI).eq_bot)
  have hdimJ : finrank (ZMod 2) J.toSubmodule = finrank (ZMod 2) I.toSubmodule :=
    hJ.choose.finrank_eq.symm
  have hdimIJ : finrank (ZMod 2) (I ⊔ J).toSubmodule =
      2 * finrank (ZMod 2) I.toSubmodule := by
    have hs := Submodule.finrank_sup_add_finrank_inf_eq I.toSubmodule J.toSubmodule
    rw [hdis.symm.eq_bot,finrank_bot,add_zero,hdimJ] at hs
    change finrank (ZMod 2) (I.toSubmodule ⊔ J.toSubmodule : Submodule (ZMod 2) V) = _
    omega
  by_cases htop : (I ⊔ J).toSubmodule = ⊤
  · rw [htop,finrank_top] at hdimIJ
    omega
  · obtain ⟨K,hK,hKIJ⟩ := hex (I ⊔ J) htop
    have hk := hK.irreducible hi
    have hdisK : Disjoint K.toSubmodule (I ⊔ J).toSubmodule := by
      rw [disjoint_iff]
      exact congrArg Subrepresentation.toSubmodule
        ((((Subrepresentation.irreducible_iff_isAtom K).mp hk).not_le_iff_disjoint.mp hKIJ).eq_bot)
    have hdimK : finrank (ZMod 2) K.toSubmodule = finrank (ZMod 2) I.toSubmodule :=
      hK.choose.finrank_eq.symm
    have hs := Submodule.finrank_sup_add_finrank_inf_eq K.toSubmodule (I ⊔ J).toSubmodule
    rw [hdisK.eq_bot,finrank_bot,add_zero,hdimK,hdimIJ] at hs
    have hle := (K.toSubmodule ⊔ (I ⊔ J).toSubmodule).finrank_le
    omega

end Representation.BinaryOffender.Homogeneous
