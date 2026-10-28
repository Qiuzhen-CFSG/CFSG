module

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.Seven.PairsBranch.ModuleSelection.Reduction
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.Seven.PairsBranch.ModuleSelection.Recognition
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.Seven.PairsBranch.ModuleSelection.FourSpace

/-!
# Module selection in the three-pairs branch of 13.8.24

For a maximal proper subrepresentation W of the actual representation on Ũ_H,
the earlier commutator-generation and monolith conditions give a faithful
irreducible quotient. The quadratic actor and its displacement bound descend
to this literal quotient. Generation by the H-translates of the irreducible
rank-two seed embeds that seed equivariantly in the quotient and preserves
invariance under L₁T.

The complete earlier classification implication is kept explicit, including
all 4, natural 6, and 4-plus-dual alternatives. `Reduction` proves that a finite
four-space plane exclusion eliminates both exceptional alternatives and gives
the requested equivariant linear equivalence, using the same φ throughout.
`Recognition` supplies the faithful strong-FF and transvection-recognition
inputs to the sibling Sieve from their stated universal B.3/B.4 consequences.

`fourPlaneExclusion` is supplied by the finite stabilizer calculation in
`ModuleSelection.FourSpace`. The assembled `natural_quotient`
therefore has no remaining plane-exclusion premise. Its hypotheses retain the
earlier universal classification implication and the preceding source
identities for the actual representation, component and seed; the parent
instantiates those data on Ũ_H. This is the module-selection deduction, not
the central-W contradiction or the final A₇ exclusion. The rank-two seed is
not replaced by a one-dimensional “line”, and the two four-dimensional
constituents are not assumed to be invariant under the whole group H.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*,
13.8.21–24, printed pp.957–959, PDF pp.974–976 (1 March 2004 manuscript).
-/

public section
open Representation Representation.BinaryOffender Subgroup
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.Seven.PairsBranch.ModuleSelection
universe u
variable {H : Type*} {E : Type u} [Group H] [AddCommGroup E] [Module (ZMod 2) E]
  [FiniteDimensional (ZMod 2) E]
  (ρ : Representation (ZMod 2) H E)

omit [FiniteDimensional (ZMod 2) E] in
private theorem quadratic_quotient (W : Subrepresentation ρ) (A : Subgroup H)
    (hq : IsQuadratic ρ A) : IsQuadratic W.quotientRepresentation A := by
  intro a ha b hb q
  induction q using Submodule.Quotient.induction_on with
  | _ v =>
    change W.toSubmodule.mkQ (ρ a (ρ b v - v)) = W.toSubmodule.mkQ (ρ b v - v)
    rw [hq a ha b hb v]

/-- Apply the full classification to the literal maximal quotient. Faithfulness,
irreducibility, the quadratic displacement bound and the invariant irreducible
rank-two seed are derived before the alternatives are eliminated. This keeps
the finite obstruction explicit for reuse; `natural_quotient` discharges it. -/
theorem natural_quotient_of_plane_exclusion
    (φ : H →* Equiv.Perm (Fin 7)) (hφ : Function.Injective φ)
    (K L T : Subgroup H) (hK : K.map φ = alternatingGroup (Fin 7)) (hLK : L ≤ K)
    (hmonolith : ∀ N : Subgroup H, N.Normal → N ≠ ⊥ → K ≤ N)
    (hcomm : subspaceCommutator ρ ⊤ K = ⊤)
    (hplacement : L ⊔ T = pairStabilizer.comap φ)
    (W : Subrepresentation ρ) (hW : IsCoatom W)
    (V : Subrepresentation (ρ.comp L.subtype)) [IsIrreducible V.toRepresentation]
    (hgen : SeedGenerates ρ V.toSubmodule)
    (hdim : Module.finrank (ZMod 2) V.toSubmodule = 2)
    (hstable : L ⊔ T ≤ subspaceStabilizer ρ V.toSubmodule)
    (A : Subgroup H) (hA : IsElementaryTwo A) (hq : IsQuadratic ρ A)
    (hbound : fixedCodim ρ A ≤ 2 * rank A)
    (hclass : SmallQuadraticInput.{_, u} φ (componentInclusion φ hφ K hK))
    (hfour : FourPlaneExclusion) :
    ∃ e : BinaryPermutation.core (Fin 7) ≃ₗ[ZMod 2] (E ⧸ W.toSubmodule),
      ∀ g v, e (BinaryPermutation.coreRepresentation (Fin 7) (φ g) v) =
        W.quotientRepresentation g (e v) := by
  let ι := componentInclusion φ hφ K hK
  have hfaith : Function.Injective W.quotientRepresentation :=
    faithful_of_nontrivial_on_monolith W.quotientRepresentation K hmonolith
      (nontrivial_on_quotient_of_generated ρ W K hW.1 hcomm)
  let : IsIrreducible W.quotientRepresentation := quotient_irreducible ρ W hW
  have hqbound : fixedCodim W.quotientRepresentation A ≤ 2 * rank A := by
    have hb := fixedCodim_quotient_add_subrepresentation_le ρ W A
    omega
  have halt : SmallModuleAlternatives W.quotientRepresentation φ ι :=
    hclass (E ⧸ W.toSubmodule) W.quotientRepresentation hfaith inferInstance
      A hA (quadratic_quotient ρ W A hq) hqbound
  let S := quotientSeed ρ L W V
  let : IsIrreducible S.toRepresentation := quotientSeed_irreducible ρ L W hW.1 V hgen
  have hSdim : Module.finrank (ZMod 2) S.toSubmodule = 2 :=
    quotientSeed_finrank ρ L W hW.1 V hgen hdim
  have hSP : pairStabilizer.comap φ ≤ subspaceStabilizer W.quotientRepresentation S.toSubmodule := by
    rw [← hplacement]
    exact quotientSeed_stable ρ L W V (L ⊔ T) hstable
  have hLi : L ≤ ι.range := by
    rw [componentInclusion_range]
    exact hLK
  exact (natural_of_alternatives W.quotientRepresentation φ ι
    (componentInclusion_compatible φ hφ K hK) L hLi S hSdim hSP hfour halt).linearEquiv

/-- The module-selection step of the three-pairs branch of 13.8.24. The literal
maximal quotient is equivariantly the natural module for the same seven-point
map. All three earlier classification alternatives are retained in `hclass`;
the proved finite stabilizer obstruction excludes both exceptional ones.

The source identities are the monolith and commutator conclusions of 13.8.21,
generation by the irreducible rank-two Ṽ₃ immediately before 13.8.22, and the
quadratic actor with displacement bound in case (2) of 13.8.8. The parent
supplies their realization on Ũ_H and the pair-stabilizer placement. -/
theorem natural_quotient
    (φ : H →* Equiv.Perm (Fin 7)) (hφ : Function.Injective φ)
    (K L T : Subgroup H) (hK : K.map φ = alternatingGroup (Fin 7)) (hLK : L ≤ K)
    (hmonolith : ∀ N : Subgroup H, N.Normal → N ≠ ⊥ → K ≤ N)
    (hcomm : subspaceCommutator ρ ⊤ K = ⊤)
    (hplacement : L ⊔ T = pairStabilizer.comap φ)
    (W : Subrepresentation ρ) (hW : IsCoatom W)
    (V : Subrepresentation (ρ.comp L.subtype)) [IsIrreducible V.toRepresentation]
    (hgen : SeedGenerates ρ V.toSubmodule)
    (hdim : Module.finrank (ZMod 2) V.toSubmodule = 2)
    (hstable : L ⊔ T ≤ subspaceStabilizer ρ V.toSubmodule)
    (A : Subgroup H) (hA : IsElementaryTwo A) (hq : IsQuadratic ρ A)
    (hbound : fixedCodim ρ A ≤ 2 * rank A)
    (hclass : SmallQuadraticInput.{_, u} φ (componentInclusion φ hφ K hK)) :
    ∃ e : BinaryPermutation.core (Fin 7) ≃ₗ[ZMod 2] (E ⧸ W.toSubmodule),
      ∀ g v, e (BinaryPermutation.coreRepresentation (Fin 7) (φ g) v) =
        W.quotientRepresentation g (e v) :=
  natural_quotient_of_plane_exclusion ρ φ hφ K L T hK hLK hmonolith hcomm
    hplacement W hW V hgen hdim hstable A hA hq hbound hclass fourPlaneExclusion

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.Seven.PairsBranch.ModuleSelection
