module

public import Theory.Alternating.Theorem523Reduction
public import Theory.AtlasPort.ExceptionalIsomorphisms.Order20160A8
public import Theory.GroupTheory.CoveringKernelBound
public import Theory.GroupTheory.CoveringKernelCard
public import Theory.GroupTheory.GeneralizedFitting.ComponentCalculus
public import Theory.GroupTheory.PerfectCentralCoverRank
public import Mathlib.FieldTheory.Finite.GaloisField

/-!
# The Schur multiplier of PSL₄(2)

The actual exceptional isomorphism PSL₄(2) ≃ A₈ transports Schur's universal
A₈ double cover. Universal lifts in both directions make the kernel of any
chosen universal cover have order two, hence identify it with C₂. Comparing
kernel orders permits different universes for the two covering groups.
The final theorem applies this calculation to the constructed universal
perfect cover of the original group and its actual projective-model map.

Source: Aschbacher–Smith, I.1.3(1), printed p.407; GLS3, Theorem 5.2.3.
The existing A₈ cover and exceptional isomorphism are reused; the attribution
for that isomorphism is retained in its imported ATLAS-port module.
-/

public section

namespace Matrix.PSL4Two

open Theory.GroupTheory PerfectCentralCovering
open GLS3.Chapter5.SchurPresentation
open scoped MatrixGroups

universe u v w

/-- The actual binary degree-four projective group over any two-element field
is the alternating group on eight points. -/
noncomputable def binaryEquivAlternatingEight
    (F : Type w) [Field F] [Finite F] (hF : Nat.card F = 2) :
    PSL(4, F) ≃* alternatingGroup (Fin 8) := by
  letI : Fintype F := Fintype.ofFinite F
  let e : F ≃+* ZMod 2 := FiniteField.ringEquivOfCardEq (by
    simpa only [← Nat.card_eq_fintype_card, Nat.card_zmod] using hF)
  exact (Atlas.fieldEquivPSL 4 e).trans
    Atlas.Comparisons.Exceptional.psl4TwoEquivAlt8

private theorem kernel_card_of_equiv_alt8
    {S : Type u} {L : Type v}
    [Group S] [Finite S] [IsQuasisimple S]
    [Group L] [Finite L] [IsQuasisimple L]
    (e : S ≃* alternatingGroup (Fin 8))
    (g : Covering L S) (hg : Covering.IsUniversal.{u, v, 0} g) :
    Nat.card g.toMonoidHom.ker = 2 := by
  let f : Covering (SchurAlternatingGroup 3) S :=
    (Covering.ofMulEquiv e.symm).comp (schurAlternatingCovering 3)
  have hf : Covering.IsUniversal.{u, 0, v} f :=
    (theorem_5_2_3_b_universality 3 (by decide) (by decide)).comp_ofMulEquiv e.symm
  have hfker : f.toMonoidHom.ker =
      (schurAlternatingCovering 3).toMonoidHom.ker := by
    ext x
    change e.symm (schurAlternatingCovering 3 x) = 1 ↔
      schurAlternatingCovering 3 x = 1
    exact e.symm.map_eq_one_iff
  have hfcard : Nat.card f.toMonoidHom.ker = 2 := by
    rw [hfker]
    exact natCard_ker_schurAlternatingCovering 3
  have hfg : Nat.card f.toMonoidHom.ker ∣ Nat.card g.toMonoidHom.ker :=
    kernel_card_dvd_of_surjective_factor g.toMonoidHom f.toMonoidHom
      (hg.lift f).toMonoidHom (hg.lift f).surjective
      (congrArg Covering.toMonoidHom (hg.lift_fac f))
  have hgf : Nat.card g.toMonoidHom.ker ∣ Nat.card f.toMonoidHom.ker :=
    kernel_card_dvd_of_surjective_factor f.toMonoidHom g.toMonoidHom
      (hf.lift g).toMonoidHom (hf.lift g).surjective
      (congrArg Covering.toMonoidHom (hf.lift_fac g))
  exact (Nat.dvd_antisymm hgf hfg).trans hfcard

/-- The actual kernel of a universal cover of a binary degree-four projective
group is C₂. The source and covering groups may lie in different universes. -/
noncomputable def kernelEquivTwo
    (F : Type w) [Field F] [Finite F] (hF : Nat.card F = 2)
    {S : Type u} {L : Type v}
    [Group S] [Finite S] [IsQuasisimple S]
    [Group L] [Finite L] [IsQuasisimple L]
    (e : S ≃* PSL(4, F)) (g : Covering L S)
    (hg : Covering.IsUniversal.{u, v, 0} g) :
    g.toMonoidHom.ker ≃* Multiplicative (ZMod 2) :=
  mulEquivOfPrimeCardEq
    (kernel_card_of_equiv_alt8 (e.trans (binaryEquivAlternatingEight F hF)) g hg)
    (by simp)

/-- The constructed universal perfect-cover kernel has the same C₂ structure.
Quasisimplicity is supplied by the actual equivalence with A₈. -/
noncomputable def schurMultiplierEquivTwo
    (F : Type w) [Field F] [Finite F] (hF : Nat.card F = 2)
    {S : Type u} [Group S] [Finite S] [Group.IsPerfect S]
    (e : S ≃* PSL(4, F)) :
    schurMultiplier S ≃* Multiplicative (ZMod 2) := by
  let e8 := e.trans (binaryEquivAlternatingEight F hF)
  letI : IsQuasisimple S := IsQuasisimple.of_mulEquiv e8.symm
  exact kernelEquivTwo F hF e (universalQuasisimpleCover S)
    (universalQuasisimpleCover_isUniversal S)

end Matrix.PSL4Two
