module
public import Theory.Mathieu.M24.LocalGeometry.FourNormalizers.Overgroups.Certificates
public import Theory.Mathieu.M24.LocalGeometry.PairOvergroups.QuotientConstruction.AffineCoverage

/-!
# Characteristic two for the fixed-octad trio stabilizer

Conjugation identifies the literal stabilizer with the standard trio stabilizer.
The affine quotient has a normal translation kernel that is a two-group.
All six generators of `EvenCandidates.elementary 0` lie in its pullback,
so they lie in the intrinsic two-core. An element centralizing this core
centralizes those generators; the existing permutation certificate makes
its square the identity. The core centralizer is therefore a normal
two-subgroup and is contained in the core.

This argument requires neither the full order of the trio stabilizer nor
an identification of its entire two-core with the six-generator candidate.
The affine coverage uses the actual native Witt-design geometry.
Source context: Aschbacher--Smith 15.3.43, printed p.1140; GLS3, Table 5.3e;
Aschbacher, *Sporadic Groups*, Lemma 20.2, for the affine trio structure.
-/

@[expose] public section
namespace Sporadic.Mathieu.M24LocalGeometry.FourNormalizers
open Subgroup PairOvergroups PairOvergroups.QuotientConstruction
open scoped Pointwise

/-- The actual stabilizer of the three fixed octads of row 3. -/
noncomputable def trioGroup : Subgroup M24 := MulAction.stabilizer M24 (rowGeometry 2)

/-- Conjugation by the certified native transporter identifies the two stabilizers. -/
noncomputable def trioEquiv : trioGroup ≃* trioStabilizer standardTrio :=
  MulAction.stabilizerEquivStabilizer transport_geometry.symm

theorem trioEquiv_apply (g : trioGroup) :
    (trioEquiv g).val = certificateElement 0 * g.val * (certificateElement 0)⁻¹ :=
  MulAction.stabilizerEquivStabilizer_apply transport_geometry.symm g

private noncomputable def trioHom : trioGroup →* QuotientModel :=
  (affineQuotient affineCoverage).comp trioEquiv.toMonoidHom

private theorem trioHom_kernel_isPGroup : IsPGroup 2 trioHom.ker := by
  intro u
  have hu : affineQuotient affineCoverage (trioEquiv u.val) = 1 := by
    have hu := u.property
    change trioHom u.val = 1 at hu
    simpa only [trioHom, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom] using hu
  let v : (affineQuotient affineCoverage).ker := ⟨trioEquiv u.val, hu⟩
  obtain ⟨n, hn⟩ := affineQuotient_kernel_isPGroup affineCoverage v
  refine ⟨n, ?_⟩
  apply Subtype.ext
  apply trioEquiv.injective
  simpa only [map_pow, map_one, Subgroup.coe_pow, Subgroup.coe_one] using
    congrArg Subtype.val hn

private noncomputable def trioGenerator (j : Fin 6) : trioGroup :=
  ⟨EvenCandidates.generator 0 j, elementary_generator_mem_trio j⟩

private theorem trioGenerator_mem_kernel (j : Fin 6) : trioGenerator j ∈ trioHom.ker := by
  change affineQuotient affineCoverage (trioEquiv (trioGenerator j)) = 1
  apply affineQuotient_eq affineCoverage (t := translationVector j)
  intro i v
  rw [trioEquiv_apply]
  simpa only [trioGenerator, Prod.fst_one, Prod.snd_one,
    Equiv.Perm.one_apply, map_one, LinearEquiv.coe_one, id_eq] using generator_translation j i v

private theorem trioGenerator_mem_core (j : Fin 6) : trioGenerator j ∈ pCore 2 trioGroup :=
  (le_sSup ⟨inferInstance, trioHom_kernel_isPGroup⟩ : trioHom.ker ≤ pCore 2 trioGroup)
    (trioGenerator_mem_kernel j)

/-- The intrinsic two-core of the fixed-octad trio stabilizer is self-centralizing.
The transported elementary candidate lies in the affine translation kernel,
so its permutation-centralizer certificate controls the core centralizer. -/
theorem trio_core_selfCentralizing :
    centralizer (pCore 2 trioGroup : Set trioGroup) ≤ pCore 2 trioGroup := by
  have hp : IsPGroup 2 (centralizer (pCore 2 trioGroup : Set trioGroup)) := by
    intro g
    refine ⟨1, ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    apply Subtype.ext
    change (g.val.val.val : Equiv.Perm (Fin 24)) ^ 2 = 1
    apply EvenCandidates.square_eq_one_of_commute 0
    intro j x
    have hc := g.property (trioGenerator j) (trioGenerator_mem_core j)
    have he := congrArg (fun a : trioGroup => a.val.val x) hc
    change (EvenCandidates.generator 0 j).val (g.val.val.val x) =
      g.val.val.val ((EvenCandidates.generator 0 j).val x) at he
    simpa only [EvenCandidates.generator_apply] using he.symm
  exact le_sSup ⟨inferInstance, hp⟩

end Sporadic.Mathieu.M24LocalGeometry.FourNormalizers
