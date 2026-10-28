module
public import Theory.GroupTheory.Recognition.JankoFour.SourceComparison.OverlapCohomology
public import Theory.Mathieu.M22.ChapterHLocalClassification.HexadAction
public import Theory.Representation.FirstCohomologyAutomorphism.Cocycle
public import Theory.Representation.FirstCohomologyLinearTransport

/-!
# Cohomology and radical fixers in the actual native hexad group

Compose the existing natural marking of the native outer hexad kernel with
the concrete polar isomorphism S6 to Sp4(2). This retains its intrinsic
kernel, original quotient map and literal conjugation on the sixteen-group.
An automorphism fixing that kernel pointwise fixes the faithful quotient
action as well. Its actual displacement therefore descends to a cocycle;
the full symplectic calculation gives one quadratic and one principal term.

Source: Aschbacher–Segev, Invent. Math. 105 (1991), (8.2), p.606.
This is the cohomology step of the overlap automorphism analysis; it does
not assert that every automorphism of the original overlap fixes its core.
-/

@[expose] public section
namespace Theory.GroupTheory.Recognition.JankoFour.SourceComparison.OverlapCohomology
open Subgroup Matrix Representation Representation.OneCohomology
open Representation.OneCohomology.SymplecticFour
open Sporadic.Mathieu.M22ChapterH.Hexad.Action
open HexadSymplecticComparison.PolarModel

noncomputable def nativeActor : Outer →* Sp :=
  sixToSymplectic.toMonoidHom.comp Natural.outerMap

noncomputable def nativeCoordinates : pCore 2 Outer ≃* Multiplicative V :=
  Natural.outerCore.trans deletedToPolar.toAddEquiv.toMultiplicative

theorem nativeActor_surjective : Function.Surjective nativeActor :=
  sixToSymplectic.surjective.comp Natural.outerMap_surjective

theorem nativeActor_ker : nativeActor.ker = pCore 2 Outer := by
  ext g
  change sixToSymplectic (Natural.outerMap g) = 1 ↔ g ∈ pCore 2 Outer
  rw [sixToSymplectic.map_eq_one_iff]
  exact congrArg (fun N : Subgroup Outer => g ∈ N) Natural.outerMap_ker |> Iff.of_eq

theorem nativeCoordinates_conjugation (g : Outer) (n : pCore 2 Outer) :
    (nativeCoordinates (MulAut.conjNormal g n)).toAdd =
      natural (nativeActor g) (nativeCoordinates n).toAdd := by
  change deletedToPolar (Natural.outerCore (MulAut.conjNormal g n)).toAdd = _
  exact (congrArg deletedToPolar (Natural.outerCore_conjugation g n)).trans
    (deletedToPolar_equivariant (Natural.outerMap g) (Natural.outerCore n).toAdd)

theorem nativeCoordinates_conjugation_symm (g : Outer) (v : V) :
    (nativeCoordinates.symm (Multiplicative.ofAdd (natural (nativeActor g) v)) : Outer) =
      g * (nativeCoordinates.symm (Multiplicative.ofAdd v) : Outer) * g⁻¹ := by
  have he := nativeCoordinates_conjugation g (nativeCoordinates.symm (Multiplicative.ofAdd v))
  rw [nativeCoordinates.apply_symm_apply] at he
  have ht := congrArg nativeCoordinates.symm (congrArg Multiplicative.ofAdd he)
  change nativeCoordinates.symm (nativeCoordinates _) =
    nativeCoordinates.symm (Multiplicative.ofAdd (natural (nativeActor g) v)) at ht
  rw [nativeCoordinates.symm_apply_apply] at ht
  exact (congrArg Subtype.val ht).symm

/-- Fixing the actual elementary radical forces identity on its faithful quotient action. -/
theorem nativeActor_fixed (α : MulAut Outer)
    (hfix : ∀ n ∈ pCore 2 Outer, α n = n) (g : Outer) :
    nativeActor (α g) = nativeActor g := by
  apply Subtype.ext
  apply Matrix.ext_iff_mulVec.mpr
  intro v
  apply Multiplicative.ofAdd.injective
  apply nativeCoordinates.symm.injective
  apply Subtype.ext
  change (nativeCoordinates.symm (Multiplicative.ofAdd (natural (nativeActor (α g)) v)) : Outer) =
    (nativeCoordinates.symm (Multiplicative.ofAdd (natural (nativeActor g) v)) : Outer)
  rw [nativeCoordinates_conjugation_symm,nativeCoordinates_conjugation_symm]
  let n := nativeCoordinates.symm (Multiplicative.ofAdd v)
  have hn := hfix n.val n.property
  have hc := hfix _ ((inferInstance : (pCore 2 Outer).Normal).conj_mem n.val n.property g)
  rw [map_mul,map_mul,map_inv,hn] at hc
  exact hc

/-- Every radical fixer has a quadratic displacement plus one principal displacement. -/
theorem native_automorphism_normal_form (α : MulAut Outer)
    (hfix : ∀ n ∈ pCore 2 Outer, α n = n) :
    ∃ (t : ZMod 2) (v : V), ∀ g : Outer,
      α g = (nativeCoordinates.symm (Multiplicative.ofAdd
        (t • quadraticCocycle.val (nativeActor g) +
          (natural (nativeActor g) v - v))) : Outer) * g := by
  have hd (g : Outer) : α g * g⁻¹ ∈ pCore 2 Outer := by
    rw [←nativeActor_ker,MonoidHom.mem_ker,map_mul,map_inv,nativeActor_fixed α hfix,mul_inv_cancel]
  obtain ⟨c,hc⟩ := exists_automorphism_cocycle_of_subkernel (pCore 2 Outer)
    nativeActor nativeActor_surjective nativeCoordinates natural nativeCoordinates_conjugation_symm
    α hd (by simpa only [nativeActor_ker] using hfix)
  obtain ⟨t,v,hv⟩ := full_normal_form c
  refine ⟨t,v,fun g => ?_⟩
  have he := hc g
  rw [hv] at he
  change t • quadraticCocycle.val (nativeActor g) + (natural (nativeActor g) v-v) = _ at he
  have hh := congrArg (fun x : V => (nativeCoordinates.symm (Multiplicative.ofAdd x) : Outer)) he
  change _ = ((nativeCoordinates.symm (nativeCoordinates ⟨α g*g⁻¹,hd g⟩)) : Outer) at hh
  rw [nativeCoordinates.symm_apply_apply] at hh
  exact (mul_inv_eq_iff_eq_mul.mp hh.symm)

noncomputable def nativeRepresentation : Representation (ZMod 2) (Outer ⧸ pCore 2 Outer) Space :=
  LinearEquiv.automorphismGroup.toLinearMapMonoidHom.comp outerQuotientAction

noncomputable def nativeQuotient : (Outer ⧸ pCore 2 Outer) ≃* Sp :=
  Natural.outerMarking.trans sixToSymplectic

noncomputable def nativeSpace : Space ≃ₗ[ZMod 2] V :=
  Natural.spaceCoordinates.trans deletedToPolar

theorem nativeSpace_equivariant (g : Outer ⧸ pCore 2 Outer) (v : Space) :
    nativeSpace (nativeRepresentation g v) = natural (nativeQuotient g) (nativeSpace v) := by
  change deletedToPolar (Natural.spaceCoordinates (outerQuotientAction g v)) = _
  rw [Natural.outerQuotientAction_natural,deletedToPolar_equivariant]
  rfl

/-- The dimension-one calculation for the literal native hexad radical action. -/
theorem native_finrank_H1 : Module.finrank (ZMod 2) (H1 nativeRepresentation) = 1 := by
  rw [(H1Congr nativeRepresentation natural nativeQuotient nativeSpace nativeSpace_equivariant).finrank_eq]
  exact full_finrank_H1

end Theory.GroupTheory.Recognition.JankoFour.SourceComparison.OverlapCohomology
