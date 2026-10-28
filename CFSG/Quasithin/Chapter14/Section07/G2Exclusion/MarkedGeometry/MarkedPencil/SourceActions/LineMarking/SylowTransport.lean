module

public import CFSG.Quasithin.Chapter14.Section07.G2Exclusion.MarkedGeometry.MarkedPencil.SourceActions.LineMarking.Canonical
public import Theory.Representation.BinaryOffender.IrreducibleTransport

/-!
# Plane recognition for every derived Sylow

The existing positive-root Sylow is a Sylow subgroup of the actual
commutator subgroup of the octonion automorphism group. Sylow conjugacy
moves a supplied plane to the standard coordinates of `Canonical`. The
commutator actor is moved by the same conjugation; its difference span is
transported through the actual representation. Octonion multiplication
and the singular-line map then transport the conclusions back.

Source: Aschbacher–Smith 14.7.55(1), printed p.1066, PDF p.1083.
The model and root conventions are those of the attributed ATLAS port,
LICENSES/ATLAS.txt. `LineMarking` applies both results to the literal
source quotient.
-/

public noncomputable section

namespace CFSG.Quasithin.Chapter14.Section07.G2Exclusion.MarkedGeometry.MarkedPencil.SourceActions.LineMarking
open Atlas.G2 Atlas.G2.Explicit Atlas.SplitOctonion Atlas.G2.Natural
open Atlas.G2.BinaryParabolicPair
open Representation.BinaryOffender
open CFSG.Quasithin.Chapter14.Section07.G2Exclusion.MarkedGeometry
open Atlas.G2.EvenLocal.NormalizerCover.OctonionHexagon
open Atlas.G2.EvenLocal.NormalizerCover.OctonionHexagon.CosetIdentification

open Subgroup

private theorem exists_standard_conjugator (S : Sylow 2 DerivedModel) :
    ∃ g : Model (ZMod 2), derivedSylowAmbient.map (MulAut.conj g).toMonoidHom =
      (S : Subgroup DerivedModel).map DerivedModel.subtype := by
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq DerivedModel derivedSylow S
  have he : (derivedSylow : Subgroup DerivedModel).map (MulAut.conj g).toMonoidHom = S :=
    congrArg Sylow.toSubgroup hg
  refine ⟨g.val, ?_⟩
  rw [← derivedSylow_map_subtype, Subgroup.map_map, ← he, Subgroup.map_map]
  rfl

section Transport
variable {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    (ρ : Representation (ZMod 2) (Model (ZMod 2)) W)

private theorem rep_inv_apply (g : Model (ZMod 2)) (v : W) : ρ g⁻¹ (ρ g v) = v := by
  rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]

private theorem rep_injective (g : Model (ZMod 2)) : Function.Injective (ρ g) :=
  Function.LeftInverse.injective (rep_inv_apply ρ g)

private theorem map_inverse (P : Submodule (ZMod 2) W) (g : Model (ZMod 2)) :
    (P.map (ρ g⁻¹)).map (ρ g) = P := by
  rw [← Submodule.map_comp]
  have he : (ρ g).comp (ρ g⁻¹) = LinearMap.id := by
    ext v
    change ρ g (ρ g⁻¹ v) = v
    simpa only [inv_inv] using rep_inv_apply ρ g⁻¹ v
  rw [he, Submodule.map_id]

private theorem conjugation_intertwines (g a : Model (ZMod 2)) (v : W) :
    ρ a (ρ g⁻¹ v) = ρ g⁻¹ (ρ (MulAut.conj g a) v) := by
  simp only [MulAut.conj_apply, ← Module.End.mul_apply, ← map_mul]
  congr 2
  group

private theorem standard_invariant (P : Submodule (ZMod 2) W) (g : Model (ZMod 2))
    (hP : derivedSylowAmbient.map (MulAut.conj g).toMonoidHom ≤ subspaceStabilizer ρ P) :
    derivedSylowAmbient ≤ subspaceStabilizer ρ (P.map (ρ g⁻¹)) := by
  apply le_subspaceStabilizer
  rintro a ha _ ⟨v, hv, rfl⟩
  rw [conjugation_intertwines]
  exact ⟨ρ (MulAut.conj g a) v, (hP (mem_map_of_mem _ ha) v).mpr hv, rfl⟩

private theorem standard_commutator (P : Submodule (ZMod 2) W) (g : Model (ZMod 2))
    (X : Subgroup (Model (ZMod 2))) (hX : subspaceCommutator ρ P X = P) :
    subspaceCommutator ρ (P.map (ρ g⁻¹)) (X.comap (MulAut.conj g).toMonoidHom) =
      P.map (ρ g⁻¹) := by
  rw [subspaceCommutator_map_embedding ρ ρ (MulAut.conj g).toMonoidHom (ρ g⁻¹)
    (conjugation_intertwines ρ g),
    Subgroup.map_comap_eq_self_of_surjective (MulAut.conj g).surjective, hX]

private theorem map_card (P : Submodule (ZMod 2) W) (g : Model (ZMod 2)) :
    Nat.card (P.map (ρ g)) = Nat.card P :=
  (Nat.card_congr (Submodule.equivMapOfInjective (ρ g) (rep_injective ρ g) P).toEquiv).symm

end Transport

theorem weyl_sylow_zeroProduct
    (P : Submodule (ZMod 2) (TraceZero (ZMod 2))) (hc : Nat.card P = 4)
    (S : Sylow 2 DerivedModel)
    (hP : (S : Subgroup DerivedModel).map DerivedModel.subtype ≤
      subspaceStabilizer (traceZeroAction (ZMod 2)) P)
    (X : Subgroup (Model (ZMod 2)))
    (hX : subspaceCommutator (traceZeroAction (ZMod 2)) P X = P) :
    ∀ x ∈ P, ∀ y ∈ P, Atlas.SplitOctonion.mul x.val y.val = 0 := by
  obtain ⟨g, hg⟩ := exists_standard_conjugator S
  rw [← hg] at hP
  have hz := weyl_canonical_zeroProduct (P.map (traceZeroAction (ZMod 2) g⁻¹))
    ((map_card _ P g⁻¹).trans hc) (standard_invariant _ P g hP)
    (X.comap (MulAut.conj g).toMonoidHom) (standard_commutator _ P g X hX)
  intro x hx y hy
  have hxy := hz _ (Submodule.mem_map_of_mem hx) _ (Submodule.mem_map_of_mem hy)
  apply (g⁻¹).val.injective
  rw [map_zero, automorphism_mul]
  exact hxy

theorem natural_sylow_line
    (P : Submodule (ZMod 2) (Space (ZMod 2))) (hc : Nat.card P = 4)
    (S : Sylow 2 DerivedModel)
    (hP : (S : Subgroup DerivedModel).map DerivedModel.subtype ≤
      subspaceStabilizer (action (ZMod 2)) P) :
    ∃ L : ZeroProductLine (ZMod 2), naturalMap.line L = P := by
  obtain ⟨g, hg⟩ := exists_standard_conjugator S
  rw [← hg] at hP
  have he := natural_canonical_line (P.map (action (ZMod 2) g⁻¹))
    ((map_card _ P g⁻¹).trans hc) (standard_invariant _ P g hP)
  refine ⟨g • standardLine, ?_⟩
  rw [naturalMap.line_equivariant (action (ZMod 2)) naturalMap_equivariant,
    he, map_inverse]

end CFSG.Quasithin.Chapter14.Section07.G2Exclusion.MarkedGeometry.MarkedPencil.SourceActions.LineMarking
