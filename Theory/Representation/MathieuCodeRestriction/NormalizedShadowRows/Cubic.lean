module
public import Theory.Representation.MathieuCodeRestriction.OddFixedSpaces.SixPoint.Normalizer.Quotient
public import Theory.Representation.MathieuCodeRestriction.CodeLocal.CentralizerGeometry.SectionAction
public import Theory.Representation.MathieuCodeRestriction.OddFixedSpaces.Spectrum
public import Theory.Representation.MathieuCodeRestriction.Duality
public import Theory.Representation.BinaryOffender.EquivariantOffender

/-!
# Pointwise centralizer of a cubic fixed code space

Six invariant octads distinguish each of the six fixed points of the standard
cubic from every other point. Fixing their code classes therefore fixes those
points, whose pointwise stabilizer is the cubic itself. Native conjugacy and
code--cocode duality give the result for every cubic of displacement six.
All octad checks are small kernel-checked finite calculations.

This proves Aschbacher--Smith H.16.6, printed pp.404--405,
refs/quasithin.pdf. The argument avoids the incorrect identification of the
sextet four-space centralizer with the intrinsic two-core in its printed proof.
-/

public noncomputable section
open Sporadic.Mathieu Sporadic.Mathieu.M24LocalGeometry
open Representation.BinaryOffender Subgroup
open scoped Pointwise
namespace MathieuCode.NormalizedShadowRows.Cubic

private def octadMessage : Fin 6 → Fin 4096 := ![1312,1156,466,3456,1928,1409]

private theorem octad_card : ∀ j, (m24GolayWord (octadMessage j)).card = 8 := by
  decide +kernel

private def fixedOctad (j : Fin 6) : Octad :=
  ⟨m24GolayWord (octadMessage j), m24GolayWord_mem_blocks_of_card_eq_eight _ (octad_card j)⟩

private theorem fixedOctad_fixed : ∀ j, SixPoint.cubicRepresentative.val • (fixedOctad j).val = (fixedOctad j).val := by
  decide +kernel

private theorem fixedOctad_recover : ∀ x y : Fin 24,
    SixPoint.cubicRepresentative.val x = x →
    (∀ j : Fin 6, x ∈ (fixedOctad j).val ↔ y ∈ (fixedOctad j).val) → x = y := by
  decide +kernel

private theorem representative_kernel_le :
    subspaceKernel codeRepresentation (fixedSpace codeRepresentation SixPoint.cubicSubgroup) ⊤ ≤
      SixPoint.cubicSubgroup := by
  intro g hg
  rw [← SixPoint.cubic_fixedPointStabilizer]
  apply (mem_fixingSubgroup_iff M24).mpr
  intro x hx
  have hx' : SixPoint.cubicRepresentative.val x = x :=
    (SixPoint.mem_fixedPoint_zpowers_iff _ _).mp hx
  apply (fixedOctad_recover x (g • x) hx' ?_).symm
  intro j
  have hv : octadVector (fixedOctad j) ∈ fixedSpace codeRepresentation SixPoint.cubicSubgroup := by
    have hy : SixPoint.cubicRepresentative ∈ octadStabilizer (fixedOctad j) := fixedOctad_fixed j
    intro a
    exact octadVector_fixed_stabilizer _ ⟨a.val, zpowers_le.mpr hy a.property⟩
  have hgj := (SectionAction.octadVector_fixed_iff (fixedOctad j) g).mp (hg.2 _ hv)
  constructor
  · intro hxj
    exact MulAction.mem_stabilizer_finset'.mp hgj hxj
  · intro h
    have hh := MulAction.mem_stabilizer_finset'.mp ((octadStabilizer (fixedOctad j)).inv_mem hgj) h
    simpa only [inv_smul_smul] using hh

/-- The full native pointwise centralizer of a six-fixed-point cubic code space. -/
theorem fixedSpace_kernel_eq (D : Subgroup M24) (hD : Nat.card D = 3)
    (hfix : Nat.card (SixPoint.FixedPoint D) = 6) :
    subspaceKernel codeRepresentation (fixedSpace codeRepresentation D) ⊤ = D := by
  apply le_antisymm
  · intro g hg
    obtain ⟨t,ht⟩ := SixPoint.cubicSubgroup_conjugacy D hD hfix
    have hb (v : Code) (hv : v ∈ fixedSpace codeRepresentation SixPoint.cubicSubgroup) :
        codeRepresentation t⁻¹ v ∈ fixedSpace codeRepresentation D := by
      intro a
      have h := hv ⟨t*a.val*t⁻¹,ht ▸ ⟨a.val,a.property,rfl⟩⟩
      change codeRepresentation (t*a.val*t⁻¹) v = v at h
      change codeRepresentation a.val (codeRepresentation t⁻¹ v) = codeRepresentation t⁻¹ v
      have h' := congrArg (codeRepresentation t⁻¹) h
      simpa only [map_mul,Module.End.mul_apply,codeRepresentation.inv_self_apply] using h'
    have hc : t*g*t⁻¹ ∈ SixPoint.cubicSubgroup := by
      apply representative_kernel_le
      refine ⟨mem_top _,?_⟩
      intro v hv
      simp only [map_mul,Module.End.mul_apply,hg.2 _ (hb v hv),codeRepresentation.self_inv_apply]
    have hm : (MulAut.conj t).toMonoidHom g ∈ D.map (MulAut.conj t).toMonoidHom := ht ▸ hc
    obtain ⟨d,hd,he⟩ := hm
    exact (MulAut.conj t).injective he ▸ hd
  · intro g hg
    exact ⟨mem_top _,fun v hv => hv ⟨g,hg⟩⟩

/-- H.16.6 on the whole native code and the full acting group. -/
theorem fixedSpace_kernel_eq_of_displacement_six (D : Subgroup M24)
    (hD : Nat.card D = 3) (hd : fixedCodim codeRepresentation D = 6) :
    subspaceKernel codeRepresentation (fixedSpace codeRepresentation D) ⊤ = D := by
  let : IsCyclic D := isCyclic_of_prime_card (p := 3) hD
  have hd' : fixedCodim cocodeRepresentation D = 6 := by
    rwa [← code_cocode_fixedCodim_cyclic]
  exact fixedSpace_kernel_eq D hD ((cocode_fixedCodim_eq_six_iff D (by decide) (by decide) hD).mp hd').2

/-- H.16.6 transports through a marking of the full actor and whole code.
The pointwise kernel is taken in the original acting group. -/
theorem fixedSpace_kernel_eq_equivariant
    {X U : Type*} [Group X] [Finite X] [AddCommGroup U] [Module (ZMod 2) U]
    [FiniteDimensional (ZMod 2) U] (ρ : Representation (ZMod 2) X U)
    (a : X ≃* M24) (E : U ≃ₗ[ZMod 2] Code)
    (hE : ∀ g v, E (ρ g v) = codeRepresentation (a g) (E v))
    (Y : Subgroup X) (hY : Nat.card Y = 3) (hd : fixedCodim ρ Y = 6) :
    subspaceKernel ρ (fixedSpace ρ Y) ⊤ = Y := by
  have hc : Nat.card (Y.map a.toMonoidHom) = 3 := by
    rwa [card_map_of_injective a.injective]
  have hd' : fixedCodim codeRepresentation (Y.map a.toMonoidHom) = 6 := by
    rwa [← fixedCodim_map_equivariant ρ codeRepresentation a.toMonoidHom E hE]
  have hk := fixedSpace_kernel_eq_of_displacement_six _ hc hd'
  apply le_antisymm
  · intro g hg
    have hm : a g ∈ Y.map a.toMonoidHom := by
      rw [← hk]
      refine ⟨mem_top _, ?_⟩
      intro w hw
      rw [← fixedSpace_map_equivariant ρ codeRepresentation a.toMonoidHom E hE] at hw
      obtain ⟨v,hv,rfl⟩ := hw
      exact (hE g v).symm.trans (congrArg E (hg.2 _ hv))
    obtain ⟨y,hy,he⟩ := hm
    exact a.injective he ▸ hy
  · intro g hg
    exact ⟨mem_top _,fun v hv => hv ⟨g,hg⟩⟩

end MathieuCode.NormalizedShadowRows.Cubic
