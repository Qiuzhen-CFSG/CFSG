module

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.LinearThree.ExternalModules.OuterActors.Context
public import Theory.Representation.PSL3Two.SingerDisplacement
public import Theory.Representation.BinaryOffender.EquivariantOffender
public import Mathlib.GroupTheory.GroupAction.ConjAct

/-!
# Displacement of paired-module outer involutions

An outer involution on the actual component has a commutator conjugate to the
specified Singer element of SL₃(2). That element displaces at least twelve
dimensions on two adjoint modules, or on two natural and two dual modules.
The genuine component intertwining equivalence transports this bound to the
ambient representation. Since a commutator displaces at most twice as many
dimensions as its first entry, the involution displaces at least six.

This proves the outer-involution calculation needed for Aschbacher–Smith
13.8.21(1), printed p.956 (combined manuscript of 1 March 2004), using the
concrete H.6.1 models. The argument uses the actual component automorphism and
restriction maps; the paired bound and quadratic-ratio assembly stay with the
outer-actor owner.
-/

public section
open Representation Representation.BinaryOffender
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.LinearThree.ExternalModules.OuterActors
open Matrix.PSL3Two.OuterInvolutionSinger BinaryLinearThree.SingerDisplacement
variable {H U : Type*} [Group H] [AddCommGroup U] [Module (ZMod 2) U]

private theorem fixedCodim_equiv {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    (ρ : Representation (ZMod 2) BinaryLinearThree.Group U)
    (τ : Representation (ZMod 2) BinaryLinearThree.Group V)
    (e : ρ.Equiv τ) (A : Subgroup BinaryLinearThree.Group) :
    fixedCodim ρ A = fixedCodim τ A := by
  simpa only [Subgroup.map_id] using fixedCodim_map_equivariant ρ τ
    (MonoidHom.id _) e.toLinearEquiv (fun g v => LinearMap.congr_fun (e.isIntertwining' g) v) A

/-- Either actual paired restriction displaces at least twelve dimensions on the Singer element. -/
theorem paired_singer_fixedCodim_ge_twelve
    (ρ : Representation (ZMod 2) BinaryLinearThree.Group U)
    (h : PairedAlternatives ρ) : 12 ≤ fixedCodim ρ (Subgroup.zpowers singer) := by
  rcases h with hs | hn
  · obtain ⟨e⟩ := hs
    rw [fixedCodim_equiv (V := BinaryLinearThree.Steinberg × BinaryLinearThree.Steinberg)
      ρ pairedSteinberg e, fixedCodim_prod]
    have hs : 6 ≤ fixedCodim BinaryLinearThree.S (Subgroup.zpowers singer) :=
      six_le_fixedCodim_singer_steinberg
    omega
  · obtain ⟨e⟩ := hn
    rw [fixedCodim_equiv ρ pairedNaturalDual e]
    change 12 ≤ fixedCodim ((BinaryLinearThree.W.prod BinaryLinearThree.W.dual).prod
      (BinaryLinearThree.W.prod BinaryLinearThree.W.dual)) (Subgroup.zpowers singer)
    rw [fixedCodim_prod, fixedCodim_prod, fixedCodim_singer_natural, fixedCodim_singer_dual]

variable [FiniteDimensional (ZMod 2) U]

/-- An involution outer on the component displaces at least six dimensions on a paired module. -/
theorem outer_involution_fixedCodim_ge_six
    (σ : Representation (ZMod 2) H U) (K X : Subgroup H)
    (eK : K ≃* BinaryLinearThree.Group) (h : PairedSetup σ K X eK)
    (a : H) (ha : a^2 = 1)
    (_haX : a ∈ Subgroup.centralizer (X : Set H)) (hout : OuterOnComponent K a) :
    6 ≤ fixedCodim σ (Subgroup.zpowers a) := by
  let : K.Normal := h.component_normal
  let α : MulAut BinaryLinearThree.Group := MulAut.congr eK (MulAut.conjNormal a)
  have hsquare : α^2 = 1 := by
    dsimp only [α]
    rw [← map_pow, ← map_pow, ha, map_one, map_one]
  have houter : ∀ g, α ≠ MulAut.conj g := by
    intro g hg
    apply hout
    refine ⟨eK.symm g, ?_⟩
    intro u
    have hh := congrArg (fun β : MulAut BinaryLinearThree.Group => eK.symm (β (eK u))) hg
    have hh' := congrArg (fun k : K => k.val) hh
    simpa [α, MulAut.congr, MulAut.conj_apply] using hh'
  have haction (g : BinaryLinearThree.Group) :
      (eK.symm (α g)).val = a * (eK.symm g).val * a⁻¹ := by
    simp [α, MulAut.conjNormal_apply]
  obtain ⟨b, c, hbc⟩ := exists_commutator_conjugate_singer α hsquare houter
  let f : BinaryLinearThree.Group →* H := K.subtype.comp eK.symm.toMonoidHom
  have hcomm : a * f b * a⁻¹ * (f b)⁻¹ = f (c * singer * c⁻¹) := by
    rw [← hbc, map_mul, map_inv]
    congr 1
    exact (haction b).symm
  have hcod : fixedCodim (componentAction σ K eK) (Subgroup.zpowers (c * singer * c⁻¹)) =
      fixedCodim σ (Subgroup.zpowers (f (c * singer * c⁻¹))) := by
    change fixedCodim (σ.comp f) _ = _
    unfold fixedCodim
    rw [fixedSpace_comp_map, f.map_zpowers]
  have hlower : 12 ≤ fixedCodim σ (Subgroup.zpowers (a * f b * a⁻¹ * (f b)⁻¹)) := by
    rw [hcomm, ← hcod, fixedCodim_zpowers_conj]
    exact paired_singer_fixedCodim_ge_twelve _ h.paired
  have hupper := fixedCodim_commutator_le_twice σ a (f b)
  omega
end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.LinearThree.ExternalModules.OuterActors
