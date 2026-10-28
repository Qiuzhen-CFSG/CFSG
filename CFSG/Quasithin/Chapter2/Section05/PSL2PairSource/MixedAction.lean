module

public import CFSG.Quasithin.Chapter2.Section05.PSL2PairSource.InitialAction
public import Theory.GroupTheory.GeneralizedFitting.StandardComponent
public import Theory.GroupTheory.DihedralTwoCore
public import Theory.GroupTheory.SpecificGroups.OddDihedralAction
public import Theory.SpecificGroups.PSL2.PrimeAutomorphismCentralizer

/-!
# Faithful odd-dihedral action in the mixed case

Conjugating the proved C_J(K) calculation makes the kernel of C_G(tᵍ)
acting on Kᵍ a two-group. A nonabelian odd-dihedral subgroup of that
centralizer therefore acts faithfully. The application uses the literal
C_K(tᵍ) action on Kᵍ; its image is not assumed to be inner. Prime-field
PGL coverage and the matrix centralizer calculation make its automorphism
centralizer have exponent at most two.

Source: Aschbacher–Smith, proof of 2.5.21, printed p.567. The odd-dihedral
model of C_K(tᵍ) remains to be constructed from the outer-action case.
-/

public section

open Subgroup Theory.GroupTheory
open CFSG.Quasithin.Chapter16.CounterexampleGeometry
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter2.PSL2PairSource
universe u
variable {G : Type u} [Group G] [Finite G] {κ : GroupClass.{u}}
variable {p : ℕ} [Fact p.Prime]
namespace Incoming
variable (d : Incoming κ G p)

/-- The genuine involution centralizer normalizes the right conjugate of K. -/
theorem conjugate_normalized (g : G) :
    centralizer ({g⁻¹ * d.t * g} : Set G) ≤ normalizer (conjugate d.K g : Set G) :=
  CrossingPair.crossing_factor_normalized d.K d.t g d.j_normalizes_k

/-- The kernel in the conjugated involution centralizer remains a two-group. -/
theorem conjugate_relative_centralizer_isTwoGroup (g : G) :
    IsPGroup 2 (centralizer ({g⁻¹ * d.t * g} : Set G) ⊓
      centralizer (conjugate d.K g : Set G) : Subgroup G) := by
  have h := d.relative_centralizer_isTwoGroup.map (MulAut.conj g⁻¹).toMonoidHom
  rw [map_inf _ _ _ (MulAut.conj g⁻¹).injective,
    map_centralizer_equiv, map_centralizer_equiv] at h
  change IsPGroup 2 (centralizer ((MulAut.conj g⁻¹) '' ({d.t} : Set G)) ⊓
    centralizer ((MulAut.conj g⁻¹) '' (d.K : Set G)) : Subgroup G) at h
  rw [Set.image_singleton] at h
  rw [show (MulAut.conj g⁻¹) d.t = g⁻¹ * d.t * g by
    change g⁻¹ * d.t * (g⁻¹)⁻¹ = _
    rw [inv_inv]] at h
  exact h

/-- The odd-dihedral subgroup acts faithfully on the actual Kᵍ through the
literal conjugation map. No inner-image assertion is made or needed. -/
theorem odd_dihedral_action_injective (g : G) (D : Subgroup G)
    (hD : D ≤ centralizer ({g⁻¹ * d.t * g} : Set G))
    {n : ℕ} (hn : Odd n) (hne : n ≠ 1) (e : D ≃* DihedralGroup n) :
    Function.Injective ((conjugate d.K g).normalizerMonoidHom.comp
      (inclusion (hD.trans (d.conjugate_normalized g)))) := by
  let f := (conjugate d.K g).normalizerMonoidHom.comp
    (inclusion (hD.trans (d.conjugate_normalized g)))
  have hk : IsPGroup 2 f.ker := by
    let C := centralizer ({g⁻¹ * d.t * g} : Set G) ⊓ centralizer (conjugate d.K g : Set G)
    let r : f.ker →* C :=
      { toFun := fun a => ⟨a.val.val, hD a.val.property, by
          have ha : inclusion (hD.trans (d.conjugate_normalized g)) a.val ∈
              (conjugate d.K g).normalizerMonoidHom.ker := a.property
          rw [normalizerMonoidHom_ker] at ha
          exact ha⟩
        map_one' := rfl
        map_mul' := by intros; rfl }
    exact (d.conjugate_relative_centralizer_isTwoGroup g).of_injective r (by
      intro a b h
      have hr : a.val.val = b.val.val := congrArg (fun c : C => (c : G)) h
      exact Subtype.ext (Subtype.ext hr))
  exact Theory.GroupTheory.odd_dihedral_injective_of_two_kernel hn hne e f hk

/-- The literal C_K(tᵍ) action used in the mixed inner/outer case. The
remaining model transport supplies its odd-dihedral isomorphism. -/
theorem mixed_centralizer_action_injective (g : G)
    {n : ℕ} (hn : Odd n) (hne : n ≠ 1)
    (e : (d.K ⊓ centralizer ({g⁻¹ * d.t * g} : Set G) : Subgroup G) ≃*
      DihedralGroup n) :
    Function.Injective ((conjugate d.K g).normalizerMonoidHom.comp
      (inclusion ((show d.K ⊓ centralizer ({g⁻¹ * d.t * g} : Set G) ≤
        centralizer ({g⁻¹ * d.t * g} : Set G) from inf_le_right).trans
          (d.conjugate_normalized g)))) :=
  d.odd_dihedral_action_injective g _ inf_le_right hn hne e

/-- The centralizer of the faithful C_K(tᵍ) image has exponent at most two.
This uses the full prime-field automorphism group, including outer elements. -/
theorem mixed_action_centralizer_square (g : G)
    {n : ℕ} (hn : Odd n) (hne : n ≠ 1)
    (e : (d.K ⊓ centralizer ({g⁻¹ * d.t * g} : Set G) : Subgroup G) ≃*
      DihedralGroup n)
    {a : MulAut (conjugate d.K g)}
    (ha : a ∈ centralizer (((conjugate d.K g).normalizerMonoidHom.comp
      (inclusion ((show d.K ⊓ centralizer ({g⁻¹ * d.t * g} : Set G) ≤
        centralizer ({g⁻¹ * d.t * g} : Set G) from inf_le_right).trans
          (d.conjugate_normalized g)))).range : Set (MulAut (conjugate d.K g)))) :
    a ^ 2 = 1 := by
  let eQ : conjugate d.K g ≃* PSL(2, ZMod p) :=
    ((MulAut.conj g⁻¹).subgroupMap d.K).symm.trans d.model
  apply Theory.PSL2.prime_automorphism_centralizer_square
    (by have := d.prime_ge; omega) eQ _ _ ha
  exact Theory.GroupTheory.odd_dihedral_range_not_commutative hn hne e _
    (d.mixed_centralizer_action_injective g hn hne e)

end Incoming
end CFSG.Quasithin.Chapter2.PSL2PairSource

end
