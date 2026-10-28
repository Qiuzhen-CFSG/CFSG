module
public import Theory.Mathieu.M22.CubicHexad.Basic
import all Theory.Mathieu.M22.CubicHexad.Basic

/-!
# Automorphism invariance of the cubic M₂₂ hexad pair

An automorphism preserving the marked Sylow subgroup comes from the full
hexad design group. The Sylow contains the pointwise hexad kernel, so its
normalizer fixes that unique hexad. Restriction to its six points and the
checked small normalizer calculation then fix the pair and its three-pair
partition separately. Thus both cubic subgroups are invariant.

Source: Aschbacher–Smith 14.3.6(6), printed p.994. This argument includes
the outer design automorphism and makes no inner-action assumption.
-/

public section
open Subgroup MulAction
open scoped Pointwise
namespace Sporadic.Mathieu.M22CubicHexad
open M22ValueBound.Concrete M22ValueBound.Concrete.PartitionStructure M22SolvableSylow

private theorem design_preserves_marks (g : m22DesignAut)
    (hg : (fixedSylow : Subgroup M22).map (m22DesignAutToAut g).toMonoidHom = fixedSylow) :
    g • m22Hexad123 = m22Hexad123 ∧ g • m22Pair12 = m22Pair12 ∧
      g • hexadPartition = hexadPartition := by
  let a := m22DesignAutToAut g
  have hcomp : (MulAut.conj g).toMonoidHom.comp inclusion =
      inclusion.comp a.toMonoidHom := by
    apply MonoidHom.ext
    intro x
    apply Subtype.ext
    exact (m22DesignAutToAut_apply_perm g x).symm
  have hn : g ∈ normalizer ((fixedSylow : Subgroup M22).map inclusion : Set m22DesignAut) := by
    rw [mem_normalizer_iff_map_conj_eq]
    change ((fixedSylow : Subgroup M22).map inclusion).map
      (MulAut.conj g).toMonoidHom = _
    rw [map_map, hcomp, ← map_map, hg]
  have hPH : (fixedSylow : Subgroup M22) ≤ stabilizer M22 m22Hexad123 :=
    inf_le_right.trans second_le_hexad
  have hhex : g • m22Hexad123 = m22Hexad123 :=
    normalizer_le_hexad_stabilizer m22Hexad123_mem fixedSylow hPH
      (kernel_le_of_sylow m22Hexad123_mem fixedSylow hPH) hn
  let p : Equiv.Perm m22Hexad123 := onFinset m22Hexad123 ⟨g, hhex⟩
  have hc (q : Equiv.Perm m22Hexad123) (hq : q ∈ smallMarked) :
      p * q * p⁻¹ ∈ smallMarked := by
    have hqr : q ∈ (m22SetAction m22Hexad123).range := by
      rw [restriction_range]
      exact hq.1.2
    obtain ⟨x, hx⟩ := hqr
    have hxp : x.val ∈ (fixedSylow : Subgroup M22) := by
      change x ∈ (first ⊓ second).subgroupOf (stabilizer M22 m22Hexad123)
      rw [← intersection_preimage]
      change m22SetAction m22Hexad123 x ∈ smallMarked
      rwa [hx]
    have hax : a x.val ∈ (fixedSylow : Subgroup M22) := by
      rw [← hg]
      exact mem_map_of_mem _ hxp
    let y : stabilizer M22 m22Hexad123 := ⟨a x.val, hPH hax⟩
    have hy : m22SetAction m22Hexad123 y ∈ smallMarked := by
      change y ∈ smallMarked.comap (m22SetAction m22Hexad123)
      rw [intersection_preimage]
      exact hax
    have he : m22SetAction m22Hexad123 y = p * q * p⁻¹ := by
      rw [← hx]
      apply Equiv.ext
      intro z
      apply Subtype.ext
      change ((m22DesignAutToAut g) x.val : Equiv.Perm (Fin 22)) z.val = _
      rw [m22DesignAutToAut_apply_perm]
      rfl
    rwa [he] at hy
  obtain ⟨hp, hpart⟩ := small_normalizer_certificate p (hc r r_mem) (hc s s_mem)
  have hagrees {S : Finset (Fin 22)} (hS : S ⊆ m22Hexad123) :
      Equiv.Perm.ofSubtype p • S = g • S := by
    simp only [Finset.smul_finset_def]
    apply Finset.image_congr
    intro x hx
    exact Equiv.Perm.ofSubtype_apply_of_mem _ (hS hx)
  have hepart : Equiv.Perm.ofSubtype p • hexadPartition = g • hexadPartition := by
    rw [Finset.smul_finset_def, Finset.smul_finset_def]
    apply Finset.image_congr
    intro S hS
    exact hagrees (subset_hexad_of_mem hS)
  exact ⟨hhex, (hagrees (subset_hexad_of_mem pair_mem_hexadPartition)).symm.trans hp,
    hepart.symm.trans hpart⟩

private theorem map_stabilizer_design {A : Type*} [MulAction m22DesignAut A]
    [MulAction M22 A] (X : A) (g : m22DesignAut)
    (hact : ∀ u : M22, ∀ x : A, inclusion u • x = u • x) :
    (stabilizer M22 X).map (m22DesignAutToAut g).toMonoidHom =
      stabilizer M22 (g • X) := by
  apply le_antisymm
  · rintro _ ⟨x, hx, rfl⟩
    change x • X = X at hx
    change (m22DesignAutToAut g) x • (g • X) = g • X
    rw [← hact]
    have he : inclusion ((m22DesignAutToAut g) x) = g * inclusion x * g⁻¹ := by
      apply Subtype.ext
      exact m22DesignAutToAut_apply_perm g x
    rw [he, mul_smul, mul_smul, inv_smul_smul, hact, hx]
  · intro x hx
    change x • (g • X) = g • X at hx
    refine ⟨(m22DesignAutToAut g).symm x, ?_, by simp⟩
    change (m22DesignAutToAut g).symm x • X = X
    rw [← hact]
    have he : inclusion ((m22DesignAutToAut g).symm x) = g⁻¹ * inclusion x * g := by
      rw [show (m22DesignAutToAut g).symm = m22DesignAutToAut g⁻¹ from
        (map_inv m22DesignAutToAut g).symm]
      apply Subtype.ext
      exact m22DesignAutToAut_apply_perm g⁻¹ x
    rw [he, mul_smul, mul_smul, hact, hx, inv_smul_smul]

theorem fixed_pair_invariant (a : MulAut M22)
    (ha : (fixedSylow : Subgroup M22).map a.toMonoidHom = fixedSylow) :
    M22SolvableSylow.pairHexad.map a.toMonoidHom = M22SolvableSylow.pairHexad ∧
      second.map a.toMonoidHom = second := by
  obtain ⟨g, rfl⟩ := m22DesignAutToAut_surjective a
  obtain ⟨hB, hpair, hpart⟩ := design_preserves_marks g ha
  constructor
  · change (stabilizer M22 m22Hexad123 ⊓ stabilizer M22 m22Pair12).map _ = _
    rw [Subgroup.map_inf _ _ _ (m22DesignAutToAut g).injective,
      map_stabilizer_design m22Hexad123 g (by intros; rfl),
      map_stabilizer_design m22Pair12 g (by intros; rfl), hB, hpair]
    rfl
  · change (stabilizer M22 hexadPartition).map _ = _
    rw [map_stabilizer_design hexadPartition g (by intros; rfl), hpart]
    rfl

end Sporadic.Mathieu.M22CubicHexad
