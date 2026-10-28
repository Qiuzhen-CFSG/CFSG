module

public import Theory.Mathieu.M22.ValueBoundParabolics.Concrete.PartitionStructure
public import Theory.Mathieu.M22.Properties.FixedHexadLocal.KernelGeometry
public import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple
public import Theory.GroupTheory.PCoreImage

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.SmallCovers.Mathieu.Transport

/-!
# The native M₂₂ parabolic radical

The standard three-pair stabilizer is a subgroup of the hexad stabilizer.
The pointwise hexad kernel fixes that partition, so it is a normal two-subgroup
of the parabolic. The genuine A₆ quotient has trivial two-core, identifying
the hexad kernel with the hexad stabilizer's actual two-core. This gives
O₂(hexad stabilizer) ≤ O₂(three-pair stabilizer) and the required reversed
fixed-space containment. Order 384 also bounds the parabolic's three-part.

Source: Aschbacher–Smith, 13.8.21(2), printed p.956, using the native
E.4.3 hexad and partition geometry. This treats the native inner actors;
identification with K∩M and the possible outer supplement remain separate.
-/

public section
open scoped Pointwise
open Subgroup Sporadic.Mathieu
open Sporadic.Mathieu.M22ValueBound.Concrete
open Sporadic.Mathieu.M22ValueBound.Concrete.PartitionStructure
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.SmallCovers.Mathieu.Native

theorem hexad_kernel_le_partition : m22HexadPointwiseKernel m22Hexad123 ≤ second := by
  rintro _ ⟨g, hg, rfl⟩
  have h : g ∈ smallGroup.comap (m22SetAction m22Hexad123) := by
    change m22SetAction m22Hexad123 g ∈ smallGroup
    rw [show m22SetAction m22Hexad123 g = 1 from hg]
    exact smallGroup.one_mem
  rw [second_preimage] at h
  exact h

theorem hexad_kernel_le_partition_core :
    m22HexadPointwiseKernel m22Hexad123 ≤ second.pCoreIn 2 := by
  apply le_pCoreIn_of_normalizes (m22HexadPointwiseKernel_isTwoGroup m22Hexad123_mem)
    hexad_kernel_le_partition
  rw [m22HexadPointwiseKernel_normalizer m22Hexad123_mem]
  exact second_le_hexad

private theorem six_twoCore_eq_bot : pCore 2 (alternatingGroup (Fin 6)) = ⊥ := by
  let : IsSimpleGroup (alternatingGroup (Fin 6)) := alternatingGroup.isSimpleGroup (by simp)
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
      (pCore 2 (alternatingGroup (Fin 6))) inferInstance with h | h
  · exact h
  · have hp : IsPGroup 2 (⊤ : Subgroup (alternatingGroup (Fin 6))) := h ▸ pCore_isPGroup
    obtain ⟨n, hn⟩ := hp.exists_card_eq
    rw [Subgroup.card_top, nat_card_alternatingGroup, Nat.card_fin] at hn
    have hd : 3 ∣ 2 ^ n := hn ▸ (by decide : 3 ∣ Nat.factorial 6 / 2)
    have hf : 3 ∣ 2 := Nat.prime_three.dvd_of_dvd_pow hd
    norm_num at hf

theorem hexad_core_eq_kernel :
    (MulAction.stabilizer M22 m22Hexad123).pCoreIn 2 =
      m22HexadPointwiseKernel m22Hexad123 := by
  let Q := MulAction.stabilizer M22 m22Hexad123
  let f : Q →* alternatingGroup (Fin 6) :=
    (m22HexadQuotientAlternatingEquiv m22Hexad123_mem).toMonoidHom.comp
      (QuotientGroup.mk' (m22SetAction m22Hexad123).ker)
  have hs : Function.Surjective f :=
    (m22HexadQuotientAlternatingEquiv m22Hexad123_mem).surjective.comp
      (QuotientGroup.mk'_surjective _)
  have hk : f.ker = (m22SetAction m22Hexad123).ker := by
    dsimp [f]
    rw [MonoidHom.ker_mulEquiv_comp, QuotientGroup.ker_mk']
  have hp : IsPGroup 2 f.ker := by
    rw [hk]
    exact IsPGroup.of_card (n := 4) (m22HexadKernel_card m22Hexad123_mem)
  have hc := f.comap_pCore_of_ker_isPGroup hs hp
  rw [six_twoCore_eq_bot] at hc
  change f.ker = pCore 2 Q at hc
  rw [hk] at hc
  exact congrArg (fun R : Subgroup Q => R.map Q.subtype) hc.symm

theorem native_core_le_partition_core :
    (MulAction.stabilizer M22 m22Hexad123).pCoreIn 2 ≤ second.pCoreIn 2 := by
  rw [hexad_core_eq_kernel]
  exact hexad_kernel_le_partition_core

/-- In the native marked parabolic, the three-part of any subgroup with
three-divisible order is exactly three. -/
theorem three_part_of_le_partition (X : Subgroup M22) (hX : X ≤ second)
    (hthree : 3 ∣ Nat.card X) : 3 ^ (Nat.card X).factorization 3 = 3 := by
  have hd : Nat.card X ∣ 384 := PartitionStructure.second_card ▸ card_dvd_of_le hX
  have hl := (Nat.prime_three.dvd_iff_one_le_factorization (Nat.card_pos.ne')).mp hthree
  have hu : ¬ 2 ≤ (Nat.card X).factorization 3 := by
    intro h
    have h9 : 9 ∣ Nat.card X :=
      (Nat.prime_three.pow_dvd_iff_le_factorization (Nat.card_pos.ne')).mpr h
    exact (by decide : ¬ 9 ∣ 384) (h9.trans hd)
  have he : (Nat.card X).factorization 3 = 1 := by omega
  rw [he]
  rfl

/-- The concrete fixed-space comparison, before transport to source actors. -/
theorem native_fixed_core_compare {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    (ρ : Representation (ZMod 2) M22 V) :
    Representation.BinaryOffender.fixedSpace ρ (second.pCoreIn 2) ≤
      Representation.BinaryOffender.fixedSpace ρ
        ((MulAction.stabilizer M22 m22Hexad123).pCoreIn 2) := by
  intro v hv q
  exact hv ⟨q, native_core_le_partition_core q.property⟩
end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.SmallCovers.Mathieu.Native
