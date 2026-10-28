module

public import Theory.Representation.GoldschmidtONan.Basic
public import Theory.Representation.BinaryOffender.SubspaceAction
public import Theory.Representation.BinaryOffender.CommutatorRank

/-!
# Fixed vectors on an odd moved support

Odd-order averaging commutes with a centralizing actor. Consequently its fixed
vectors on the moved space are exactly the displacements of its fixed vectors.
The square-zero displacement of an involution bounds an invariant subspace by
twice its fixed dimension. Odd fixed/moved splitting also makes the original
faithful odd actor faithful on its own moved support.

These are the linear steps in Aschbacher--Smith D.2.14, printed p.186,
paragraphs (+) and (++), used by the central-line Frattini exclusion.
-/

public section

open Subgroup Representation Representation.BinaryOffender
namespace CFSG.Quasithin.ChapterD.ElementaryCore.SupportExclusion
variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V)

/-- The two existing span conventions agree on the original vectors. -/
theorem moved_eq (Z : Subgroup G) (W : Submodule (ZMod 2) V) :
    subspaceCommutator ρ W Z =
      RegularCyclicNormalClosure.displacementSpan ρ Z W := by
  unfold subspaceCommutator RegularCyclicNormalClosure.displacementSpan
  congr 1
  ext v
  simp only [Set.mem_ofPred_eq, eq_comm]

/-- Normalization of the odd actor preserves its actual moved support. -/
theorem moved_stable (Z H : Subgroup G) (hn : H ≤ normalizer (Z : Set G)) :
    H ≤ subspaceStabilizer ρ (subspaceCommutator ρ ⊤ Z) := by
  apply le_subspaceStabilizer
  intro h hh v hv
  rw [moved_eq] at hv ⊢
  have he := RegularCyclicNormalClosure.displacementSpan_map_of_normalized ρ Z h
    (mem_normalizer_iff_map_conj_eq.mp (hn hh))
  exact he ▸ Submodule.mem_map_of_mem hv

/-- Odd averaging identifies fixed vectors on the moved support with
displacements of fixed vectors of the commuting actor. -/
theorem fixed_moved [Finite G] (Z B : Subgroup G) (hodd : Odd (Nat.card Z))
    (hc : B ≤ centralizer (Z : Set G)) :
    subspaceCommutator ρ ⊤ Z ⊓ fixedSpace ρ B =
      subspaceCommutator ρ (fixedSpace ρ B) Z := by
  classical
  let := Fintype.ofFinite Z
  have hcard : (Fintype.card Z : ZMod 2) = 1 := by
    obtain ⟨k, hk⟩ := hodd
    rw [← Nat.card_eq_fintype_card, hk]
    simp only [Nat.cast_add, Nat.cast_mul, ZMod.natCast_self, zero_mul, Nat.cast_one, zero_add]
  let N : V →ₗ[ZMod 2] V := ∑ z : Z, ρ z
  have hN (v : V) : N v = ∑ z : Z, ρ z v := LinearMap.sum_apply _ _ _
  have hright (z : Z) (v : V) : N (ρ z v) = N v := by
    simp only [hN, ← Module.End.mul_apply, ← map_mul]
    change (∑ y : Z, ρ ((y * z : Z) : G) v) = ∑ y : Z, ρ y v
    exact (Group.mulRight_bijective z).sum_comp (fun y : Z => ρ y v)
  have hkill : subspaceCommutator ρ ⊤ Z ≤ N.ker := by
    apply Submodule.span_le.mpr
    rintro _ ⟨z, hz, v, _, rfl⟩
    change N (ρ z v - v) = 0
    rw [map_sub, hright ⟨z, hz⟩, sub_self]
  apply le_antisymm
  · intro v hv
    have hm : (∑ z : Z, (ρ z v - v)) ∈ subspaceCommutator ρ (fixedSpace ρ B) Z :=
      Submodule.sum_mem _ fun z _ => Submodule.subset_span ⟨z, z.property, v, hv.2, rfl⟩
    rw [Finset.sum_sub_distrib, ← hN, Finset.sum_const, Finset.card_univ,
      ← Nat.cast_smul_eq_nsmul (ZMod 2), hcard, one_smul, hkill hv.1, zero_sub] at hm
    simpa only [neg_neg] using (subspaceCommutator ρ (fixedSpace ρ B) Z).neg_mem hm
  · apply Submodule.span_le.mpr
    rintro _ ⟨z, hz, v, hv, rfl⟩
    refine ⟨Submodule.subset_span ⟨z, hz, v, by trivial, rfl⟩, ?_⟩
    intro b
    have he : ρ b (ρ z v) = ρ z (ρ b v) := by
      simp only [← Module.End.mul_apply, ← map_mul]
      rw [(mem_centralizer_iff.mp (hc b.property) z hz).symm]
    change ρ b (ρ z v - v) = ρ z v - v
    rw [map_sub, he, show ρ b v = v from hv b]

/-- Odd-order averaging splits the original module into fixed and moved spaces. -/
theorem moved_split [Finite G] (Z : Subgroup G) (hodd : Odd (Nat.card Z)) :
    IsCompl (fixedSpace ρ Z) (subspaceCommutator ρ ⊤ Z) := by
  rw [moved_eq]
  exact GoldschmidtONan.isCompl_fixed_moved_of_odd hodd

/-- An odd subgroup of a faithful representation is faithful on its own support. -/
theorem moved_faithful [Finite G] (hf : Function.Injective ρ)
    (Z : Subgroup G) (hodd : Odd (Nat.card Z)) :
    subspaceKernel ρ (subspaceCommutator ρ ⊤ Z) Z = ⊥ := by
  apply (subspaceKernel_eq_bot_iff _ _ _).mpr
  intro z hz hfix
  apply hf
  ext v
  obtain ⟨u, hu, w, hw, rfl⟩ := Submodule.mem_sup.mp
    (show v ∈ fixedSpace ρ Z ⊔ subspaceCommutator ρ ⊤ Z by
      rw [(moved_split ρ Z hodd).sup_eq_top]; trivial)
  have hu' : ρ z u = u := hu ⟨z, hz⟩
  simp only [map_add, map_one, Module.End.one_apply, hu', hfix w hw]

/-- Rank-nullity for a square-zero displacement bounds an invariant space
by twice the dimension fixed by the involution. -/
theorem involution_bound [FiniteDimensional (ZMod 2) V]
    (t : G) (ht : t ^ 2 = 1) (U : Submodule (ZMod 2) V)
    (hu : ∀ v ∈ U, ρ t v ∈ U) :
    Module.finrank (ZMod 2) U ≤
      2 * Module.finrank (ZMod 2) (U ⊓ fixedSpace ρ (zpowers t) : Submodule (ZMod 2) V) := by
  let N := ρ t - LinearMap.id
  have hchar (v : V) : v + v = 0 := by
    have he : (1 + 1 : ZMod 2) = 0 := by decide
    simpa only [add_smul, one_smul, zero_smul] using congrArg (fun r => r • v) he
  have htt (v : V) : ρ t (ρ t v) = v := by
    simpa only [pow_two, map_mul, Module.End.mul_apply, map_one, Module.End.one_apply]
      using congrArg (fun a => ρ a v) ht
  have hker : N.ker = fixedSpace ρ (zpowers t) := by
    ext v
    rw [mem_fixedSpace_zpowers_iff]
    exact sub_eq_zero
  have hle : U.map N ≤ U ⊓ N.ker := by
    rintro _ ⟨v, hv, rfl⟩
    refine ⟨U.sub_mem (hu v hv) hv, ?_⟩
    change ρ t (ρ t v - v) - (ρ t v - v) = 0
    rw [map_sub, htt]
    calc
      v - ρ t v - (ρ t v - v) = (v + v) - (ρ t v + ρ t v) := by abel
      _ = 0 := by rw [hchar, hchar, sub_self]
  have hr := (N.domRestrict U).finrank_range_add_finrank_ker
  rw [LinearMap.range_domRestrict, LinearMap.ker_domRestrict] at hr
  have he : Module.finrank (ZMod 2) (N.ker.comap U.subtype) =
      Module.finrank (ZMod 2) (U ⊓ N.ker : Submodule (ZMod 2) V) := by
    rw [← U.map_comap_subtype N.ker, Submodule.finrank_map_subtype_eq]
  rw [he] at hr
  have hb := Submodule.finrank_mono hle
  rw [hker] at hr hb
  omega

end CFSG.Quasithin.ChapterD.ElementaryCore.SupportExclusion
