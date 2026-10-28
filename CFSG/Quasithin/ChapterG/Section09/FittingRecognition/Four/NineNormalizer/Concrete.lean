module

public import Theory.LinearAlgebra.QuadraticForm.BinaryFourPlus
public import Theory.PGroupCore
public import Theory.ElementaryAbelian.Quotient
public import Mathlib.GroupTheory.Sylow
import Mathlib.Tactic

/-!
# The full normalizer of the two cubic plane actions

The product of two cyclic groups of order three acts independently on two
binary planes. Each plane is irreducible. A nonzero vector has a nontrivial
stabilizer precisely when it is nonsingular for `BinaryFourPlus.q`. Thus the
full linear normalizer preserves this quadratic form. Conversely, every
isometry preserves or swaps the planes, and each plane automorphism normalizes
its cubic subgroup. The order-nine subgroup is consequently the three-core
of the full isometry group, which has order 72.

The finite checks use only the three cubic elements, six plane permutations,
and sixteen vectors; there is no enumeration of GL₄(2).
Source: Aschbacher--Smith, G.9.4, printed p.355 / PDF p.366.
-/

public section

open BinaryFourPlus
namespace CFSG.Quasithin.ChapterG.Section09.FittingRecognition.Four.NineNormalizer
instance : Finite (BinaryFourPlus.V ≃ₗ[ZMod 2] BinaryFourPlus.V) :=
  Finite.of_injective (fun e : BinaryFourPlus.V ≃ₗ[ZMod 2] BinaryFourPlus.V => (e : BinaryFourPlus.V → BinaryFourPlus.V)) DFunLike.coe_injective
abbrev C3 := Multiplicative (ZMod 3)
abbrev E9 := C3 × C3

@[expose] def cycle : Plane ≃ₗ[ZMod 2] Plane where
  toFun v := ![v 1, v 0 + v 1]
  invFun v := ![v 0 + v 1, v 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel
  map_add' := by decide +kernel
  map_smul' := by decide +kernel

@[expose] def planeAction (a : C3) : Plane ≃ₗ[ZMod 2] Plane :=
  if a.toAdd = 0 then 1 else if a.toAdd = 1 then cycle else cycle * cycle

@[expose] def planeHom : C3 →* (Plane ≃ₗ[ZMod 2] Plane) where
  toFun := planeAction
  map_one' := by apply LinearEquiv.ext; exact (by decide +kernel)
  map_mul' := by
    intro a b
    apply LinearEquiv.ext
    exact (by decide +kernel : ∀ a b v, planeAction (a*b) v = planeAction a (planeAction b v)) a b

@[expose] def nineHom : E9 →* (BinaryFourPlus.V ≃ₗ[ZMod 2] BinaryFourPlus.V) where
  toFun a := (planeHom a.1).prodCongr (planeHom a.2)
  map_one' := by ext v <;> simp
  map_mul' a b := by ext v <;> simp [LinearEquiv.mul_apply]

theorem nineHom_injective : Function.Injective nineHom := by
  intro a b h
  have hh := congrArg (fun g : BinaryFourPlus.V ≃ₗ[ZMod 2] BinaryFourPlus.V => g (![1,0], ![1,0])) h
  exact (by decide +kernel : ∀ a b, nineHom a (![1,0], ![1,0]) = nineHom b (![1,0], ![1,0]) → a = b) a b hh

@[expose] def nine : Subgroup (BinaryFourPlus.V ≃ₗ[ZMod 2] BinaryFourPlus.V) := nineHom.range

theorem card_nine : Nat.card nine = 9 := by
  change Nat.card nineHom.range = 9
  rw [← Nat.card_congr (MonoidHom.ofInjective nineHom_injective).toEquiv]
  simp [E9, C3]

theorem q_one_iff_fixed : ∀ v : BinaryFourPlus.V, q v = 1 ↔
    v ≠ 0 ∧ ∃ a : E9, a ≠ 1 ∧ nineHom a v = v := by decide +kernel


theorem normalizer_preserves_one (g : BinaryFourPlus.V ≃ₗ[ZMod 2] BinaryFourPlus.V)
    (hg : g ∈ Subgroup.normalizer (nine : Set _))
    (v : BinaryFourPlus.V) (hv : q v = 1) : q (g v) = 1 := by
  obtain ⟨hv0, a, ha, hav⟩ := (q_one_iff_fixed v).mp hv
  obtain ⟨b, hb⟩ := (Subgroup.mem_normalizer_iff.mp hg (nineHom a)).mp
    (show nineHom a ∈ nine from ⟨a, rfl⟩)
  apply (q_one_iff_fixed (g v)).mpr
  refine ⟨fun h => hv0 (g.map_eq_zero_iff.mp h), b, ?_, ?_⟩
  · intro h
    have h1 : nineHom a = 1 := by
      have hh := congrArg (fun f => g⁻¹ * f * g) hb
      simpa [h, mul_assoc] using hh.symm
    exact ha (nineHom_injective (h1.trans nineHom.map_one.symm))
  · rw [hb]
    simpa only [LinearEquiv.mul_apply, LinearEquiv.coe_inv, LinearEquiv.symm_apply_apply] using congrArg g hav

theorem normalizer_le_isometry : Subgroup.normalizer (nine : Set _) ≤ q.isometrySubgroup := by
  intro g hg
  apply (QuadraticMap.mem_isometrySubgroup q g).mpr
  intro v
  apply (by decide : ∀ a b : ZMod 2, (a = 1 ↔ b = 1) → a = b)
  constructor
  · intro hv
    have hh := normalizer_preserves_one g⁻¹ (Subgroup.inv_mem _ hg)
      (g v) hv
    simpa using hh
  · exact normalizer_preserves_one g hg v

private def cubicPerm (c : C3) : Equiv.Perm (Fin 3) :=
  let t := Equiv.swap 0 1 * Equiv.swap 1 2
  if c.toAdd = 0 then 1 else if c.toAdd = 1 then t else t * t

private theorem planeHom_nonzeroVector : ∀ c i,
    planeHom c (nonzeroVector i) = nonzeroVector (cubicPerm c i) := by decide +kernel

theorem plane_conjugates (a : Plane ≃ₗ[ZMod 2] Plane) (c : C3) :
    ∃ d : C3, ∀ v : Plane, a (planeHom c v) = planeHom d (a v) := by
  have ht : ∀ (p : Equiv.Perm (Fin 3)) (c : C3), ∃ d : C3,
      ∀ i, p (cubicPerm c i) = cubicPerm d (p i) := by decide +kernel
  obtain ⟨d, hd⟩ := ht (planeAutPerm a) c
  refine ⟨d, fun v => ?_⟩
  by_cases hv : v = 0
  · simp [hv]
  have hn : ∀ v : Plane, v ≠ 0 → ∃ i, nonzeroVector i = v := by decide +kernel
  obtain ⟨i, hi'⟩ := hn v hv
  rw [← hi', planeHom_nonzeroVector, ← planeAutPerm_apply,
    ← planeAutPerm_apply, planeHom_nonzeroVector, hd]

theorem isometry_le_normalizer : q.isometrySubgroup ≤ Subgroup.normalizer (nine : Set _) := by
  intro g hg
  apply Subgroup.mem_normalizer_fintype
  rintro x ⟨c, rfl⟩
  obtain h | h := exists_factors ⟨g,hg⟩
  · obtain ⟨a,b,hab⟩ := h
    obtain ⟨ca,hca⟩ := plane_conjugates a c.1
    obtain ⟨cb,hcb⟩ := plane_conjugates b c.2
    refine ⟨(ca,cb), ?_⟩
    apply LinearEquiv.ext
    intro v
    obtain ⟨w,rfl⟩ := g.surjective v
    simp only [LinearEquiv.mul_apply, LinearEquiv.coe_inv, LinearEquiv.symm_apply_apply]
    simp only [hab, nineHom, MonoidHom.coe_mk, OneHom.coe_mk, LinearEquiv.prodCongr_apply]
    exact (Prod.ext (hca w.1) (hcb w.2)).symm
  · obtain ⟨a,b,hab⟩ := h
    obtain ⟨ca,hca⟩ := plane_conjugates a c.2
    obtain ⟨cb,hcb⟩ := plane_conjugates b c.1
    refine ⟨(ca,cb), ?_⟩
    apply LinearEquiv.ext
    intro v
    obtain ⟨w,rfl⟩ := g.surjective v
    simp only [LinearEquiv.mul_apply, LinearEquiv.coe_inv, LinearEquiv.symm_apply_apply]
    simp only [hab, nineHom, MonoidHom.coe_mk, OneHom.coe_mk, LinearEquiv.prodCongr_apply]
    exact (Prod.ext (hca w.2) (hcb w.1)).symm

theorem normalizer_nine : Subgroup.normalizer (nine : Set _) = q.isometrySubgroup :=
  le_antisymm normalizer_le_isometry isometry_le_normalizer


theorem nine_le_isometry : nine ≤ q.isometrySubgroup :=
  nine.le_normalizer.trans normalizer_le_isometry

theorem nine_is_core : nine.subgroupOf q.isometrySubgroup = pCore 3 q.isometrySubgroup := by
  let : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let N := nine.subgroupOf q.isometrySubgroup
  have hn : N.Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer nine_le_isometry).mpr
    isometry_le_normalizer
  have hc : Nat.card N = 9 :=
    (Nat.card_congr (Subgroup.subgroupOfEquivOfLe nine_le_isometry).toEquiv).trans card_nine
  have hi : N.index = 8 := by
    have hh := N.card_mul_index
    rw [hc, card_isometrySubgroup] at hh
    omega
  let S : Sylow 3 q.isometrySubgroup :=
    (IsPGroup.of_card (p := 3) (n := 2) hc).toSylow (by rw [hi]; decide)
  apply le_antisymm
  · exact le_sSup ⟨hn, IsPGroup.of_card (p := 3) (n := 2) hc⟩
  · exact (show IsPGroup 3 (pCore 3 q.isometrySubgroup) from pCore_isPGroup).le_sylow_of_normal S


theorem plane_irreducible (U : Submodule (ZMod 2) Plane)
    (hU : ∀ c v, v ∈ U → planeHom c v ∈ U) : U = ⊥ ∨ U = ⊤ := by
  by_cases hb : U = ⊥
  · exact Or.inl hb
  right
  obtain ⟨v, hv, hv0⟩ := U.ne_bot_iff.mp hb
  have hc := hU (Multiplicative.ofAdd (1 : ZMod 3)) v hv
  have table : ∀ v w : Plane, v ≠ 0 → w = 0 ∨ w = v ∨
      w = planeHom (Multiplicative.ofAdd (1 : ZMod 3)) v ∨
      w = v + planeHom (Multiplicative.ofAdd (1 : ZMod 3)) v := by decide +kernel
  apply top_unique
  intro w _
  rcases table v w hv0 with rfl | rfl | rfl | rfl
  · exact U.zero_mem
  · exact hv
  · exact hc
  · exact U.add_mem hv hc


instance elementary_nineCarrier : IsElementaryAbelian 3 E9 where
  toIsMulCommutative := inferInstance
  exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr (by decide +kernel)

end CFSG.Quasithin.ChapterG.Section09.FittingRecognition.Four.NineNormalizer
