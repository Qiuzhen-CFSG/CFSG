module

public import CFSG.Quasithin.ChapterD.Section02.FittingOffenders.Configurations.Defs
public import CFSG.Quasithin.ChapterD.Section02.FittingOffenders.Configurations.LinearBudget
public import CFSG.Quasithin.ChapterD.Section02.FittingOffenders.Configurations.FourDimensionalMarking.Core
public import Theory.GroupAction.NineSixteenFixedFactors
public import Theory.Representation.BinaryGroupAction
public import Theory.Representation.BinaryOffender.EquivariantOffender
public import Mathlib.LinearAlgebra.Projection

/-!
# Literal support factors in the four-dimensional branch

For the original faithful elementary core on the binary four-space, the core
rank is two. Coprime fixed-point generation supplies complementary core lines
with complementary fixed planes. Commutativity makes the moved space of each
line lie in the opposite fixed plane, and coprime fixed/moved splitting makes
this an equality. Each moved space therefore has dimension two.

The chosen lines are subgroups of the original core. Their multiplication
bijection and the addition bijection of their moved spaces use the canonical
inclusions, with the exact list-product and finite-sum formulas of
`SupportFactors`.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, D.2.14(3),
the full-support four-dimensional branch on printed p.187.
-/

open Representation.BinaryOffender Representation.BinaryGroupAction
namespace CFSG.Quasithin.ChapterD.FittingConfigurations

private theorem moved_comp_subtype {G V : Type*} [Group G]
    [AddCommGroup V] [Module (ZMod 2) V]
    (ρ : Representation (ZMod 2) G V) (P : Subgroup G) (K : Subgroup P) :
    subspaceCommutator (ρ.comp P.subtype) ⊤ K =
      subspaceCommutator ρ ⊤ (K.map P.subtype) := by
  unfold subspaceCommutator
  congr 1
  ext v
  constructor
  · rintro ⟨k, hk, w, hw, rfl⟩
    exact ⟨k, Subgroup.mem_map_of_mem P.subtype hk, w, hw, rfl⟩
  · rintro ⟨_, ⟨k, hk, rfl⟩, w, hw, rfl⟩
    exact ⟨k, hk, w, hw, rfl⟩

private theorem moved_eq_opposite_fixed {H V : Type*} [CommGroup H] [Finite H]
    [AddCommGroup V] [Module (ZMod 2) V]
    (σ : Representation (ZMod 2) H V) (K L : Subgroup H)
    (hK : Odd (Nat.card K)) (hC : IsCompl (fixedSpace σ K) (fixedSpace σ L)) :
    subspaceCommutator σ ⊤ K = fixedSpace σ L := by
  have hle : subspaceCommutator σ ⊤ K ≤ fixedSpace σ L := by
    apply Submodule.span_le.mpr
    rintro _ ⟨k, hk, v, _, rfl⟩
    obtain ⟨u, hu, w, hw, rfl⟩ := Submodule.mem_sup.mp
      (show v ∈ fixedSpace σ K ⊔ fixedSpace σ L from hC.sup_eq_top ▸ Submodule.mem_top)
    have hu' : σ k u = u := hu ⟨k, hk⟩
    rw [map_add, hu', add_sub_add_left_eq_sub]
    intro l
    change σ (l : H) (σ k w - w) = σ k w - w
    rw [map_sub]
    have hc : σ (l : H) (σ k w) = σ k (σ (l : H) w) := by
      simp only [← Module.End.mul_apply, ← map_mul, mul_comm]
    have hw' : σ (l : H) w = w := hw l
    rw [hc, hw']
  exact (le_iff_eq_of_codisjoint_of_disjoint
    (odd_fixed_moved_complement σ hK).codisjoint hC.disjoint).mp hle

private theorem two_factor_product_bijective {H : Type*} [Group H] [Finite H]
    (K L : Subgroup H) (hcard : Nat.card K * Nat.card L = Nat.card H)
    (hd : Disjoint K L) :
    Function.Bijective (fun x : (i : Fin 2) → (![K, L] i : Subgroup H) =>
      (List.ofFn fun i => (x i : H)).prod) := by
  have hp : Function.Bijective (fun x : K × L => (x.1 : H) * (x.2 : H)) :=
    (Subgroup.isComplement_iff_bijective K L).mp
      (Subgroup.isComplement'_of_card_mul_and_disjoint hcard hd)
  have hh : Function.Bijective (fun x : (i : Fin 2) → (![K, L] i : Subgroup H) =>
      (x 0 : H) * (x 1 : H)) :=
    hp.comp (piFinTwoEquiv (fun i => (![K, L] i : Subgroup H))).bijective
  simpa only [List.ofFn_succ, List.ofFn_zero, List.prod_cons, List.prod_nil, mul_one, Fin.succ_zero_eq_one] using hh

private theorem two_support_sum_bijective {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    (U : Fin 2 → Submodule (ZMod 2) V) (hU : IsCompl (U 0) (U 1)) :
    Function.Bijective (fun v : (i : Fin 2) → U i => ∑ i, (v i : V)) := by
  have hh := (Submodule.prodEquivOfIsCompl (U 0) (U 1) hU).bijective.comp
    (piFinTwoEquiv (fun i => U i)).bijective
  simpa only [Function.comp_def, piFinTwoEquiv_apply,
    Submodule.coe_prodEquivOfIsCompl', Fin.sum_univ_two] using hh

variable {G V : Type*} [Group G] [Finite G]
  [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V)

/-- The full-support four-space has two literal order-three support factors,
whose original moved planes sum bijectively onto the original module. -/
public theorem Reduced.fullSupport_supportFactors {P A : Subgroup G} {s : ℕ}
    (h : Reduced ρ P A s) (hfull : FullSupport ρ P A) :
    Nonempty (SupportFactors ρ P s) := by
  obtain ⟨Z, hZ, hmove, hdim⟩ := hfull
  have hs := h.core_rank_eq_two_of_finrank_four ρ hdim
  subst s
  let : IsElementaryAbelian 3 P := h.elementary
  let : CommGroup P := IsMulCommutative.instCommGroup
  let σ : Representation (ZMod 2) P V := ρ.comp P.subtype
  let := action σ
  let := Representation.BinaryGroupAction.elementary (V := V)
  let : Finite V := Module.finite_of_finite (ZMod 2)
  have hfσ : Function.Injective σ := fun x y he => Subtype.ext (h.faithful he)
  let := Representation.BinaryGroupAction.faithful σ hfσ
  have hP : Nat.card P = 9 := by rw [h.card_core]; rfl
  have hV : Nat.card (Multiplicative V) = 16 := by
    change Nat.card V = 16
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod, hdim]
    norm_num
  have hf : FixedPoints.subgroup (⊤ : Subgroup P) (Multiplicative V) = ⊥ := by
    rw [fixedPoints_eq σ, fixedSpace_comp_map, ← MonoidHom.range_eq_map,
      Subgroup.range_subtype, h.fixedSpace_core_eq_bot ρ]
    exact (submoduleEquivSubgroup (V := V)).map_bot
  obtain ⟨K, L, hK, hL, hKL, hFK, hFL, hF⟩ :=
    nine_sixteen_fixed_factor_decomposition hP hV hf
  have hC : IsCompl (fixedSpace σ K) (fixedSpace σ L) := by
    apply (submoduleEquivSubgroup (V := V)).isCompl_iff.mpr
    simpa only [← fixedPoints_eq σ] using hF
  have hdimF (M : Subgroup P)
      (hc : Nat.card (FixedPoints.subgroup M (Multiplicative V)) = 4) :
      Module.finrank (ZMod 2) (fixedSpace σ M) = 2 := by
    rw [fixedPoints_eq σ, card_submoduleEquivSubgroup,
      Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod] at hc
    exact Nat.pow_right_injective (by decide : 2 ≤ 2) hc
  have hMK : subspaceCommutator ρ ⊤ (K.map P.subtype) = fixedSpace σ L := by
    rw [← moved_comp_subtype]
    exact moved_eq_opposite_fixed σ K L (hK ▸ (by decide : Odd 3)) hC
  have hML : subspaceCommutator ρ ⊤ (L.map P.subtype) = fixedSpace σ K := by
    rw [← moved_comp_subtype]
    exact moved_eq_opposite_fixed σ L K (hL ▸ (by decide : Odd 3)) hC.symm
  refine ⟨{
    factor := ![K, L]
    card_factor := ?_
    multiply_bijective := two_factor_product_bijective K L (by rw [hK, hL, hP]) hKL.disjoint
    support_dim := ?_
    add_bijective := ?_ }⟩
  · intro i
    fin_cases i
    · exact hK
    · exact hL
  · intro i
    fin_cases i
    · change Module.finrank (ZMod 2) (subspaceCommutator ρ ⊤ (K.map P.subtype)) = 2
      rw [hMK]
      exact hdimF L hFL
    · change Module.finrank (ZMod 2) (subspaceCommutator ρ ⊤ (L.map P.subtype)) = 2
      rw [hML]
      exact hdimF K hFK
  · apply two_support_sum_bijective
    simpa only [Matrix.cons_val_zero, Matrix.cons_val_one, hMK, hML] using hC.symm

end CFSG.Quasithin.ChapterD.FittingConfigurations
