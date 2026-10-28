module

public import Theory.SpecificGroups.Classical.BinarySylowExponent
public import Theory.SpecificGroups.Suzuki.StandardSubgroups
public import Theory.AtlasPort.ExceptionalIsomorphisms.Order20160A8
public import CFSG.Quasithin.ClassicalModels
public import Mathlib.Algebra.CharP.CharAndCard
/-!
# Order-eight obstructions to binary source models

The actual Sylow order-eight element cannot occur in binary PSL of dimension
at most four or in ternary PSU, by the matrix nilpotence bound. Suzuki root
coordinates give the same fourth-power bound. The faithful exceptional
PSL₄(2) comparison also excludes A₈. Every witness is transported through the
literal model and Sylow maps.

Source: Aschbacher–Smith F.6.18(12)–(13), printed p.310.
-/

public section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterF.SourceAssembly.ComponentSieve.LargeGoldschmidt
variable {G : Type*} [Group G] [Finite G]
private theorem not_order_eight_of_pow_four {A : Type*} [Group A] (x : A)
    (h : x ^ 4 = 1) : orderOf x ≠ 8 := by
  intro he
  have hd := orderOf_dvd_of_pow_eq_one h
  rw [he] at hd
  norm_num at hd

theorem not_binary_small_linear_of_sylow_order_eight
    (P : Sylow 2 G) (x : P) (hx : orderOf x = 8)
    {n f : ℕ} [NeZero n] (hn : n ≤ 4) : ¬ ClassicalGroup.IsPSL G n (2 ^ f) := by
  rintro ⟨F,_,_,hc,⟨j⟩⟩
  let : Fintype F := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow (p := 2) (f := f) (by
    simpa [Nat.card_eq_fintype_card] using hc)
  let Q := P.mapSurjective (f := j.toMonoidHom) j.surjective
  let e : P ≃* Q := (P : Subgroup G).equivMapOfInjective j.toMonoidHom j.injective
  have h4 : x ^ 4 = 1 := e.injective (by
    rw [map_pow,map_one]
    exact Theory.ClassicalSmallSylow.binary_psl_small_dimension_sylow_pow_four hn Q (e x))
  exact not_order_eight_of_pow_four x h4 hx

theorem not_binary_unitary_three_of_sylow_order_eight
    (P : Sylow 2 G) (x : P) (hx : orderOf x = 8) {f : ℕ} :
    ¬ ClassicalGroup.IsPSU G 3 (2 ^ f) := by
  rintro ⟨F,_,_,J,hc,_,⟨j⟩⟩
  let : Fintype F := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow (p := 2) (f := f * 2) (by
    simpa [Nat.card_eq_fintype_card,pow_mul] using hc)
  let Q := P.mapSurjective (f := j.toMonoidHom) j.surjective
  let e : P ≃* Q := (P : Subgroup G).equivMapOfInjective j.toMonoidHom j.injective
  have h4 : x ^ 4 = 1 := e.injective (by
    rw [map_pow,map_one]
    exact Theory.ClassicalSmallSylow.binary_psu_three_sylow_pow_four J Q (e x))
  exact not_order_eight_of_pow_four x h4 hx

theorem not_suzuki_of_sylow_order_eight
    (P : Sylow 2 G) (x : P) (hx : orderOf x = 8) {m : ℕ} (hm : 0 < m) :
    ¬ Nonempty (G ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m) := by
  rintro ⟨j⟩
  let Q := P.mapSurjective (f := j.toMonoidHom) j.surjective
  obtain ⟨R,hR⟩ := BenderSuzuki.MatrixGroups.suzukiRootSubgroup_isSylow m hm
  let e : P ≃* BenderSuzuki.MatrixGroups.SuzukiRootSubgroup m :=
    ((P : Subgroup G).equivMapOfInjective j.toMonoidHom j.injective).trans
      ((Q.equiv R).trans (MulEquiv.subgroupCongr hR))
  have h4 : x ^ 4 = 1 := e.injective (by
    rw [map_pow,map_one]
    exact BenderSuzuki.MatrixGroups.suzukiRootSubgroup_pow_four m hm (e x))
  exact not_order_eight_of_pow_four x h4 hx

theorem not_alternating_eight_of_sylow_order_eight
    (P : Sylow 2 G) (x : P) (hx : orderOf x = 8) :
    ¬ Nonempty (G ≃* alternatingGroup (Fin 8)) := by
  rintro ⟨j⟩
  apply not_binary_small_linear_of_sylow_order_eight P x hx (n := 4) (f := 1) (by decide)
  refine ⟨ZMod 2,inferInstance,inferInstance,by simp,?_⟩
  exact ⟨j.trans Atlas.Comparisons.Exceptional.alt8EquivPSL4Two⟩
end CFSG.Quasithin.ChapterF.SourceAssembly.ComponentSieve.LargeGoldschmidt
