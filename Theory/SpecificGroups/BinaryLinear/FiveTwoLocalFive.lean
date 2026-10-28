module
public import Theory.SpecificGroups.BinaryLinear.FiveElementaryNormalizer

/-!
# Two-subgroups of GL₅(2) with a factor five in their normalizer

An element of order five forces every nonzero proper invariant subspace of
the natural module to be a line or a hyperplane. The fixed space of a
nontrivial two-subgroup is such a subspace. In the line case, the GL₄(2)
quotient has no nontrivial two-subgroup normalized by a five-element, so the
original subgroup lies in the order-sixteen translation kernel. The graph
automorphism reduces the hyperplane case to the line case.

This extends the order-sixteen normalizer calculation without assuming the
order in advance. Its consumer is the literal PSL₅(2) exclusion in
Aschbacher--Smith 12.6.12, printed pp.825--826.
-/

public section
noncomputable section
open Subgroup
namespace BinaryLinear.FiveTwoLocalFive
open OuterCyclic Theory.LinearAlgebra FiveElementaryNormalizer
private instance : Finite (LinearGroup 5) :=
  Finite.of_equiv (Matrix.GeneralLinearGroup (Fin 5) (ZMod 2))
    (matrixEquivLinear 5).toEquiv

private theorem card_le_of_fixed_point (U : Subgroup (LinearGroup 5))
    (hU : IsPGroup 2 U)
    (hfive : 5 ∣ Nat.card (normalizer (U : Set (LinearGroup 5))))
    (v : Space 5) (hv : v ≠ 0)
    (hNv : normalizer (U : Set (LinearGroup 5)) ≤ BinaryFivePointStabilizer.stabilizer v) :
    Nat.card U ≤ 16 := by
  let P := BinaryFivePointStabilizer.stabilizer v
  let A := U.subgroupOf P
  let q := pointQuotient v hv
  have hUP : U ≤ P := U.le_normalizer.trans hNv
  have hqker : IsPGroup 2 q.ker := by
    rw [pointQuotient_ker]
    exact IsElementaryAbelian.isPGroup 2 _
  have hA : IsPGroup 2 A := hU.comap_subtype
  have him : A.map q = ⊥ := by
    by_contra hne
    apply FourTwoLocalFive.five_not_dvd_normalizer (A.map q) (hA.map q) hne
    let : Fact (Nat.Prime 5) := ⟨by decide⟩
    obtain ⟨g,hg⟩ := exists_prime_orderOf_dvd_card' 5 hfive
    let a : P := ⟨g.val,hNv g.property⟩
    have ha : orderOf a = 5 := by
      have hh := orderOf_injective P.subtype P.subtype_injective a
      exact hh.symm.trans ((orderOf_injective _
        (normalizer (U : Set (LinearGroup 5))).subtype_injective g).trans hg)
    have haq : orderOf (q a) = 5 :=
      (q.orderOf_map_eq_of_coprime_of_isPGroup_ker hqker a (by rw [ha]; decide)).trans ha
    have han : a ∈ normalizer (A : Set P) := by
      change a ∈ normalizer (U.subgroupOf P : Set P)
      rw [← subgroupOf_normalizer_eq hUP]
      exact g.property
    have hqan : q a ∈ normalizer (A.map q : Set (LinearGroup 4)) :=
      le_normalizer_map q (mem_map_of_mem q han)
    have hd := (normalizer (A.map q : Set (LinearGroup 4))).orderOf_dvd_natCard hqan
    rwa [haq] at hd
  have hAk : A ≤ q.ker := by
    rw [← Subgroup.map_eq_bot_iff]
    exact him
  have hUk : U ≤ (BinaryFivePointStabilizer.kernel v).map P.subtype := by
    rw [← map_subgroupOf_eq_of_le hUP]
    exact map_mono (pointQuotient_ker v hv ▸ hAk)
  have hh := card_le_of_le hUk
  rwa [card_map_of_injective P.subtype_injective,
    BinaryFivePointStabilizer.natCard_kernel v hv (by simp [Space])] at hh

/-- A two-subgroup whose normalizer contains a factor five has order at most
sixteen, regardless of whether it is elementary or normal in a Sylow. -/
theorem card_le_sixteen (U : Subgroup (LinearGroup 5))
    (hU : IsPGroup 2 U)
    (hfive : 5 ∣ Nat.card (normalizer (U : Set (LinearGroup 5)))) :
    Nat.card U ≤ 16 := by
  by_cases hU0 : U = ⊥
  · rw [hU0,card_bot]; decide
  let W := fixedSpace U
  have hW0 : W ≠ ⊥ := fixedSpace_ne_bot (by norm_num [Space,Nat.card_fun]) hU
  have hWt : W ≠ ⊤ := fixedSpace_ne_top hU0
  have hNW : normalizer (U : Set (LinearGroup 5)) ≤ parabolic W :=
    normalizer_le_parabolic_fixedSpace U
  rcases (FiveFlagGeometry.GeometricFlags.invariant_subspaces_of_five_dvd _ hfive).1
      W hW0 hWt hNW with hd | hd
  · obtain ⟨b,hb⟩ := FiveFlagGeometry.GeometricFlags.exists_flagSpace W 0 hd
    rw [FiveFlagGeometry.flagSpace_zero] at hb
    apply card_le_of_fixed_point U hU hfive (b 0) (b.ne_zero 0)
    rw [←FiveFlagGeometry.pointParabolic_eq_stabilizer (b.ne_zero 0),hb]
    exact hNW
  · obtain ⟨b,hb⟩ := FiveFlagGeometry.GeometricFlags.exists_flagSpace W 3 hd
    rw [FiveFlagGeometry.flagSpace_last] at hb
    let f := b.coord 4
    have hf : f ≠ 0 := by
      intro he
      have hh := LinearMap.congr_fun he (b 4)
      simp [f,Module.Basis.coord_apply] at hh
    obtain ⟨v,hv,he⟩ := FiveParabolicStabilizer.hyperplane_map_graph hf
    let a := graphLinear 5
    let V := U.map a.toMonoidHom
    have hV : IsPGroup 2 V := hU.map _
    have hNV : normalizer (V : Set (LinearGroup 5)) =
        (normalizer (U : Set (LinearGroup 5))).map a.toMonoidHom :=
      (map_equiv_normalizer_eq U a).symm
    have hVfive : 5 ∣ Nat.card (normalizer (V : Set (LinearGroup 5))) := by
      rw [hNV,card_map_of_injective a.injective]
      exact hfive
    have hVP : normalizer (V : Set (LinearGroup 5)) ≤
        BinaryFivePointStabilizer.stabilizer v := by
      rw [←FiveFlagGeometry.pointParabolic_eq_stabilizer hv,hNV,←he]
      exact map_mono (hb.symm ▸ hNW)
    have hh := card_le_of_fixed_point V hV hVfive v hv hVP
    rwa [card_map_of_injective a.injective] at hh
end BinaryLinear.FiveTwoLocalFive
