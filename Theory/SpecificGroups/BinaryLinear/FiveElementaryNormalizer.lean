module
public import Theory.SpecificGroups.BinaryLinear.FiveFlagGeometry.Residuals.GeometricFlags
public import Theory.SpecificGroups.BinaryLinear.FourTwoLocalFive
public import Theory.LinearAlgebra.BinaryFivePointStabilizer.KernelCard
public import Theory.GroupTheory.PrimeOrderLift

/-!
# Sixteen-group normalizers in GL₅(2)

A two-subgroup of order sixteen whose normalizer has a factor five has a
proper nonzero fixed space of dimension one or four. In the point case,
the image in GL₄(2) is trivial: a nontrivial two-subgroup there has no factor
five in its normalizer. Equality of orders identifies the full point radical.
Inverse transpose treats the hyperplane case. Thus the actual normalizer
is an endpoint parabolic, without an assumed placement or normalizer bound.

Source: Aschbacher–Smith 2.4.25, printed p.543, the binary-five local inspection.
-/

public section
noncomputable section
open Subgroup
namespace BinaryLinear.FiveElementaryNormalizer
open OuterCyclic Theory.LinearAlgebra
private instance : Finite (LinearGroup 5) :=
  Finite.of_equiv (Matrix.GeneralLinearGroup (Fin 5) (ZMod 2))
    (matrixEquivLinear 5).toEquiv

def pointQuotient (v : Space 5) (hv : v ≠ 0) :
    BinaryFivePointStabilizer.stabilizer v →* LinearGroup 4 :=
  (((BinaryFivePointStabilizer.quotientEquivGL4 v hv (by simp [Space])).trans
    (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) (Space 4))).toMonoidHom).comp
      (QuotientGroup.mk' (BinaryFivePointStabilizer.kernel v))

theorem pointQuotient_surjective (v : Space 5) (hv : v ≠ 0) :
    Function.Surjective (pointQuotient v hv) :=
  ((BinaryFivePointStabilizer.quotientEquivGL4 v hv (by simp [Space])).trans
    (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) (Space 4))).surjective.comp
      (QuotientGroup.mk'_surjective (BinaryFivePointStabilizer.kernel v))

theorem pointQuotient_ker (v : Space 5) (hv : v ≠ 0) :
    (pointQuotient v hv).ker = BinaryFivePointStabilizer.kernel v := by
  ext g
  let e := (BinaryFivePointStabilizer.quotientEquivGL4 v hv (by simp [Space])).trans
    (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) (Space 4))
  change e (QuotientGroup.mk' (BinaryFivePointStabilizer.kernel v) g) = 1 ↔ _
  rw [e.map_eq_one_iff]
  exact QuotientGroup.eq_one_iff g

/-- A sixteen-group with a factor five in its normalizer is the whole
point radical whenever that normalizer fixes a nonzero vector. -/
theorem eq_point_kernel (U : Subgroup (LinearGroup 5))
    (hU : IsPGroup 2 U) (hc : Nat.card U = 16)
    (hfive : 5 ∣ Nat.card (normalizer (U : Set (LinearGroup 5))))
    (v : Space 5) (hv : v ≠ 0)
    (hNv : normalizer (U : Set (LinearGroup 5)) ≤ BinaryFivePointStabilizer.stabilizer v) :
    U = (BinaryFivePointStabilizer.kernel v).map
      (BinaryFivePointStabilizer.stabilizer v).subtype := by
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
  apply eq_of_le_of_card_ge hUk
  rw [card_map_of_injective P.subtype_injective,
    BinaryFivePointStabilizer.natCard_kernel v hv (by simp [Space]),hc]


theorem point_kernel_map (v : Space 5) :
    (BinaryFivePointStabilizer.kernel v).map
      (BinaryFivePointStabilizer.stabilizer v).subtype =
        radical (Submodule.span (ZMod 2) {v}) := by
  ext g
  constructor
  · rintro ⟨g,hg,rfl⟩
    exact ⟨BinaryFivePointStabilizer.fixes_line v g,
      (BinaryFivePointStabilizer.mem_kernel_iff v g).mp hg⟩
  · intro hg
    have hp : g ∈ BinaryFivePointStabilizer.stabilizer v :=
      hg.1 v (Submodule.mem_span_singleton_self v)
    exact ⟨⟨g,hp⟩,(BinaryFivePointStabilizer.mem_kernel_iff v _).mpr hg.2,rfl⟩

private theorem normalizer_eq_point (U : Subgroup (LinearGroup 5))
    (hU : IsPGroup 2 U) (hc : Nat.card U = 16)
    (hfive : 5 ∣ Nat.card (normalizer (U : Set (LinearGroup 5))))
    (v : Space 5) (hv : v ≠ 0)
    (hNv : normalizer (U : Set (LinearGroup 5)) ≤
      parabolic (Submodule.span (ZMod 2) {v})) :
    normalizer (U : Set (LinearGroup 5)) =
      parabolic (Submodule.span (ZMod 2) {v}) := by
  have he := eq_point_kernel U hU hc hfive v hv (by
    rwa [FiveFlagGeometry.pointParabolic_eq_stabilizer hv] at hNv)
  rw [point_kernel_map] at he
  rw [he, normalizer_radical (mt Submodule.span_singleton_eq_bot.mp hv)]

/-- The actual normalizer is an endpoint parabolic; no placement or
normalizer-control hypothesis is assumed. -/
theorem normalizer_isEndParabolic (U : Subgroup (LinearGroup 5))
    (hU : IsPGroup 2 U) (hc : Nat.card U = 16)
    (hfive : 5 ∣ Nat.card (normalizer (U : Set (LinearGroup 5)))) :
    FiveParabolicStabilizer.IsEndParabolic (normalizer (U : Set (LinearGroup 5))) := by
  have hU0 : U ≠ ⊥ := by intro he; rw [he,card_bot] at hc; omega
  let W := fixedSpace U
  have hW0 : W ≠ ⊥ := fixedSpace_ne_bot (by norm_num [Space,Nat.card_fun]) hU
  have hWt : W ≠ ⊤ := fixedSpace_ne_top hU0
  have hNW : normalizer (U : Set (LinearGroup 5)) ≤ parabolic W :=
    normalizer_le_parabolic_fixedSpace U
  rcases (FiveFlagGeometry.GeometricFlags.invariant_subspaces_of_five_dvd _ hfive).1
      W hW0 hWt hNW with hd | hd
  · obtain ⟨b,hb⟩ := FiveFlagGeometry.GeometricFlags.exists_flagSpace W 0 hd
    rw [FiveFlagGeometry.flagSpace_zero] at hb
    exact Or.inl ⟨b 0,b.ne_zero 0,
      normalizer_eq_point U hU hc hfive _ (b.ne_zero 0) (hb.symm ▸ hNW)⟩
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
    have hVc : Nat.card V = 16 := (card_map_of_injective a.injective).trans hc
    have hNV : normalizer (V : Set (LinearGroup 5)) =
        (normalizer (U : Set (LinearGroup 5))).map a.toMonoidHom :=
      (map_equiv_normalizer_eq U a).symm
    have hVfive : 5 ∣ Nat.card (normalizer (V : Set (LinearGroup 5))) := by
      rw [hNV,card_map_of_injective a.injective]
      exact hfive
    have hVP : normalizer (V : Set (LinearGroup 5)) ≤
        parabolic (Submodule.span (ZMod 2) {v}) := by
      rw [hNV,←he]
      exact map_mono (hb.symm ▸ hNW)
    have heq := normalizer_eq_point V hV hVc hVfive v hv hVP
    refine Or.inr ⟨f,hf,?_⟩
    apply Subgroup.map_injective (f := a.toMonoidHom) a.injective
    exact hNV.symm.trans (heq.trans he.symm)

end BinaryLinear.FiveElementaryNormalizer
