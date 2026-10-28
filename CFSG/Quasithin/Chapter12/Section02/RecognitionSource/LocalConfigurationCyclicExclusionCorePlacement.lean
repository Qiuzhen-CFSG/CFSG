module
public import CFSG.Quasithin.Chapter12.Section02.RecognitionSource.LocalConfigurationCyclicExclusionNumericalSize
public import Theory.SpecificGroups.BinaryLinear.SmallParabolicLevi.FirstPair
public import Theory.GroupTheory.TwoCoreOddSylowSupplement
public import Theory.GroupTheory.SylowLocalCore
public import Theory.GroupTheory.SylowNormalizerFrattini
public import Theory.GroupTheory.PResidual.NormalizedImageContainment

/-!
# Placing the extraspecial Frattini group and its module in L

The literal product Φ(P)T has index p over T. Faithfulness on V forces
its action kernel to be a two-group. The image of its normal intersection
with L contains a full Sylow of GL₃(2). Self-normalization of that Sylow
and the Frattini argument make this intersection's image the full product
image. Lifting through the two-kernel places the odd Φ(P) inside L.
Since W=[W,Φ(P)] and W normalizes L, the whole W lies in L as well.

LocalConfigurationCyclicExclusionCoreGeometry uses both placements on the
original subgroups. The remaining core module reconstruction and final
assembly belong to qt-d-12213-cyclic-block.
Source: Aschbacher–Smith, 12.2.23, printed p.804.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative Pointwise
namespace CFSG.Quasithin.Chapter12.Section02.RecognitionSource
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {L V H P U W : Subgroup G} {d p : ℕ} {g v : G}
namespace InvariantOddLocalAnalysis
variable (S : InvariantOddLocalAnalysis T L V d p H P U W g v)
include S

private theorem frattini_sylow_action_two_kernel
    (he : IsExtraspecial p P)
    {K : Type*} [Group K]
    (f : ((frattini P).map P.subtype ⊔ (T : Subgroup G) : Subgroup G) →* K)
    (hinj : Function.Injective (f.comp (inclusion
      (le_sup_left : (frattini P).map P.subtype ≤ _)))) : IsPGroup 2 f.ker := by
  let Φ := (frattini P).map P.subtype
  let B := Φ ⊔ (T : Subgroup G)
  let b := f.comp (inclusion (le_sup_left : Φ ≤ B))
  have hb : Nat.card b.range = p :=
    (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm.trans
      (S.frattini_card_of_extraspecial he)
  have hpdiv : p ∣ Nat.card f.range := by
    rw [← hb]
    apply card_dvd_of_le
    rintro x ⟨z, rfl⟩
    exact ⟨inclusion (le_sup_left : Φ ≤ B) z, rfl⟩
  obtain ⟨m, hm⟩ := hpdiv
  have hB := relIndex_mul_relIndex (⊥ : Subgroup G) (T : Subgroup G) B bot_le le_sup_right
  rw [relIndex_bot_left, relIndex_bot_left, S.extraspecial_frattini_sylow_index he] at hB
  have hk := f.ker.card_mul_index
  rw [index_ker, hm] at hk
  have hc : Nat.card f.ker * m = Nat.card T := by
    apply Nat.eq_of_mul_eq_mul_left S.prime.pos
    calc
      p * (Nat.card f.ker * m) = Nat.card f.ker * (p * m) := by ring
      _ = Nat.card B := hk
      _ = p * Nat.card T := by rw [← hB, Nat.mul_comm]
  obtain ⟨n, hn⟩ := T.isPGroup'.exists_card_eq
  apply IsPGroup.of_card_dvd_pow (n := n)
  rw [← hn, ← hc]
  exact dvd_mul_right _ _

/-- The embedded Frattini subgroup lies in the original component. -/
theorem extraspecial_frattini_le_component
    (D : ChosenModule T L V) (A : NaturalLocalAnalysis T L V d)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
    (he : IsExtraspecial p P)
    (hf : W ⊓ centralizer (((frattini P).map P.subtype : Subgroup G) : Set G) = ⊥)
    (hd : d = 3) : (frattini P).map P.subtype ≤ L := by
  subst d
  let Φ := (frattini P).map P.subtype
  let B := Φ ⊔ (T : Subgroup G)
  have hBN : B ≤ normalizer (V : Set G) := sup_le S.frattini_normalizes hTV
  have hBM : B ≤ normalizer (L : Set G) := sup_le
    (by change (frattini P).map P.subtype ≤ _; rw [S.frattini_intersection]; exact inf_le_right) D.sylow_normalizes_component
  obtain ⟨_, E, _⟩ := A.natural
  let eAut := MulEquiv.ofBijective (Representation.binaryNaturalAut 3)
    (Representation.binaryNaturalAut_bijective 3)
  let c : MulAut V ≃* BinaryLinear.OuterCyclic.LinearGroup 3 :=
    (MulAut.congr E).trans (eAut.symm.trans (BinaryLinear.OuterCyclic.slEquivLinear 3))
  let f : B →* BinaryLinear.OuterCyclic.LinearGroup 3 :=
    c.toMonoidHom.comp (V.normalizerMonoidHom.comp (inclusion hBN))
  let a : L →* BinaryLinear.OuterCyclic.LinearGroup 3 :=
    c.toMonoidHom.comp (V.normalizerMonoidHom.comp (inclusion D.normalizes))
  have ha : Function.Surjective a := c.surjective.comp (A.componentAut_surjective D)
  let : Finite (BinaryLinear.OuterCyclic.LinearGroup 3) := Finite.of_surjective a ha
  let J := L ⊔ (T : Subgroup G)
  obtain ⟨R, hR⟩ := (T.subtype (show (T : Subgroup G) ≤ J from le_sup_right)).exists_map_subtype_eq_inf_of_normalizes
    (show L ≤ J from le_sup_left) (sup_le L.le_normalizer D.sylow_normalizes_component)
  have hR' : (R : Subgroup L).map L.subtype = (T : Subgroup G) ⊓ L := by
    simpa only [Sylow.coe_subtype, map_subgroupOf_eq_of_le
      (show (T : Subgroup G) ≤ J from le_sup_right)] using hR
  let R' := R.mapSurjective ha
  let C := L.subgroupOf B
  let : C.Normal := normal_subgroupOf_of_le_normalizer hBM
  have hRC : (R' : Subgroup _) ≤ C.map f := by
    rintro x ⟨l, hl, rfl⟩
    have ht : (l : G) ∈ (T : Subgroup G) := (hR' ▸ mem_map_of_mem L.subtype hl).1
    exact ⟨⟨l, (le_sup_right : (T : Subgroup G) ≤ B) ht⟩, l.property, rfl⟩
  have hnorm : f.range ≤ normalizer (C.map f : Set _) := by
    simpa only [normalizer_eq_top, ← MonoidHom.range_eq_map] using C.le_normalizer_map f
  have hcover := le_normalizer_sylow_sup (C.map f) f.range (map_le_range _ _)
    hnorm (R'.subtype hRC)
  have hmapR : ((R'.subtype hRC : Sylow 2 (C.map f)) : Subgroup (C.map f)).map
      (C.map f).subtype = (R' : Subgroup _) := map_subgroupOf_eq_of_le hRC
  have hself : normalizer ((R' : Subgroup (BinaryLinear.OuterCyclic.LinearGroup 3)) : Set _) = (R' : Subgroup (BinaryLinear.OuterCyclic.LinearGroup 3)) := by
    obtain ⟨b, hb⟩ := BinaryLinear.InvariantNodeActions.sylow_eq_cutStabilizer (m := 2) R'
    rw [hb]
    exact BinaryLinear.SylowFlagOvergroups.normalizer_fullFlag_eq b
  rw [hmapR, hself, sup_eq_right.mpr hRC] at hcover
  have hk : IsPGroup 2 f.ker := S.frattini_sylow_action_two_kernel he f
    (c.injective.comp (S.frattini_chosen_action_faithful A he hf))
  have hPhi : IsPPerfect 2 (Φ.subgroupOf B) := by
    let : Fact p.Prime := ⟨S.prime⟩
    apply (pResidual_eq_top_iff 2 (Φ.subgroupOf B)).mp
    exact top_unique (odd_prime_subgroup_le_twoResidual S.odd_prime ⊤
      (((S.pgroup.to_le (map_subtype_le _)).comap_subtype).to_subgroup ⊤))
  have hle := isPPerfect_le_of_map_le_of_kernel_normalizes f (Φ.subgroupOf B) C
    hPhi hk (by rw [normalizer_eq_top]; exact le_top)
    ((map_le_range _ _).trans hcover)
  intro x hx
  exact hle (show (⟨x, (le_sup_left : Φ ≤ B) hx⟩ : B) ∈ Φ.subgroupOf B from hx)

/-- The fixed-point-free Frattini displacement places the whole W in L. -/
theorem extraspecial_module_le_component
    (D : ChosenModule T L V) (A : NaturalLocalAnalysis T L V d)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
    (he : IsExtraspecial p P)
    (hf : W ⊓ centralizer (((frattini P).map P.subtype : Subgroup G) : Set G) = ⊥)
    (hd : d = 3) : W ≤ L := by
  rw [← S.frattini_moves_module hf]
  exact (commutator_mono le_rfl (S.extraspecial_frattini_le_component D A hTV he hf hd)).trans
    (le_normalizer_iff_commutator_le_right.mp
      (S.module_le_sylow.trans D.sylow_normalizes_component))

end InvariantOddLocalAnalysis
end CFSG.Quasithin.Chapter12.Section02.RecognitionSource
