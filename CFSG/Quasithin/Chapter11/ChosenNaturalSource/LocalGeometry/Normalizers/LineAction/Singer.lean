module

public import CFSG.Quasithin.ChapterA.Section01.Linear.Singer
public import Theory.GroupTheory.CyclicSylowTwoComplement
public import Theory.Representation.BinarySingerNormalizer
public import Mathlib.GroupTheory.SpecificGroups.Cyclic
public import Theory.GroupTheory.NormalizedSupCard

/-!
# Singer normality in the source line action

The actual Sylow image lies in the normalizer of the regular cyclic Cartan
image. Its cyclicity gives an odd normal complement. Apply A.1.12 to the
product of the odd core with the Cartan image. The whole action group then
normalizes that image. Its centralizer is the image itself, and the
automorphism group of the cyclic image is abelian. Hence every intermediate
subgroup containing the image is normal in its normalizer. This proves the normality needed for
the first Frattini argument without a choice of semilinear coordinates.

Source: Aschbacher--Smith, combined manuscript, 1 March 2004,
11.2.3, printed pp.768--769, using A.1.12 and A.1.38.
-/

open Subgroup
open scoped commutatorElement IsMulCommutative
public noncomputable section
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.LineAction

private theorem cyclic_normalizer_intermediate
    {H : Type*} [Group H] (X A : Subgroup H) [IsCyclic X]
    (hC : centralizer (X : Set H) ≤ X) (hXA : X ≤ A)
    (hAN : A ≤ normalizer (X : Set H)) :
    normalizer (X : Set H) ≤ normalizer (A : Set H) := by
  apply le_normalizer_iff_commutator_le_right.mpr
  apply commutator_le.mpr
  intro g hg a ha
  let q := X.normalizerMonoidHom
  let g' : normalizer (X : Set H) := ⟨g, hg⟩
  let a' : normalizer (X : Set H) := ⟨a, hAN ha⟩
  have hc : Commute (q g') (q a') := by
    apply (IsCyclic.mulAutMulEquiv X).injective
    exact (map_mul _ _ _).trans ((mul_comm _ _).trans (map_mul _ _ _).symm)
  have hk : ⁅g',a'⁆ ∈ q.ker := by
    rw [MonoidHom.mem_ker, map_commutatorElement]
    exact commutatorElement_eq_one_iff_mul_comm.mpr hc.eq
  rw [normalizerMonoidHom_ker] at hk
  exact hXA (hC hk)

variable {W : Type*} [AddCommGroup W] [Module (ZMod 2) W] [Finite W]

/-- Two-subgroups normalizing this actual Singer group are cyclic. -/
theorem regular_two_subgroup_cyclic
    (X P : Subgroup (W ≃ₗ[ZMod 2] W)) [IsCyclic X]
    (hreg : LinearGroup.IsRegularOnNonzero X)
    (hP : IsPGroup 2 P) (hPN : P ≤ normalizer (X : Set _)) : IsCyclic P := by
  let e := (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) W).symm
  let C := X.map e.toMonoidHom
  let Q := P.map e.toMonoidHom
  let : IsCyclic C := isCyclic_of_surjective (e.toMonoidHom.subgroupMap X)
    (e.toMonoidHom.subgroupMap_surjective X)
  have hr : ∀ v w : W, v ≠ 0 → w ≠ 0 →
      ∃! c : C, (c.val : Module.End (ZMod 2) W) v = w := by
    intro v w hv hw
    obtain ⟨x,hx,hu⟩ := hreg v w hv hw
    refine ⟨⟨e x, mem_map_of_mem _ x.property⟩, hx, ?_⟩
    rintro ⟨a, b, hb, rfl⟩ ha
    have hbx := hu ⟨b,hb⟩ ha
    exact Subtype.ext (congrArg e (congrArg Subtype.val hbx))
  let : IsCyclic Q := Representation.BinarySingerNormalizer.isCyclic_of_isPGroup_le_normalizer
    C hr Q (hP.map e.toMonoidHom)
    ((map_mono hPN).trans (X.le_normalizer_map e.toMonoidHom))
  exact (P.equivMapOfInjective e.toMonoidHom e.injective).isCyclic.mpr inferInstance

/-- The actual action group normalizes the join of its Cartan and Sylow images. -/
theorem singer_sylow_join_normalized
    [FiniteDimensional (ZMod 2) W] [Nontrivial W]
    (X Y : Subgroup (W ≃ₗ[ZMod 2] W)) [IsCyclic X]
    (hreg : LinearGroup.IsRegularOnNonzero X) (hXY : X ≤ Y)
    (hodd : Odd (Nat.card X)) (P : Sylow 2 Y)
    (hPN : (P : Subgroup Y).map Y.subtype ≤ normalizer (X : Set _)) :
    Y ≤ normalizer ((X ⊔ (P : Subgroup Y).map Y.subtype : Subgroup _) : Set _) := by
  let : Finite (W ≃ₗ[ZMod 2] W) := Finite.of_injective
    (fun g : W ≃ₗ[ZMod 2] W => (g : W → W)) DFunLike.coe_injective
  let O := pPrimeCore 2 Y
  let B := X.subgroupOf Y
  let U := O ⊔ B
  have hUodd : Odd (Nat.card U) := by
    have ho : Odd (Nat.card O) := Nat.coprime_two_left.mp
      (pPrimeCore_coprime_card (p := 2) (G := Y))
    have hb : Odd (Nat.card B) := by
      rwa [Nat.card_congr (subgroupOfEquivOfLe hXY).toEquiv]
    have hh := card_mul_eq_card_inf_mul_card_sup_of_normalizes O B
      (show B ≤ normalizer (O : Set Y) from le_normalizer_of_normal)
    exact (Nat.odd_mul.mp (hh ▸ ho.mul hb)).2
  have hXU : X ≤ U.map Y.subtype := by
    rw [← map_subgroupOf_eq_of_le hXY]
    exact map_mono le_sup_right
  have hN := (normal_subgroupOf_iff_le_normalizer hXU).mp
    (CFSG.Quasithin.ChapterA.Singer.normal_of_odd X (U.map Y.subtype)
      inferInstance hreg hXU (by
        rwa [Nat.card_congr (U.equivMapOfInjective Y.subtype Y.subtype_injective).toEquiv] at hUodd))
  have hON : O.map Y.subtype ≤ normalizer (X : Set _) :=
    (map_mono le_sup_left).trans hN
  have hcyc : IsCyclic P := by
    let hp := regular_two_subgroup_cyclic X ((P : Subgroup Y).map Y.subtype)
      hreg (P.isPGroup'.map Y.subtype) hPN
    exact ((P : Subgroup Y).equivMapOfInjective Y.subtype Y.subtype_injective).isCyclic.mpr hp
  have hcover : O ⊔ (P : Subgroup Y) = ⊤ := by
    by_cases heven : 2 ∣ Nat.card Y
    · simpa only [sup_comm] using (P.isComplement'_pPrimeCore_of_isCyclic hcyc heven).sup_eq_top
    · have ht : O = ⊤ := top_unique (le_sSup (show
        (⊤ : Subgroup Y) ∈ normalPPrimeSubgroups 2 Y from
        ⟨inferInstance, by simpa using Nat.prime_two.coprime_iff_not_dvd.mpr heven⟩))
      rw [ht, top_sup_eq]
  have hYN : Y ≤ normalizer (X : Set _) := by
    have hm := congrArg (map Y.subtype) hcover
    rw [Subgroup.map_sup, ← MonoidHom.range_eq_map, Y.range_subtype] at hm
    rw [← hm]
    exact sup_le hON hPN
  exact hYN.trans (cyclic_normalizer_intermediate X _ hreg.centralizer_eq.le le_sup_left
    (sup_le X.le_normalizer hPN))

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.LineAction
