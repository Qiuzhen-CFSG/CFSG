module

public import CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.Centralizers.Pure.Sylows.Four.SourceOmegaBoundary
public import CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.Centralizers.Nonsingular.Adapted
public import Theory.GroupTheory.IndexTwoCentralizerFixedCard

/-!
# The exact small point-omega branch in degree four

The original doubled orbit has a one-dimensional fixed space under the full
Sylow. The marked point centralizer has index two in that Sylow, so its
fixed subgroup in the doubled orbit has order at most four. The original
pure point is fixed by that subgroup but not by the full Sylow; consequently
the order is exactly four. Combining this with the global omega splitting
identifies the remaining branch of the marked fixed-subgroup problem.
No MS classification, ambient Sylow conclusion, or fusion assertion is used.
-/

public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative

namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter12.Section01.DoubleNaturalSource
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

/-- The actual full Sylow fixes exactly a line in the original doubled orbit. -/
theorem doubleNatural_sylow_fixed_card_two
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    {n : ℕ} (B : DoubledBranch T L V n) :
    letI := D.doubledOrbit_elementary h
    ∀ _ : B.SourceModel,
      Nat.card (componentOrbit V (T : Subgroup G) ⊓ centralizer (T : Set G) : Subgroup G) = 2 := by
  let := D.doubledOrbit_elementary h
  intro S
  let W := componentOrbit V (T : Subgroup G)
  have hn : 0 < n := by have := B.degree; omega
  let v : BinaryLinear.OuterCyclic.Space n := fun _ => 1
  let φ : Module.Dual (ZMod 2) (BinaryLinear.OuterCyclic.Space n) := LinearMap.proj ⟨0, hn⟩
  let w : W := B.coordinates.symm (Multiplicative.ofAdd (v, φ))
  have hq : B.quadratic (Additive.ofMul w) = 1 := by
    rw [B.quadratic_apply]
    change (B.coordinates (B.coordinates.symm (Multiplicative.ofAdd (v, φ)))).toAdd.2
      (B.coordinates (B.coordinates.symm (Multiplicative.ofAdd (v, φ)))).toAdd.1 = 1
    rw [B.coordinates.apply_symm_apply]
    rfl
  obtain ⟨_, _, _, ha⟩ := D.doubleNatural_adaptedPoint h B S w hq
  have hd := ha.fixed_rank
  let e : B.fixedSpace (T : Subgroup G) ≃ (W ⊓ centralizer (T : Set G) : Subgroup G) := {
    toFun x := ⟨x.val.toMul.val, x.val.toMul.property,
      (mem_subgroupSpace _ _ x.val).mp x.property⟩
    invFun x := ⟨Additive.ofMul ⟨x.val, x.property.1⟩,
      (mem_subgroupSpace _ _ _).mpr x.property.2⟩
    left_inv _ := rfl
    right_inv _ := rfl }
  rw [← Nat.card_congr e, Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod, hd]
  rfl

/-- The same marked point two-group fixes exactly a four-group in the original
doubled orbit, without assuming that it is an ambient point Sylow. -/
theorem doubleNatural_marked_point_fixed_card_four
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    {n : ℕ} (B : DoubledBranch T L V n) :
    letI := D.doubledOrbit_elementary h
    ∀ S : B.SourceModel, ∀ w : componentOrbit V (T : Subgroup G), w ≠ 1 →
      ∀ hp : (B.coordinates w).toAdd.2 = 0,
      (⟨Additive.ofMul w, (S.natural_marking w).mpr hp⟩ : S.setup.natural) ∈
        S.setup.naturalFixed (S.setup.naturalSylowNormalizer
          ((T.subtype D.sylow_normalizes_component).mapSurjective B.actionProjection_surjective)) →
      Nat.card (componentOrbit V (T : Subgroup G) ⊓
        centralizer (B.pointSylow w : Set G) : Subgroup G) = 4 := by
  let := D.doubledOrbit_elementary h
  intro S w hw hp hfix
  let W := componentOrbit V (T : Subgroup G)
  let R := B.pointSylow w
  let A := W ⊓ centralizer (R : Set G)
  let C := W ⊓ centralizer (T : Set G)
  let : IsElementaryAbelian 2 A := IsElementaryAbelian.of_le (show A ≤ W from inf_le_left)
  have he := S.marked_centralizer_eq D.sylow_normalizes_component w hw hp hfix
  change R = _ at he
  have hi : R.relIndex (T : Subgroup G) = 2 := by
    rw [he]
    exact S.naturalSylowNormalizer_relIndex D.sylow_normalizes_component
  let := normal_of_index_eq_two hi
  have hTR : (T : Subgroup G) ≤ normalizer (R : Set G) :=
    (normal_subgroupOf_iff_le_normalizer (show R ≤ (T : Subgroup G) from inf_le_left)).mp inferInstance
  have hTW : (T : Subgroup G) ≤ normalizer (W : Set G) := by
    dsimp [W]
    rw [B.orbit_eq]
    exact D.sylow_normalizes_component.trans (le_normalizer_componentOrbit _ _)
  have hTA : (T : Subgroup G) ≤ normalizer (A : Set G) :=
    (le_inf hTW (hTR.trans (normalizer_le_normalizer_centralizer R))).trans
      inf_normalizer_le_normalizer_inf
  have hCA : C ≤ A := inf_le_inf_left _ (centralizer_le (show R ≤ (T : Subgroup G) from inf_le_left))
  have hc : Nat.card C = 2 := D.doubleNatural_sylow_fixed_card_two h B S
  have hiC : (centralizer (T : Set G)).subgroupOf A = C.subgroupOf A := by
    ext x
    exact ⟨fun hx => ⟨x.property.1, hx⟩, fun hx => hx.2⟩
  have hb := card_le_centralizer_card_sq_of_relIndex_two A R (T : Subgroup G)
    hTA inf_le_right hi
  change Nat.card A ≤ Nat.card ((centralizer (T : Set G)).subgroupOf A) ^ 2 at hb
  rw [hiC, Nat.card_congr (subgroupOfEquivOfLe hCA).toEquiv, hc] at hb
  have hwA : (w : G) ∈ A := by
    refine ⟨w.property, ?_⟩
    intro r hr
    exact mem_centralizer_singleton_iff.mp hr.2
  have hwC : (w : G) ∉ C := by
    intro hwC
    have hle : (T : Subgroup G) ≤ R := by
      intro t ht
      exact ⟨ht, mem_centralizer_singleton_iff.mpr (hwC.2 t ht)⟩
    have hone := relIndex_eq_one.mpr hle
    omega
  have hlt : C < A := lt_of_le_of_ne hCA (fun hh => hwC (hh.symm ▸ hwA))
  have hcLt : Nat.card C < Nat.card A := lt_of_le_of_ne (card_le_of_le hCA)
    (fun hh => hlt.ne (eq_of_le_of_card_ge hCA hh.symm.le))
  have hd := card_dvd_of_le hCA
  rw [hc] at hcLt hd
  change Nat.card A = 4
  omega

/-- Failure of the marked fixed-subgroup conclusion forces a literal
four-group point omega and no extra global core-omega summand. -/
theorem doubleNatural_four_pure_omega_fixed_or_card_four
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (B : DoubledBranch T L V 4) :
    letI := D.doubledOrbit_elementary h
    ∀ S : B.SourceModel, ∀ w : componentOrbit V (T : Subgroup G), w ≠ 1 →
      ∀ hp : (B.coordinates w).toAdd.2 = 0,
      (⟨Additive.ofMul w, (S.natural_marking w).mpr hp⟩ : S.setup.natural) ∈
        S.setup.naturalFixed (S.setup.naturalSylowNormalizer
          ((T.subtype D.sylow_normalizes_component).mapSurjective B.actionProjection_surjective)) →
      ¬ Chapter1.IsSylowIn 2 (B.pointSylow w) (B.pointCentralizer w) →
      omegaCenterIn (B.pointSylow w) ⊓ centralizer (L : Set G) ≠ ⊥ ∨
        (omegaCenterIn ((L ⊔ (T : Subgroup G)).pCoreIn 2) =
            componentOrbit V (T : Subgroup G) ∧
          omegaCenterIn (B.pointSylow w) =
            componentOrbit V (T : Subgroup G) ⊓ centralizer (B.pointSylow w : Set G) ∧
          Nat.card (omegaCenterIn (B.pointSylow w)) = 4) := by
  let := D.doubledOrbit_elementary h
  intro S w hw hp hfix hf
  rcases D.doubleNatural_four_pure_omega_fixed_or_core_omega_eq_orbit
    h hmany B S w hw hp hfix hf with hne | ⟨hQ, hR⟩
  · exact Or.inl hne
  · exact Or.inr ⟨hQ, hR, hR ▸ D.doubleNatural_marked_point_fixed_card_four h B S w hw hp hfix⟩

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
