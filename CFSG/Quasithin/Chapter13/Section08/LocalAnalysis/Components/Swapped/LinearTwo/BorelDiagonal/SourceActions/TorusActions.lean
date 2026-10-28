module

public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.Components.Swapped.LinearTwo.BorelDiagonal.SourceActions.OrbitActions

/-!
# Descent to the actual common torus coordinates

The binary Borel quotient maps its two axes onto the two torus axes.
Equivariance with the literal source map identifies the induced action with
SourceTorus.normalizerAction. Thus the derived binary axis formulas descend
to this particular action on the common torus. The known factor order also
gives oddness; no additional model-order theorem is used.

Source: Aschbacher–Smith, proof of 13.8.16(1), printed p.952/PDF p.969.
-/

@[expose] public section

open Subgroup
namespace CFSG.Quasithin.Chapter13.Section08.Components.Swapped.LinearTwo.SourceActions
variable {G Q : Type*} [Group G] [Finite G] [Group Q] [Finite Q]
variable (H K₀ : Subgroup G) (hK : K₀ ≤ H)
  (e : Source.starImage H K₀ ≃* Q × Q)
  (S : Sylow 2 (Source.starImage H K₀))
variable {n : ℕ} (hn : 2 ≤ n) (hmodel : ClassicalGroup.IsPSL Q 2 (2 ^ n))

/-- The common torus is the literal first factor quotient. -/
abbrev CommonTorus := BinaryBorel.Torus (BinaryBorel.firstSylow (SourceTorus.chosenSylow H K₀ e S))

/-- The binary Borel map into the same pair of tori as toCommonTori. -/
noncomputable def binaryToCommon : BinaryBorel.borel (SourceTorus.chosenSylow H K₀ e S) →*
    CommonTorus H K₀ e S × CommonTorus H K₀ e S :=
  (SourceTorus.commonTorusCoordinates H K₀ e S hn hmodel).toMonoidHom.comp
    (BinaryBorel.productMap (SourceTorus.chosenSylow H K₀ e S))

theorem binaryToCommon_toBinary (x : SourceTorus.chosenLift H K₀ hK S) :
    binaryToCommon H K₀ e S hn hmodel (SourceTorus.toBinary H K₀ hK e S x) =
      SourceTorus.toCommonTori H K₀ hK e S hn hmodel x := rfl

/-- The first binary axis maps onto precisely the first common torus axis. -/
theorem binaryToCommon_first :
    (BinaryBorel.firstAxis (SourceTorus.chosenSylow H K₀ e S)).map
      (binaryToCommon H K₀ e S hn hmodel) = CartanAction.firstFactor (CommonTorus H K₀ e S) := by
  rw [binaryToCommon, ← map_map, BinaryBorel.firstAxis_map]
  ext z
  rw [mem_map_equiv, CartanAction.mem_firstFactor]
  change (BinaryBorel.torusEquiv hn hmodel _ _).symm z.2 = 1 ↔ z.2 = 1
  exact (BinaryBorel.torusEquiv hn hmodel _ _).symm.map_eq_one_iff

/-- The second binary axis maps onto precisely the second common torus axis. -/
theorem binaryToCommon_second :
    (BinaryBorel.secondAxis (SourceTorus.chosenSylow H K₀ e S)).map
      (binaryToCommon H K₀ e S hn hmodel) = CartanAction.secondFactor (CommonTorus H K₀ e S) := by
  rw [binaryToCommon, ← map_map, BinaryBorel.secondAxis_map]
  ext z
  rw [mem_map_equiv, CartanAction.mem_secondFactor]
  rfl

/-- The binary action and the existing source torus action agree on actual representatives. -/
theorem normalizerAction_binaryToCommon {g : G} (hgH : g ∈ H)
    (hgK : g ∈ normalizer (K₀ : Set G))
    (hgB : g ∈ normalizer (SourceTorus.chosenLift H K₀ hK S : Set G))
    (x : BinaryBorel.borel (SourceTorus.chosenSylow H K₀ e S)) :
    SourceTorus.normalizerAction H K₀ hK e S hn hmodel ⟨g, hgB⟩
      (binaryToCommon H K₀ e S hn hmodel x) =
        binaryToCommon H K₀ e S hn hmodel (binaryAction H K₀ hK e S hgH hgK hgB x) := by
  obtain ⟨b, rfl⟩ := SourceTorus.toBinary_surjective H K₀ hK e S x
  rw [binaryToCommon_toBinary, binaryAction_toBinary, binaryToCommon_toBinary,
    SourceTorus.normalizerAction_toCommonTori]
  rfl

/-- Conjugation on subgroup images commutes with the common torus map. -/
theorem normalizerAction_map {g : G} (hgH : g ∈ H)
    (hgK : g ∈ normalizer (K₀ : Set G))
    (hgB : g ∈ normalizer (SourceTorus.chosenLift H K₀ hK S : Set G))
    (A : Subgroup (BinaryBorel.borel (SourceTorus.chosenSylow H K₀ e S))) :
    (A.map (binaryToCommon H K₀ e S hn hmodel)).map
      (SourceTorus.normalizerAction H K₀ hK e S hn hmodel ⟨g, hgB⟩).toMonoidHom =
        (A.map (binaryAction H K₀ hK e S hgH hgK hgB).toMonoidHom).map
          (binaryToCommon H K₀ e S hn hmodel) := by
  rw [map_map, map_map]
  congr 1
  exact MonoidHom.ext (normalizerAction_binaryToCommon H K₀ hK e S hn hmodel hgH hgK hgB)

/-- Both binary axis preservations descend to the actual common torus action. -/
theorem normalizerAction_preserves {g : G} (hgH : g ∈ H)
    (hgK : g ∈ normalizer (K₀ : Set G))
    (hgB : g ∈ normalizer (SourceTorus.chosenLift H K₀ hK S : Set G))
    (h₁ : (BinaryBorel.firstAxis (SourceTorus.chosenSylow H K₀ e S)).map
      (binaryAction H K₀ hK e S hgH hgK hgB).toMonoidHom =
        BinaryBorel.firstAxis (SourceTorus.chosenSylow H K₀ e S))
    (h₂ : (BinaryBorel.secondAxis (SourceTorus.chosenSylow H K₀ e S)).map
      (binaryAction H K₀ hK e S hgH hgK hgB).toMonoidHom =
        BinaryBorel.secondAxis (SourceTorus.chosenSylow H K₀ e S)) :
    CartanAction.PreservesFactors (SourceTorus.normalizerAction H K₀ hK e S hn hmodel ⟨g, hgB⟩) := by
  constructor
  · rw [← binaryToCommon_first H K₀ e S hn hmodel,
      normalizerAction_map H K₀ hK e S hn hmodel hgH hgK hgB, h₁]
  · rw [← binaryToCommon_second H K₀ e S hn hmodel,
      normalizerAction_map H K₀ hK e S hn hmodel hgH hgK hgB, h₂]

/-- Both binary axis exchanges descend to the actual common torus action. -/
theorem normalizerAction_exchanges {g : G} (hgH : g ∈ H)
    (hgK : g ∈ normalizer (K₀ : Set G))
    (hgB : g ∈ normalizer (SourceTorus.chosenLift H K₀ hK S : Set G))
    (h₁ : (BinaryBorel.firstAxis (SourceTorus.chosenSylow H K₀ e S)).map
      (binaryAction H K₀ hK e S hgH hgK hgB).toMonoidHom =
        BinaryBorel.secondAxis (SourceTorus.chosenSylow H K₀ e S))
    (h₂ : (BinaryBorel.secondAxis (SourceTorus.chosenSylow H K₀ e S)).map
      (binaryAction H K₀ hK e S hgH hgK hgB).toMonoidHom =
        BinaryBorel.firstAxis (SourceTorus.chosenSylow H K₀ e S)) :
    CartanAction.ExchangesFactors (SourceTorus.normalizerAction H K₀ hK e S hn hmodel ⟨g, hgB⟩) := by
  constructor
  · rw [← binaryToCommon_first H K₀ e S hn hmodel,
      normalizerAction_map H K₀ hK e S hn hmodel hgH hgK hgB, h₁,
      binaryToCommon_second]
  · rw [← binaryToCommon_second H K₀ e S hn hmodel,
      normalizerAction_map H K₀ hK e S hn hmodel hgH hgK hgB, h₂,
      binaryToCommon_first]

include hn hmodel in
/-- The common torus is odd, using only the already proved factor order. -/
theorem commonTorus_odd : Odd (Nat.card (CommonTorus H K₀ e S)) := by
  rw [BinaryBorel.torus_card hn hmodel]
  have hp : 0 < (2 : ℕ) ^ n := pow_pos (by decide) _
  have hm := Nat.mod_eq_zero_of_dvd (dvd_pow_self 2 (show n ≠ 0 by omega))
  rw [Nat.odd_iff]
  omega

include hn hmodel in
theorem commonTori_odd : Odd (Nat.card (CommonTorus H K₀ e S × CommonTorus H K₀ e S)) := by
  rw [Nat.card_prod]
  exact (commonTorus_odd H K₀ e S hn hmodel).mul (commonTorus_odd H K₀ e S hn hmodel)

end CFSG.Quasithin.Chapter13.Section08.Components.Swapped.LinearTwo.SourceActions

end
