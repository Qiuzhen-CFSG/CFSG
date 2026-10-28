module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.ComponentControl.Characteristic
public import Theory.GroupTheory.CComponent.QuasisimpleSupplement
public import Theory.GroupTheory.SolvableResidual
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.ComponentControl.CharacteristicNormalizers.SeedMovement.Assembly

/-!
# Seed movement for the radical replacement

The replacement in 13.6.16(2) supplements the solvable radical and is
normalized by S = C_T(v). If K₀/O₂(K₀) is quasisimple, that replacement
is K₀ itself: O₂(K₀) lies in S, so it normalizes the replacement, and the
radical-supplement theorem applies inside K₀. This includes quasisimple
quotients with odd center; it never assumes that the radical fixes z.

The application uses the literal residual of N_{K₀}(C). Its invariance
and supplement equality are supplied by the construction in the parent
CharacteristicNormalizers module, which is deliberately not imported here.

The independent seed-action route is now proved in `Assembly`: assuming the
earlier characteristic-two conclusion 13.6.6 and the corrected universal B.5.6
input, every radical supplement moves z. The nonquasisimple action case yields
a moving component in the Thompson normalizer and contradicts universal
13.6.16(1). The quasisimple action case transfers movement through its actual
quotient. This does not require K₀/O₂(K₀) to be quasisimple.

The marked source application and literal residual transfer are included.
The existing producer of the characteristic-two result and its local
configuration is still required for source-only assembly. The older
quasisimple two-core-quotient lemmas below remain available independently.
No 13.6.8–15 conclusion is used in the new route.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
Lemma 13.6.16(2), printed p.930; Proposition 1.2.1(4), printed p.504.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.SeedMovement
variable {G : Type*} [Group G] [Finite G]

/-- In the quasisimple two-core-quotient branch, the already constructed
S-invariant radical supplement equals the original local component. -/
theorem replacement_eq_of_quasisimple
    (S K₀ K₁ : Subgroup G) (hK₀ : K₀ ∈ Chapter1.L G S)
    (hS₀ : S ≤ normalizer (K₀ : Set G))
    (hS₁ : S ≤ normalizer (K₁ : Set G))
    (hgen : (solvableRadical K₀).map K₀.subtype ⊔ K₁ = K₀)
    (hquasi : IsQuasisimple (K₀ ⧸ pCore 2 K₀)) : K₁ = K₀ := by
  let H := K₀ ⊔ S
  have hQH : K₀.pCoreIn 2 ≤ H.pCoreIn 2 :=
    le_pCoreIn_of_normalizes (isPGroup_pCoreIn 2 K₀)
      ((pCoreIn_le 2 K₀).trans le_sup_left)
      ((sup_le K₀.le_normalizer hS₀).trans
        (normalizer_le_normalizer_characteristic_image K₀ (pCore 2 K₀)))
  obtain ⟨P, hP⟩ := hK₀.2.1
  have hQS : K₀.pCoreIn 2 ≤ S := hQH.trans ((pCoreIn_le_sylow H P).trans_eq hP)
  have hle : K₁ ≤ K₀ := le_sup_right.trans_eq hgen
  let B := K₁.subgroupOf K₀
  have hgenB : solvableRadical K₀ ⊔ B = ⊤ := by
    apply map_injective K₀.subtype_injective
    simpa only [Subgroup.map_sup, B, map_subgroupOf_eq_of_le hle,
      ← MonoidHom.range_eq_map, range_subtype] using hgen
  have hn : pCore 2 K₀ ≤ normalizer (B : Set K₀) := by
    apply le_normalizer_iff.mpr
    intro x hx y hy
    exact (mem_normalizer_iff.mp (hS₁ (hQS (mem_map.mpr ⟨x, hx, rfl⟩)))
      (y : G)).mp hy
  let := Chapter1.mem_L_isPerfect hK₀
  let := hquasi
  have he : B = ⊤ :=
    eq_top_of_radical_supplement_of_quasisimple_quotient (pCore 2 K₀) B hn hgenB
  exact le_antisymm hle (subgroupOf_eq_top.mp he)

/-- Movement for the literal normalizer residual, using exactly the
invariance and supplement outputs of the parent's construction.
Quasisimplicity is an explicit branch condition, not an asserted consequence
of the general Chapter 13 setup. -/
theorem normalizer_residual_moves_of_quasisimple
    (T : Sylow 2 G) (z v : G) (K₀ K₁ : Subgroup G)
    (hK₀ : K₀ ∈ Chapter1.LIn (Gv v) (Tv (T : Subgroup G) v))
    (hS₀ : Tv (T : Subgroup G) v ≤ normalizer (K₀ : Set G))
    (hS₁ : Tv (T : Subgroup G) v ≤ normalizer (K₁ : Set G))
    (hgen : (solvableRadical K₀).map K₀.subtype ⊔ K₁ = K₀)
    (hmoving : ¬ K₀ ≤ centralizer ({z} : Set G))
    (C : Subgroup (Tv (T : Subgroup G) v)) [C.Characteristic]
    (hres : K₁ =
      (solvableResidual (K₀ ⊓ normalizer (C.map (Tv (T : Subgroup G) v).subtype : Set G) : Subgroup G)).map
        (K₀ ⊓ normalizer (C.map (Tv (T : Subgroup G) v).subtype : Set G)).subtype)
    (hquasi : IsQuasisimple (K₀ ⧸ pCore 2 K₀)) :
    ¬ (solvableResidual (K₀ ⊓ normalizer (C.map (Tv (T : Subgroup G) v).subtype : Set G) : Subgroup G)).map
      (K₀ ⊓ normalizer (C.map (Tv (T : Subgroup G) v).subtype : Set G)).subtype ≤
        centralizer ({z} : Set G) := by
  rw [← hres, replacement_eq_of_quasisimple _ K₀ K₁ hK₀.2 hS₀ hS₁ hgen hquasi]
  exact hmoving

/-- The fixed-replacement obstruction from the parent is necessarily in
the nonquasisimple two-core-quotient branch. No classification or radical
centralization conclusion is inserted as a premise. -/
theorem fixed_normalizer_residual_not_quasisimple
    (T : Sylow 2 G) (z v : G) (K₀ K₁ : Subgroup G)
    (hK₀ : K₀ ∈ Chapter1.LIn (Gv v) (Tv (T : Subgroup G) v))
    (hS₀ : Tv (T : Subgroup G) v ≤ normalizer (K₀ : Set G))
    (hS₁ : Tv (T : Subgroup G) v ≤ normalizer (K₁ : Set G))
    (hgen : (solvableRadical K₀).map K₀.subtype ⊔ K₁ = K₀)
    (hmoving : ¬ K₀ ≤ centralizer ({z} : Set G))
    (C : Subgroup (Tv (T : Subgroup G) v)) [C.Characteristic]
    (hres : K₁ =
      (solvableResidual (K₀ ⊓ normalizer (C.map (Tv (T : Subgroup G) v).subtype : Set G) : Subgroup G)).map
        (K₀ ⊓ normalizer (C.map (Tv (T : Subgroup G) v).subtype : Set G)).subtype)
    (hfixed : K₁ ≤ centralizer ({z} : Set G)) :
    ¬ IsQuasisimple (K₀ ⧸ pCore 2 K₀) := by
  intro hquasi
  apply normalizer_residual_moves_of_quasisimple T z v K₀ K₁ hK₀ hS₀ hS₁ hgen
    hmoving C hres hquasi
  rwa [← hres]

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.SeedMovement

end
