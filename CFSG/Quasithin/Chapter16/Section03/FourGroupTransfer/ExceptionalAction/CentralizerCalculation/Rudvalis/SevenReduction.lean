module

public import CFSG.Quasithin.Chapter16.Section03.FourGroupTransfer.ExceptionalAction.CentralizerCalculation.Rudvalis.Reduction
public import Theory.SpecificGroups.Suzuki.SubgroupParameters

/-!
# Bounding the Suzuki centralizer using a seven-element

The actual Sz(8) model is centerless and contains an element x of order seven.
Suppose C_Ru(x) has a homomorphism to E₄ with kernel contained in ⟨x⟩.
The restriction to C_Ru(P), for any embedded P ≃ Sz(8) containing x, is
injective: its kernel lies in P ∩ C_Ru(P) = Z(P) = 1. Consequently the full
element centralizer of P has order at most four and every element squares
to one. This supplies `ElementCentralizerBound` without an embedding-class
assertion or a bound on the abstract order of Ru.

`SevenCentralizerProjection` is the precise remaining intrinsic obligation.
It follows from the expected actual C_Ru(x)/⟨x⟩ ≃ E₄, but this file does not
assert that quotient calculation. The kernel containment names the actual
cyclic subgroup, so an unrelated product model does not discharge it.

Source: GLS3 Table 5.3r, printed p.279, the 7A row
(`refs/KGroup/GLS3/Chapter5(sec3-).tex`). This is a route to the Ru–Sz(8)
calculation used by Aschbacher–Smith 16.3.5, printed pp.1178–1179.
The only Suzuki model facts used are the checked XI.3.3 order formula
and XI.3.6 simplicity and nonsolvability.
-/

public section

namespace CFSG.Quasithin.Chapter16.FourGroupTransfer.ExceptionalAction.CentralizerCalculation.RudvalisPair
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative

/-- A concrete elementary abelian group of order four. -/
abbrev Four := Fin 2 → Multiplicative (ZMod 2)

/-- A map out of each actual order-seven centralizer whose kernel is contained
in that element's cyclic subgroup. Surjectivity is unnecessary for the bound. -/
@[expose] def SevenCentralizerProjection : Prop :=
  ∀ x : Model, orderOf x = 7 →
    ∃ f : centralizer ({x} : Set Model) →* Four,
      f.ker ≤ (zpowers x).subgroupOf (centralizer ({x} : Set Model))

private theorem suzuki_center_eq_bot {P : Subgroup Model} (e : P ≃* SzEight) :
    center P = ⊥ := by
  let := (BenderSuzuki.External.huppert_blackburn_XI_3_6 1 (by decide)).1
  let := e.isSimpleGroup
  rcases (inferInstance : (center P).Normal).eq_bot_or_eq_top with h | h
  · exact h
  · let : IsMulCommutative P := center_eq_top_iff.mp h
    have hs : Group.IsSolvable SzEight :=
      Group.isSolvable_of_surjective (f := e.toMonoidHom) e.surjective
    exact (BenderSuzuki.External.suzukiMatrixGroup_not_isSolvable 1 (by decide) hs).elim

private theorem suzuki_exists_seven {P : Subgroup Model} (e : P ≃* SzEight) :
    ∃ x : P, orderOf x = 7 := by
  let : Fact (Nat.Prime 7) := ⟨by decide⟩
  apply exists_prime_orderOf_dvd_card' 7
  rw [Nat.card_congr e.toEquiv]
  change 7 ∣ Nat.card (BenderSuzuki.MatrixGroups.SuzukiMatrixGroup 1)
  rw [BenderSuzuki.MatrixGroups.suzukiMatrixGroup_card 1 (by decide)]
  norm_num

/-- The order-seven centralizer calculation bounds the centralizer of every
actual embedded Sz(8). The faithful actor's lower bound is not needed here. -/
theorem elementCentralizerBound_of_sevenCentralizers
    (hseven : SevenCentralizerProjection) : ElementCentralizerBound := by
  rintro P ⟨e⟩ _
  obtain ⟨x, hx⟩ := suzuki_exists_seven e
  have hxM : orderOf (x : Model) = 7 := (orderOf_coe x).trans hx
  obtain ⟨f, hf⟩ := hseven x hxM
  let C := centralizer (P : Set Model)
  let D := centralizer ({(x : Model)} : Set Model)
  have hCD : C ≤ D := by
    intro c hc
    rw [mem_centralizer_singleton_iff]
    exact (mem_centralizer_iff.mp hc x x.property).symm
  let j : C →* D := inclusion hCD
  let k : C →* Four := f.comp j
  have hk : Function.Injective k := by
    apply (MonoidHom.ker_eq_bot_iff k).mp
    apply le_bot_iff.mp
    intro c hc
    have hcp : (c : Model) ∈ P :=
      (zpowers_le.mpr x.property) (hf hc)
    have hcz : (⟨c, hcp⟩ : P) ∈ center P := by
      rw [mem_center_iff]
      intro p
      exact Subtype.ext (mem_centralizer_iff.mp c.property p p.property)
    have hce : (⟨c, hcp⟩ : P) = 1 := by
      simpa only [suzuki_center_eq_bot e, mem_bot] using hcz
    exact mem_bot.mpr (Subtype.ext (congrArg (fun p : P => (p : Model)) hce))
  constructor
  · have hc := Nat.card_le_card_of_injective k hk
    have hFour : Nat.card Four = 4 := by simp [Four, Nat.card_eq_fintype_card]
    exact hc.trans_eq hFour
  · intro c
    apply hk
    rw [map_pow, map_one]
    exact (show ∀ z : Four, z ^ 2 = 1 from by decide) (k c)

end CFSG.Quasithin.Chapter16.FourGroupTransfer.ExceptionalAction.CentralizerCalculation.RudvalisPair
