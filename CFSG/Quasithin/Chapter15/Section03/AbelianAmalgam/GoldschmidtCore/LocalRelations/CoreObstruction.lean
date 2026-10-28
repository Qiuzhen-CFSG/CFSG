module

public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Basic
public import Stellmacher.ElementaryAbelianMaxJ
public import Mathlib.Data.ZMod.Basic

/-!
# An obstruction to the printed common-core equality

The proof of 15.3.68(2), printed p.1154 (PDF p.1171), writes
`O₂(G₁) ∩ O₂(G₂) = R`, with `G₂=X_E T_E` and `R=C_T(V)`.
But 15.3.67(3),(4) give `X_E/O₂(X_E) ≃ C₃` and `X_E=[X_E,J(R)]`.
If `R≤O₂(G₂)`, normality of that intrinsic core forces `X_E≤O₂(G₂)`,
contradicting its cyclic three quotient. Thus those preceding source
conclusions imply the negation of the printed equality.

These are obstruction theorems, not proofs of 15.3.68. They retain the
original definitions and intrinsic quotient kernels. A corrected proof
of the centrality clause requires a separate argument; no correction is
silently substituted here.

Source: Aschbacher–Smith, combined manuscript (1 March 2004),
printed pp.1152–1154, PDF pp.1169–1171.
-/

public section

open Subgroup Stellmacher
namespace CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.LocalRelations
variable {G : Type*} [Group G]

private theorem lineX_not_two (E : Subgroup G)
    (hquot : Nonempty ((lineX E ⧸ pCore 2 (lineX E)) ≃* Multiplicative (ZMod 3))) :
    ¬ IsPGroup 2 (lineX E) := by
  obtain ⟨e⟩ := hquot
  have hc : Nat.card (lineX E ⧸ pCore 2 (lineX E)) = 3 := by
    rw [Nat.card_congr e.toEquiv]
    simp [Nat.card_eq_fintype_card]
  intro hp
  have h := (hp.to_quotient (pCore 2 (lineX E))).card_eq_or_dvd
  norm_num [hc] at h

/-- The genuine cyclic quotient from 15.3.67(3) prevents `X_E` from
lying in the intrinsic two-core of `G₂`. -/
theorem lineX_not_le_secondCore (T E : Subgroup G)
    (hquot : Nonempty ((lineX E ⧸ pCore 2 (lineX E)) ≃* Multiplicative (ZMod 3))) :
    ¬ lineX E ≤ twoCoreAmbient (secondAmalgamGroup T E) := by
  intro h
  exact lineX_not_two E hquot ((pCore_isPGroup.map (secondAmalgamGroup T E).subtype).to_le h)

/-- Source 15.3.67(3),(4) forbid `R ≤ O₂(G₂)`. Since the two-core is
normal in `G₂`, it would contain `[X_E,J(R)] = X_E`, a contradiction. -/
theorem centralizer_not_le_secondCore (T V E : Subgroup G)
    (hquot : Nonempty ((lineX E ⧸ pCore 2 (lineX E)) ≃* Multiplicative (ZMod 3)))
    (hcomm : lineX E = ⁅lineX E, elementaryAbelianMaxJ (T ⊓ centralizer (V : Set G))⁆) :
    ¬ T ⊓ centralizer (V : Set G) ≤ twoCoreAmbient (secondAmalgamGroup T E) := by
  intro hR
  have hJ : elementaryAbelianMaxJ (T ⊓ centralizer (V : Set G)) ≤
      twoCoreAmbient (secondAmalgamGroup T E) :=
    (sSup_le fun _ hA => hA.1).trans hR
  have hN : lineX E ≤ normalizer (twoCoreAmbient (secondAmalgamGroup T E) : Set G) :=
    (show lineX E ≤ secondAmalgamGroup T E from le_sup_left).trans
      ((secondAmalgamGroup T E).le_normalizer.trans
        (normalizer_le_normalizer_characteristic_image _ (pCore 2 _)))
  apply lineX_not_le_secondCore T E hquot
  rw [hcomm]
  exact (commutator_mono le_rfl hJ).trans
    (le_normalizer_iff_commutator_le_right.mp hN)

/-- The equality printed in the proof of 15.3.68(2) is incompatible with
the preceding source conclusions. This is a diagnostic, not a proof of
15.3.68. The weaker containment needed for centrality is not ruled out. -/
theorem commonCore_ne_centralizer (Y T V E F : Subgroup G)
    (hquot : Nonempty ((lineX E ⧸ pCore 2 (lineX E)) ≃* Multiplicative (ZMod 3)))
    (hcomm : lineX E = ⁅lineX E, elementaryAbelianMaxJ (T ⊓ centralizer (V : Set G))⁆) :
    twoCoreAmbient (firstAmalgamGroup Y T E F) ⊓
        twoCoreAmbient (secondAmalgamGroup T E) ≠ T ⊓ centralizer (V : Set G) := by
  intro h
  exact centralizer_not_le_secondCore T V E hquot hcomm (h ▸ inf_le_right)

end CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.LocalRelations
