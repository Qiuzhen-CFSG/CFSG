module

public import CFSG.Quasithin.Chapter1.Section03.Radical.Normalizers.Residual.Components
public import CFSG.Quasithin.Chapter1.Section03.Radical.Normalizers.Residual.Commutator
public import CFSG.Quasithin.Chapter1.Section03.Radical.Normalizers.Residual.Actions
public import CFSG.Quasithin.Chapter1.Section03.Radical.Normalizers.Residual.SourceStructure

/-!
# Residual normalizers of radical members

The Frattini factorization in the proof of Proposition 1.3.8, printed
pp.512–513 of Aschbacher–Smith, follows from A.4.2(4),(5). It identifies
the residual of N_LT(R) with Y = N_L(R)^∞ and compares the actual Y and
L actions on Ξ_p(L)/O₂(Ξ_p(L)) and its Frattini quotient.

The component argument is reduced to solvability of C_LT(X/O₂(X)); the
source-structure leaves prove that solvability from the earlier A.3.6/A.3.8
interfaces.  The exported assembly below then gives Y, every
characteristic-normalizer residual L_C, and [L_C,Y] = L_C.  Commutator
generation [X,Y] = X gives X ≤ Y and nonquasisimplicity of Y/O₂(Y), while the
action and section fields retain the actual odd factors and Sylow subgroups.
-/

@[expose] public section

open Subgroup Theory.GroupTheory
open CFSG.Quasithin.Chapter1
open CFSG.Quasithin.Chapter1.Section02
open CFSG.Quasithin.Chapter1.Section02.LocalModels
open CFSG.Quasithin.Chapter1.RadicalActions
open CFSG.Quasithin.ChapterA.Section04
open scoped Pointwise

namespace CFSG.Quasithin.Chapter1.RadicalNormalizers

universe u

variable {G : Type u} [Group G] [Finite G]

/-- The complete residual package used in the proof of Proposition 1.3.8.

The fields are stated with the actual subgroups occurring in the source:
`R = O₂(Ξ_p(L)T)`, `Y = N_L(R)^∞`, the section centralizer in `LT`, and a
Sylow subgroup of `Ξ_p(L)`.  In particular, the action field is the actual
Frattini action on every odd Fitting factor, while the final field keeps the
characteristic subgroup inside `R` (and hence relative normality) explicit.
Source: Aschbacher–Smith, combined manuscript of 1 March 2004, proof of
Proposition 1.3.8, printed pp.512–513.
-/
structure ResidualNormalizerData (p : ℕ) (L T : Subgroup G) : Prop where
  t_normalizes : T ≤ normalizer (L : Set G)
  sylow_core : IsSylowIn 2 (radicalCore p L T)
    (twoSectionCentralizer (XiP p L) (L ⊔ T))
  frattini_factorization :
    twoSectionCentralizer (XiP p L) (L ⊔ T) ⊔
      ((L ⊔ T) ⊓ normalizer (radicalCore p L T : Set G)) = L ⊔ T
  frattini_set_product :
    ((L ⊔ T : Subgroup G) : Set G) =
      (twoSectionCentralizer (XiP p L) (L ⊔ T) : Set G) *
        ((((L ⊔ T) ⊓ normalizer (radicalCore p L T : Set G)) : Subgroup G) : Set G)
  section_centralizer_solvable :
    Group.IsSolvable (twoSectionCentralizer (XiP p L) (L ⊔ T))
  t_normalizes_Y : T ≤ normalizer
    (normalizerResidual L (radicalCore p L T) : Set G)
  Y_normal_in_localNormalizer :
    ((normalizerResidual L (radicalCore p L T)).subgroupOf
      ((L ⊔ T) ⊓ normalizer (radicalCore p L T : Set G))).Normal
  Y_mem_L : normalizerResidual L (radicalCore p L T) ∈
    CFSG.Quasithin.Chapter1.L G T
  X_le_Y : XiP p L ≤ normalizerResidual L (radicalCore p L T)
  Y_ne_bot : normalizerResidual L (radicalCore p L T) ≠ ⊥
  Y_cComponent :
    ((normalizerResidual L (radicalCore p L T)).subgroupOf
      ((L ⊔ T) ⊓ normalizer (radicalCore p L T : Set G))).IsCComponent
  Y_not_quasisimple :
    ¬ IsQuasisimple (XiQuotient (normalizerResidual L (radicalCore p L T)))
  actions : ∀ q : ℕ, q.Prime → Odd q →
    q ∣ Nat.card (fittingSubgroup (XiQuotient L)) →
    ⁅XiP q L, normalizerResidual L (radicalCore p L T)⁆ = XiP q L ∧
    ∀ A : Subgroup (XiFrattiniQuotient (XiP q L)),
      (∀ y : normalizerResidual L (radicalCore p L T), ∀ a ∈ A,
        xiFrattiniAction _ _ (Y_normalizes_XiP p q L T) y a ∈ A) →
        A = ⊥ ∨ A = ⊤
  sl_section : ∀ P : Sylow p (XiP p L),
    ∃ r : ℕ, r.Prime ∧ (r = p ∨ r = 5) ∧
      IsSL (XiQuotient L ⧸ fittingSubgroup (XiQuotient L)) 2 r ∧
      ∃ S : Subgroup G,
        S ≤ normalizerResidual L (radicalCore p L T) ⊓
          normalizer ((P : Subgroup (XiP p L)).map (XiP p L).subtype : Set G) ∧
        ∃ K : Subgroup S, ∃ _ : K.Normal, IsSL (S ⧸ K) 2 r
  characteristic_local : ∀ (C : Subgroup (radicalCore p L T)),
    C.Characteristic → C ≠ ⊥ →
      normalizerResidual L (C.map (radicalCore p L T).subtype) ∈
          CFSG.Quasithin.Chapter1.L G T ∧
      normalizerResidual L (radicalCore p L T) ≤
        normalizerResidual L (C.map (radicalCore p L T).subtype) ∧
      ⁅normalizerResidual L (C.map (radicalCore p L T).subtype),
        normalizerResidual L (radicalCore p L T)⁆ =
        normalizerResidual L (C.map (radicalCore p L T).subtype)

/-- Assemble the nonsolvable residual normalizer from the actual Chapter 1
hypotheses and the universal earlier A.3.6/A.3.8 implications.

No residual containment, action, component, solvability, or section assertion
is assumed: each is obtained from the corresponding Frattini, action,
source-structure, component, and commutator lemmas.
-/
theorem residual_normalizer_data_of_source
    {𝒦 : GroupClass.{u}}
    (hA36 : ∀ (E : Type u) [Group E] [Finite E],
      IsSQTK 𝒦 E → pCore 2 E = ⊥ → ∀ C : Subgroup E,
      C.IsCComponent → A36Conclusion C)
    (hA38 : ∀ (E : Type u) [Group E] [Finite E],
      IsSQTK 𝒦 E → pCore 2 E = ⊥ → ∀ C : Subgroup E,
      C.IsCComponent → C.Normal ∨ IsQuasisimple C)
    {T L : Subgroup G} (hL : L ∈ LStar G T)
    (hQ : IsSQTK 𝒦 ((L ⊔ T : Subgroup G) ⧸ pCore 2 (L ⊔ T : Subgroup G)))
    (hn : ¬ IsQuasisimple (XiQuotient L)) {p : ℕ} [Fact p.Prime]
    (hp : Odd p) (hd : p ∣ Nat.card (fittingSubgroup (XiQuotient L))) :
    ResidualNormalizerData p L T := by
  have hT : T ≤ normalizer (L : Set G) :=
    radicalLocal_invariant_of_A38 hA38 hL.1 hQ hn
  have hSyl : IsSylowIn 2 (radicalCore p L T)
      (twoSectionCentralizer (XiP p L) (L ⊔ T)) :=
    sylow_radicalCore p L T hL.1.2.1 hT
  have hFrattini := radical_frattini p L T hL.1.2.1 hT
  have hFrattiniSet := radical_frattini_mul p L T hL.1.2.1 hT
  let P : Sylow p (XiP p L) := Classical.arbitrary _
  have hPirr := XiP_normalizer_irreducible_of_A36 hA36 hL.1 hQ hn hp hd P
  have hsol := sectionCentralizer_solvable_of_source hA36 hA38 hL hQ hn hp hd P hPirr
  have hacts := XiP_Y_actions_of_A36 hA36 hA38 hL hQ hn hp hd
  have hpact := hacts p (Fact.out : p.Prime) hp hd
  have hcomm : ⁅XiP p L, normalizerResidual L (radicalCore p L T)⁆ = XiP p L :=
    hpact.1
  have hXY := XiP_le_Y_of_commutator p L T hcomm
  have hshape : XiOddQuotient p (XiQuotient (XiP p L)) :=
    (XiP_oddQuotient_of_A36 hA36 hL.1 hQ hn hp hd).2
  let : Nontrivial (XiQuotient (XiP p L)) :=
    Finite.one_lt_card_iff_nontrivial.mp (hshape.one_lt_card (Fact.out : p.Prime))
  have hYq := Y_not_quasisimple_of_commutator p (L := L) (T := T) hp hcomm
  have hYc := Y_cComponent_of_solvable_sectionCentralizer p L T hL.1 hT hsol
  have hYne := Y_ne_bot_of_solvable_sectionCentralizer p L T hL.1 hT hsol
  have hYT := t_le_normalizer_Y p hT
  have hYnormal := Y_normal_in_localNormalizer p hT
  have hYmem := Y_mem_L_of_cComponent p hL.1 hYc
  refine
    { t_normalizes := hT
      sylow_core := hSyl
      frattini_factorization := hFrattini
      frattini_set_product := hFrattiniSet
      section_centralizer_solvable := hsol
      t_normalizes_Y := hYT
      Y_normal_in_localNormalizer := hYnormal
      Y_mem_L := hYmem
      X_le_Y := hXY
      Y_ne_bot := hYne
      Y_cComponent := hYc
      Y_not_quasisimple := hYq
      actions := hacts
      sl_section := by
        intro P
        have hPirr := XiP_normalizer_irreducible_of_A36 hA36 hL.1 hQ hn hp hd P
        exact residual_SL_section_of_source hA36 hA38 hL hQ hn hp hd P hPirr hXY
      characteristic_local := ?_ }
  intro C hC hneC
  let _ : C.Characteristic := hC
  exact ⟨characteristicResidual_mem_L_of_solvable_sectionCentralizer
      p L T hL.1 hT hsol C hneC,
    normalizerResidual_le_of_characteristic L (radicalCore p L T) C,
    characteristicResidual_commutator_of_solvable_sectionCentralizer
      p L T hL.1 hT hsol C hneC⟩

end CFSG.Quasithin.Chapter1.RadicalNormalizers
