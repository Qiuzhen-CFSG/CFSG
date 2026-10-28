module
public import CFSG.Quasithin.Chapter12.Section02.RecognitionSource.FusionReducibleNormalizerReduction
public import Theory.GroupTheory.ElementaryThompsonRelative
public import Theory.GroupTheory.PResidual.PrimeTo

/-!
# The residual–Thompson contradiction in the reducible normalizer argument

Set Z = Ω₁Z(T), X = O²(C_L(Z)), and R = O₂(XT), all as literal ambient
subgroups. The Sylow normalizer acts on C_G(Z), hence on its O^{3'} residual.
If that residual is X, it acts on R and J(R). If J(R) = J(O₂(LT)),
uniqueness forces the Sylow normalizer into N_G(L): the latter Thompson
subgroup is nontrivial and normal in LT.

The reducible choice already gives C_G(Z) = C_{N_G(L)}(Z). The model-specific
residual and Thompson identities remain explicit. This proves the elementary
invariance and contradiction used in 3.3.21(e), avoiding its later triality
analysis when those identities are supplied for the actual eight-letter row.

Source: Aschbacher–Smith 3.3.21(d–e), printed p.596; compare 3.3.25(2), p.599.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter12.Section02.RecognitionSource.FusionReducibleNormalizer
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

/-- The literal two-residual O²(C_L(Ω₁Z(T))), mapped into the ambient group. -/
def omegaLocalResidual (T : Sylow 2 G) (L : Subgroup G) : Subgroup G :=
  (pResidual 2 (L ⊓ centralizer (omegaCenterIn (T : Subgroup G) : Set G) : Subgroup G)).map
    (L ⊓ centralizer (omegaCenterIn (T : Subgroup G) : Set G)).subtype

/-- The literal O₂(XT) for the source omega-centralizer residual X. -/
def omegaResidualCore (T : Sylow 2 G) (L : Subgroup G) : Subgroup G :=
  (omegaLocalResidual T L ⊔ (T : Subgroup G)).pCoreIn 2

/-- The reducible fixed subgroup identifies the full and local omega-centralizers. -/
theorem omega_centralizer_eq_local
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (hne : V ⊓ centralizer (L : Set G) ≠ ⊥) :
    centralizer (omegaCenterIn (T : Subgroup G) : Set G) =
      normalizer (L : Set G) ⊓ centralizer (omegaCenterIn (T : Subgroup G) : Set G) :=
  (inf_eq_right.mpr (omega_centralizer_le h D hne)).symm

omit [Finite G] in
/-- The whole Sylow normalizer normalizes the full omega-centralizer. -/
theorem sylow_normalizer_normalizes_omega_centralizer :
    normalizer (T : Set G) ≤
      normalizer (centralizer (omegaCenterIn (T : Subgroup G) : Set G) : Set G) :=
  (normalizer_le_normalizer_omegaCenterIn (T : Subgroup G)).trans
    (normalizer_le_normalizer_centralizer _)

omit [Finite G] in
/-- An intrinsic O^{3′} description makes the component two-residual invariant. -/
theorem sylow_normalizer_normalizes_omegaLocalResidual
    (he : (primeToResidual 3 (centralizer (omegaCenterIn (T : Subgroup G) : Set G))).map
        (centralizer (omegaCenterIn (T : Subgroup G) : Set G)).subtype = omegaLocalResidual T L) :
    normalizer (T : Set G) ≤ normalizer (omegaLocalResidual T L : Set G) := by
  rw [← he]
  exact sylow_normalizer_normalizes_omega_centralizer.trans
    (normalizer_le_normalizer_characteristic_image _ (primeToResidual 3 _))

omit [Finite G] in
/-- Invariance passes to the literal two-core O₂(XT). -/
theorem sylow_normalizer_normalizes_omegaResidualCore
    (he : (primeToResidual 3 (centralizer (omegaCenterIn (T : Subgroup G) : Set G))).map
        (centralizer (omegaCenterIn (T : Subgroup G) : Set G)).subtype = omegaLocalResidual T L) :
    normalizer (T : Set G) ≤ normalizer (omegaResidualCore T L : Set G) := by
  have hn : normalizer (T : Set G) ≤
      normalizer ((omegaLocalResidual T L ⊔ (T : Subgroup G) : Subgroup G) : Set G) :=
    (le_inf (sylow_normalizer_normalizes_omegaLocalResidual he) le_rfl).trans
      (normalizer_inf_normalizer_le_normalizer_sup _ _)
  exact hn.trans (normalizer_le_normalizer_characteristic_image _ (pCore 2 _))

/-- The actual residual and Thompson identities imply the required normalizer bound. -/
theorem sylow_normalizer_le_of_omegaResidual_thompson
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (he : (primeToResidual 3 (centralizer (omegaCenterIn (T : Subgroup G) : Set G))).map
        (centralizer (omegaCenterIn (T : Subgroup G) : Set G)).subtype = omegaLocalResidual T L)
    (hJ : elementaryAbelianMaxJ (omegaResidualCore T L) =
      elementaryAbelianMaxJ ((L ⊔ (T : Subgroup G)).pCoreIn 2)) :
    normalizer (T : Set G) ≤ normalizer (L : Set G) := by
  let Q := (L ⊔ (T : Subgroup G)).pCoreIn 2
  have hQ : Q ≠ ⊥ := fun he => D.ne_bot (bot_unique (D.le_core.trans_eq he))
  have hnQ : L ⊔ (T : Subgroup G) ≤ normalizer (Q : Set G) :=
    (L ⊔ (T : Subgroup G)).le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image _ (pCore 2 _))
  have hNJ : normalizer (elementaryAbelianMaxJ Q : Set G) ≤ normalizer (L : Set G) :=
    D.normal_subgroup_normalizer_le h.toHypothesis1221
      ((sSup_le fun _ hA => hA.1).trans (map_subtype_le _))
      (elementaryAbelianMaxJ_ne_bot_of_finite_pGroup Q (pCore_isPGroup.map _) hQ)
      (hnQ.trans (normalizer_le_normalizer_elementaryAbelianMaxJ Q))
  apply le_trans _ hNJ
  change normalizer (T : Set G) ≤
    normalizer (elementaryAbelianMaxJ ((L ⊔ (T : Subgroup G)).pCoreIn 2) : Set G)
  rw [← hJ]
  exact (sylow_normalizer_normalizes_omegaResidualCore he).trans
    (normalizer_le_normalizer_elementaryAbelianMaxJ _)

end CFSG.Quasithin.Chapter12.Section02.RecognitionSource.FusionReducibleNormalizer
