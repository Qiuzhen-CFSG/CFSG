module
public import CFSG.Quasithin.Chapter15.Section02.SourcePlaneUniqueness.CharacteristicTwo.ComponentModels.LinearThree.FactorRecognition
public import CFSG.Quasithin.Chapter15.Section02.SourcePlaneUniqueness.CharacteristicTwo.ComponentModels.LinearThree.Endgame

/-!
# Exclusion of the source linear-three MS branch

The actual wreath quotient gives at least four distinct Sylow actors on
K/O₂(K). Restriction to two cubic lines proves independent inversions,
and the two-residual preimage argument identifies all invariant cubic
candidates with the constructed residual pair. Thus the complementary
factor proved in BinaryComplement is the other member of that pair.

The literal component alternatives of 15.2.12(2) discharge the radical
premise. The all-degree exclusion now has neither a factor-recognition
callback nor a radical-consequence callback. It retains only the earlier
faithful NI action and outside-Mc reduction, 15.2.12(2), Kc ≤ MI, and the
seed-family Frattini commutator. Their producers are respectively
qt-e-152-char2-component-models / qt-e-152-char2-block-exclusion,
qt-e-152-plane-geometry, and qt-e-152-char2-small-actions.
Final discharge belongs to qt-e-152-char2-component-models and
qt-e-152-plane-uniqueness.

The auxiliary joins with S below are used solely by the proved
conjugate-pair normalizer argument; no identification with the source's
earlier parabolics is inferred from those joins.
Source: Aschbacher--Smith, original 15.2.23, C.2.7(3)(g),
printed pp.145 and 1116; refs/quasithin.pdf.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section02.PlaneUniquenessPreceding.LinearThree
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc V H ZS I X : Subgroup G}
variable {hsource : ChosenSmallSource T M Mc V}
variable (d : PlaneUniquenessPreceding hsource H ZS)

private def residualPairSplit (hI : PlaneEscapes Mc ZS I) {t : G}
    (p : SmallActionsSource.ResidualPair (T : Subgroup G) (planeSylow T ZS)
      (smallActionK H) t) :
    SmallActionSplit (T : Subgroup G) (planeSylow T ZS) (smallActionK H) where
  H₁ := p.K₁ ⊔ planeSylow T ZS
  H₂ := p.K₂ ⊔ planeSylow T ZS
  K₁ := p.K₁
  K₂ := p.K₂
  t := t
  t_mem := p.t_mem
  t_not_mem := p.t_not_mem
  K_sup_S := by rw [sup_sup_sup_comm,sup_idem,p.span]
  K₁_sup_K₂ := p.span
  K₁_le := p.first.1
  K₂_le := p.second.1
  K₁_conj := p.conjugate
  S_normalizes_K₁ := p.normalized
  S_normalizes_K₂ := p.second_normalized inf_le_left (d.escape_index hI).2

include d in
/-- Exclude the original linear-three branch from the authorized earlier
source inputs, with both local recognition and radical callbacks discharged. -/
theorem Branch.false_of_earlier_source
    {n : ℕ} {F : Type} [Field F] [Finite F] (b : Branch M I X n F)
    (hI : PlaneEscapes Mc ZS I) (hfit : generalizedFitting I = pCore 2 I)
    (hout : n = 1 → ¬ X ≤ Mc)
    (f : (M ⊓ I : Subgroup G) →* Equiv.Perm (Fin 3))
    (hker : f.ker = (centralizer (V : Set G)).subgroupOf (M ⊓ I))
    (hKcI : smallActionKc H Mc ≤ Mc ⊓ I)
    (hc : ChosenGeometry.StructuralAlternatives T H Mc)
    (t : G) (ht : t ∈ (T : Subgroup G)) (htS : t ∉ planeSylow T ZS)
    (hYY : let Y := (primeToResidual 3 (M ⊓ I : Subgroup G)).map (M ⊓ I).subtype;
      ⁅Y,Y.map (MulAut.conj t).toMonoidHom⁆ ≤ Y ⊓ Y.map (MulAut.conj t).toMonoidHom) :
    False := by
  have hn := b.degree_eq_one d hI
  subst n
  have hnot := (b.binary_factor_data_of_action d hI (hout rfl) f hker).2.2.2.2.2
  obtain ⟨p⟩ := SmallActionsSource.exists_residualPair d hI hnot t ht htS
  let s := residualPairSplit d hI p
  exact b.binary_false_of_conjugate_pair d hI hfit (hout rfl) f hker
    (b.binary_centralizer_threePrime_of_source_alternatives d hI (hout rfl)
      f hker hKcI hc) s
    (fun E hEK hp hc hSE => classify_residualPair d hI hnot p E hEK hp hc hSE)
    hYY p.commutator_le

include d in
open Chapter1.RadicalExclusions.ModelReduction
  Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface in
/-- Literal application to C.2.7(3)(g): on the original I, O₂(NI), NI, X,
the printed linear-three parabolic and MS clauses cannot both occur. -/
theorem not_linearThree_ms
    (input : Input KnownSimple.IsKnownSimple I ((M ⊓ I).pCoreIn 2) (M ⊓ I) X)
    {n : ℕ} {F : Type} [Field F] [Finite F]
    (hn : 1 ≤ n) (hF : Nat.card F = 2 ^ n)
    (hpar : IsLinearMaximalParabolic
      ((starM X ((M ⊓ I).pCoreIn 2) (M ⊓ I)).subgroupOf
        (starImage X ((M ⊓ I).pCoreIn 2) X)) 3 F)
    (hI : PlaneEscapes Mc ZS I) (hfit : generalizedFitting I = pCore 2 I)
    (hout : n = 1 → ¬ X ≤ Mc)
    (f : (M ⊓ I : Subgroup G) →* Equiv.Perm (Fin 3))
    (hker : f.ker = (centralizer (V : Set G)).subgroupOf (M ⊓ I))
    (hKcI : smallActionKc H Mc ≤ Mc ⊓ I)
    (hc : ChosenGeometry.StructuralAlternatives T H Mc)
    (t : G) (ht : t ∈ (T : Subgroup G)) (htS : t ∉ planeSylow T ZS)
    (hYY : let Y := (primeToResidual 3 (M ⊓ I : Subgroup G)).map (M ⊓ I).subtype;
      ⁅Y,Y.map (MulAut.conj t).toMonoidHom⁆ ≤ Y ⊓ Y.map (MulAut.conj t).toMonoidHom) :
    ¬ MSDescription KnownSimple.IsKnownSimple X ((M ⊓ I).pCoreIn 2) n F := by
  intro hms
  exact (Branch.mk input hn hF hpar hms).false_of_earlier_source d hI hfit hout
    f hker hKcI hc t ht htS hYY

end CFSG.Quasithin.Chapter15.Section02.PlaneUniquenessPreceding.LinearThree
