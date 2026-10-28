module

public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.M22Identification.OrderRecognition.LocalAnalysis.InvolutionNormalizers.Interfaces
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.M22Identification.OrderRecognition.LocalAnalysis.InvolutionNormalizers.FAction.Transport
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.M22Identification.OrderRecognition.LocalAnalysis.InvolutionNormalizers.FAction.Orbits
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.M22Identification.OrderRecognition.LocalAnalysis.InvolutionNormalizers.FAction.Identification

/-!
# Janko's F-normalizer quotient and fusion

Conjugation transports the actual normalizer quotient to its faithful image
in the automorphism group of the coordinate elementary sixteen. The proved
ambient Sylow and stabilizer constraints supply `FiniteSetup` without any
simplicity or global-fusion assumption. The finite orbit argument proves
transitivity and order 120. The finite identification theorem constructs a
faithful action on five triples and identifies this image with S5.

The resulting `fNormalizerAction_of_caseII` proves the actual normalizer
quotient and fusion clauses of Janko's Lemma 2 from the single source
z–d conjugacy hypothesis. Splitting is handled by the separate consumer.

Source: Z. Janko, *A characterization of the Mathieu simple groups, I*,
J. Algebra 9 (1968), Section 2, Lemma 2, pp.4–5.
-/

open Subgroup
namespace Theory.GroupTheory.HeldM22A10.M22Identification
open LocalModelDichotomy
universe u
variable {G : Type u} [Group G] [Finite G] (D : LocalData G)
  (k : TwistedModel ≃* D.centralizer)

open CaseII.FAction in
omit [Finite G] in
/-- Transport orbit witnesses from the faithful automizer to the actual normalizer. -/
public theorem fNormalizer_fusion_of_automizer
    (htrans : ∀ x y : CaseII.modelF, x ≠ 1 → y ≠ 1 →
      ∃ a : automizer D k, (a : MulAut CaseII.modelF) x = y) :
    ∀ x y : CaseII.F D k, x ≠ 1 → y ≠ 1 →
      ∃ g : normalizer (CaseII.F D k : Set G), (g : G) * x * (g : G)⁻¹ = y := by
  intro x y hx hy
  let e := coordinates D k
  have hx' : e.symm x ≠ 1 := by
    intro h
    apply hx
    simpa only [e.apply_symm_apply, map_one] using congrArg e h
  have hy' : e.symm y ≠ 1 := by
    intro h
    apply hy
    simpa only [e.apply_symm_apply, map_one] using congrArg e h
  obtain ⟨a, ha⟩ := htrans (e.symm x) (e.symm y) hx' hy'
  obtain ⟨g, hg⟩ := a.property
  refine ⟨g, ?_⟩
  rw [← hg] at ha
  have h := congrArg (fun v : CaseII.modelF => CaseII.into D k v) ha
  rw [action_apply] at h
  have hxval : CaseII.into D k (e.symm x) = (x : G) :=
    congrArg Subtype.val (e.apply_symm_apply x)
  have hyval : CaseII.into D k (e.symm y) = (y : G) :=
    congrArg Subtype.val (e.apply_symm_apply y)
  simpa only [hxval, hyval] using h

open CaseII.FAction in
/-- Transport actual isomorphism and orbit witnesses from the faithful automizer. -/
public theorem fNormalizerAction_of_automizer
    (hiso : Nonempty (automizer D k ≃* Equiv.Perm (Fin 5)))
    (htrans : ∀ x y : CaseII.modelF, x ≠ 1 → y ≠ 1 →
      ∃ a : automizer D k, (a : MulAut CaseII.modelF) x = y) :
    FNormalizerAction D k :=
  ⟨hiso.map (fun e => (quotientEquiv D k).trans e),
    fNormalizer_fusion_of_automizer D k htrans⟩

open CaseII.FAction in
/-- Conditional assembly with separate orbit and identification inputs.
`CaseII.FAction.finite_orbits` now supplies the first input. -/
public theorem fNormalizerAction_of_finite_results
    (horbits : ∀ H : Subgroup (MulAut CaseII.modelF), FiniteSetup H →
      Nat.card H = 120 ∧ ∀ x y : CaseII.modelF, x ≠ 1 → y ≠ 1 →
        ∃ a : H, (a : MulAut CaseII.modelF) x = y)
    (hidentify : ∀ H : Subgroup (MulAut CaseII.modelF), localAutomizer ≤ H →
      Nat.card H = 120 →
      (∀ x y : CaseII.modelF, x ≠ 1 → y ≠ 1 →
        ∃ a : H, (a : MulAut CaseII.modelF) x = y) →
      Nonempty (H ≃* Equiv.Perm (Fin 5)))
    (hd : IsConj D.z (CaseII.into D k CaseII.d)) : FNormalizerAction D k := by
  have h := finiteSetup D k hd
  obtain ⟨hcard, htrans⟩ := horbits (automizer D k) h
  exact fNormalizerAction_of_automizer D k
    (hidentify (automizer D k) h.local_le hcard htrans) htrans

open CaseII.FAction in
/-- The orbit clause of Lemma 2 follows from the single source fusion hypothesis. -/
public theorem fNormalizer_fusion_of_caseII
    (hd : IsConj D.z (CaseII.into D k CaseII.d)) :
    ∀ x y : CaseII.F D k, x ≠ 1 → y ≠ 1 →
      ∃ g : normalizer (CaseII.F D k : Set G), (g : G) * x * (g : G)⁻¹ = y :=
  fNormalizer_fusion_of_automizer D k
    (finite_orbits (automizer D k) (finiteSetup D k hd)).2

open CaseII.FAction in
/-- The actual normalizer has order 1920 under the source fusion hypothesis. -/
public theorem fNormalizer_card_of_caseII
    (hd : IsConj D.z (CaseII.into D k CaseII.d)) :
    Nat.card (normalizer (CaseII.F D k : Set G)) = 1920 := by
  rw [normalizer_card, (finite_orbits (automizer D k) (finiteSetup D k hd)).1]

open CaseII.FAction in
/-- Conditional assembly with the finite S5 identification supplied separately. -/
public theorem fNormalizerAction_of_finite_identification
    (hidentify : ∀ H : Subgroup (MulAut CaseII.modelF), localAutomizer ≤ H →
      Nat.card H = 120 →
      (∀ x y : CaseII.modelF, x ≠ 1 → y ≠ 1 →
        ∃ a : H, (a : MulAut CaseII.modelF) x = y) →
      Nonempty (H ≃* Equiv.Perm (Fin 5)))
    (hd : IsConj D.z (CaseII.into D k CaseII.d)) : FNormalizerAction D k :=
  fNormalizerAction_of_finite_results D k finite_orbits hidentify hd

/-- The quotient and fusion clauses of Janko's Lemma 2: conjugacy of the
marked involution with `d` makes the actual F-normalizer quotient S5 and
fuses every pair of nonidentity elements of F inside that normalizer. -/
public theorem fNormalizerAction_of_caseII
    (hd : IsConj D.z (CaseII.into D k CaseII.d)) : FNormalizerAction D k :=
  fNormalizerAction_of_finite_identification D k CaseII.FAction.finite_identification hd

end Theory.GroupTheory.HeldM22A10.M22Identification
