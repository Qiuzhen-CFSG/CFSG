module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Linear.Collapse
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry


/-!
# Cartan action on the original opposite pair

An element normalizing X transports its normalization of W to the right
conjugate Wˣ. Hence X normalizes the opposite pair for a Cartan-normalizer
frame. The pair is a two-group as a subgroup of Wˣ; the source Hall condition
makes X odd, giving the exact coprimality needed in the core argument.

The actual consumer applies these results to the published core-containment
and collapse proofs. It retains the three layer-generation identities explicitly;
these are still obligations of this task, not assertions of source 11.5.7.
All other premises are the permitted preceding Chapter 11 conclusions.
Source: Aschbacher--Smith, 11.5.7, printed pp.781--782.
-/

open Subgroup
open CFSG.Quasithin.Chapter12.Section02
public section
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Linear
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    {D : ChosenModule T L V} (E : Geometry D)

omit [Finite G] in
private theorem normalizes_right_conjugate {A B : Subgroup G} {x : G}
    (hx : x ∈ normalizer (A : Set G)) (hAB : A ≤ normalizer (B : Set G)) :
    A ≤ normalizer (ChapterG.Section02.Setup.conjugate B x : Set G) := by
  have he : A.map (MulAut.conj x⁻¹).toMonoidHom = A :=
    mem_normalizer_iff_map_conj_eq.mp ((normalizer (A : Set G)).inv_mem hx)
  have hm := (map_mono (f := (MulAut.conj x⁻¹).toMonoidHom) hAB).trans
    (B.le_normalizer_map (MulAut.conj x⁻¹).toMonoidHom)
  rwa [he] at hm

/-- A Cartan-normalizer frame makes the opposite pair X-invariant. -/
theorem Cartan_normalizes_oppositePair {x y : G}
    (hX : E.X ≤ E.G₁) (hx : x ∈ normalizer (E.X : Set G))
    (hy : y ∈ normalizer (E.X : Set G)) :
    E.X ≤ normalizer (oppositePair E x y : Set G) := by
  have hXW := hX.trans (le_normalizer_conjugateSpanBy V E.G₁)
  exact (le_inf (normalizes_right_conjugate hx hXW)
    (normalizes_right_conjugate hy hXW)).trans inf_normalizer_le_normalizer_inf

/-- The literal Hall Cartan has order coprime to the opposite pair. -/
theorem Cartan_coprime_oppositePair (x y : G)
    (hUT : E.W ≤ (T : Subgroup G)) (hX : LocalGeometry.IsCartan T L E.X) :
    Nat.Coprime (Nat.card E.X) (Nat.card (oppositePair E x y)) := by
  have hp : IsPGroup 2 (oppositePair E x y) :=
    ((T.isPGroup'.to_le hUT).map (MulAut.conj x⁻¹).toMonoidHom).to_le inf_le_left
  obtain ⟨n, hn⟩ := hp.exists_card_eq
  rw [hn]
  exact (Nat.coprime_two_right.mpr hX.odd).pow_right n

/-- Apply the three generation identities, discharging pair normalization and coprimality. -/
theorem threeCore_collapse_of_generation {x y : G}
    (d : ChapterG.Section02.LinearThree.Hypothesis (setup E)
      E.input.field.Carrier E.input.field.degree x y)
    (hUT : E.W ≤ (T : Subgroup G))
    (hf : (frattini E.W).map E.W.subtype ≤ E.V₁)
    (hTG : (T : Subgroup G) ≤ E.G₁) (hXG : E.X ≤ E.G₁)
    (hX : LocalGeometry.IsCartan T L E.X)
    (hx : x ∈ normalizer (E.X : Set G)) (hy : y ∈ normalizer (E.X : Set G))
    (hUQ : E.W ≤ E.G₁.pCoreIn 2)
    (hgen : E.G₁ ≤ (E.K ⊔ E.Y) ⊔ E.M₁)
    (hSL : threeCore E x y = ⁅threeCore E x y,E.L₁⁆ ⊔ oppositePair E x y)
    (hSX : threeCore E x y ≤ ⁅threeCore E x y,E.X⁆ ⊔
      (threeCore E x y ⊓ E.W))
    (hEX : oppositePair E x y ≤ ⁅oppositePair E x y,E.X⁆ ⊔ triple E x y)
    (hcartan : ∀ P : Subgroup G, P ≤ (T : Subgroup G) → P = ⁅P,E.X⁆ →
      (frattini P).map P.subtype ≤ E.G₁.pCoreIn 2 → ⁅P,E.Y⁆ ≤ E.Y.pCoreIn 2)
    (hcoreX : ⁅(L ⊔ (T : Subgroup G)).pCoreIn 2,E.X⁆ ≤
      (E.K ⊔ (T : Subgroup G)).pCoreIn 2)
    (hcentral : ⁅E.W,E.G₁.pCoreIn 2⁆ ≤ E.V₁) :
    threeCore E x y ≤ E.G₁.pCoreIn 2 ∧ threeCore E x y = triple E x y := by
  have hSQ := threeCore_le_point_core_of_cartan E d hUT hf hTG hXG hUQ hgen
    hSL hSX hEX (Cartan_normalizes_oppositePair E hXG hx hy)
    (Cartan_coprime_oppositePair E x y hUT hX) hcartan hcoreX
  exact ⟨hSQ, threeCore_eq_triple E d hUT hf hSQ hcentral⟩

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Linear
