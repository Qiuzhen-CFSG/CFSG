module

public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.A10Identification.NoncentralAnalysis.Fusion.AmbientGeometry

/-!
# The elementary eight-group in Held's tau fusion case

Under pi~mu, pi~tau and pi not~lambda, the global pi-class in S is exactly
the seven nonidentity elements of U=<pi,mu,tau>. Thus N_G(S) normalizes U.
The concrete centralizer calculation C_H(U)=S, together with pi in U,
gives C_G(U)=S. This prepares the faithful action on U used to determine
the normalizer order in Held, Illinois J. Math. 13 (1969), Lemma 2.6, p.228.
All conjugation and centralizer calculations use the actual A10 model.
-/

open Subgroup Equiv
open scoped IsMulCommutative
namespace Theory.GroupTheory.HeldM22A10.A10Identification.NoncentralAnalysis.Fusion
open Coordinates

private abbrev TauCode := Fin 2 × Fin 2 × Fin 2
private def tauWord (a : TauCode) : H := elementaryWord 1 (a.1, a.2.1, a.2.2, 0)

private theorem tauWord_mul : ∀ a b, tauWord (a + b) = tauWord a * tauWord b := by
  decide +kernel

private theorem tauWord_injective : Function.Injective tauWord := by decide +kernel

private def tauHom : Multiplicative TauCode →* H where
  toFun a := tauWord a.toAdd
  map_one' := by decide +kernel
  map_mul' a b := tauWord_mul a.toAdd b.toAdd

/-- The concrete subgroup U=<pi,mu,tau> of S. -/
public def tauFusionSpaceModel : Subgroup H := tauHom.range

private theorem mem_tauFusionSpaceModel (x : H) :
    x ∈ tauFusionSpaceModel ↔ ∃ a, tauWord a = x := Iff.rfl

public theorem tauFusionSpaceModel_card : Nat.card tauFusionSpaceModel = 8 := by
  have hi : Function.Injective tauHom := tauWord_injective
  rw [tauFusionSpaceModel, ← Nat.card_congr (MonoidHom.ofInjective hi).toEquiv]
  simp [TauCode]

public theorem tauFusionSpaceModel_le_S : tauFusionSpaceModel ≤ modelS := by
  rintro x ⟨a, rfl⟩
  exact (mem_elementary 1 _).mpr ⟨(a.toAdd.1, a.toAdd.2.1, a.toAdd.2.2, 0), rfl⟩

private theorem tau_generators_mem (i : Fin 3) :
    (![pi, mu, tau] : Fin 3 → H) i ∈ tauFusionSpaceModel := by
  rw [mem_tauFusionSpaceModel]
  have h : ∀ j : Fin 3, ∃ a, tauWord a = (![pi, mu, tau] : Fin 3 → H) j := by
    decide +kernel
  exact h i

public theorem pi_mem_tauFusionSpaceModel : pi ∈ tauFusionSpaceModel := tau_generators_mem 0

private theorem word_mem_tauFusionSpaceModel (a : BaseCode) :
    elementaryWord 1 a ∈ tauFusionSpaceModel ↔ a.2.2.2 = 0 := by
  rw [mem_tauFusionSpaceModel]
  have h : ∀ a : BaseCode,
      (∃ b, tauWord b = elementaryWord 1 a) ↔ a.2.2.2 = 0 := by decide +kernel
  exact h a

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
private theorem centralizing_tau_code : ∀ b : Code,
    (∀ i : Fin 3, (![pi, mu, tau] : Fin 3 → H) i * word b =
      word b * (![pi, mu, tau] : Fin 3 → H) i) →
    elementaryCode 1 (b.1.1, b.1.2.1, b.2.1, b.2.2.2.2) = b := by
  decide +kernel

public theorem tauFusionSpaceModel_centralizer :
    centralizer (tauFusionSpaceModel : Set H) = modelS := by
  apply le_antisymm
  · intro x hx
    obtain ⟨a, rfl⟩ := word_bijective.surjective x
    apply (mem_elementary 1 _).mpr
    refine ⟨(a.1.1, a.1.2.1, a.2.1, a.2.2.2.2), ?_⟩
    rw [elementaryWord_eq_word]
    exact congrArg word (centralizing_tau_code a
      (fun i => mem_centralizer_iff.mp hx _ (tau_generators_mem i)))
  · change elementary 1 ≤ _
    rw [← elementary_selfCentralizing 1]
    exact centralizer_le tauFusionSpaceModel_le_S

private def tauRepresentative : Fin 6 → H := ![1, pi, mu, tau, lam, pi * lam]
private def tauOrbitLabel (a : BaseCode) : Fin 6 :=
  if a.2.2.2 = 1 then (if a.1 = a.2.1 * a.2.2.1 then 4 else 5)
  else if a.2.2.1 = 1 then 3 else if a.2.1 = 1 then 2 else if a.1 = 1 then 1 else 0
private def tauConjugator (b : TauCode) : H :=
  mup ^ b.1.val * taup ^ b.2.1.val * xi ^ b.2.2.val

private theorem tauOrbit_conjugate : ∀ a : BaseCode, ∃ b : TauCode,
    tauConjugator b * tauRepresentative (tauOrbitLabel a) * (tauConjugator b)⁻¹ =
      elementaryWord 1 a := by decide +kernel

private theorem tauOrbit_selected : ∀ a : BaseCode,
    (tauOrbitLabel a = 1 ∨ tauOrbitLabel a = 2 ∨ tauOrbitLabel a = 3) ↔
      a.2.2.2 = 0 ∧ elementaryWord 1 a ≠ 1 := by decide +kernel

/-- The six concrete Sylow orbits determine every invariant class predicate on S. -/
public theorem tauFusionSpaceModel_class (p : H → Prop)
    (hconj : ∀ g y : H, p (g * y * g⁻¹) ↔ p y)
    (h1 : ¬ p 1) (hpi : p pi) (hmu : p mu) (htau : p tau)
    (hlam : ¬ p lam) (hpiLam : ¬ p (Coordinates.pi * lam))
    {x : H} (hx : x ∈ modelS) :
    p x ↔ x ∈ tauFusionSpaceModel ∧ x ≠ 1 := by
  have hr (i : Fin 6) : p (tauRepresentative i) ↔ i = 1 ∨ i = 2 ∨ i = 3 := by
    fin_cases i <;> simp [tauRepresentative, h1, hpi, hmu, htau, hlam, hpiLam]
  obtain ⟨a, rfl⟩ := (mem_elementary 1 x).mp hx
  have hp : p (elementaryWord 1 a) ↔ p (tauRepresentative (tauOrbitLabel a)) := by
    obtain ⟨b, hb⟩ := tauOrbit_conjugate a
    rw [← hb]
    exact hconj _ _
  rw [hp, hr, tauOrbit_selected, word_mem_tauFusionSpaceModel]

end Theory.GroupTheory.HeldM22A10.A10Identification.NoncentralAnalysis.Fusion
