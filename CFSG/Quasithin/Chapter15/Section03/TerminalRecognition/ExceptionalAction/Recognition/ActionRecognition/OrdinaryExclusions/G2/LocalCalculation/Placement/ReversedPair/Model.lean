module

public import Theory.AtlasPort.LinearGroups.G2.EvenLocal.LongCore
public import Theory.AtlasPort.LinearGroups.G2.BinaryParabolicPair.CoreIdentification
public import Theory.GroupTheory.QuaternionCentralProductResidualRecognition.Residual

/-!
# The involution test for the reversed binary G₂ pair

Two explicit commutators with the second parabolic's cubic generate the
sixteen positive-root elements with coordinates e = 0 and f = c + d. They
belong to the two-core of the actual two-residual: each commutator lies in
both the residual and the normal five-root two-core. A subgroup containing
these sixteen elements and one element of the other coset contains the whole
second core. The square-one elements among the sixteen have f = 0, so lie
in the first parabolic's core.

This gives the model calculation used by ReversedPair to exploit the source
Thompson normalization and nonzero marked commutator, without identifying an
arbitrary representation. Source: Aschbacher–Smith, final proof of 15.3.1,
printed p.1155; the five-root conventions are those of the licensed ATLAS port
in the imports (LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff).
-/

public section

open Subgroup Atlas.G2 Atlas.G2.Explicit Atlas.G2.BinaryCore
open Atlas.G2.BinaryParabolicPair Atlas.G2.LieParabolicSetup
open scoped commutatorElement

namespace CFSG.Quasithin.Chapter15.Section03.TerminalRecognition.ExceptionalAction.ActionRecognition.OrdinaryExclusions.G2.LocalCalculation.Placement.ReversedPair

private abbrev residual : Subgroup (Model (ZMod 2)) :=
  (pResidual 2 secondParabolic).map secondParabolic.subtype

private lemma commutator_mem_residual_core {x : Model (ZMod 2)}
    (hx : x ∈ radical₂) : ⁅x, movingActor⁆ ∈ residual.pCoreIn 2 := by
  have hRN : secondParabolic ≤ normalizer (residual : Set (Model (ZMod 2))) := by
    intro g hg
    apply le_normalizer_map secondParabolic.subtype
    exact ⟨⟨g, hg⟩, by rw [normalizer_eq_top]; trivial, rfl⟩
  have hQN : secondParabolic ≤ normalizer (radical₂ (F := ZMod 2) : Set (Model (ZMod 2))) :=
    EvenLocal.parabolic₂_le_normalizer_radical₂
  have hQ : IsPGroup 2 (radical₂ (F := ZMod 2)) := radical₂_isTwoGroup
  have hle : residual ⊓ radical₂ ≤ residual.pCoreIn 2 :=
    le_pCoreIn_of_normalizes (hQ.to_le inf_le_right) inf_le_left
      ((le_inf residual.le_normalizer ((map_subtype_le _).trans hQN)).trans
        inf_normalizer_le_normalizer_inf)
  apply hle
  constructor
  · exact (le_normalizer_iff_commutator_le_right.mp hRN)
      (commutator_mem_commutator (radical₂_le_local₂.trans local₂_le_parabolic₂ hx)
        (mem_map_of_mem secondParabolic.subtype movingActor_residual))
  · exact (le_normalizer_iff_commutator_le_left.mp hQN)
      (commutator_mem_commutator hx movingActor_mem)

private def u : Fin 6 → ZMod 2 := ![1,1,0,1,0,1]
private def v : Fin 6 → ZMod 2 := ![1,1,1,0,0,1]

private lemma u_eq : unipotentProduct u = ⁅rootF (1 : ZMod 2), movingActor⁆ := by
  apply Subtype.ext
  apply LinearEquiv.toLinearMap_injective
  apply (Pi.basisFun (ZMod 2) (Fin 8)).ext
  intro j
  funext i
  simp only [Pi.basisFun_apply]
  revert j i
  decide +kernel

private lemma v_eq : unipotentProduct v = ⁅rootD (1 : ZMod 2), movingActor⁆ := by
  apply Subtype.ext
  apply LinearEquiv.toLinearMap_injective
  apply (Pi.basisFun (ZMod 2) (Fin 8)).ext
  intro j
  funext i
  simp only [Pi.basisFun_apply]
  revert j i
  decide +kernel

private lemma u_mem : unipotentProduct u ∈ residual.pCoreIn 2 := by
  rw [u_eq]
  exact commutator_mem_residual_core ⟨![0,0,0,0,0,1], rfl, by simp [unipotentProduct]⟩

private lemma v_mem : unipotentProduct v ∈ residual.pCoreIn 2 := by
  rw [v_eq]
  exact commutator_mem_residual_core ⟨![0,0,0,1,0,0], rfl, by simp [unipotentProduct]⟩

private def powerParams (t : Fin 6 → ZMod 2) : ℕ → Fin 6 → ZMod 2
  | 0 => 0
  | n+1 => unipotentProductParameters (powerParams t n) t

private lemma powerParams_spec (t : Fin 6 → ZMod 2) (n : ℕ) :
    unipotentProduct (powerParams t n) = unipotentProduct t ^ n := by
  induction n with
  | zero => exact unipotentProduct_zero
  | succ n ih => rw [powerParams, ← unipotentProduct_mul, ih, pow_succ]

private lemma even_coverage : ∀ a b c d : ZMod 2, ∃ i j : Fin 4,
    unipotentProductParameters (powerParams u i.val) (powerParams v j.val) =
      ![a,b,c,d,0,c+d] := by
  decide +kernel

private lemma even_mem (t : Fin 6 → ZMod 2) (ht : t 4 = 0) (he : t 5 = t 2 + t 3) :
    unipotentProduct t ∈ residual.pCoreIn 2 := by
  obtain ⟨i,j,hij⟩ := even_coverage (t 0) (t 1) (t 2) (t 3)
  have ht' : ![t 0,t 1,t 2,t 3,0,t 2+t 3] = t := by
    ext k
    fin_cases k <;> simp [ht,he]
  rw [← ht', ← hij, ← unipotentProduct_mul, powerParams_spec, powerParams_spec]
  exact (residual.pCoreIn 2).mul_mem
    ((residual.pCoreIn 2).pow_mem u_mem _) ((residual.pCoreIn 2).pow_mem v_mem _)

private lemma square_test : ∀ t : Fin 6 → ZMod 2, t 4 = 0 →
    unipotentProductParameters t t = 0 → t 5 = t 2 + t 3 → t 5 = 0 := by
  decide +kernel

private lemma parity_test : ∀ a b c d e f : ZMod 2,
    c ≠ a+b → f ≠ d+e → f+c = (d+a)+(e+b) := by decide +kernel

/-- If C contains the second residual core but not the whole second core,
every square-one element of their intersection lies in the first core. -/
theorem involution_mem_first_core (C : Subgroup (Model (ZMod 2)))
    (hR : ((pResidual 2 secondParabolic).map secondParabolic.subtype).pCoreIn 2 ≤ C)
    (hQ : ¬ secondParabolic.pCoreIn 2 ≤ C)
    {x : Model (ZMod 2)} (hx : x ∈ secondParabolic.pCoreIn 2)
    (hsq : x ^ 2 = 1) (hxC : x ∈ C) : x ∈ firstParabolic.pCoreIn 2 := by
  rw [show secondParabolic.pCoreIn 2 = radical₂ from EvenLocal.parabolic₂_pCoreIn] at hx
  obtain ⟨t, ht, rfl⟩ := hx
  have hs : unipotentProductParameters t t = 0 := by
    apply unipotentProduct_injective
    rw [← unipotentProduct_mul, ← pow_two, hsq, unipotentProduct_zero]
  have he : t 5 = t 2 + t 3 := by
    by_contra he
    apply hQ
    rw [show secondParabolic.pCoreIn 2 = radical₂ from EvenLocal.parabolic₂_pCoreIn]
    rintro y ⟨s, hs0, rfl⟩
    by_cases hs1 : s 5 = s 2+s 3
    · exact hR (even_mem s hs0 hs1)
    · have hst0 : unipotentProductParameters s t 4 = 0 := by
        simp [unipotentProductParameters, ht, hs0]
      have hst1 : unipotentProductParameters s t 5 =
          unipotentProductParameters s t 2 + unipotentProductParameters s t 3 := by
        simpa [unipotentProductParameters, ht, show (2 : ZMod 2) = 0 from rfl] using
          parity_test (s 2) (s 3) (s 5) (t 2) (t 3) (t 5) hs1 he
      have hm := hR (even_mem (unipotentProductParameters s t) hst0 hst1)
      rw [← unipotentProduct_mul] at hm
      exact (C.mul_mem_cancel_right hxC).mp hm
  have ht5 := square_test t ht hs he
  rw [firstParabolic_pCore]
  refine ⟨⟨t 0,t 1,t 2,t 3,t 4⟩, ?_⟩
  simp [embedding, parameters, unipotentProduct, ht5]

end CFSG.Quasithin.Chapter15.Section03.TerminalRecognition.ExceptionalAction.ActionRecognition.OrdinaryExclusions.G2.LocalCalculation.Placement.ReversedPair
