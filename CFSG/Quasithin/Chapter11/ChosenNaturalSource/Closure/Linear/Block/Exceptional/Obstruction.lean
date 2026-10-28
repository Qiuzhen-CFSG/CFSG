module

public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Linear.Block.Exceptional.Obstruction.Intrinsic
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Linear.Block.Exceptional.Source

/-!
# The complete surviving odd-extension obstruction in 11.5.7

Relative C-component membership gives the intrinsic C-component structure of
Q = K/O₂(K). SQTK passes from the original overgroup to K and then through
its two-core. The intrinsic obstruction excludes Q/Z(Q) from GL₈(2) whenever
the genuine quotient Q/O₂′(Q) is SL₂(p), p>3.

This stronger route covers every nilpotent SL₂(5) extension, including every
primary factor and homocyclic exponent, and every elementary SL₂(p) extension.
It needs no restriction to a partial model list or SQTK inheritance through
Q/Z(Q). The two quotients remain distinct throughout.

The original-E application uses the parent's complete alternative sieve and
actual action/section theorem. Only inherited SQTK, relative component
membership, the preceding 11.1.2/11.4.1(2) outputs, and the special-structure
outputs remain at the authorized source boundary. Their producers are
qt-d-1222-natural-relative-components, qt-d-1222-shadow-component-triangle,
and qt-d-1222-sl3-special-factor. The parent qt-d-1222-sl3-exceptional-action
retains final K=L₁ assembly and discharge of those earlier inputs.

Source: Aschbacher–Smith 11.1.1–2, 11.4.1(2), and 11.5.7,
refs/quasithin.pdf, printed pp.761–765,775–776,782; A.3.14(13–14), p.50.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open CFSG.Quasithin.Chapter12.Section02
open CFSG.Quasithin.ChapterG.Section02.LinearThree
open CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Linear.Block.Exceptional.Obstruction
variable {G : Type*} [Group G] [Finite G] {H K : Subgroup G}

/-- The literal central quotient fails the order bound in every surviving case (1).
Only relative C-component membership is needed; ambient normality is not assumed. -/
theorem coreCentral_not_card_dvd_of_case_one
    {κ : GroupClass} (hH : IsSQTK κ H) (hK : Source.ComponentIn H K)
    {p : ℕ} (hp : p = 5 ∨ (p.Prime ∧ 11 ≤ p))
    (hm : Source.IsSL (Source.TwoOddQuotient K) 2 p) :
    ¬ Nat.card (coreCentralQuotient K) ∣
      Nat.card (Matrix.GeneralLinearGroup (Fin 8) (ZMod 2)) := by
  let e : (K.subgroupOf H) ≃* K := subgroupOfEquivOfLe hK.1
  have hKt : (⊤ : Subgroup K).IsCComponent := by
    have ht : (⊤ : Subgroup (K.subgroupOf H)).IsCComponent := by
      simpa using hK.2.subgroupOf le_rfl
    simpa only [map_top_of_surjective e.toMonoidHom e.surjective] using ht.map_equiv e
  have hKs : IsSQTK κ K := (IsSQTK.equiv e).mp (hH.subgroup (K.subgroupOf H))
  let Q := K ⧸ pCore 2 K
  let : Group.IsNilpotent (pCore 2 K) := pCore_isPGroup.isNilpotent
  have hQt : (⊤ : Subgroup Q).IsCComponent := by
    simpa only [map_top_of_surjective _ (QuotientGroup.mk'_surjective _)] using
      hKt.map_quotient (pCore 2 K)
  have hQs : IsSQTK κ Q := by
    refine ⟨?_, hKs.isKGroup.quotient _⟩
    intro r hr ho
    let : Fact r.Prime := ⟨hr⟩
    exact (primeRank_quotient_le_of_isTwoGroup r ho _ pCore_isPGroup).trans
      (hKs.stronglyQuasithin r hr ho)
  have hprime : p.Prime := hp.elim (fun he => he ▸ (by decide)) And.left
  have hlarge : 3 < p := by rcases hp with rfl | ⟨_,h⟩ <;> omega
  exact not_central_order_of_SL2_odd_quotient hQs (pCore_quotient_pCore_eq_bot 2)
    hQt hprime hlarge hm

/-- The exact nonsection obstruction, retaining both different residual quotients. -/
theorem coreCentral_not_isSectionOf_binary_eight
    {κ : GroupClass} (hH : IsSQTK κ H) (hK : Source.ComponentIn H K)
    {p : ℕ} (hp : p = 5 ∨ (p.Prime ∧ 11 ≤ p))
    (hm : Source.IsSL (Source.TwoOddQuotient K) 2 p) :
    ¬ CFSG.Quasithin.ChapterA.Section02.IsSectionOf (coreCentralQuotient K)
      (Matrix.GeneralLinearGroup (Fin 8) (ZMod 2)) := by
  rintro ⟨U,f,hf⟩
  exact coreCentral_not_card_dvd_of_case_one hH hK hp hm
    ((card_dvd_of_surjective f hf).trans U.card_subgroup_dvd_card)

variable {T : Sylow 2 G} {L V : Subgroup G} {D : ChosenModule T L V}
  (E : Geometry D) {x y : G}
  (d : Hypothesis (setup E) E.input.field.Carrier E.input.field.degree x y)

include d

/-- The original chosen geometry has no binary degree-eight section in the strict branch. -/
theorem strict_coreCentral_not_isSectionOf_binary_eight
    {κ : GroupClass} (hG₁ : IsSQTK κ E.G₁) (hK : Source.NormalComponentIn E.G₁ E.K)
    (h : RefinementAlternative T L E.L₁ E.L₂ E.K E.X 0 E.input.field.degree)
    (htriangle : ¬ FieldFourTriangle T L E.L₁ E.L₂ E.K E.X)
    (hlt : E.L₁ < E.K) :
    ¬ CFSG.Quasithin.ChapterA.Section02.IsSectionOf (coreCentralQuotient E.K)
      (Matrix.GeneralLinearGroup (Fin 8) (ZMod 2)) := by
  obtain ⟨_,_,⟨p,hp,hm⟩⟩ := case_one_of_strict E d h htriangle hlt
  exact coreCentral_not_isSectionOf_binary_eight hG₁ hK.1 hp hm

/-- Applying the checked original action and section witness gives the contradiction
required by the parent's K=L₁ assembly. No action-kernel premise remains. -/
theorem strict_case_one_false
    {κ : GroupClass} (hG₁ : IsSQTK κ E.G₁) (hK : Source.NormalComponentIn E.G₁ E.K)
    (hUT : E.W ≤ (T : Subgroup G))
    (hfixed : E.W ⊓ centralizer (E.L₁ : Set G) = closureCenter E)
    (hz : E.K ≤ centralizer (closureCenter E : Set G))
    [IsElementaryAbelian 2 (CentralQuotient E)]
    (hr : Group.rank (CentralQuotient E) = 4 * E.input.field.degree)
    (h : RefinementAlternative T L E.L₁ E.L₂ E.K E.X 0 E.input.field.degree)
    (htriangle : ¬ FieldFourTriangle T L E.L₁ E.L₂ E.K E.X)
    (hlt : E.L₁ < E.K) : False := by
  obtain ⟨_,_,_,⟨p,hp,hm⟩,_⟩ :=
    strict_case_one_action_order E d hUT hfixed hz hr h htriangle hlt
  exact coreCentral_not_isSectionOf_binary_eight hG₁ hK.1 hp hm
    (strict_coreCentral_isSectionOf_binary_eight E d hUT hfixed hz hr h hlt)

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Linear.Block.Exceptional.Obstruction
