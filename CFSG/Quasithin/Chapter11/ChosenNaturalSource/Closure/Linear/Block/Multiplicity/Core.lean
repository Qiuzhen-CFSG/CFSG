module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Linear.Block.Multiplicity.Transport
public import Theory.GroupTheory.PCoreInRestriction

/-!
# The original solvable-residual two-core

A product of two elementary matrices fixes no nonzero vector in a
natural plane, hence in a sum of natural planes. Lift that actor to K.
Its quotient displacements are onto. Since V₁=[V,U] lies in Φ(U),
Frattini nongeneration puts all of U in K=L₁. The original relative
normality then puts U in O₂(K).

For the reverse containment, the checked point-radical theorem identifies
the starred image of U with the two-core of the full point normalizer.
The starred kernel inside L is now O₂(L)=V≤U. Pulling back gives the
full point-normalizer core, and hence the core of the original solvable
residual. The argument retains the literal original quotient maps.
Source: Aschbacher--Smith, 11.5.7, printed p.782; G.2.5(1).
-/

@[expose] public noncomputable section
open Subgroup Representation Matrix.SpecialLinearGroup
open scoped commutatorElement
open CFSG.Quasithin.Chapter12.Section02
open CFSG.Quasithin.ChapterG.Section02.LinearThree
open CFSG.Quasithin.ChapterB.QuasisimpleSource
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Linear.Block.Multiplicity
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {D : ChosenModule T L V} (E : Geometry D)

private def movingMatrix :=
  transvection (by decide : (0 : Fin 2) ≠ 1) (1 : E.input.field.Carrier) *
    transvection (by decide : (1 : Fin 2) ≠ 0) (1 : E.input.field.Carrier)

private theorem movingMatrix_fixed (v : Fin 2 → E.input.field.Carrier)
    (hv : linearNatural E.input.field 2 (movingMatrix E) v = v) : v = 0 := by
  change specialLinearNatural 2 (movingMatrix E) v = v at hv
  simp only [movingMatrix, map_mul, Module.End.mul_apply,
    OneCohomology.SLHigherNatural.action_transvection] at hv
  have h0 := congrFun hv 0
  have h1 := congrFun hv 1
  have hv0 : v 0 = 0 := by simpa [Pi.single_apply] using h1
  have hv1 : v 1 = 0 := by simpa [Pi.single_apply, hv0] using h0
  ext i
  fin_cases i <;> assumption

theorem exists_fixedFree_actor (f : E.ClosureFlag) (hK : E.K = E.L₁) {r : ℕ}
    (e : ActionEquiv (action E f hK) (repeated (linearNatural E.input.field 2) r)) :
    ∃ k : E.K, ∀ v : Space E f,
      action E f hK (QuotientGroup.mk' (pCore 2 E.K) k) v = v → v = 0 := by
  obtain ⟨k, hk⟩ := QuotientGroup.mk'_surjective (pCore 2 E.K)
    (e.groupEquiv.symm (movingMatrix E))
  refine ⟨k, ?_⟩
  intro v hv
  apply e.linearEquiv.injective
  rw [map_zero]
  funext i
  apply movingMatrix_fixed E
  have h := e.intertwines (QuotientGroup.mk' (pCore 2 E.K) k) v
  rw [hv, hk, e.groupEquiv.apply_symm_apply] at h
  exact (congrFun h i).symm

theorem point_le_frattini {x y : G}
    (d : Hypothesis (setup E) E.input.field.Carrier E.input.field.degree x y)
    (hUT : E.W ≤ (T : Subgroup G))
    (hf : (frattini E.W).map E.W.subtype ≤ E.V₁) :
    E.V₁.subgroupOf E.W ≤ frattini E.W := by
  let : Fact (IsPGroup 2 E.W) := ⟨T.isPGroup'.to_le hUT⟩
  have hder : ⁅E.W,E.W⁆ ≤ (frattini E.W).map E.W.subtype := by
    have h := map_mono (f := E.W.subtype)
      (commutator_le_frattini_of_isPGroup (R := E.W) (p := 2))
    rwa [map_commutator_eq, range_subtype] at h
  have hp : E.V₁ ≤ (frattini E.W).map E.W.subtype := by
    have he : ⁅V,E.W⁆ = E.V₁ := d.commutator_V_U_eq_point hUT hf
    exact he.ge.trans ((commutator_mono (le_conjugateSpanBy V E.G₁) le_rfl).trans hder)
  intro z hz
  obtain ⟨a, ha, he⟩ := hp hz
  exact (Subtype.ext he : a = z) ▸ ha

set_option backward.isDefEq.respectTransparency false in
theorem closure_le_original_residual (f : E.ClosureFlag) (hseed : E.V₃ = V)
    (hK : E.K = E.L₁) {r : ℕ}
    (e : ActionEquiv (action E f hK) (repeated (linearNatural E.input.field 2) r))
    {x y : G}
    (d : Hypothesis (setup E) E.input.field.Carrier E.input.field.degree x y)
    (hUT : E.W ≤ (T : Subgroup G))
    (hf : (frattini E.W).map E.W.subtype ≤ E.V₁) : E.W ≤ E.L₁ := by
  obtain ⟨k, hk⟩ := exists_fixedFree_actor E f hK e
  let q := QuotientGroup.mk' (E.V₁.subgroupOf E.W)
  let π : E.W →* E.tilde (E.localClosure E.G₁) :=
    (quotientEquiv E hseed).toMonoidHom.comp q
  have hπ : Function.Surjective π := (quotientEquiv E hseed).surjective.comp
    (QuotientGroup.mk'_surjective _)
  let δ : Space E f →ₗ[ZMod 2] Space E f :=
    action E f hK (QuotientGroup.mk' (pCore 2 E.K) k) - LinearMap.id
  have hi : Function.Injective δ := by
    apply LinearMap.ker_eq_bot.mp
    apply bot_unique
    intro v hv
    exact hk v (sub_eq_zero.mp hv)
  have hs := Finite.surjective_of_injective hi
  let a : MulAut E.W := E.W.normalizerMonoidHom
    ⟨k, le_normalizer_conjugateSpanBy V E.G₁ (E.K_le_G₁ k.property)⟩
  have hact (w : E.W) : π (a w) =
      (action E f hK (QuotientGroup.mk' (pCore 2 E.K) k)
        (Additive.ofMul (π w))).toMul := by
    have h := quotientEquiv_action E hseed f hK k (q w)
    rw [Outside.quotientAction_apply_mk] at h
    exact congrArg Additive.toMul h
  have htop : E.K.subgroupOf E.W = ⊤ := by
    apply frattini_nongenerating
    apply top_unique
    intro w _
    obtain ⟨v, hv⟩ := hs (Additive.ofMul (π w))
    obtain ⟨u, hu⟩ := hπ v.toMul
    have hδ : π (a u * u⁻¹) = π w := by
      rw [map_mul, map_inv, hact, hu]
      have hh := congrArg (fun t : Space E f => t.toMul) hv
      change (action E f hK (QuotientGroup.mk' (pCore 2 E.K) k) v).toMul /
        v.toMul = π w at hh
      change (action E f hK (QuotientGroup.mk' (pCore 2 E.K) k) v).toMul *
        v.toMul⁻¹ = π w
      simpa only [div_eq_mul_inv] using hh
    have he : q (a u * u⁻¹) = q w := (quotientEquiv E hseed).injective hδ
    have hn : (a u * u⁻¹)⁻¹ * w ∈ E.V₁.subgroupOf E.W := QuotientGroup.eq.mp he
    have hdis : a u * u⁻¹ ∈ E.K.subgroupOf E.W := by
      change ⁅(k : G), (u : G)⁆ ∈ E.K
      exact (le_normalizer_iff_commutator_le_left.mp
        ((Outside.closure_le_point_normalizer E).trans E.G₁_normalizes_K))
          (commutator_mem_commutator k.property u.property)
    have hh := (E.K.subgroupOf E.W ⊔ frattini E.W).mul_mem
      (mem_sup_left hdis) (mem_sup_right (point_le_frattini E d hUT hf hn))
    simpa only [mul_inv_cancel_left] using hh
  intro w hw
  have hkW : (⟨w,hw⟩ : E.W) ∈ E.K.subgroupOf E.W := htop.ge (mem_top _)
  exact hK ▸ hkW

private theorem star_core (A : Subgroup G) (hA : A ≤ (setup E).LT) :
    (setup E).star (A.pCoreIn 2) = ((setup E).star A).pCoreIn 2 := by
  let q := QuotientGroup.mk' (pCore 2 (setup E).LT)
  have hk : IsPGroup 2 q.ker := by rw [QuotientGroup.ker_mk']; exact pCore_isPGroup
  have he := map_pCoreIn_of_ker_isPGroup q hk (A.subgroupOf (setup E).LT)
  rw [pCoreIn_subgroupOf 2 A (setup E).LT hA] at he
  exact he

theorem pointNormalizer_core_eq {x y : G}
    (d : Hypothesis (setup E) E.input.field.Carrier E.input.field.degree x y)
    (hUT : E.W ≤ (T : Subgroup G))
    (hf : (frattini E.W).map E.W.subtype ≤ E.V₁)
    (hUL : E.W ≤ L) (hcore : L.pCoreIn 2 = V) :
    (L ⊓ E.G₁).pCoreIn 2 = E.W := by
  have hP : L ⊓ E.G₁ ≤ (setup E).LT := inf_le_left.trans le_sup_left
  have he : (setup E).star ((L ⊓ E.G₁).pCoreIn 2) = (setup E).star E.W := by
    rw [star_core E _ hP]
    exact (d.star_U_eq_point_core hUT hf).symm
  apply le_antisymm
  · intro z hz
    let zi : (setup E).LT := ⟨z, hP (pCoreIn_le 2 _ hz)⟩
    have hzL : z ∈ L := (pCoreIn_le 2 _ hz).1
    have hzstar : QuotientGroup.mk' (pCore 2 (setup E).LT) zi ∈
        (setup E).star E.W := he.le (mem_map_of_mem _ hz)
    obtain ⟨w, hw, hew⟩ := hzstar
    have hdiff : w⁻¹ * zi ∈ pCore 2 (setup E).LT := QuotientGroup.eq.mp hew
    have hv : (w : G)⁻¹ * z ∈ V := by
      apply hcore.le
      exact inf_pCoreIn_le_of_le 2 (show L ≤ L ⊔ (T : Subgroup G) from le_sup_left)
        ⟨L.mul_mem (L.inv_mem (hUL hw)) hzL, mem_map_of_mem _ hdiff⟩
    have hw' : (w : G) ∈ E.W := hw
    have hm := E.W.mul_mem hw' (le_conjugateSpanBy V E.G₁ hv)
    simpa only [mul_inv_cancel_left] using hm
  · exact le_pCoreIn_of_normalizes (T.isPGroup'.to_le hUT)
      (le_inf hUL (Outside.closure_le_point_normalizer E))
      (inf_le_right.trans (le_normalizer_conjugateSpanBy V E.G₁))

theorem original_residual_core_eq (f : E.ClosureFlag) (hseed : E.V₃ = V)
    (hK : E.K = E.L₁) {r : ℕ}
    (e : ActionEquiv (action E f hK) (repeated (linearNatural E.input.field 2) r))
    {x y : G}
    (d : Hypothesis (setup E) E.input.field.Carrier E.input.field.degree x y)
    (hUT : E.W ≤ (T : Subgroup G))
    (hf : (frattini E.W).map E.W.subtype ≤ E.V₁)
    (hc : threeCore E x y = triple E x y) :
    E.W = E.K.pCoreIn 2 ∧ E.W = E.L₁.pCoreIn 2 := by
  have hs := original_core_and_split E f hK hseed d hUT hf hc ⟨r, ⟨e⟩⟩
  have hWL := closure_le_original_residual E f hseed hK e d hUT hf
  have hW : E.W = E.K.pCoreIn 2 := by
    apply le_antisymm
    · exact le_pCoreIn_of_normalizes (T.isPGroup'.to_le hUT) (hK.symm ▸ hWL)
        (E.K_le_G₁.trans (le_normalizer_conjugateSpanBy V E.G₁))
    · rw [← pointNormalizer_core_eq E d hUT hf hs.1 hs.2.1]
      exact pCoreIn_mono_of_normalizes
        (le_inf (hK.symm ▸ E.L₁_le) E.K_le_G₁)
        (inf_le_right.trans E.G₁_normalizes_K)
  exact ⟨hW, by simpa only [hK] using hW⟩

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Linear.Block.Multiplicity
