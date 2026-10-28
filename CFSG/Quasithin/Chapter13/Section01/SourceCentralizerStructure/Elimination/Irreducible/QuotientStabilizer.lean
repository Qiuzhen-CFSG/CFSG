module
public import CFSG.Quasithin.Chapter13.Section01.SourceCentralizerStructure.Elimination.Irreducible.SylowIrreducible
public import Theory.GroupAction.PerfectCentralQuotient

/-!
# The original stabilizer action on the component quotients

Conjugation by C_L(u) acts on Q = K/O₂(K). Its kernel acts trivially on
X/O₂(X), since the pullback of O₂(K) to X is a normal two-subgroup of X.
Thus the original odd Frattini image is a quotient of this precise action
image. The S₃ section from the original moved-module branch survives.

Perfectness of Q makes Aut(Q) act faithfully on Q/Z(Q), so the same S₃
section survives transport through an actual central-quotient model. This
does not assert that it survives in Out(Q): proving that the relevant inner
kernel acts trivially remains part of qt-d-1317-centralizer-irreducible.
The final source application retains SieveActions, whose earlier 13.1.10
construction belongs to qt-d-1317-module-orbits.

Source: Aschbacher–Smith, 13.1.12(3), printed p.874.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section01.SourceCentralizerStructure.Elimination
open Chapter1
variable {G : Type*} [Group G] [Finite G]

/-- The original point stabilizer acts on the actual component two-core quotient. -/
@[expose] def componentStabilizerCoreAction (L K : Subgroup G) (u : G)
    (hn : L ⊓ centralizer ({u} : Set G) ≤ normalizer (K : Set G)) :
    (L ⊓ centralizer ({u} : Set G) : Subgroup G) →* MulAut (XiQuotient K) :=
  (quotientAut (pCore 2 K)).comp (K.normalizerMonoidHom.comp (inclusion hn))

omit [Finite G] in
private theorem core_kernel_le_frattini (A X K : Subgroup G)
    (hAX : A ≤ normalizer (X : Set G)) (hAK : A ≤ normalizer (K : Set G))
    (hXK : X ≤ K) :
    ((quotientAut (pCore 2 K)).comp (K.normalizerMonoidHom.comp (inclusion hAK))).ker ≤
      (xiFrattiniAction A X hAX).ker := by
  let _ := conjMulDistribMulActionOfLeNormalizer A X hAX
  let i := inclusion hXK
  have hc : (pCore 2 K).comap i ≤ pCore 2 X :=
    le_sSup ⟨inferInstance,pCore_isPGroup.comap_of_injective i (inclusion_injective hXK)⟩
  intro a ha
  apply MulEquiv.ext
  intro v
  induction v using QuotientGroup.induction_on with | H v =>
    induction v using QuotientGroup.induction_on with | H x =>
      let y : X := MulDistribMulAction.toMulAut A X a x
      have he : QuotientGroup.mk' (pCore 2 K) (i y) =
          QuotientGroup.mk' (pCore 2 K) (i x) := by
        have hh := DFunLike.congr_fun ha (QuotientGroup.mk' (pCore 2 K) (i x))
        change quotientAut (pCore 2 K)
          (K.normalizerMonoidHom (inclusion hAK a))
          (QuotientGroup.mk' (pCore 2 K) (i x)) = _ at hh
        rw [quotientAut_apply_mk] at hh
        exact hh
      have hx : y⁻¹ * x ∈ pCore 2 X := hc (by
        change i (y⁻¹ * x) ∈ pCore 2 K
        simpa only [map_mul,map_inv] using QuotientGroup.eq.mp he)
      have heX : QuotientGroup.mk' (pCore 2 X) y = QuotientGroup.mk' (pCore 2 X) x :=
        QuotientGroup.eq.mpr hx
      change xiFrattiniAction A X hAX a
        (QuotientGroup.mk' _ (QuotientGroup.mk' _ x)) = _
      simp only [xiFrattiniAction,MonoidHom.comp_apply,quotientAut_apply_mk]
      exact congrArg (QuotientGroup.mk' (frattini (XiQuotient X))) heX

variable {T : Sylow 2 G} {L : Subgroup G} {p : ℕ} [Fact p.Prime]

/-- The full local normalizer bound restricts to the literal component stabilizer. -/
theorem Context.stabilizer_normalizes_component (h : Context T L p)
    {u : G} (s : Selected T L u) {K : Subgroup G} (e : Escape T L p u K)
    (hi : ComponentNormalizerIrreducible L K p u) :
    L ⊓ centralizer ({u} : Set G) ≤ normalizer (K : Set G) :=
  (inf_le_inf_right _ L.le_normalizer).trans (h.local_normalizes_component s e hi)

/-- The original Frattini image is a quotient of the actual action image on K/O₂(K).
This identifies the maps on each element of C_L(u), not just their group families. -/
theorem Context.stabilizer_frattini_factors_core (h : Context T L p)
    {u : G} (s : Selected T L u) {K : Subgroup G} (e : Escape T L p u K)
    (hi : ComponentNormalizerIrreducible L K p u) :
    let ρ := componentStabilizerCoreAction L K u (h.stabilizer_normalizes_component s e hi)
    let σ := componentStabilizerFrattiniAction L p u
    ∃ f : ρ.range →* σ.range, Function.Surjective f ∧
      ∀ a : (L ⊓ centralizer ({u} : Set G) : Subgroup G),
        f (ρ.rangeRestrict a) = σ.rangeRestrict a := by
  let ρ := componentStabilizerCoreAction L K u (h.stabilizer_normalizes_component s e hi)
  let σ := componentStabilizerFrattiniAction L p u
  have hk : ρ.ker ≤ σ.ker :=
    core_kernel_le_frattini _ _ _ (inf_le_left.trans (XiP_invariant p L.le_normalizer))
      (h.stabilizer_normalizes_component s e hi) (h.radical_le_component s e hi)
  let f : ρ.range →* σ.range := ρ.rangeRestrict.liftOfSurjective
    ρ.rangeRestrict_surjective ⟨σ.rangeRestrict,by
      simpa only [MonoidHom.ker_rangeRestrict] using hk⟩
  have he (a : (L ⊓ centralizer ({u} : Set G) : Subgroup G)) :
      f (ρ.rangeRestrict a) = σ.rangeRestrict a := by simp [f]
  refine ⟨f,?_,he⟩
  intro y
  obtain ⟨a,rfl⟩ := σ.rangeRestrict_surjective y
  exact ⟨ρ.rangeRestrict a,he a⟩

/-- The source's S₃ section survives in the actual action on K/O₂(K).
No claim about the outer quotient or the whole component is implicit. -/
theorem Context.stabilizer_core_symmetric_three (h : Context T L p)
    {u : G} (s : Selected T L u) {K : Subgroup G} (e : Escape T L p u K)
    (hi : ComponentNormalizerIrreducible L K p u)
    (hs : SymmetricThreeStabilizerQuotient L p u) :
    ∃ f : (componentStabilizerCoreAction L K u
        (h.stabilizer_normalizes_component s e hi)).range →* Equiv.Perm (Fin 3),
      Function.Surjective f := by
  obtain ⟨f,hf,_⟩ := h.stabilizer_frattini_factors_core s e hi
  obtain ⟨g,hg⟩ := hs
  exact ⟨g.comp f,hg.comp hf⟩

/-- The proved Sylow branch reduction supplies the S₃ quotient in the exact
core action needed by the remaining reducible-Sylow model sieve. -/
theorem Context.sylow_reducible_core_symmetric_three (h : Context T L p)
    (a : SieveActions h) (c : Control T L p)
    {u : G} (s : Selected T L u)
    (hnt : ¬ (T : Subgroup G) ≤ centralizer ({u} : Set G))
    {K : Subgroup G} (e : Escape T L p u K)
    (hi : ComponentNormalizerIrreducible L K p u) :
    ¬ SylowRadicalIrreducible h u ∧
      ∃ f : (componentStabilizerCoreAction L K u
        (h.stabilizer_normalizes_component s e hi)).range →* Equiv.Perm (Fin 3),
        Function.Surjective f := by
  obtain ⟨hs,hthree⟩ := h.sylow_reducible_and_symmetric_three a c s hnt e hi
  exact ⟨hs,h.stabilizer_core_symmetric_three s e hi hthree⟩


/-- The S₃ section survives the actual perfect central quotient and any
specified model equivalence. This is an action on Q/Z(Q), for Q=K/O₂(K). -/
theorem Context.stabilizer_model_symmetric_three (h : Context T L p)
    {u : G} (s : Selected T L u) {K : Subgroup G} (e : Escape T L p u K)
    (hi : ComponentNormalizerIrreducible L K p u)
    (hs : SymmetricThreeStabilizerQuotient L p u)
    {D : Type*} [Group D] (j : (XiQuotient K ⧸ center (XiQuotient K)) ≃* D) :
    ∃ f : ((MulAut.centralQuotientAction j).comp
        (componentStabilizerCoreAction L K u
          (h.stabilizer_normalizes_component s e hi))).range →* Equiv.Perm (Fin 3),
      Function.Surjective f := by
  let : IsQuasisimple (XiQuotient K) := e.quotient
  let ρ := componentStabilizerCoreAction L K u (h.stabilizer_normalizes_component s e hi)
  let τ := (MulAut.centralQuotientAction j).comp ρ
  have hk : τ.ker ≤ ρ.ker := by
    intro a ha
    apply MulAut.centralQuotientAction_injective j
    exact ha.trans (map_one (MulAut.centralQuotientAction j)).symm
  let f : τ.range →* ρ.range := τ.rangeRestrict.liftOfSurjective
    τ.rangeRestrict_surjective ⟨ρ.rangeRestrict,by
      simpa only [MonoidHom.ker_rangeRestrict] using hk⟩
  have he (a : (L ⊓ centralizer ({u} : Set G) : Subgroup G)) :
      f (τ.rangeRestrict a) = ρ.rangeRestrict a := by simp [f]
  have hf : Function.Surjective f := by
    intro y
    obtain ⟨a,rfl⟩ := ρ.rangeRestrict_surjective y
    exact ⟨τ.rangeRestrict a,he a⟩
  obtain ⟨g,hg⟩ := h.stabilizer_core_symmetric_three s e hi hs
  exact ⟨g.comp f,hg.comp hf⟩

end CFSG.Quasithin.Chapter13.Section01.SourceCentralizerStructure.Elimination
