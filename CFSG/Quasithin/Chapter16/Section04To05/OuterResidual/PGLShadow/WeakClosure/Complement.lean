module
public import CFSG.Quasithin.Chapter16.Section04To05.OuterResidual.PGLShadow.Action
public import CFSG.Quasithin.Chapter16.Section04To05.OuterResidual.Basic
public import Theory.GroupTheory.NormalizerInnerAutomorphisms
public import Theory.SpecificGroups.AlternatingSix.ShadowLocal.Basic

/-!
# The genuine R₀ complement in the PGL₂ shadow

The action is conjugation by the actual elements of R, transported to PSL₂.
Pulling back an index-two model subgroup and adjoining the marked element r
recovers R. Pair fixed-subgroup generation therefore feeds the previously
proved tight-embedding argument and gives R = ⟨r⟩.

For the prime case the inner preimage is proved to be R ∩ LC_G(L). For the
exceptional case the definition uses the natural permutation S₆ inside
Aut(A₆), transported through an actual PSL₂–A₆ equivalence. Its index is
proved, while the exclusion of r and pair generation remain intrinsic inputs.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
Lemma 16.4.6, printed p.1184, first paragraph. No weak-closure conclusion
is asserted by this module.
-/

@[expose] public section
namespace CFSG.Quasithin.Chapter16.Intersections.OuterResidual.PGLShadow.WeakClosure
open Subgroup GorensteinWalter
variable {G F : Type*} [Group G] [Finite G] [Field F]
variable {T : Sylow 2 G} {z g r : G} {L R : Subgroup G}

def modelAction (h : IntersectionSetup T z L g R) (e : L ≃* PSL2 F) :
    R →* MulAut (PSL2 F) :=
  (MulAut.congr e).toMonoidHom.comp
    (L.normalizerMonoidHom.comp (inclusion (h.le_sylow.trans h.sylow_normalizes)))

theorem modelAction_apply (h : IntersectionSetup T z L g R) (e : L ≃* PSL2 F)
    (a : R) : modelAction h e a = MulAut.congr e (involutionAction h a.property) := rfl

/-- Changing the Sylow choice or the setup proofs does not change the actual action. -/
theorem modelAction_setup_independent {S : Sylow 2 G} {w a : G}
    (h : IntersectionSetup T z L g R) (h' : IntersectionSetup S w L a R)
    (e : L ≃* PSL2 F) : modelAction h e = modelAction h' e := rfl

/-- The complement is the actual preimage inside R, embedded back into G. -/
def modelComplement (h : IntersectionSetup T z L g R) (e : L ≃* PSL2 F)
    (M : Subgroup (MulAut (PSL2 F))) : Subgroup G :=
  (M.comap (modelAction h e)).map R.subtype

theorem modelComplement_le (h : IntersectionSetup T z L g R) (e : L ≃* PSL2 F)
    (M : Subgroup (MulAut (PSL2 F))) : modelComplement h e M ≤ R := map_subtype_le _

theorem mem_modelComplement (h : IntersectionSetup T z L g R) (e : L ≃* PSL2 F)
    (M : Subgroup (MulAut (PSL2 F))) {x : G} :
    x ∈ modelComplement h e M ↔ ∃ hx : x ∈ R, modelAction h e ⟨x, hx⟩ ∈ M := by
  constructor
  · rintro ⟨a, ha, rfl⟩
    exact ⟨a.property, ha⟩
  · rintro ⟨hx, ha⟩
    exact ⟨⟨x, hx⟩, ha, rfl⟩

theorem sup_modelComplement_zpowers (h : IntersectionSetup T z L g R)
    (e : L ≃* PSL2 F) (M : Subgroup (MulAut (PSL2 F))) (hM : M.index = 2)
    (hr : r ∈ R) (hout : modelAction h e ⟨r, hr⟩ ∉ M) :
    R = modelComplement h e M ⊔ zpowers r := by
  apply le_antisymm
  · intro x hx
    by_cases hxm : modelAction h e ⟨x, hx⟩ ∈ M
    · exact mem_sup_left ((mem_modelComplement h e M).mpr ⟨hx, hxm⟩)
    · have hmul : modelAction h e (⟨x, hx⟩ * ⟨r, hr⟩⁻¹) ∈ M := by
        rw [map_mul, map_inv, M.mul_mem_iff_of_index_two hM, inv_mem_iff]
        exact iff_of_false hxm hout
      have hxmul : x * r⁻¹ ∈ modelComplement h e M :=
        (mem_modelComplement h e M).mpr ⟨R.mul_mem hx (R.inv_mem hr), hmul⟩
      simpa only [inv_mul_cancel_right] using
        (modelComplement h e M ⊔ zpowers r).mul_mem
          (mem_sup_left hxmul) (mem_sup_right (mem_zpowers r))
  · exact sup_le (modelComplement_le h e M) (zpowers_le.mpr hr)

theorem eq_zpowers_of_index_two_model (h : IntersectionSetup T z L g R)
    (hnot : ¬ L ≤ normalizer ((centralizer (L : Set G)).conjBy g : Set G))
    (hr : r ∈ R) (hr2 : orderOf r = 2) (e : L ≃* PSL2 F)
    (M : Subgroup (MulAut (PSL2 F))) (hM : M.index = 2)
    (hout : modelAction h e ⟨r, hr⟩ ∉ M)
    (hgen : ∀ b : MulAut (PSL2 F), b ∈ M → orderOf b = 2 →
      (MulAut.congr e (involutionAction h hr)).fixedSubgroup ⊔ b.fixedSubgroup = ⊤)
    (hfaith : R ⊓ centralizer (L : Set G) = ⊥) :
    R = zpowers r ∧ Nat.card R = 2 := by
  apply eq_zpowers_of_model_pair_generation h hnot hr hr2 e
    (modelComplement h e M) (modelComplement_le h e M)
    (sup_modelComplement_zpowers h e M hM hr hout)
  intro i hi hi2
  obtain ⟨hiR, him⟩ := (mem_modelComplement h e M).mp hi
  apply hgen _ him
  rw [modelAction_apply, (MulAut.congr e).orderOf_eq]
  exact involutionAction_order h hfaith hiR hi2

theorem modelComplement_inner (h : IntersectionSetup T z L g R) (e : L ≃* PSL2 F) :
    modelComplement h e (MulAut.conj : PSL2 F →* MulAut (PSL2 F)).range =
      R ⊓ (L ⊔ centralizer (L : Set G)) := by
  ext x
  rw [mem_modelComplement]
  constructor
  · rintro ⟨hx, y, hy⟩
    refine ⟨hx, ?_⟩
    have hi : L.normalizerMonoidHom ⟨x, h.sylow_normalizes (h.le_sylow hx)⟩ ∈
        (MulAut.conj : L →* MulAut L).range := by
      refine ⟨e.symm y, ?_⟩
      apply (MulAut.congr e).injective
      rw [MulAut.congr_conj, e.apply_symm_apply]
      exact hy
    change (⟨x, h.sylow_normalizes (h.le_sylow hx)⟩ : normalizer (L : Set G)) ∈
      ((MulAut.conj : L →* MulAut L).range.comap L.normalizerMonoidHom) at hi
    rwa [normalizerMonoidHom_comap_conj_range] at hi
  · rintro ⟨hx, hi⟩
    refine ⟨hx, ?_⟩
    have him : (⟨x, h.sylow_normalizes (h.le_sylow hx)⟩ : normalizer (L : Set G)) ∈
        ((MulAut.conj : L →* MulAut L).range.comap L.normalizerMonoidHom) := by
      rwa [normalizerMonoidHom_comap_conj_range]
    obtain ⟨y, hy⟩ := him
    refine ⟨e y, ?_⟩
    rw [← MulAut.congr_conj]
    exact congrArg (MulAut.congr e) hy

/-- The outer PGL matrix condition excludes the genuine inner subgroup. -/
theorem modelAction_not_inner [Finite F] (h : IntersectionSetup T z L g R)
    (hr : r ∈ R) (e : L ≃* PSL2 F)
    (hF : IsOddPrimePower (Nat.card F)) (hcard : 3 < Nat.card F)
    (hout : InducesOuterPGL h hr e) :
    modelAction h e ⟨r, hr⟩ ∉ (MulAut.conj : PSL2 F →* MulAut (PSL2 F)).range := by
  rintro ⟨y, hy⟩
  apply not_inner_of_inducesOuterPGL h hr e hF hcard hout
  refine ⟨e.symm y, ?_⟩
  apply (MulAut.congr e).injective
  rw [MulAut.congr_conj, e.apply_symm_apply]
  exact hy.symm

/-- The exceptional complement uses the natural S₆ inside the actual Aut(A₆). -/
def naturalSixComplement (h : IntersectionSetup T z L g R) (e : L ≃* PSL2 F)
    (e₆ : PSL2 F ≃* AlternatingSix.ShadowLocal.A6) : Subgroup G :=
  modelComplement h e (AlternatingSix.ShadowLocal.natural.comap
    (MulAut.congr e₆).toMonoidHom)

theorem mem_naturalSixComplement (h : IntersectionSetup T z L g R)
    (e : L ≃* PSL2 F) (e₆ : PSL2 F ≃* AlternatingSix.ShadowLocal.A6) {x : G} :
    x ∈ naturalSixComplement h e e₆ ↔ ∃ hx : x ∈ R,
      MulAut.congr e₆ (modelAction h e ⟨x, hx⟩) ∈ AlternatingSix.ShadowLocal.natural :=
  mem_modelComplement h e _

theorem naturalSix_index (e₆ : PSL2 F ≃* AlternatingSix.ShadowLocal.A6) :
    (AlternatingSix.ShadowLocal.natural.comap (MulAut.congr e₆).toMonoidHom).index = 2 := by
  rw [index_comap_of_surjective _ (MulAut.congr e₆).surjective]
  exact GLS3.Chapter5.naturalAlternatingAutomorphismSubgroup_index
end CFSG.Quasithin.Chapter16.Intersections.OuterResidual.PGLShadow.WeakClosure
