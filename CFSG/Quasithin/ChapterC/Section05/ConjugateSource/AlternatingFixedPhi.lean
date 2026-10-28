module
public import CFSG.Quasithin.ChapterC.Section05.ConjugateSource.AlternatingPhiNormalizer
public import CFSG.Quasithin.ChapterC.Section05.ConjugateSource.AlternatingFrattini
public import Theory.GroupTheory.TwoFixedLinesIrreducible
public import Theory.GroupTheory.CharacteristicCentralizerFusion

/-!
# The fixed Frattini subgroup in a pair of alternating-five blocks

For two commuting blocks permuted by the original Sylow subgroup, put
I = C_{Baum(S)}(K) and Φ = C_{Φ(I)}(N_S(K)). The opposite block module meets
Φ(I) nontrivially. The fixed-point theorem for two-groups then shows that
it meets Φ nontrivially. A block interchange cannot normalize Φ, because
that module meets the centralizer of its own block trivially. This identifies
N_S(Φ) with N_S(K). The original escaping conjugator preserves Φ by C.5.6.

Source: Aschbacher–Smith, proof of 2.4.25, printed pp.541–542.
-/

@[expose] public noncomputable section
open Subgroup
namespace CFSG.Quasithin.ChapterC.Section05.ConjugateSource
namespace AlternatingFixedPhi
variable {G : Type*} [Group G]

def I (S K : Subgroup G) : Subgroup G := ChapterB.baumann S ⊓ centralizer (K : Set G)
def P (S K : Subgroup G) : Subgroup G := (frattini (I S K)).map (I S K).subtype
def SI (S K : Subgroup G) : Subgroup G := S ⊓ normalizer (K : Set G)
def Phi (S K : Subgroup G) : Subgroup G := P S K ⊓ centralizer (SI S K : Set G)

theorem P_le_I (S K : Subgroup G) : P S K ≤ I S K := map_subtype_le _
theorem Phi_le_centralizer (S K : Subgroup G) : Phi S K ≤ centralizer (K : Set G) :=
  inf_le_left.trans ((P_le_I S K).trans inf_le_right)

variable [Finite G] {S K L : Subgroup G}
omit [Finite G] in
private theorem blocks_ne (h : AlternatingPairSetup S K L) : K ≠ L := by
  intro he
  have hdis := alternatingModule_disjoint_of_commuting K L h.block h.commute
  have hU : sourceModule K = ⊥ := le_bot_iff.mp (fun u hu =>
    hdis.le_bot ⟨hu,he ▸ (map_subtype_le _ hu)⟩)
  have hc := h.module_card
  rw [hU,card_bot] at hc
  omega

omit [Finite G] in
private theorem SI_normalizes_second
    (h₁ : AlternatingPairSetup S K L) (h₂ : AlternatingPairSetup S L K) :
    SI S K ≤ normalizer (L : Set G) := by
  intro s hs
  rcases h₂.permutes s hs.1 with he | he
  · exact mem_normalizer_iff_map_conj_eq.mpr he
  · have hk := mem_normalizer_iff_map_conj_eq.mp hs.2
    exact (blocks_ne h₁ ((map_injective (MulAut.conj s).injective) (hk.trans he.symm))).elim

private theorem SI_normalizes_P
    (h₁ : AlternatingPairSetup S K L) (h₂ : AlternatingPairSetup S L K) :
    SI S K ≤ normalizer (P S K : Set G) := by
  have he := h₁.phi_normalizer_eq_block_normalizer h₂
  change S ⊓ normalizer (P S K : Set G) = SI S K at he
  exact he.ge.trans inf_le_right

/-- The opposite block contributes a nontrivial fixed subgroup to the literal Φ. -/
theorem opposite_module_inf_Phi_ne_bot
    (h₁ : AlternatingPairSetup S K L) (h₂ : AlternatingPairSetup S L K) :
    sourceModule L ⊓ Phi S K ≠ ⊥ := by
  let W := sourceModule L ⊓ P S K
  have hWne : W ≠ ⊥ := by
    have hn := h₂.module_inf_block_frattini_ne_bot
    have hb : ChapterB.baumann S ⊓ L ≤ I S K := le_inf inf_le_left (inf_le_right.trans h₁.commute)
    have hp := frattini_image_le_of_le hb
      (h₁.twoGroup.to_le (show I S K ≤ S from inf_le_left.trans inf_le_left))
    exact fun he => hn (le_bot_iff.mp ((inf_le_inf_left _ hp).trans he.le))
  have hSW : SI S K ≤ normalizer (W : Set G) :=
    (le_inf ((SI_normalizes_second h₁ h₂).trans
      (normalizer_le_normalizer_characteristic_image L (blockU L)))
      (SI_normalizes_P h₁ h₂)).trans inf_normalizer_le_normalizer_inf
  have hWS : W ≤ S := inf_le_right.trans ((P_le_I S K).trans (inf_le_left.trans inf_le_left))
  have hn := inf_centralizer_ne_bot_of_pGroups (SI S K) W
    (h₁.twoGroup.to_le inf_le_left) (h₁.twoGroup.to_le hWS) hSW hWne
  simpa only [W,Phi,inf_assoc] using hn

/-- The source subgroup C_{Φ(I)}(S_I) is nontrivial. -/
theorem Phi_ne_bot
    (h₁ : AlternatingPairSetup S K L) (h₂ : AlternatingPairSetup S L K) : Phi S K ≠ ⊥ := by
  intro he
  exact opposite_module_inf_Phi_ne_bot h₁ h₂ (by rw [he,inf_bot_eq])

/-- Its stabilizer in the original Sylow subgroup is precisely the block stabilizer. -/
theorem normalizer_Phi_eq
    (h₁ : AlternatingPairSetup S K L) (h₂ : AlternatingPairSetup S L K) :
    S ⊓ normalizer (Phi S K : Set G) = SI S K := by
  apply le_antisymm
  · intro s hs
    refine ⟨hs.1,?_⟩
    rcases h₁.permutes s hs.1 with hk | hk
    · exact mem_normalizer_iff_map_conj_eq.mpr hk
    · have hp : Phi S K ≤ centralizer (L : Set G) := by
        have hh := map_mono (f := (MulAut.conj s).toMonoidHom) (Phi_le_centralizer S K)
        have hfix : (Phi S K).map (MulAut.conj s).toMonoidHom = Phi S K :=
          mem_normalizer_iff_map_conj_eq.mp hs.2
        rw [hfix] at hh
        have hc := map_centralizer_le_centralizer_image (K : Set G) (MulAut.conj s).toMonoidHom
        have him : (MulAut.conj s).toMonoidHom '' (K : Set G) = (L : Set G) := by
          exact congrArg (fun A : Subgroup G => (A : Set G)) hk
        rw [him] at hc
        exact hh.trans hc
      have hd := alternatingModule_disjoint_of_commuting L (centralizer (L : Set G)) h₂.block le_rfl
      have hb : sourceModule L ⊓ Phi S K = ⊥ :=
        le_bot_iff.mp ((inf_le_inf_left _ hp).trans hd.le_bot)
      exact (opposite_module_inf_Phi_ne_bot h₁ h₂ hb).elim
  · exact le_inf inf_le_left
      ((le_inf (SI_normalizes_P h₁ h₂)
        ((SI S K).le_normalizer.trans (normalizer_le_normalizer_centralizer (SI S K)))).trans
          inf_normalizer_le_normalizer_inf)

/-- The C.5.6 escaping conjugator normalizes the literal Φ used to define G_I. -/
theorem conjugator_normalizes_Phi
    (h₁ : AlternatingPairSetup S K L) (h₂ : AlternatingPairSetup S L K)
    (x : G) (hx : x ∈ normalizer (S : Set G))
    (hnc : ¬ (sourceModule K).map (MulAut.conj x⁻¹).toMonoidHom ≤
      centralizer (sourceModule K : Set G)) : x ∈ normalizer (Phi S K : Set G) := by
  have hxP : x ∈ normalizer (P S K : Set G) := by
    have hi : x⁻¹ ∈ normalizer (P S K : Set G) :=
      mem_normalizer_iff_map_conj_eq.mpr (h₁.frattini_invariant x hx hnc)
    simpa only [inv_inv] using (normalizer (P S K : Set G)).inv_mem hi
  have he := h₁.phi_normalizer_eq_block_normalizer h₂
  change S ⊓ normalizer (P S K : Set G) = SI S K at he
  have hxSI : x ∈ normalizer (SI S K : Set G) := by
    rw [←he]
    exact inf_normalizer_le_normalizer_inf ⟨hx,(normalizer (P S K : Set G)).le_normalizer hxP⟩
  exact inf_normalizer_le_normalizer_inf
    ⟨hxP,normalizer_le_normalizer_centralizer (SI S K) hxSI⟩

end AlternatingFixedPhi
end CFSG.Quasithin.ChapterC.Section05.ConjugateSource
