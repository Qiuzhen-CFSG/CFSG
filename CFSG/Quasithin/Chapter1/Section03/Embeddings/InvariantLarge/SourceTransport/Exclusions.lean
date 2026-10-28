module
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantLarge.SourceTransport.Action

/-!
# Irreducibility exclusions in the faithful image

The transported intrinsic action rules out cyclic complements, two cyclic
factors with the first normalizer-invariant, power actions, and power actions
together with one involution. The proofs work on the literal Frattini quotient.
A normalized cyclic factor lies in Φ(B); its cyclic supplement would then
generate all of B. For a single involution, irreducibility makes its fixed
space trivial or total, reducing its action to inversion or identity.

These are the action exclusions applied to A.3.15(3),(5) in
Aschbacher–Smith 1.3.4, printed pp.510–511.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter1.XiEmbedding.InvariantLarge.SourceTransport
private theorem cyclic_of_irreducible_power_action
    {S V : Type*} [Group S] [Group V] (f : S →* MulAut V)
    (hirr : ∀ A : Subgroup V,
      (∀ s : S, ∀ a ∈ A, f s a ∈ A) → A = ⊥ ∨ A = ⊤)
    (hpower : ∀ s v, f s v ∈ zpowers v) : IsCyclic V := by
  by_cases hV : Subsingleton V
  · let _ := hV
    infer_instance
  · let _ : Nontrivial V := not_subsingleton_iff_nontrivial.mp hV
    obtain ⟨v, hv⟩ := exists_ne (1 : V)
    have hstable : ∀ s : S, ∀ a ∈ zpowers v, f s a ∈ zpowers v :=
      fun s a ha => (zpowers_le.mpr ha) (hpower s a)
    rcases hirr (zpowers v) hstable with hb | ht
    · exact False.elim (hv (Subgroup.mem_bot.mp (hb ▸ mem_zpowers v)))
    · exact isCyclic_iff_exists_zpowers_eq_top.mpr ⟨v, ht⟩

private theorem cyclic_of_irreducible_power_involution_action
    {S V : Type*} [Group S] [Group V] [IsMulCommutative V]
    (f : S →* MulAut V) (g : MulAut V) (hg : g ^ 2 = 1)
    (hirr : ∀ A : Subgroup V,
      (∀ s : S, ∀ a ∈ A, f s a ∈ A) → A = ⊥ ∨ A = ⊤)
    (hpower : ∀ s v, f s v ∈ zpowers v ∨ f s v ∈ zpowers (g v)) :
    IsCyclic V := by
  let C := g.toMonoidHom.eqLocus (MonoidHom.id V)
  have hC : ∀ s : S, ∀ a ∈ C, f s a ∈ C := by
    intro s a ha
    rcases hpower s a with hp | hp
    · exact (zpowers_le.mpr ha) hp
    · have hga : g a = a := ha
      rw [hga] at hp
      exact (zpowers_le.mpr ha) hp
  have hsign : (∀ v, g v = v) ∨ (∀ v, g v = v⁻¹) := by
    rcases hirr C hC with hb | ht
    · right
      intro v
      have hv : g v * v ∈ C := by
        change g (g v * v) = g v * v
        have hh := DFunLike.congr_fun hg v
        change g (g v) = v at hh
        rw [map_mul, hh, mul_comm]
      exact mul_eq_one_iff_eq_inv.mp (Subgroup.mem_bot.mp (hb ▸ hv))
    · exact Or.inl (fun v => show v ∈ C from ht.symm ▸ mem_top v)
  apply cyclic_of_irreducible_power_action f hirr
  intro s v
  rcases hpower s v with hp | hp
  · exact hp
  · rcases hsign with he | he
    · simpa only [he] using hp
    · rw [he] at hp
      exact (zpowers_le.mpr ((zpowers v).inv_mem (mem_zpowers v))) hp


variable {J : Type*} [Group J] [Finite J] {p : ℕ} [Fact p.Prime]
variable {S B : Subgroup J}

theorem PairAction.not_power (h : PairAction p S B) :
    ¬ ∀ s v, frattiniConjugationAction (S ⊓ normalizer B) B inf_le_right s v ∈ zpowers v := by
  intro hp
  exact OddInvolutionFrattini.noncyclic_frattini_quotient h.oddComplement.not_isCyclic
    (cyclic_of_irreducible_power_action _ h.irreducible hp)

theorem PairAction.not_power_involution (h : PairAction p S B)
    (g : MulAut (B ⧸ frattini B)) (hg : g ^ 2 = 1) :
    ¬ ∀ s v, frattiniConjugationAction (S ⊓ normalizer B) B inf_le_right s v ∈ zpowers v ∨
      frattiniConjugationAction (S ⊓ normalizer B) B inf_le_right s v ∈ zpowers (g v) := by
  let : Fact (IsPGroup p B) := ⟨h.oddComplement.isPGroup⟩
  let : IsElementaryAbelian p (B ⧸ frattini B) := isElementaryAbelian_quotient_frattini
  intro hp
  exact OddInvolutionFrattini.noncyclic_frattini_quotient h.oddComplement.not_isCyclic
    (cyclic_of_irreducible_power_involution_action _ g hg h.irreducible hp)

theorem PairAction.not_cyclic_factorization (h : PairAction p S B)
    (A C : Subgroup B) [IsCyclic A] [IsCyclic C] (hgen : A ⊔ C = ⊤)
    (hn : S ⊓ normalizer B ≤ normalizer (A.map B.subtype)) : False := by
  let q := QuotientGroup.mk' (frattini B)
  have hinv : ∀ s : (S ⊓ normalizer B : Subgroup J), ∀ a ∈ A.map q,
      frattiniConjugationAction _ _ inf_le_right s a ∈ A.map q := by
    intro s a ha
    obtain ⟨b, hb, rfl⟩ := ha
    let _ := conjMulDistribMulActionOfLeNormalizer (S ⊓ normalizer B) B inf_le_right
    refine ⟨MulDistribMulAction.toMulAut (S ⊓ normalizer B : Subgroup J) B s b, ?_, ?_⟩
    · have hm := (mem_normalizer_iff.mp (hn s.property) (b : J)).mp
        (mem_map_of_mem B.subtype hb)
      obtain ⟨c, hc, he⟩ := hm
      have he' : c = MulDistribMulAction.toMulAut (S ⊓ normalizer B : Subgroup J) B s b :=
        Subtype.ext he
      exact he' ▸ hc
    · exact (quotientAut_apply_mk _ _ _).symm
  have hAF : A ≤ frattini B := by
    rcases h.irreducible (A.map q) hinv with hb | ht
    · simpa only [Subgroup.map_eq_bot_iff, q, QuotientGroup.ker_mk'] using hb
    · have he : A = ⊤ := frattini_nongenerating (by
        have hh := congrArg (Subgroup.comap q) ht
        simpa only [comap_map_eq, q, QuotientGroup.ker_mk', comap_top] using hh)
      have hi : IsCyclic (⊤ : Subgroup B) := he ▸ inferInstance
      let _ := hi
      exact (h.oddComplement.not_isCyclic
        (isCyclic_of_surjective topEquiv.toMonoidHom topEquiv.surjective)).elim
  have hC : C = ⊤ := frattini_nongenerating (by
    apply top_unique
    rw [← hgen]
    exact sup_le (hAF.trans le_sup_right) le_sup_left)
  have hc : IsCyclic (⊤ : Subgroup B) := hC ▸ inferInstance
  let _ := hc
  exact h.oddComplement.not_isCyclic
    (isCyclic_of_surjective topEquiv.toMonoidHom topEquiv.surjective)

end CFSG.Quasithin.Chapter1.XiEmbedding.InvariantLarge.SourceTransport
