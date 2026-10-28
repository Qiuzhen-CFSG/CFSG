module

public import CFSG.Quasithin.ChapterE.Section01.ValuesEvenClassical.RankTwoUpper.LinearThree.InnerFamilies.LocalPair
public import CFSG.Quasithin.ChapterE.Section01.ValuesEvenClassical.RankTwoUpper.LinearThree.InnerFamilies.TauGeometry
public import CFSG.Quasithin.ChapterE.Section01.ValuesEvenClassical.RankTwoUpper.LinearThree.InnerFamilies.TauMembers
public import CFSG.Quasithin.Defs

/-!
# Assembly for large inner families in ambient PSL₃ extensions

If T preserves both locals, either a family member acts outside a local core
and supplies an E-member containing that local, or the whole weak closure is
inside that core and the local normalizes it. If T exchanges the locals, one
E-member supplied by a large inner actor gives both locals by conjugation.
The literal locals generate the socle, so both requested parabolics lie in
the E-generation subgroup. No Borel-normalizes-T assertion is used.

`parabolics_le_of_inner_sylow` proves the nonbinary case T ≤ L using the
actual local E-members, with no additional model calculation assumed.

The final theorem is conditional on three explicit model calculations:
permutation of the actual local pair, tau control for a large inner actor,
and E-membership of a local enlarged by tau when tau normalizes it. In the
last condition the intrinsic core, radical quotient, residual, and binary
E1 clauses are part of `IsEMemberAt`, not replaced by family tags. The
unconditional E.1.14 branch remains to be assembled after proving these
calculations under the source's simple-F*(G), SQTK, and G = LT hypotheses.

Source: Aschbacher--Smith E.1.1--6, pp.209--211, E.1.14(1), p.214,
and F.1.12(I)(1), pp.263--264.
-/

public section
open Subgroup Theory.GroupTheory Matrix.PSL3.LinearThree
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterE.ValuesEvenClassical.RankTwoUpper.LinearThree.InnerFamilies
variable {G F : Type*} [Group G] [Finite G] [Field F] [Finite F]

private theorem member_le_target {f : ℕ} (T : Subgroup G)
    {Ω : Set (Subgroup G)} {A H : Subgroup G} (hA : A ∈ Ω) (hAT : A ≤ T)
    (hH : IsEMemberAt f T A H) :
    H ≤ eFamilySubgroup f T Ω ⊔ normalizer (weakClosure T Ω : Set G) :=
  (show H ≤ eSubgroup f T A from le_sSup hH).trans
    ((le_iSup (fun B : {B : Subgroup G // B ∈ Ω ∧ B ≤ T} => eSubgroup f T B.1)
      ⟨A,hA,hAT⟩).trans le_sup_left)

private theorem local_le_target {f : ℕ} (T K Q : Subgroup G)
    (hQT : Q ≤ T) (hKQ : K ≤ normalizer (Q : Set G))
    (Ω : Set (Subgroup G)) (hΩ : IsElementaryFamily Ω)
    (hlarge : ∀ A ∈ Ω, A ≤ T → A ≠ ⊥ → f < Group.rank A)
    (hmember : ∀ A : Subgroup G, IsElementaryAbelian 2 A → A ≤ T →
      f < Group.rank A → ¬ A ≤ Q → ∃ H : Subgroup G, K ≤ H ∧ IsEMemberAt f T A H) :
    K ≤ eFamilySubgroup f T Ω ⊔ normalizer (weakClosure T Ω : Set G) := by
  classical
  by_cases hex : ∃ A ∈ Ω, A ≤ T ∧ ¬ A ≤ Q
  · obtain ⟨A,hA,hAT,hAQ⟩ := hex
    have hne : A ≠ ⊥ := fun h => hAQ (h ▸ bot_le)
    obtain ⟨H,hKH,hH⟩ := hmember A (hΩ.1 A hA) hAT (hlarge A hA hAT hne) hAQ
    exact hKH.trans (member_le_target T hA hAT hH)
  · have hW : weakClosure T Ω ≤ Q := by
      apply sSup_le
      rintro A ⟨hA,hAT⟩
      by_contra hAQ
      exact hex ⟨A,hA,hAT,hAQ⟩
    have he : weakClosure T Ω = weakClosure Q Ω := le_antisymm
      (SubgroupFamily.span_le_span_of_span_le hW) (SubgroupFamily.span_mono Ω hQT)
    rw [he]
    exact (hKQ.trans (RankOneUpper.normalizer_le_weakClosure_normalizer Q hΩ)).trans
      le_sup_right

omit [Finite G] in
private theorem conjugate_le {K M : Subgroup G} (hKM : K ≤ M) {g : G} (hg : g ∈ M) :
    K.map (MulAut.conj g).toMonoidHom ≤ M := by
  rintro _ ⟨x,hx,rfl⟩
  exact M.mul_mem (M.mul_mem hg (hKM hx)) (M.inv_mem hg)

omit [Finite G] in
private theorem parabolics_le_of_locals (L : Subgroup G) (e : L ≃* PSL(3,F))
    (M : Subgroup G) (h : ∀ b, localImage L e b ≤ M) :
    (pointParabolic F).map (linearThreeEmbedding L e) ≤ M ∧
      (lineParabolic F).map (linearThreeEmbedding L e) ≤ M := by
  have hL : L ≤ M := by
    rw [← localImages_sup L e]
    exact sup_le (h true) (h false)
  have hmap (P : Subgroup PSL(3,F)) : P.map (linearThreeEmbedding L e) ≤ L :=
    (P.map_le_range _).trans_eq (linearThreeEmbedding_range L e)
  exact ⟨(hmap _).trans hL, (hmap _).trans hL⟩

/-- The nonbinary branch with no outer Sylow actor needs no extra model input.
This applies the actual ambient local E-members and the weak-closure dichotomy. -/
theorem parabolics_le_of_inner_sylow [CharP F 2]
    (L : Subgroup G) (e : L ≃* PSL(3,F)) (T : Sylow 2 G)
    {f : ℕ} (hf : 0 < f) (hF : Nat.card F = 2^f) (hcard : 4 ≤ Nat.card F)
    (halign : (unipotent F).map (linearThreeEmbedding L e) ≤ (T : Subgroup G))
    (hTL : (T : Subgroup G) ≤ L)
    (Ω : Set (Subgroup G)) (hΩ : IsElementaryFamily Ω)
    (hlarge : ∀ A ∈ Ω, A ≤ (T : Subgroup G) → A ≠ ⊥ → f < Group.rank A) :
    let M := eFamilySubgroup f (T : Subgroup G) Ω ⊔
      normalizer (weakClosure (T : Subgroup G) Ω : Set G)
    (pointParabolic F).map (linearThreeEmbedding L e) ≤ M ∧
      (lineParabolic F).map (linearThreeEmbedding L e) ≤ M := by
  apply parabolics_le_of_locals L e
  intro b
  have hTK : (T : Subgroup G) ≤ localImage L e b := by
    intro x hx
    have hxL := hTL hx
    rw [← linearThreeEmbedding_range L e] at hxL
    obtain ⟨y,rfl⟩ := hxL
    have hy : y ∈ unipotent F := by
      rw [← sylow_comap_eq L e T hf hF halign]
      exact hx
    exact mem_map_of_mem _ (unipotent_le_localModel b hy)
  apply local_le_target (T : Subgroup G) (localImage L e b) (coreImage L e b)
    (coreImage_le_sylow L e T hf hF halign b)
    (localImage_le_coreImage_normalizer L e b) Ω hΩ hlarge
  intro A hA hAT _ hAQ
  exact ⟨localImage L e b, le_rfl,
    localImage_isEMemberAt L e T hf hF hcard halign b A hA hAT (hAT.trans hTK)
      ((tau_le _ _).trans hTK) hAQ⟩

/-- Conditional final assembly for the requested inner-family branch.
The two independent model inputs are local geometry (pair permutation and
inner-actor tau control) and the actual tau-extension E-member calculation. -/
theorem parabolics_le_of_local_calculations
    (L : Subgroup G) (e : L ≃* PSL(3,F)) (T : Sylow 2 G)
    {f : ℕ} (hf : 0 < f) (hF : Nat.card F = 2^f)
    (halign : (unipotent F).map (linearThreeEmbedding L e) ≤ (T : Subgroup G))
    (hpair : ∀ g ∈ (T : Subgroup G),
      (∀ b, (localImage L e b).map (MulAut.conj g).toMonoidHom = localImage L e b) ∨
      (∀ b, (localImage L e b).map (MulAut.conj g).toMonoidHom = localImage L e (!b)))
    (hactor : ∀ A : Subgroup G, IsElementaryAbelian 2 A → A ≤ (T : Subgroup G) →
      A ≤ L → f < Group.rank A → ∃ b : Bool,
        tau (T : Subgroup G) A ≤ localImage L e b ∧ ¬ A ≤ coreImage L e b)
    (hmember : ∀ (b : Bool) (A : Subgroup G),
      IsElementaryAbelian 2 A → A ≤ (T : Subgroup G) → f < Group.rank A →
      ¬ A ≤ coreImage L e b →
      tau (T : Subgroup G) A ≤ normalizer (localImage L e b : Set G) →
      IsEMemberAt f (T : Subgroup G) A (localImage L e b ⊔ tau (T : Subgroup G) A))
    (Ω : Set (Subgroup G)) (hΩ : IsElementaryFamily Ω)
    (hex : ∃ A ∈ Ω, A ≤ (T : Subgroup G) ∧ A ≠ ⊥ ∧ A ≤ L)
    (hlarge : ∀ A ∈ Ω, A ≤ (T : Subgroup G) → A ≠ ⊥ → f < Group.rank A) :
    let M := eFamilySubgroup f (T : Subgroup G) Ω ⊔
      normalizer (weakClosure (T : Subgroup G) Ω : Set G)
    (pointParabolic F).map (linearThreeEmbedding L e) ≤ M ∧
      (lineParabolic F).map (linearThreeEmbedding L e) ≤ M := by
  classical
  let M := eFamilySubgroup f (T : Subgroup G) Ω ⊔
    normalizer (weakClosure (T : Subgroup G) Ω : Set G)
  have hT : (T : Subgroup G) ≤ M :=
    (Subgroup.le_normalizer.trans
      (RankOneUpper.normalizer_le_weakClosure_normalizer (T : Subgroup G) hΩ)).trans
      le_sup_right
  have hlocals : ∀ b, localImage L e b ≤ M := by
    by_cases hfix : ∀ g ∈ (T : Subgroup G), ∀ b,
        (localImage L e b).map (MulAut.conj g).toMonoidHom = localImage L e b
    · intro b
      apply local_le_target (T : Subgroup G) (localImage L e b) (coreImage L e b)
        (coreImage_le_sylow L e T hf hF halign b)
        (localImage_le_coreImage_normalizer L e b) Ω hΩ hlarge
      intro A hA hAT hr hAQ
      refine ⟨localImage L e b ⊔ tau (T : Subgroup G) A, le_sup_left,
        hmember b A hA hAT hr hAQ ?_⟩
      apply (tau_le _ _).trans
      intro g hg
      exact mem_normalizer_iff_map_conj_eq.mpr (hfix g hg b)
    · push Not at hfix
      obtain ⟨g,hg,b₀,hb₀⟩ := hfix
      have hswap := (hpair g hg).resolve_left (fun h => hb₀ (h b₀))
      obtain ⟨A,hA,hAT,hne,hAL⟩ := hex
      obtain ⟨b,htau,hAQ⟩ := hactor A (hΩ.1 A hA) hAT hAL (hlarge A hA hAT hne)
      have hmem := hmember b A (hΩ.1 A hA) hAT (hlarge A hA hAT hne) hAQ
        (htau.trans Subgroup.le_normalizer)
      rw [sup_eq_left.mpr htau] at hmem
      have hb : localImage L e b ≤ M := member_le_target _ hA hAT hmem
      have hb' : localImage L e (!b) ≤ M := by
        rw [← hswap b]
        exact conjugate_le hb (hT hg)
      intro c
      cases b <;> cases c <;> assumption
  exact parabolics_le_of_locals L e M hlocals

/-! The preceding theorem isolates the three model calculations used by the
source argument.  For the actual simple generalized-Fitting setup they are
all available from the literal PSL₃ action: the aligned Sylow permutes the
point and line locals, a large inner family member supplies the selected tau,
and the normalized tau join is an E-member.  This is the source-facing
assembly of E.1.14(1)(1); the outer-family branch and the final E-generation
assembly remain with their owners. -/
theorem parabolics_le_of_source {K : CFSG.Quasithin.GroupClass}
    (_hG : CFSG.Quasithin.IsSQTK K G)
    [IsSimpleGroup (generalizedFitting G)]
    (e : generalizedFitting G ≃* PSL(3,F)) (T : Sylow 2 G)
    {f : ℕ} (hf : 0 < f) (hF : Nat.card F = 2^f)
    (hgen : generalizedFitting G ⊔ (T : Subgroup G) = ⊤)
    (halign : (unipotent F).map
      (linearThreeEmbedding (generalizedFitting G) e) ≤ (T : Subgroup G))
    (Ω : Set (Subgroup G)) (hΩ : IsElementaryFamily Ω)
    (hex : ∃ A ∈ Ω, A ≤ (T : Subgroup G) ∧ A ≠ ⊥ ∧
      A ≤ generalizedFitting G)
    (hlarge : ∀ A ∈ Ω, A ≤ (T : Subgroup G) → A ≠ ⊥ →
      f < Group.rank A) :
    let M := eFamilySubgroup f (T : Subgroup G) Ω ⊔
      normalizer (weakClosure (T : Subgroup G) Ω : Set G)
    (pointParabolic F).map
        (linearThreeEmbedding (generalizedFitting G) e) ≤ M ∧
      (lineParabolic F).map
        (linearThreeEmbedding (generalizedFitting G) e) ≤ M := by
  let L := generalizedFitting G
  let _ : L.Normal := generalizedFitting_normal
  refine parabolics_le_of_local_calculations L e T hf hF halign ?_ ?_ ?_ Ω hΩ hex hlarge
  · intro g hg
    exact local_pair_action L e T hf hF halign g hg
  · intro A hA hAT hAL hr
    exact large_actor_tau e T hgen hf hF halign A hA hAT hAL hr
  · intro b A hA hAT hr hne hn
    exact tauJoin_isEMemberAt e T hf hF halign b A hA hAT hne hn

end CFSG.Quasithin.ChapterE.ValuesEvenClassical.RankTwoUpper.LinearThree.InnerFamilies
