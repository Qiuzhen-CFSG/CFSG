module
public import CFSG.Quasithin.Chapter5.Section03TrialitySource.NativeLift
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalTrialityMaximal
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalNormalizerAction

/-!
# The faithful triality action of the whole common normalizer

Conjugation preserves the source parabolics and their entire overlap. The
normalizer-pair centralizer theorem makes this action faithful. Transport
through the given comparison and unique native lifting then retain the
original endpoint maps and exactly the full Borel as inner preimage.

Source: Aschbacher–Smith 5.3.1–2, pp.658–659, and F.4.3, p.274.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
open _root_.Triality.Standard _root_.Triality.Standard.Parabolics
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
open Chapter5.Section03TrialitySource
open ChapterF.SourceCompletion.TrialityNonbinary
variable {G : Type*} [Group G]

private theorem normalizes_source_parabolic
    {N S : Subgroup G} {J : Fin 2 → Subgroup G}
    (hNS : N ≤ normalizer (S : Set G))
    (hNJ : ∀ i, N ≤ normalizer (J i : Set G)) (i : Fin 2) :
    N ≤ normalizer (ChapterF.Source.parabolic J S i : Set G) := by
  have hb (j : Fin 2) : N ≤ normalizer (ChapterF.Source.borel (J j) S : Set G) := by
    have hi := (le_inf hNS (hNJ j)).trans inf_normalizer_le_normalizer_inf
    exact (le_inf (hNJ j) (hi.trans (normalizer _).le_normalizer)).trans
      inf_normalizer_le_normalizer_inf
  exact (le_inf ((le_inf (hNJ i) hNS).trans (normalizer_inf_normalizer_le_normalizer_sup _ _))
    (hb (ChapterF.Source.other i))).trans (normalizer_inf_normalizer_le_normalizer_sup _ _)

private def conjugationPair (P Q N : Subgroup G)
    (hP : N ≤ normalizer (P : Set G)) (hQ : N ≤ normalizer (Q : Set G)) :
    N →* RankTwoAmalgam.Iso
      (RankTwoAmalgam.ofSubgroups P (P ⊓ Q) Q inf_le_left inf_le_right)
      (RankTwoAmalgam.ofSubgroups P (P ⊓ Q) Q inf_le_left inf_le_right) where
  toFun g :=
    { left := P.normalizerMonoidHom (inclusion hP g)
      middle := (P ⊓ Q).normalizerMonoidHom
        (inclusion ((le_inf hP hQ).trans inf_normalizer_le_normalizer_inf) g)
      right := Q.normalizerMonoidHom (inclusion hQ g)
      left_commutes _ := Subtype.ext rfl
      right_commutes _ := Subtype.ext rfl }
  map_one' := by
    apply RankTwoAmalgam.Iso.ext <;> ext x <;> simp
  map_mul' a b := by
    apply RankTwoAmalgam.Iso.ext <;> ext x <;> simp [mul_assoc]

variable [Finite G]

/-- The full common normalizer acts faithfully on the exact pure source amalgam. -/
theorem Preparation.triality_source_middle_action
    {T : Sylow 2 G} {L W H A B : Subgroup G} {n : ℕ}
    (d : Preparation T L H A B (residual H))
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hp : Group.IsPerfect (residual H))
    (m : ℕ) (hm : 0 < m)
    (e : RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H))
      (ChapterF.SourceCompletion.TrialityNonbinary.nativeAmalgam m hm).reverse) :
    ∃ ρ : (normalizer (L : Set G) ⊓ normalizer (residual H : Set G) : Subgroup G) →*
      RankTwoAmalgam.Iso (sourceParabolicAmalgam ![L,residual H] (sourceS L H))
        (sourceParabolicAmalgam ![L,residual H] (sourceS L H)),
      Function.Injective ρ ∧
      (∀ g x, ((ρ g).left x).val = g.val * x.val * g.val⁻¹) ∧
      (∀ g x, ((ρ g).middle x).val = g.val * x.val * g.val⁻¹) ∧
      (∀ g x, ((ρ g).right x).val = g.val * x.val * g.val⁻¹) := by
  let N := normalizer (L : Set G) ⊓ normalizer (residual H : Set G)
  let P := ChapterF.Source.parabolic ![L,residual H] (sourceS L H)
  have hl := d.triality_normalizer_local_conditions h hH hp m hm (Or.inr ⟨e⟩)
  have hsL : sourceS L H ≤ L := (d.triality_sourceS_le_factors h hH.1.1.2 hp m hm (Or.inr ⟨e⟩)) 0
  have hs : sourceS L H = (T : Subgroup G) ⊓ L :=
    (inf_eq_left.mpr hsL).symm.trans d.left_intersection
  have hNS : N ≤ normalizer (sourceS L H : Set G) := by
    rw [hs, hl.normalizer_eq_middle]
    exact le_rfl
  have hNP (i : Fin 2) : N ≤ normalizer (P i : Set G) := by
    apply normalizes_source_parabolic hNS
    intro j
    fin_cases j
    · exact inf_le_left
    · exact inf_le_right
  let ρ := conjugationPair (P 0) (P 1) N (hNP 0) (hNP 1)
  refine ⟨ρ, ?_, fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl⟩
  apply ρ.ker_eq_bot_iff.mp
  apply bot_unique
  intro g hg
  have heq : ρ g = 1 := hg
  have hcP : g.val ∈ centralizer (P 0 : Set G) ∧ g.val ∈ centralizer (P 1 : Set G) := by
    constructor
    · intro x hx
      have hh := congrArg (fun a => ((a.left ⟨x,hx⟩ : P 0) : G)) heq
      change g.val*x*g.val⁻¹=x at hh
      exact (mul_inv_eq_iff_eq_mul.mp hh).symm
    · intro x hx
      have hh := congrArg (fun a => ((a.right ⟨x,hx⟩ : P 1) : G)) heq
      change g.val*x*g.val⁻¹=x at hh
      exact (mul_inv_eq_iff_eq_mul.mp hh).symm
  have hLP : L ≤ P 0 := le_sup_left.trans le_sup_left
  have hKP : residual H ≤ P 1 := le_sup_left.trans le_sup_left
  have hc : L ⊔ residual H ≤ centralizer ({g.val} : Set G) := by
    refine sup_le ?_ ?_
    · intro x hx
      exact mem_centralizer_singleton_iff.mpr (hcP.1 x (hLP hx))
    · intro x hx
      exact mem_centralizer_singleton_iff.mpr (hcP.2 x (hKP hx))
  have hgC : g.val ∈ centralizer ((L ⊔ residual H : Subgroup G) : Set G) := by
    intro x hx
    exact (mem_centralizer_singleton_iff.mp (hc hx))
  rw [normalizer_pair_centralizer_eq_bot hl] at hgC
  exact Subtype.ext (mem_bot.mp hgC)

/-- The action uses the supplied comparison on all three groups. -/
structure TrialityMarkedMiddleAction (L K S : Subgroup G) (m : ℕ) (hm : 0 < m)
    (e : RankTwoAmalgam.Iso (sourceParabolicAmalgam ![L,K] S)
      (nativeAmalgam m hm).reverse) where
  middle_le : (ChapterF.Source.parabolic ![L,K] S 0 ⊓
    ChapterF.Source.parabolic ![L,K] S 1 : Subgroup G) ≤
      normalizer (L : Set G) ⊓ normalizer (K : Set G)
  action : (normalizer (L : Set G) ⊓ normalizer (K : Set G) : Subgroup G) →*
    RankTwoAmalgam.Iso (nativeAmalgam m hm).reverse (nativeAmalgam m hm).reverse
  faithful : Function.Injective action
  left_conjugation : ∀ g x,
    (e.left.symm ((action g).left x)).val =
      g.val * (e.left.symm x).val * g.val⁻¹
  middle_conjugation : ∀ g x,
    (e.middle.symm ((action g).middle x)).val =
      g.val * (e.middle.symm x).val * g.val⁻¹
  right_conjugation : ∀ g x,
    (e.right.symm ((action g).right x)).val =
      g.val * (e.right.symm x).val * g.val⁻¹

/-- The actual source action, transported through the original comparison. -/
theorem Preparation.triality_marked_middle_action
    {T : Sylow 2 G} {L W H A B : Subgroup G} {n : ℕ}
    (d : Preparation T L H A B (residual H))
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hp : Group.IsPerfect (residual H)) (m : ℕ) (hm : 0 < m)
    (e : RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H))
      (nativeAmalgam m hm).reverse) :
    Nonempty (TrialityMarkedMiddleAction L (residual H) (sourceS L H) m hm e) := by
  obtain ⟨ρ,hf,hl,hm',hr⟩ := d.triality_source_middle_action h hH hp m hm e
  have hf11 := d.hypothesisF11 h hH.1.1.2
  have hC : (ChapterF.Source.parabolic ![L,residual H] (sourceS L H) 0 ⊓
      ChapterF.Source.parabolic ![L,residual H] (sourceS L H) 1 : Subgroup G) ≤
        normalizer (L : Set G) ⊓ normalizer (residual H : Set G) := by
    rw [ChapterF.Source.lemma_F_1_3_6 hf11]
    exact le_inf (hf11.commonBorel_normalizes_local 0) (hf11.commonBorel_normalizes_local 1)
  let σ := (RankTwoAmalgam.automorphismConjEquiv e).toMonoidHom.comp ρ
  refine ⟨⟨hC, σ, (RankTwoAmalgam.automorphismConjEquiv e).injective.comp hf, ?_, ?_, ?_⟩⟩
  · intro g x
    change (e.left.symm (e.left ((ρ g).left (e.left.symm x)))).val = _
    rw [e.left.symm_apply_apply]
    exact hl g _
  · intro g x
    change (e.middle.symm (e.middle ((ρ g).middle (e.middle.symm x)))).val = _
    rw [e.middle.symm_apply_apply]
    exact hm' g _
  · intro g x
    change (e.right.symm (e.right ((ρ g).right (e.right.symm x)))).val = _
    rw [e.right.symm_apply_apply]
    exact hr g _

namespace TrialityMarkedMiddleAction
variable {L K S : Subgroup G} {m : ℕ} {hm : 0 < m}
variable {e : RankTwoAmalgam.Iso (sourceParabolicAmalgam ![L,K] S)
  (nativeAmalgam m hm).reverse}

omit [Finite G] in
/-- On the entire pure common Borel, the transported action is the native
inner action, including the Cartan elements. -/
theorem native_inner_action
    (a : TrialityMarkedMiddleAction L K S m hm e)
    (b : (ChapterF.Source.parabolic ![L,K] S 0 ⊓
      ChapterF.Source.parabolic ![L,K] S 1 : Subgroup G)) :
    a.action (inclusion a.middle_le b) =
      reverseRestriction
        (innerBorel (e.middle b)) := by
  apply RankTwoAmalgam.Iso.ext
  · apply MulEquiv.ext
    intro x
    have hx : e.left.symm ((a.action (inclusion a.middle_le b)).left x) =
        (sourceParabolicAmalgam ![L,K] S).left b * e.left.symm x *
          ((sourceParabolicAmalgam ![L,K] S).left b)⁻¹ :=
      Subtype.ext (a.left_conjugation (inclusion a.middle_le b) x)
    have hh := congrArg e.left hx
    simp only [map_mul, map_inv, e.left_commutes,
      e.left.apply_symm_apply] at hh
    apply Subtype.ext
    change ((a.action (inclusion a.middle_le b)).left x).val =
      (e.middle b).val * x.val * (e.middle b).val⁻¹
    exact congrArg Subtype.val hh
  · apply MulEquiv.ext
    intro x
    have hx : e.middle.symm ((a.action (inclusion a.middle_le b)).middle x) =
        b * e.middle.symm x * b⁻¹ :=
      Subtype.ext (a.middle_conjugation (inclusion a.middle_le b) x)
    have hh := congrArg e.middle hx
    simp only [map_mul, map_inv, e.middle.apply_symm_apply] at hh
    apply Subtype.ext
    change ((a.action (inclusion a.middle_le b)).middle x).val =
      (e.middle b).val * x.val * (e.middle b).val⁻¹
    exact congrArg Subtype.val hh
  · apply MulEquiv.ext
    intro x
    have hx : e.right.symm ((a.action (inclusion a.middle_le b)).right x) =
        (sourceParabolicAmalgam ![L,K] S).right b * e.right.symm x *
          ((sourceParabolicAmalgam ![L,K] S).right b)⁻¹ :=
      Subtype.ext (a.right_conjugation (inclusion a.middle_le b) x)
    have hh := congrArg e.right hx
    simp only [map_mul, map_inv, e.right_commutes,
      e.right.apply_symm_apply] at hh
    apply Subtype.ext
    change ((a.action (inclusion a.middle_le b)).right x).val =
      (e.middle b).val * x.val * (e.middle b).val⁻¹
    exact congrArg Subtype.val hh

omit [Finite G] in
/-- No further element of the full common normalizer induces a Borel-inner
marked action. This preserves the whole pure overlap exactly. -/
theorem native_inner_action_iff
    (a : TrialityMarkedMiddleAction L K S m hm e)
    (g : (normalizer (L : Set G) ⊓ normalizer (K : Set G) : Subgroup G)) :
    a.action g ∈ (reverseRestriction.comp
      (innerBorel (m := m) (hm := hm))).range ↔
      g.val ∈ (ChapterF.Source.parabolic ![L,K] S 0 ⊓
        ChapterF.Source.parabolic ![L,K] S 1 : Subgroup G) := by
  constructor
  · rintro ⟨c, hc⟩
    let b := e.middle.symm c
    have he : a.action (inclusion a.middle_le b) = a.action g := by
      rw [a.native_inner_action]
      dsimp only [b]
      rw [e.middle.apply_symm_apply]
      exact hc
    have hv := congrArg Subtype.val (a.faithful he)
    exact hv ▸ b.property
  · intro hg
    let b : (ChapterF.Source.parabolic ![L,K] S 0 ⊓
      ChapterF.Source.parabolic ![L,K] S 1 : Subgroup G) := ⟨g.val,hg⟩
    exact ⟨e.middle b, (a.native_inner_action b).symm⟩

omit [Finite G] in
/-- Unique simultaneous lifting gives a faithful native homomorphism whose
inner preimage is exactly the entire source overlap. -/
theorem native_lift (hm2 : 1 < m)
    (a : TrialityMarkedMiddleAction L K S m hm e) :
    ∃ σ : (normalizer (L : Set G) ⊓ normalizer (K : Set G) : Subgroup G) →*
        flagAutomorphisms m hm,
      Function.Injective σ ∧ reverseRestriction.comp σ = a.action ∧
      ∀ g, (σ g).val ∈ (MulAut.conj : BinaryCarrier m hm →* MulAut (BinaryCarrier m hm)).range ↔
        g.val ∈ (ChapterF.Source.parabolic ![L,K] S 0 ⊓
          ChapterF.Source.parabolic ![L,K] S 1 : Subgroup G) := by
  obtain ⟨σ, hσ, _⟩ := existsUnique_reverse_lift a.action
    (fun g => native_amalgam_automorphism_surjective_reverse hm2 (a.action g))
  have hs (g) : reverseRestriction (σ g) = a.action g :=
    congrArg (fun f => f g) hσ
  refine ⟨σ, ?_, hσ, ?_⟩
  · intro x y hxy
    apply a.faithful
    exact (hs x).symm.trans ((congrArg reverseRestriction hxy).trans (hs y))
  · intro g
    constructor
    · rintro ⟨x, hx⟩
      have hb : x ∈ borel (binaryParameters m hm) := (inner_flag_iff x).mp (by
        rw [hx]
        exact (σ g).property)
      have he : innerBorel (⟨x,hb⟩ : borel (binaryParameters m hm)) = σ g :=
        Subtype.ext hx
      apply (a.native_inner_action_iff g).mp
      refine ⟨⟨x,hb⟩, ?_⟩
      change reverseRestriction (innerBorel ⟨x,hb⟩) = _
      rw [he, hs]
    · intro hg
      obtain ⟨b, hb⟩ := (a.native_inner_action_iff g).mpr hg
      have he : innerBorel b = σ g :=
        reverseRestriction_injective (hb.trans (hs g).symm)
      exact ⟨b.val, congrArg Subtype.val he⟩

end TrialityMarkedMiddleAction
end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
