module
public import CFSG.Quasithin.Chapter5.Section03LinearSource.Endpoint
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalLinearAmbient.NativeAction

/-!
# The prepared maximal linear full-normalizer extension

The faithful common-normalizer action on PSL₃(F) extends across the two full
normalizers by the source products Mᵢ = PᵢD. The common Borel is self-normalizing
in the model because it is a Sylow normalizer. Thus the inner preimage of the
common action is exactly the whole source Borel, and the gluing maps are faithful.
The same extension and both pure markings are retained in either orientation.

This proves the compatible realization needed in source 5.3.2 without assuming
recognition of the factor join, ambient generation, or an order bound. The
literal completion and order applications now need only source generation and
the Hall-quotient cube-in-middle witness. These remaining premises, the outer
Sylow argument, ambient recognition and GlobalExit stay with this task.
Source: Aschbacher–Smith 5.3.1–2, pp.658–659, and F.4.3,49, pp.274,298–299
of `refs/quasithin.pdf`.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
open Chapter5.Section03LinearSource Matrix.PSL3.LinearThree
open ChapterF.SourceCompletion.LinearThreeEven
variable {G : Type*} [Group G]

/-- Full-normalizer realization retaining both pure endpoint markings. -/
structure LinearNormalizerMarking (L K S : Subgroup G) (F : Type*) [Field F] where
  extension : SourceExtension F
  left_le : ChapterF.Source.parabolic ![L,K] S 0 ≤ normalizer (L : Set G)
  right_le : ChapterF.Source.parabolic ![L,K] S 1 ≤ normalizer (K : Set G)
  comparison :
    (∃ a : MarkedAction (ChapterF.Source.parabolic ![L,K] S 0)
        (ChapterF.Source.parabolic ![L,K] S 1)
        (normalizer (L : Set G) ⊓ normalizer (K : Set G)) (pointParabolic F) (lineParabolic F),
      ∃ f : RankTwoAmalgam.Iso
        (ChapterF.SourceCompletion.UnitaryNonbinary.Generated.amalgam (normalizer (L : Set G))
          (normalizer (K : Set G))) extension.amalgam,
        (∀ x, (f.left (inclusion left_le x)).val = MulAut.conj (a.left x).val) ∧
        (∀ x, (f.right (inclusion right_le x)).val = MulAut.conj (a.right x).val) ∧
        ∀ b, (f.middle b).val = a.action b) ∨
    (∃ a : MarkedAction (ChapterF.Source.parabolic ![L,K] S 0)
        (ChapterF.Source.parabolic ![L,K] S 1)
        (normalizer (L : Set G) ⊓ normalizer (K : Set G)) (lineParabolic F) (pointParabolic F),
      ∃ f : RankTwoAmalgam.Iso
        (ChapterF.SourceCompletion.UnitaryNonbinary.Generated.amalgam (normalizer (L : Set G))
          (normalizer (K : Set G))) extension.amalgam.reverse,
        (∀ x, (f.left (inclusion left_le x)).val = MulAut.conj (a.left x).val) ∧
        (∀ x, (f.right (inclusion right_le x)).val = MulAut.conj (a.right x).val) ∧
        ∀ b, (f.middle b).val = a.action b)

def LinearNormalizerMarking.fullComparison {L K S : Subgroup G} {F : Type*} [Field F]
    (a : LinearNormalizerMarking L K S F) : LinearCompletion.NormalizerComparison L K a.extension :=
  Classical.choice (by
    rcases a.comparison with ⟨_,f,_⟩ | ⟨_,f,_⟩
    · exact ⟨Sum.inl f⟩
    · exact ⟨Sum.inr f⟩)

private theorem native_borel_self_normalizing (F : Type*) [Field F] [Finite F] [CharP F 2]
    {m : ℕ} (hm : 0 < m) (hF : Nat.card F = 2^m) :
    normalizer ((pointParabolic F ⊓ lineParabolic F : Subgroup PSL(3,F)) : Set PSL(3,F)) =
      pointParabolic F ⊓ lineParabolic F := by
  rw [projective_parabolics_inf,←normalizer_unipotent F hm hF]
  exact Sylow.normalizer_normalizer (unipotentSylow F hm hF)

variable [Finite G]
variable {T : Sylow 2 G} {L W H A B : Subgroup G} {n : ℕ}
    (d : Preparation T L H A B (residual H))
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hp : Group.IsPerfect (residual H))
    (F : Type) [Field F] [Finite F] [CharP F 2]
    {m : ℕ} (hm : 0 < m) (hF : Nat.card F = 2^m)
    (he : Nonempty (RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H))
      (ChapterF.GreenBook.LieModels.LinearThree.amalgam F)) ∨
      Nonempty (RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H))
      (ChapterF.GreenBook.LieModels.LinearThree.amalgam F).reverse))
    (hmax : residual H ∈ Chapter1.LStar G (T : Subgroup G))
include d h hH hp hm hF he hmax



/-- Source 5.3.2 for the actual prepared maximal linear row, in both orientations. -/
theorem Preparation.linear_full_normalizer_marking :
    m = n ∧ Nonempty (LinearNormalizerMarking L (residual H) (sourceS L H) F) := by
  let P := ChapterF.Source.parabolic ![L,residual H] (sourceS L H)
  let M₁ := normalizer (L : Set G)
  let M₂ := normalizer (residual H : Set G)
  let D := M₁ ⊓ M₂
  let C := P 0 ⊓ P 1
  have hf11 := d.hypothesisF11 h hH.1.1.2
  have hl := d.linear_normalizer_local_conditions h hH hp F hm hF he hmax
  have hSP := d.linear_sourceS_le_factors h hH.1.1.2 hp F hm hF he
  have hDN : D = normalizer (sourceS L H : Set G) :=
    (d.linear_common_normalizer_eq h hH hp F hm hF he hmax).symm
  have hPM : P 0 ≤ M₁ :=
    (normal_subgroupOf_iff_le_normalizer (show L ≤ P 0 from le_sup_left.trans le_sup_left)).mp
      (hf11.local_normal_in_parabolic 0)
  have hQM : P 1 ≤ M₂ :=
    (normal_subgroupOf_iff_le_normalizer (show residual H ≤ P 1 from le_sup_left.trans le_sup_left)).mp
      (hf11.local_normal_in_parabolic 1)
  have hPD (i : Fin 2) : P i ⊓ D = C := by
    rw [hDN,show C = ChapterF.Source.commonBorel ![L,residual H] (sourceS L H) from
      ChapterF.Source.lemma_F_1_3_6 hf11]
    simpa only [inf_eq_left.mpr (hSP i)] using (hf11.commonBorel_eq_normalizer i).symm
  have hprod₁ : ∀ x ∈ M₁, ∃ p ∈ P 0, ∃ b ∈ D, x = p*b := by
    intro x hx
    obtain ⟨p,hp,b,hb,he⟩ := hl.factor_left x hx
    exact ⟨p,(show L ≤ P 0 from le_sup_left.trans le_sup_left) hp,b,hb,he⟩
  have hprod₂ : ∀ x ∈ M₂, ∃ p ∈ P 1, ∃ b ∈ D, x = p*b := by
    intro x hx
    obtain ⟨p,hp,b,hb,he⟩ := hl.factor_right x hx
    exact ⟨p,(show residual H ≤ P 1 from le_sup_left.trans le_sup_left) hp,b,hb,he⟩
  obtain ⟨hmn,ha⟩ := d.linear_native_middle_action h hH hp F hm hF he hmax
  refine ⟨hmn,?_⟩
  rcases ha with ha | ha <;> obtain ⟨a⟩ := ha
  · obtain ⟨E,f,hfP,hfQ,hfD⟩ := a.extension (native_conj_injective F)
      (parabolics_sup_eq_top F) (native_borel_self_normalizing F hm hF)
      M₁ M₂ hPM hQM inf_le_left inf_le_right (hPD 0) (hPD 1) hprod₁ hprod₂
    exact ⟨⟨E,hPM,hQM,Or.inl ⟨a,f,hfP,hfQ,hfD⟩⟩⟩
  · obtain ⟨E,f,hfQ,hfP,hfD⟩ := a.reverse.extension (native_conj_injective F)
      (parabolics_sup_eq_top F) (native_borel_self_normalizing F hm hF)
      M₂ M₁ hQM hPM inf_le_right inf_le_left
      ((hPD 1).trans (inf_comm _ _)) ((hPD 0).trans (inf_comm _ _)) hprod₂ hprod₁
    exact ⟨⟨E,hPM,hQM,Or.inr ⟨a,f.reverse,hfP,hfQ,hfD⟩⟩⟩

/-- The full-normalizer comparison is constructed without ambient generation or an order bound. -/
theorem Preparation.linear_full_normalizer_extension :
    m = n ∧ ∃ E : SourceExtension F,
      Nonempty (LinearCompletion.NormalizerComparison L (residual H) E) := by
  obtain ⟨hmn,⟨a⟩⟩ := d.linear_full_normalizer_marking h hH hp F hm hF he hmax
  exact ⟨hmn,a.extension,⟨a.fullComparison⟩⟩

/-- Choose the same marked extension for subsequent source and completion arguments. -/
def Preparation.linearNormalizerMarking : LinearNormalizerMarking L (residual H) (sourceS L H) F :=
  (d.linear_full_normalizer_marking h hH hp F hm hF he hmax).2.some

/-- Actual completion in the original G once its generation is proved;
the extension and compatible comparison are no longer additional inputs. -/
theorem Preparation.linear_prepared_completion_input
    (hgen : normalizer (L : Set G) ⊔ normalizer (residual H : Set G) = ⊤) :
    let a := d.linearNormalizerMarking h hH hp F hm hF he hmax
    ∃ c : Completion a.extension G,
      c.middle.range = normalizer (L : Set G) ⊓ normalizer (residual H : Set G) ∧
      c.left.range ⊓ c.right.range = c.middle.range := by
  let a := d.linearNormalizerMarking h hH hp F hm hF he hmax
  exact ⟨LinearCompletion.normalizerCompletion L (residual H) a.extension a.fullComparison hgen,
    LinearCompletion.normalizerCompletion_middle L (residual H) a.extension a.fullComparison hgen,
    LinearCompletion.normalizerCompletion_overlap L (residual H) a.extension a.fullComparison hgen⟩

/-- The source Hall-quotient cubic witness yields full ambient order for the
constructed extension; generation and the cubic witness remain source duties. -/
theorem Preparation.linear_prepared_card_eq
    (hgen : normalizer (L : Set G) ⊔ normalizer (residual H : Set G) = ⊤)
    (s t : G) (hs : s ∈ normalizer (L : Set G)) (ht : t ∈ normalizer (residual H : Set G))
    (hsout : s ∉ normalizer (L : Set G) ⊓ normalizer (residual H : Set G))
    (htout : t ∉ normalizer (L : Set G) ⊓ normalizer (residual H : Set G))
    (hs2 : s^2=1) (ht2 : t^2=1)
    (hcube : (s*t)^3 ∈ normalizer (L : Set G) ⊓ normalizer (residual H : Set G)) :
    Nat.card G = Nat.card (d.linearNormalizerMarking h hH hp F hm hF he hmax).extension.carrier := by
  let a := d.linearNormalizerMarking h hH hp F hm hF he hmax
  exact LinearCompletion.normalizerCompletion_card_eq L (residual H) a.extension
    a.fullComparison hgen hF s t hs ht hsout htout hs2 ht2 hcube

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
