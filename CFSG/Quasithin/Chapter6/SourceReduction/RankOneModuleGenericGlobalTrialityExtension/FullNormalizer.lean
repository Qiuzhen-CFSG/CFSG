module
public import CFSG.Quasithin.Chapter5.Section03TrialitySource.Endpoint
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalTrialityExtension.MarkedAction
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalTrialitySmallCompletion.Recognition

/-!
# The full-normalizer triality extension with the given marking

The source products identify each full normalizer with its parabolic times
the whole common normalizer. Their intersection with each parabolic is the
full common Borel. The faithful native middle action therefore glues across
both endpoints. This constructs every algebraic source-extension field and
retains the given central/arms comparison. Only the subsequent ambient order
bound is used by recognition, on this same selected extension carrier.

Source: Aschbacher–Smith 5.3.1–2, pp.658–659, and F.4.3, p.274.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
open _root_.Triality.Standard _root_.Triality.Standard.Parabolics
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
open ChapterF.SourceCompletion.TrialityNonbinary
open ChapterF.SourceCompletion
open Chapter5.Section03TrialitySource
variable {G : Type*} [Group G]

/-- A realized whole-normalizer extension with all restrictions fixed by e. -/
structure TrialityNormalizerMarking (L K S : Subgroup G) (m : ℕ) (hm : 0 < m)
    (e : RankTwoAmalgam.Iso (sourceParabolicAmalgam ![L,K] S)
      (nativeAmalgam m hm).reverse) where
  extension : SourceExtension m hm
  left_le : ChapterF.Source.parabolic ![L,K] S 0 ≤ normalizer (L : Set G)
  right_le : ChapterF.Source.parabolic ![L,K] S 1 ≤ normalizer (K : Set G)
  rho : (normalizer (L : Set G) ⊓ normalizer (K : Set G) : Subgroup G) →*
    MulAut (BinaryCarrier m hm)
  faithful : Function.Injective rho
  comparison : RankTwoAmalgam.Iso
    (UnitaryNonbinary.Generated.amalgam (normalizer (L : Set G)) (normalizer (K : Set G)))
    extension.amalgam.reverse
  left_marked : ∀ x, (comparison.left (inclusion left_le x)).val = MulAut.conj (e.left x).val
  right_marked : ∀ x, (comparison.right (inclusion right_le x)).val = MulAut.conj (e.right x).val
  middle_marked : ∀ d, (comparison.middle d).val = rho d
  inner_marked : ∀ b, rho (inclusion (le_inf (inf_le_left.trans left_le)
    (inf_le_right.trans right_le)) b) = MulAut.conj (e.middle b).val
  inner_preimage : ∀ d, rho d ∈ UnitaryNonbinary.inner (BinaryCarrier m hm) ↔
    d.val ∈ (ChapterF.Source.parabolic ![L,K] S 0 ⊓ ChapterF.Source.parabolic ![L,K] S 1 : Subgroup G)

private theorem conjugation_transport {U : Type*} [Group U]
    (P : Subgroup G) (R : Subgroup U) (e : P ≃* R)
    (a : MulAut R) (f : MulAut U) (d : G)
    (hc : ∀ x, (e.symm (a x)).val = d * (e.symm x).val * d⁻¹)
    (hf : ∀ x : R, (a x).val = f x.val) (x : P) :
    ∃ hx : d*x.val*d⁻¹ ∈ P, (e ⟨d*x.val*d⁻¹,hx⟩).val = f (e x).val := by
  have hh := hc (e x)
  rw [e.symm_apply_apply] at hh
  refine ⟨hh ▸ (e.symm (a (e x))).property, ?_⟩
  have he : (⟨d*x.val*d⁻¹,hh ▸ (e.symm (a (e x))).property⟩ : P) =
      e.symm (a (e x)) := Subtype.ext hh.symm
  rw [he,e.apply_symm_apply,hf]

variable [Finite G]

/-- The exact source parabolics in their original full normalizers. -/
structure TrialityNormalizerLocalData (L K S : Subgroup G) : Prop where
  left_le : ChapterF.Source.parabolic ![L,K] S 0 ≤ normalizer (L : Set G)
  right_le : ChapterF.Source.parabolic ![L,K] S 1 ≤ normalizer (K : Set G)
  left_inf : ChapterF.Source.parabolic ![L,K] S 0 ⊓
    (normalizer (L : Set G) ⊓ normalizer (K : Set G)) =
    ChapterF.Source.parabolic ![L,K] S 0 ⊓ ChapterF.Source.parabolic ![L,K] S 1
  right_inf : ChapterF.Source.parabolic ![L,K] S 1 ⊓
    (normalizer (L : Set G) ⊓ normalizer (K : Set G)) =
    ChapterF.Source.parabolic ![L,K] S 0 ⊓ ChapterF.Source.parabolic ![L,K] S 1
  left_product : ∀ x ∈ normalizer (L : Set G),
    ∃ p ∈ ChapterF.Source.parabolic ![L,K] S 0,
    ∃ d ∈ normalizer (L : Set G) ⊓ normalizer (K : Set G), x = p*d
  right_product : ∀ x ∈ normalizer (K : Set G),
    ∃ p ∈ ChapterF.Source.parabolic ![L,K] S 1,
    ∃ d ∈ normalizer (L : Set G) ⊓ normalizer (K : Set G), x = p*d

/-- Original source normality and local products give both exact full-normalizer
intersections with the common Borel. -/
theorem Preparation.triality_normalizer_local_data
    {T : Sylow 2 G} {L W H A B : Subgroup G} {n : ℕ}
    (d : Preparation T L H A B (residual H))
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hp : Group.IsPerfect (residual H))
    (m : ℕ) (hm : 0 < m)
    (e : RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H))
      (nativeAmalgam m hm).reverse) :
    TrialityNormalizerLocalData L (residual H) (sourceS L H) := by
  let P := ChapterF.Source.parabolic ![L,residual H] (sourceS L H)
  let M₁ := normalizer (L : Set G)
  let M₂ := normalizer (residual H : Set G)
  let D := M₁ ⊓ M₂
  let C := P 0 ⊓ P 1
  have hf11 := d.hypothesisF11 h hH.1.1.2
  have hl := d.triality_normalizer_local_conditions h hH hp m hm (Or.inr ⟨e⟩)
  have hSP := d.triality_sourceS_le_factors h hH.1.1.2 hp m hm (Or.inr ⟨e⟩)
  have hS : sourceS L H = (T : Subgroup G) ⊓ L :=
    (inf_eq_left.mpr (hSP 0)).symm.trans d.left_intersection
  have hDN : D = normalizer (sourceS L H : Set G) := by
    rw [hS]
    exact hl.normalizer_eq_middle.symm
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
  exact ⟨hPM,hQM,hPD 0,hPD 1,hprod₁,hprod₂⟩

omit [Finite G] in
private theorem marking_of_reverse {L K S : Subgroup G} {m : ℕ} {hm : 0 < m}
    {e : RankTwoAmalgam.Iso (sourceParabolicAmalgam ![L,K] S) (nativeAmalgam m hm).reverse}
    (q : TrialityNormalizerLocalData L K S) (E : SourceExtension m hm)
    (ρ : (normalizer (L : Set G) ⊓ normalizer (K : Set G) : Subgroup G) →*
      MulAut (BinaryCarrier m hm)) (hρ : Function.Injective ρ)
    (f : RankTwoAmalgam.Iso
      (RankTwoAmalgam.ofSubgroups (normalizer (K : Set G))
        (normalizer (L : Set G) ⊓ normalizer (K : Set G))
        (normalizer (L : Set G)) inf_le_right inf_le_left) E.amalgam)
    (hl : ∀ x, (f.right (inclusion q.left_le x)).val = MulAut.conj (e.left x).val)
    (hr : ∀ x, (f.left (inclusion q.right_le x)).val = MulAut.conj (e.right x).val)
    (hmid : ∀ g, (f.middle g).val = ρ g)
    (hc : ∀ b, ρ (inclusion (le_inf (inf_le_left.trans q.left_le)
      (inf_le_right.trans q.right_le)) b) = MulAut.conj (e.middle b).val)
    (hi : ∀ g, ρ g ∈ UnitaryNonbinary.inner (BinaryCarrier m hm) ↔
      g.val ∈ (ChapterF.Source.parabolic ![L,K] S 0 ⊓ ChapterF.Source.parabolic ![L,K] S 1 : Subgroup G)) :
    Nonempty (TrialityNormalizerMarking L K S m hm e) := by
  exact ⟨{ extension := E
           left_le := q.left_le
           right_le := q.right_le
           rho := ρ
           faithful := hρ
           comparison := f.reverse
           left_marked := hl
           right_marked := hr
           middle_marked := hmid
           inner_marked := hc
           inner_preimage := hi }⟩

omit [Finite G] in
private theorem lift_inner_marked {L K S : Subgroup G} {m : ℕ} {hm : 0 < m}
    {e : RankTwoAmalgam.Iso (sourceParabolicAmalgam ![L,K] S) (nativeAmalgam m hm).reverse}
    (a : TrialityMarkedMiddleAction L K S m hm e)
    (σ : (normalizer (L : Set G) ⊓ normalizer (K : Set G) : Subgroup G) →* flagAutomorphisms m hm)
    (hs : reverseRestriction.comp σ = a.action)
    (b : (ChapterF.Source.parabolic ![L,K] S 0 ⊓ ChapterF.Source.parabolic ![L,K] S 1 : Subgroup G)) :
    (σ (inclusion a.middle_le b)).val = MulAut.conj (e.middle b).val := by
  have hh : σ (inclusion a.middle_le b) = innerBorel (e.middle b) :=
    reverseRestriction_injective
      ((DFunLike.congr_fun hs _).trans (a.native_inner_action b))
  exact congrArg Subtype.val hh

omit [Finite G] in
private theorem lift_left_marked {L K S : Subgroup G} {m : ℕ} {hm : 0 < m}
    {e : RankTwoAmalgam.Iso (sourceParabolicAmalgam ![L,K] S) (nativeAmalgam m hm).reverse}
    (a : TrialityMarkedMiddleAction L K S m hm e)
    (σ : (normalizer (L : Set G) ⊓ normalizer (K : Set G) : Subgroup G) →* flagAutomorphisms m hm)
    (hs : reverseRestriction.comp σ = a.action)
    (g : (normalizer (L : Set G) ⊓ normalizer (K : Set G) : Subgroup G))
    (x : ChapterF.Source.parabolic ![L,K] S 0) :
    ∃ hx : g.val*x.val*g.val⁻¹ ∈ ChapterF.Source.parabolic ![L,K] S 0,
      (e.left ⟨_,hx⟩).val = (σ g).val (e.left x).val := by
  apply conjugation_transport _ (parabolic (binaryParameters m hm) .central) e.left (a.action g).left
    (σ g).val g.val (a.left_conjugation g)
  intro y
  exact (congrArg (fun z => (z.left y).val) (DFunLike.congr_fun hs g)).symm

omit [Finite G] in
private theorem lift_right_marked {L K S : Subgroup G} {m : ℕ} {hm : 0 < m}
    {e : RankTwoAmalgam.Iso (sourceParabolicAmalgam ![L,K] S) (nativeAmalgam m hm).reverse}
    (a : TrialityMarkedMiddleAction L K S m hm e)
    (σ : (normalizer (L : Set G) ⊓ normalizer (K : Set G) : Subgroup G) →* flagAutomorphisms m hm)
    (hs : reverseRestriction.comp σ = a.action)
    (g : (normalizer (L : Set G) ⊓ normalizer (K : Set G) : Subgroup G))
    (x : ChapterF.Source.parabolic ![L,K] S 1) :
    ∃ hx : g.val*x.val*g.val⁻¹ ∈ ChapterF.Source.parabolic ![L,K] S 1,
      (e.right ⟨_,hx⟩).val = (σ g).val (e.right x).val := by
  apply conjugation_transport _ (parabolic (binaryParameters m hm) .arms) e.right (a.action g).right
    (σ g).val g.val (a.right_conjugation g)
  intro y
  exact (congrArg (fun z => (z.right y).val) (DFunLike.congr_fun hs g)).symm

omit [Finite G] in
private theorem left_commutes_val {U : Type*} [Group U]
    {P C Q : Subgroup G} {A B R : Subgroup U}
    {hCP : C ≤ P} {hCQ : C ≤ Q} {hBA : B ≤ A} {hBR : B ≤ R}
    (e : RankTwoAmalgam.Iso (RankTwoAmalgam.ofSubgroups P C Q hCP hCQ)
      (RankTwoAmalgam.ofSubgroups A B R hBA hBR)) (b : C) (hb : b.val ∈ P) :
    (e.left ⟨b.val,hb⟩).val = (e.middle b).val :=
  congrArg Subtype.val (e.left_commutes b)

omit [Finite G] in
private theorem right_commutes_val {U : Type*} [Group U]
    {P C Q : Subgroup G} {A B R : Subgroup U}
    {hCP : C ≤ P} {hCQ : C ≤ Q} {hBA : B ≤ A} {hBR : B ≤ R}
    (e : RankTwoAmalgam.Iso (RankTwoAmalgam.ofSubgroups P C Q hCP hCQ)
      (RankTwoAmalgam.ofSubgroups A B R hBA hBR)) (b : C) (hb : b.val ∈ Q) :
    (e.right ⟨b.val,hb⟩).val = (e.middle b).val :=
  congrArg Subtype.val (e.right_commutes b)

omit [Finite G] in
private theorem source_left_common_marked {L K S : Subgroup G} {m : ℕ} {hm : 0 < m}
    (e : RankTwoAmalgam.Iso (sourceParabolicAmalgam ![L,K] S) (nativeAmalgam m hm).reverse)
    (q : TrialityNormalizerLocalData L K S)
    (b : (ChapterF.Source.parabolic ![L,K] S 0 ⊓ ChapterF.Source.parabolic ![L,K] S 1 : Subgroup G)) :
    (e.left ⟨b.val,(q.left_inf.ge b.property).1⟩).val = (e.middle b).val :=
  left_commutes_val (hBA := borel_le_parabolic _ .central)
    (hBR := borel_le_parabolic _ .arms) e b _

omit [Finite G] in
private theorem source_right_common_marked {L K S : Subgroup G} {m : ℕ} {hm : 0 < m}
    (e : RankTwoAmalgam.Iso (sourceParabolicAmalgam ![L,K] S) (nativeAmalgam m hm).reverse)
    (q : TrialityNormalizerLocalData L K S)
    (b : (ChapterF.Source.parabolic ![L,K] S 0 ⊓ ChapterF.Source.parabolic ![L,K] S 1 : Subgroup G)) :
    (e.right ⟨b.val,(q.right_inf.ge b.property).1⟩).val = (e.middle b).val :=
  right_commutes_val (hBA := borel_le_parabolic _ .central)
    (hBR := borel_le_parabolic _ .arms) e b _

omit [Finite G] in
private theorem extension_of_native_lift_on_source {L K S : Subgroup G} {m : ℕ} {hm : 0 < m}
    {e : RankTwoAmalgam.Iso (sourceParabolicAmalgam ![L,K] S) (nativeAmalgam m hm).reverse}
    (q : TrialityNormalizerLocalData L K S)
    (a : TrialityMarkedMiddleAction L K S m hm e)
    (σ : (normalizer (L : Set G) ⊓ normalizer (K : Set G) : Subgroup G) →* flagAutomorphisms m hm)
    (hσ : Function.Injective σ) (hs : reverseRestriction.comp σ = a.action)
    (hi : ∀ g, (σ g).val ∈ UnitaryNonbinary.inner (BinaryCarrier m hm) ↔
      g.val ∈ (ChapterF.Source.parabolic ![L,K] S 0 ⊓ ChapterF.Source.parabolic ![L,K] S 1 : Subgroup G)) :
    ∃ E : SourceExtension m hm,
      ∃ f : RankTwoAmalgam.Iso
        (RankTwoAmalgam.ofSubgroups (normalizer (K : Set G))
          (normalizer (L : Set G) ⊓ normalizer (K : Set G))
          (normalizer (L : Set G)) inf_le_right inf_le_left) E.amalgam,
        (∀ x, (f.left (inclusion q.right_le x)).val = MulAut.conj (e.right x).val) ∧
        (∀ x, (f.right (inclusion q.left_le x)).val = MulAut.conj (e.left x).val) ∧
        (∀ g, (f.middle g).val = (σ g).val) := by
  let P := ChapterF.Source.parabolic ![L,K] S
  let M₁ := normalizer (L : Set G)
  let M₂ := normalizer (K : Set G)
  let D := M₁ ⊓ M₂
  let C := P 0 ⊓ P 1
  exact Chapter5.Section03TrialitySource.extension_of_native_lift (G := G) (m := m) (hm := hm)
    (P 1) (P 0) M₂ M₁ D C q.right_le q.left_le inf_le_right inf_le_left a.middle_le
    q.right_inf q.left_inf q.right_product q.left_product e.right e.left e.middle
    (source_right_common_marked e q)
    (source_left_common_marked e q) σ hσ hi (lift_inner_marked a σ hs)
      (lift_right_marked a σ hs) (lift_left_marked a σ hs)

omit [Finite G] in
private theorem marking_of_native_lift {L K S : Subgroup G} {m : ℕ} {hm : 0 < m}
    {e : RankTwoAmalgam.Iso (sourceParabolicAmalgam ![L,K] S) (nativeAmalgam m hm).reverse}
    (q : TrialityNormalizerLocalData L K S)
    (a : TrialityMarkedMiddleAction L K S m hm e)
    (σ : (normalizer (L : Set G) ⊓ normalizer (K : Set G) : Subgroup G) →* flagAutomorphisms m hm)
    (hσ : Function.Injective σ) (hs : reverseRestriction.comp σ = a.action)
    (hi : ∀ g, (σ g).val ∈ UnitaryNonbinary.inner (BinaryCarrier m hm) ↔
      g.val ∈ (ChapterF.Source.parabolic ![L,K] S 0 ⊓ ChapterF.Source.parabolic ![L,K] S 1 : Subgroup G)) :
    Nonempty (TrialityNormalizerMarking L K S m hm e) := by
  obtain ⟨E,f,hfQ,hfP,hfD⟩ := extension_of_native_lift_on_source q a σ hσ hs hi
  exact marking_of_reverse q E ((flagAutomorphisms m hm).subtype.comp σ)
    (Subtype.val_injective.comp hσ) f hfP hfQ hfD (lift_inner_marked a σ hs) hi

/-- Construct the full-normalizer extension and every marked restriction from
the original prepared row and the supplied central/arms comparison. -/
theorem Preparation.triality_full_normalizer_marking
    {T : Sylow 2 G} {L W H A B : Subgroup G} {n : ℕ}
    (d : Preparation T L H A B (residual H))
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hp : Group.IsPerfect (residual H))
    (m : ℕ) (hm : 0 < m)
    (e : RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H))
      (nativeAmalgam m hm).reverse) :
    m=n ∧ 1<m ∧ Nonempty (TrialityNormalizerMarking L (residual H) (sourceS L H) m hm e) := by
  obtain ⟨hmn,hm2,_⟩ := d.triality_local_structure h hH.1.1.2 hp m hm e
  obtain ⟨a⟩ := d.triality_marked_middle_action h hH hp m hm e
  obtain ⟨σ,hσ,hs,hi⟩ := a.native_lift hm2
  exact ⟨hmn,hm2,marking_of_native_lift
    (d.triality_normalizer_local_data h hH hp m hm e) a σ hσ hs hi⟩

/-- Fix the constructed extension for every subsequent order comparison. -/
def Preparation.trialityNormalizerMarking
    {T : Sylow 2 G} {L W H A B : Subgroup G} {n : ℕ}
    (d : Preparation T L H A B (residual H))
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hp : Group.IsPerfect (residual H))
    (m : ℕ) (hm : 0 < m)
    (e : RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H))
      (nativeAmalgam m hm).reverse) :
    TrialityNormalizerMarking L (residual H) (sourceS L H) m hm e :=
  (d.triality_full_normalizer_marking h hH hp m hm e).2.2.some

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
