module
public import CFSG.Quasithin.Chapter5.Section03SymplecticSource.Endpoint
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalSymplecticExtensionOrder.NativeLift
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalSymplecticCompletion

/-!
# The prepared full-normalizer symplectic extension

The original products Mᵢ = LᵢD also give Mᵢ = PᵢD for the pure parabolics.
The local Sylow-normalizer identities identify Pᵢ ∩ D with the entire pure
Borel. The previously constructed faithful native action of D therefore
glues across both full normalizers. This produces a genuine SourceExtension
and a compatible isomorphism on the whole normalizer pair, retaining both
pure endpoint maps and their common Borel map in either orientation.

The constructed extension is fixed for the subsequent order comparison.
The literal completion application discharges its extension and comparison
inputs and retains only the full ambient order bound. No ambient generation,
recognition or order hypothesis is used in constructing the extension.
All exponents n > 1, including n = 2, and the whole residual are retained.

Source: Aschbacher–Smith 5.3.1–2, printed pp.658–659, and Definition F.4.3,
p.274 of `refs/quasithin.pdf`. Ambient fusion, outer transfer and the order
comparison of F.4.35–43 are subsequent obligations.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory Theory.SpecificGroups.SymplecticFour
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
open ChapterF.SourceCompletion.SymplecticFour
variable {G : Type*} [Group G]

/-- A full-normalizer extension retaining the same pure parabolic and Borel
markings, in either orientation. No ambient order assertion is included. -/
structure SymplecticNormalizerMarking (L K S : Subgroup G)
    (F : Type*) [Field F] where
  extension : SourceExtension F
  left_le : ChapterF.Source.parabolic ![L,K] S 0 ≤ normalizer (L : Set G)
  right_le : ChapterF.Source.parabolic ![L,K] S 1 ≤ normalizer (K : Set G)
  comparison :
    (∃ e : RankTwoAmalgam.Iso (sourceParabolicAmalgam ![L,K] S)
        (SourceNormalizerExtension.diagram F),
      ∃ f : RankTwoAmalgam.Iso (SymplecticCompletion.diagram L K) extension.amalgam,
        (∀ x, (f.left (inclusion left_le x)).val = MulAut.conj (e.left x).val) ∧
        (∀ x, (f.right (inclusion right_le x)).val = MulAut.conj (e.right x).val) ∧
        ∀ b, (f.middle (inclusion (le_inf (inf_le_left.trans left_le)
          (inf_le_right.trans right_le)) b)).val = MulAut.conj (e.middle b).val) ∨
    (∃ e : RankTwoAmalgam.Iso (sourceParabolicAmalgam ![L,K] S)
        (SourceNormalizerExtension.diagram F).reverse,
      ∃ f : RankTwoAmalgam.Iso (SymplecticCompletion.diagram L K) extension.amalgam.reverse,
        (∀ x, (f.left (inclusion left_le x)).val = MulAut.conj (e.left x).val) ∧
        (∀ x, (f.right (inclusion right_le x)).val = MulAut.conj (e.right x).val) ∧
        ∀ b, (f.middle (inclusion (le_inf (inf_le_left.trans left_le)
          (inf_le_right.trans right_le)) b)).val = MulAut.conj (e.middle b).val)

/-- Forgetting only the pure marking gives the literal full-normalizer
comparison required by the completion recognizer. -/
theorem SymplecticNormalizerMarking.full_comparison
    {L K S : Subgroup G} {F : Type*} [Field F]
    (a : SymplecticNormalizerMarking L K S F) :
    Nonempty (RankTwoAmalgam.Iso (SymplecticCompletion.diagram L K) a.extension.amalgam) ∨
    Nonempty (RankTwoAmalgam.Iso (SymplecticCompletion.diagram L K) a.extension.amalgam.reverse) := by
  rcases a.comparison with ⟨_,f,_⟩ | ⟨_,f,_⟩
  · exact Or.inl ⟨f⟩
  · exact Or.inr ⟨f⟩

private theorem conjugation_transport {F : Type*} [Field F]
    (P : Subgroup G) (R : Subgroup (Sp F)) (e : P ≃* R)
    (a : MulAut R) (f : MulAut (Sp F)) (d : G)
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

/-- The original prepared source pair constructs a genuine full-normalizer
extension, preserving the given pure pair coherently. -/
theorem Preparation.symplectic_full_normalizer_marking
    {T : Sylow 2 G} {L W H A B : Subgroup G} {n : ℕ}
    (d : Preparation T L H A B (residual H))
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hp : Group.IsPerfect (residual H))
    (F : Type) [Field F] [Finite F] [CharP F 2]
    {m : ℕ} (hm : 0 < m) (hF : Nat.card F = 2^m)
    (he : Nonempty (RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H))
      (ChapterF.GreenBook.LieModels.SymplecticFour.amalgam F)) ∨
      Nonempty (RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H))
      (ChapterF.GreenBook.LieModels.SymplecticFour.amalgam F).reverse)) :
    m = n ∧ Nonempty (SymplecticNormalizerMarking L (residual H) (sourceS L H) F) := by
  let P := ChapterF.Source.parabolic ![L,residual H] (sourceS L H)
  let M₁ := normalizer (L : Set G)
  let M₂ := normalizer (residual H : Set G)
  let D := M₁ ⊓ M₂
  let C := P 0 ⊓ P 1
  have hf11 := d.hypothesisF11 h hH.1.1.2
  have hl := d.symplectic_normalizer_local_conditions h hH hp F hm hF he
  have hSP := d.symplectic_sourceS_le_factors h hH.1.1.2 hp F hm hF he
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
  obtain ⟨hmn,ha⟩ := d.symplectic_native_middle_lift h hH hp F hm hF he
  refine ⟨hmn,?_⟩
  rcases ha with ⟨a,σ,hσ,hs,_,hi⟩ | ⟨a,σ,hσ,hs,_,hi⟩
  · have hag (b : C) : (σ (inclusion a.middle_le b)).val =
        MulAut.conj (a.comparison.middle b).val := by
      have hh : σ (inclusion a.middle_le b) =
          SourceNormalizerExtension.innerBorel (a.comparison.middle b) :=
        SourceNormalizerExtension.restriction_injective
          ((DFunLike.congr_fun hs _).trans (a.native_inner_action b))
      exact congrArg Subtype.val hh
    have hcP (g : D) (x : P 0) : ∃ hx : g.val*x.val*g.val⁻¹ ∈ P 0,
        (a.comparison.left ⟨_,hx⟩).val = (σ g).val (a.comparison.left x).val := by
      apply conjugation_transport (P 0) pointParabolic a.comparison.left (a.action g).left
        (σ g).val g.val (a.left_conjugation g)
      intro y
      exact (congrArg (fun e => (e.left y).val) (DFunLike.congr_fun hs g)).symm
    have hcQ (g : D) (x : P 1) : ∃ hx : g.val*x.val*g.val⁻¹ ∈ P 1,
        (a.comparison.right ⟨_,hx⟩).val = (σ g).val (a.comparison.right x).val := by
      apply conjugation_transport (P 1) planeParabolic a.comparison.right (a.action g).right
        (σ g).val g.val (a.right_conjugation g)
      intro y
      exact (congrArg (fun e => (e.right y).val) (DFunLike.congr_fun hs g)).symm
    obtain ⟨E,f,hfP,hfQ,hfD⟩ := Chapter5.Section03SymplecticSource.extension_of_native_lift
      (P 0) (P 1) M₁ M₂ D C hPM hQM inf_le_left inf_le_right a.middle_le
      (hPD 0) (hPD 1) hprod₁ hprod₂ a.comparison.left a.comparison.right a.comparison.middle
      (fun b => congrArg Subtype.val (a.comparison.left_commutes b))
      (fun b => congrArg Subtype.val (a.comparison.right_commutes b)) σ hσ hi hag hcP hcQ
    exact ⟨⟨E,hPM,hQM,Or.inl ⟨a.comparison,f,hfP,hfQ,
      fun b => (hfD (inclusion a.middle_le b)).trans (hag b)⟩⟩⟩
  · have hag (b : C) : (σ (inclusion a.middle_le b)).val =
        MulAut.conj (a.comparison.middle b).val := by
      have hh : σ (inclusion a.middle_le b) =
          SourceNormalizerExtension.innerBorel (a.comparison.middle b) :=
        SourceNormalizerExtension.reverseRestriction_injective
          ((DFunLike.congr_fun hs _).trans (a.native_inner_action_reverse b))
      exact congrArg Subtype.val hh
    have hcP (g : D) (x : P 0) : ∃ hx : g.val*x.val*g.val⁻¹ ∈ P 0,
        (a.comparison.left ⟨_,hx⟩).val = (σ g).val (a.comparison.left x).val := by
      apply conjugation_transport (P 0) planeParabolic a.comparison.left (a.action g).left
        (σ g).val g.val (a.left_conjugation g)
      intro y
      exact (congrArg (fun e => (e.left y).val) (DFunLike.congr_fun hs g)).symm
    have hcQ (g : D) (x : P 1) : ∃ hx : g.val*x.val*g.val⁻¹ ∈ P 1,
        (a.comparison.right ⟨_,hx⟩).val = (σ g).val (a.comparison.right x).val := by
      apply conjugation_transport (P 1) pointParabolic a.comparison.right (a.action g).right
        (σ g).val g.val (a.right_conjugation g)
      intro y
      exact (congrArg (fun e => (e.right y).val) (DFunLike.congr_fun hs g)).symm
    obtain ⟨E,f,hfQ,hfP,hfD⟩ := Chapter5.Section03SymplecticSource.extension_of_native_lift
      (P 1) (P 0) M₂ M₁ D C hQM hPM inf_le_right inf_le_left a.middle_le
      (hPD 1) (hPD 0) hprod₂ hprod₁ a.comparison.right a.comparison.left a.comparison.middle
      (fun b => congrArg Subtype.val (a.comparison.right_commutes b))
      (fun b => congrArg Subtype.val (a.comparison.left_commutes b)) σ hσ hi hag hcQ hcP
    exact ⟨⟨E,hPM,hQM,Or.inr ⟨a.comparison,f.reverse,hfP,hfQ,
      fun b => (hfD (inclusion a.middle_le b)).trans (hag b)⟩⟩⟩

/-- The source inputs alone supply the full-normalizer extension comparison.
The ambient order bound is a separate remaining source obligation. -/
theorem Preparation.symplectic_full_normalizer_extension
    {T : Sylow 2 G} {L W H A B : Subgroup G} {n : ℕ}
    (d : Preparation T L H A B (residual H))
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hp : Group.IsPerfect (residual H))
    (F : Type) [Field F] [Finite F] [CharP F 2]
    {m : ℕ} (hm : 0 < m) (hF : Nat.card F = 2^m)
    (he : Nonempty (RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H))
      (ChapterF.GreenBook.LieModels.SymplecticFour.amalgam F)) ∨
      Nonempty (RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H))
      (ChapterF.GreenBook.LieModels.SymplecticFour.amalgam F).reverse)) :
    m = n ∧ ∃ E : SourceExtension F,
      Nonempty (RankTwoAmalgam.Iso (SymplecticCompletion.diagram L (residual H)) E.amalgam) ∨
      Nonempty (RankTwoAmalgam.Iso (SymplecticCompletion.diagram L (residual H)) E.amalgam.reverse) := by
  obtain ⟨hmn,⟨a⟩⟩ := d.symplectic_full_normalizer_marking h hH hp F hm hF he
  exact ⟨hmn,a.extension,a.full_comparison⟩

/-- Fix one of the constructed marked extensions, so the subsequent ambient
order comparison and completion application refer to exactly the same carrier. -/
def Preparation.symplecticNormalizerMarking
    {T : Sylow 2 G} {L W H A B : Subgroup G} {n : ℕ}
    (d : Preparation T L H A B (residual H))
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hp : Group.IsPerfect (residual H))
    (F : Type) [Field F] [Finite F] [CharP F 2]
    {m : ℕ} (hm : 0 < m) (hF : Nat.card F = 2^m)
    (he : Nonempty (RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H))
      (ChapterF.GreenBook.LieModels.SymplecticFour.amalgam F)) ∨
      Nonempty (RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H))
      (ChapterF.GreenBook.LieModels.SymplecticFour.amalgam F).reverse)) : SymplecticNormalizerMarking L (residual H) (sourceS L H) F :=
  (d.symplectic_full_normalizer_marking h hH hp F hm hF he).2.some

/-- Apply the literal completion consumer to the constructed extension. Only
the ambient order comparison remains explicit; neither an extension nor a
compatible full-normalizer isomorphism is supplied as an extra premise. -/
theorem Preparation.symplectic_prepared_extension_completion_of_order
    {T : Sylow 2 G} {L W H A B : Subgroup G} {n : ℕ}
    (d : Preparation T L H A B (residual H))
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hp : Group.IsPerfect (residual H))
    (F : Type) [Field F] [Finite F] [CharP F 2]
    {m : ℕ} (hm : 0 < m) (hF : Nat.card F = 2^m)
    (he : Nonempty (RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H))
      (ChapterF.GreenBook.LieModels.SymplecticFour.amalgam F)) ∨
      Nonempty (RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H))
      (ChapterF.GreenBook.LieModels.SymplecticFour.amalgam F).reverse))
    (hcard : Nat.card G ≤ Nat.card
      (d.symplecticNormalizerMarking h hH hp F hm hF he).extension.carrier) :
    let E := (d.symplecticNormalizerMarking h hH hp F hm hF he).extension
    m = n ∧ Nat.card F = 2^n ∧
      Chapter5.Section03GreenExtension.SourceLocalConditions
        (normalizerAmalgam L (residual H)) L (residual H) ((T : Subgroup G) ⊓ L) ∧
      ∃ c : Completion E (SymplecticCompletion.join L (residual H)),
        c.middle.range = (normalizer (L : Set G) ⊓ normalizer (residual H : Set G)).subgroupOf
          (SymplecticCompletion.join L (residual H)) ∧
        c.left.range ⊓ c.right.range = c.middle.range ∧
        Nat.card (SymplecticCompletion.join L (residual H)) ≤ Nat.card E.carrier ∧
        c.middle.range.normalCore = ⊥ ∧
        Function.Injective (MulAction.toPermHom (SymplecticCompletion.join L (residual H))
          (Subgroup.CosetGeometry.RankTwo.Vertex c.cosetFamily)) ∧
        Nat.card c.unipotentMap.range = Nat.card F ^ 4 ∧
        Nat.card c.torusMap.range = (Nat.card F - 1)^2 ∧
        c.torusMap.range ≤ normalizer (c.unipotentMap.range : Set (SymplecticCompletion.join L (residual H))) ∧
        c.unipotentMap.range ⊓ centralizer (c.torusMap.range : Set (SymplecticCompletion.join L (residual H))) = ⊥ :=
  d.symplectic_extension_completion h hH hp F hm hF he
    (d.symplecticNormalizerMarking h hH hp F hm hF he).extension
    (d.symplecticNormalizerMarking h hH hp F hm hF he).full_comparison hcard

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
