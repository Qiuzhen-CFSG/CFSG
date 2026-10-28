module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.OriginalExtension.G2NativeLift
public import Theory.AtlasPort.LinearGroups.G2.LieAutomorphismExtensions.Semilinear
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.OriginalExtension.FlagRestoration
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.OriginalExtension.BinaryBorel

/-!
# Restoring the original G₂ pair

The native lift preserves both reduced endpoint maps. The full Borel is the
intersection of the self-normalizing parabolics. Faithful conjugation and the
original Borel action therefore glue into a type-preserving automorphism
extension, retaining both orientations and all reduced restrictions.
For the binary full model, the order-64 Borel instead forces equality of
the original and reduced Sylows, giving the original marking directly.

Source: DGS, Groups and Graphs (1985), (15.2), pp.226–228.
The genuine marked reduced comparison remains an earlier recognition input.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory RankTwoAmalgam
namespace CFSG.Quasithin.ChapterF.Source.DGS85.OriginalExtension.G2Native
open Atlas.G2 Atlas.G2.LieParabolicSetup Atlas.G2.LieAutomorphismExtensions
variable (F : Type*) [Field F]

def endpoint (short : Bool) : Subgroup (Model F) := if short then parabolic₁ else parabolic₂

theorem borel_le_endpoint (short : Bool) : Atlas.G2.borel (K := F) ≤ endpoint F short := by
  cases short
  · exact borel_le_parabolic₂
  · exact borel_le_parabolic₁

def amalgam (short : Bool) : RankTwoAmalgam (endpoint F short)
    (Atlas.G2.borel (K := F)) (endpoint F (!short)) :=
  ofSubgroups _ _ _ (borel_le_endpoint F short) (borel_le_endpoint F (!short))

theorem endpoints_inf (short : Bool) :
    endpoint F short ⊓ endpoint F (!short) = Atlas.G2.borel (K := F) := by
  cases short
  · exact (inf_comm _ _).trans parabolics_intersection
  · exact parabolics_intersection

theorem endpoints_generate (short : Bool) : endpoint F short ⊔ endpoint F (!short) = ⊤ := by
  cases short
  · exact (sup_comm _ _).trans Atlas.G2.LieParabolicSetup.parabolics_generate
  · exact Atlas.G2.LieParabolicSetup.parabolics_generate

variable [Finite F] [CharP F 2]

theorem native_lifts (hq : 2 < Nat.card F) (short : Bool)
    (a : Iso (amalgam F short) (amalgam F short)) :
    ∃ f : Model F →* Model F,
      (∀ x : endpoint F short, f x.val = (a.left x).val) ∧
      (∀ x : endpoint F (!short), f x.val = (a.right x).val) := by
  cases short
  · obtain ⟨f,hl,hr⟩ := G2NativeLift.native_lifts hq a.reverse
    exact ⟨f,hr,hl⟩
  · exact G2NativeLift.native_lifts hq a

theorem endpoint_normalizer (short : Bool) :
    normalizer (endpoint F short : Set (Model F)) = endpoint F short := by
  apply NativeRestoration.self_normalizing_of_sylow (sylow (F := F))
  · exact sylow_le_borel.trans (borel_le_endpoint F short)
  · change normalizer (unipotent (K := F) : Set (Model F)) ≤ _
    rw [SylowNormalizer.normalizer_unipotent]
    exact borel_le_endpoint F short

theorem inner_flag (short : Bool) (g : Model F)
    (hl : (endpoint F short).map (MulAut.conj g).toMonoidHom = endpoint F short)
    (hr : (endpoint F (!short)).map (MulAut.conj g).toMonoidHom = endpoint F (!short)) :
    g ∈ Atlas.G2.borel (K := F) := by
  rw [←endpoints_inf F short]
  constructor
  · have hh := mem_normalizer_iff_map_conj_eq.mpr hl
    rwa [endpoint_normalizer] at hh
  · have hh := mem_normalizer_iff_map_conj_eq.mpr hr
    rwa [endpoint_normalizer] at hh

/-- Original endpoint and full-Borel maps into the same regular extension,
with the prescribed restrictions to every reduced element. -/
theorem exists_original_extension_iso
    {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}
    (h : HypothesisF11 L S) (hq : 2 < Nat.card F) (short : Bool)
    (e : Iso (reducedAmalgam L S) (amalgam F short)) :
    ∃ E : SourceCompletion.UnitaryNonbinary.SourceExtension
      (endpoint F short) (endpoint F (!short)),
      ∃ f : Iso (originalAmalgam L S) E.amalgam,
        (∀ x : parabolic L (SuzukiContainment.reducedSylow L S) 0,
          (f.left (inclusion (SuzukiContainment.reduced_parabolic_le h 0) x) : MulAut (Model F)) =
            MulAut.conj (e.left x : Model F)) ∧
        (∀ x : parabolic L (SuzukiContainment.reducedSylow L S) 1,
          (f.right (inclusion (SuzukiContainment.reduced_parabolic_le h 1) x) : MulAut (Model F)) =
            MulAut.conj (e.right x : Model F)) ∧
        (∀ b : commonBorel L (SuzukiContainment.reducedSylow L S),
          (f.middle (inclusion (SuzukiContainment.reduced_commonBorel_le h) b) : MulAut (Model F)) =
            MulAut.conj (e.middle b : Model F)) := by
  exact exists_original_extension_of_native_flag h
    (endpoint F short) (endpoint F (!short)) (Atlas.G2.borel (K := F))
    (borel_le_endpoint F short) (borel_le_endpoint F (!short))
    (endpoints_inf F short) (endpoints_generate F short)
    (conj_injective_of_center_eq_bot (model_center_eq_bot hq))
    (inner_flag F short) (native_lifts F hq short) e



omit [CharP F 2] in
/-- In the binary row the entire native Borel has order 64. -/
theorem binary_borel_isPGroup (hF : Nat.card F = 2) :
    IsPGroup 2 (Atlas.G2.borel (K := F)) := by
  apply IsPGroup.of_card (n := 6)
  rw [card_borel,hF]
  norm_num

omit [CharP F 2] in
/-- The binary full G₂ row has no original enlargement: the reduced and
original Sylows, and hence both endpoints and the full middle, coincide. -/
theorem original_sylow_eq_reduced_of_card_two
    {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}
    (h : HypothesisF11 L S) (hF : Nat.card F = 2) (short : Bool)
    (e : Iso (reducedAmalgam L S) (amalgam F short)) :
    S = SuzukiContainment.reducedSylow L S :=
  BinaryBorel.original_sylow_eq_reduced h
    ((binary_borel_isPGroup F hF).of_injective e.middle.toMonoidHom e.middle.injective)

/-- The binary marking is restored by identity on original ambient elements,
without replacing full G₂(2) by its derived subgroup. -/
def originalIsoOfCardTwo
    {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}
    (h : HypothesisF11 L S) (hF : Nat.card F = 2) (short : Bool)
    (e : Iso (reducedAmalgam L S) (amalgam F short)) :
    Iso (originalAmalgam L S) (amalgam F short) :=
  (NativeRestoration.originalIsoReduced
    (original_sylow_eq_reduced_of_card_two F h hF short e)).trans e

end CFSG.Quasithin.ChapterF.Source.DGS85.OriginalExtension.G2Native
