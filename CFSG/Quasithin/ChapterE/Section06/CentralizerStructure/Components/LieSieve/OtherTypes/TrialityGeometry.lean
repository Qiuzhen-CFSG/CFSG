module

public import CFSG.Quasithin.ChapterE.Section06.CentralizerStructure.Components.LieSieve.OtherTypes.Setup
public import CFSG.Quasithin.ChapterE.Section06.CentralizerStructure.Components.LieSieve.OtherTypes.TrialityGeometry.Transport
public import CFSG.Quasithin.ChapterE.Section06.CentralizerStructure.Components.LieSieve.OtherTypes.TrialityGeometry.Normalization
public import CFSG.Quasithin.ChapterE.Section06.CentralizerStructure.Components.LieSieve.OtherTypes.TrialityGeometry.BlockTransfer
public import CFSG.Quasithin.ChapterE.Section06.CentralizerStructure.Components.LieSieve.OtherTypes.TrialityGeometry.IntrinsicBlocks
public import CFSG.Quasithin.ChapterE.Section06.CentralizerStructure.Components.LieSieve.OtherTypes.TrialityGeometry.ModelSeparation
public import CFSG.Quasithin.ChapterE.Section06.CentralizerStructure.Components.LieSieve.OtherTypes.TrialityGeometry.LocalExtensions
public import Theory.SpecificGroups.Triality.ParabolicGeometry
public import Theory.SpecificGroups.Triality.Model.QTKE

/-!
# The genuine triality branch of E.6.8

The exact field-order predicate identifies L with the binary D4 graph-field
carrier. Sylow conjugacy then marks its positive subgroup as the actual Q ∩ L.
The transport module constructs the images of both parabolics in the literal
quotient (L Q_L)/O₂(L Q_L), and proves the generation and pullback identities.

`triality_geometry` proves Q-normalization and constructs the complete
block-free quotient family. The sole earlier source input is the full universal
1.2.1(3) alternative: model separation excludes its four nonnormal-component
models. The concrete finite root geometry supplies the Sylow subgroup and
parabolic generation. `LocalExtensions` proves invariance and characteristic
two in the actual joins with Q. `IntrinsicBlocks` excludes relatively subnormal
chi-zero blocks in both parabolics, and `BlockTransfer` lifts this exclusion
through the two-group supplement. Every model premise is thus discharged,
including at q = 2. The E.6.7 application and final exclusion remain with the
OtherTypes assembly.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), E.6.8,
printed pp.247–248 (PDF pp.258–259).
-/

public section
noncomputable section

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterE.Section06.Components.OtherTypes.TrialityGeometry
open _root_.Triality.Standard

variable {G : Type*} [Group G] [Finite G]
variable {K : GroupClass} {T : Sylow 2 G} {M V U Q L : Subgroup G}

/-- Align the actual model at the specified binary field order. The root Sylow
assertion is supplied by the finite geometry, not inferred from its name. -/
theorem exists_marked_binary_model_equiv (h : HypothesisE61 K T M V)
    (hU : U ∈ obstructionFamily M V)
    (hL : ComponentIn (centralizer (U : Set G)) L)
    (hQ : Q = sylowCentralizer (T : Subgroup G) V)
    (f : ℕ) (hf : 1 ≤ f) (hm : IsTrialityGroupAt (2 ^ f) L)
    (hSylow : ∃ S : Sylow 2 (BinaryCarrier f (by omega)),
      (S : Subgroup _) = Parabolics.unipotent (binaryParameters f (by omega))) :
    ∃ e : L ≃* BinaryCarrier f (by omega),
      (Q.subgroupOf L).map e.toMonoidHom =
        Parabolics.unipotent (binaryParameters f (by omega)) := by
  obtain ⟨e⟩ := (isTrialityGroupAt_binary_iff L f (by omega)).mp hm
  exact exists_marked_model_equiv h hU hL hQ e hSylow

/-- The conditional deduction consumed by the final assembly: mark the model,
transport automorphism invariance, absorb the quotient kernel in Q, and lift
intrinsic block exclusion through the two-group supplement. All local model
premises below still need their separate proofs. -/
theorem family_of_marked_model_calculations (h : HypothesisE61 K T M V)
    (hU : U ∈ obstructionFamily M V)
    (hL : ComponentIn (centralizer (U : Set G)) L)
    (hQ : Q = sylowCentralizer (T : Subgroup G) V)
    (hN : Q ≤ normalizer (L : Set G))
    {P : Parameters} (e : L ≃* Carrier P)
    (hmark : (Q.subgroupOf L).map e.toMonoidHom = Parabolics.unipotent P)
    (hgen : Parabolics.parabolic P .arms ⊔ Parabolics.parabolic P .central = ⊤)
    (hstable : ∀ a (β : MulAut (Carrier P)),
      (Parabolics.unipotent P).map β.toMonoidHom = Parabolics.unipotent P →
      (Parabolics.parabolic P a).map β.toMonoidHom = Parabolics.parabolic P a)
    (hchar : ∀ a, HasCharacteristicTwo (parabolicJoin Q e a))
    (hfree : ∀ a, NoChiZeroBlocks (componentParabolic e a)) :
    Nonempty (BlockFreeQuotientFamily Q L) := by
  have hinv (a : Parabolics.Node) : Q ≤ normalizer (componentParabolic e a : Set G) := by
    simpa only [componentNormalizer_eq hN] using
      componentParabolic_invariant_of_stabilizer e hmark a (hstable a)
  have hQp : IsPGroup 2 Q := by
    rw [hQ]
    exact T.isPGroup'.to_le inf_le_left
  exact family_of_local_parabolics h hU hL hQ hN e hgen hinv hchar
    (fun a => noChiZeroBlocks_sup hQp (hinv a) (hfree a))

/-- Construct both invariant parabolics in the literal component quotient.
The actual positive Sylow subgroup, generation, characteristic-two joins and
relative block exclusions discharge all the conditional model premises. -/
theorem family_of_normalizes (h : HypothesisE61 K T M V)
    (hU : U ∈ obstructionFamily M V)
    (hL : ComponentIn (centralizer (U : Set G)) L)
    (hQ : Q = sylowCentralizer (T : Subgroup G) V)
    (hN : Q ≤ normalizer (L : Set G))
    {f : ℕ} (hf : 1 ≤ f) (hm : IsTrialityGroupAt (2 ^ f) L) :
    Nonempty (BlockFreeQuotientFamily Q L) := by
  obtain ⟨e, hmark⟩ := exists_marked_binary_model_equiv h hU hL hQ f hf hm
    ⟨Parabolics.unipotentSylow (binaryParameters f (by omega)) rfl, rfl⟩
  obtain ⟨hstable, hchar⟩ := local_extension_calculations h hU hL hQ hN rfl e hmark
  exact family_of_marked_model_calculations h hU hL hQ hN e hmark
    (Parabolics.parabolic_sup_binary _ rfl) hstable hchar (noChiZeroBlocks rfl e)

/-- The E.6.8 invariant-parabolic construction for exactly
`RankTwoTheoremC.triality`, including q = 2. Only the full universal source
1.2.1(3) statement remains explicit; no model calculation is assumed. -/
theorem triality_geometry (h : HypothesisE61 K T M V)
    (hU : U ∈ obstructionFamily M V)
    (hL : ComponentIn (centralizer (U : Set G)) L)
    (hQ : Q = sylowCentralizer (T : Subgroup G) V)
    (source : ∀ H : Subgroup G, H ∈ Chapter1.H G → ∀ B : Subgroup H,
      B.IsCComponent → B.Normal ∨ (normalizer (B : Set H)).index = 2 ∧
        Chapter1.Section02.NonnormalCComponentModel (B ⧸ pCore 2 B))
    {f : ℕ} (hf : 1 ≤ f) (hm : IsTrialityGroupAt (2 ^ f) L) :
    Q ≤ normalizer (L : Set G) ∧ Nonempty (BlockFreeQuotientFamily Q L) := by
  let : IsQuasisimple L := IsComponentIn.quasisimple hL
  have hN := normalizes_of_source_1_2_1 h hU hL hQ source
    (not_nonnormalCComponentModel hf hm)
  exact ⟨hN, family_of_normalizes h hU hL hQ hN hf hm⟩

end CFSG.Quasithin.ChapterE.Section06.Components.OtherTypes.TrialityGeometry
