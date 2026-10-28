module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components.Triangle.ReselectedNatural
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components.Refinement.FirstPrimeLinear
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Triangle.Reselection.Geometry.Forward.Plane
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Triangle.Reselection.Geometry.Forward.Cartan
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Triangle.Reselection.Geometry.Forward.PointOrbit
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.FlagCartan.G2.SourceFixed

/-!
# The reselected point and both original flag residuals

In source 11.1.2, once the containing component K centralizes the Sylow
omega-center Z, the reselected fixed layer must vanish. Otherwise its
intersection with Z is a nontrivial two-subgroup centralized by IT and K.
Nonsolvable uniqueness puts K in N_G(I), then puts L in N_G(I), and
identifies this maximal local subgroup with N_G(L). That contradicts the
strict original component enlargement. This uses only earlier uniqueness,
not the later shadow theorem 11.3.2.

The unchanged natural quotient now places K₀ in the new point residual.
Rank-one covering makes that containment equality. Full-Sylow parabolic
placement identifies the original L₂ with the new plane residual, without
assuming an orientation of the triangle. Its exact second radical is
therefore unchanged. Finally the actual Sp₄/G₂ fixed-line calculation,
including the O₂(IT) term in source T_I, supplies the Cartan-orbit input
used to centralize the entire new point by K.

ReselectedPointSp4 applies these results to the literal common-Q join.
The earlier assertion [Z,K] = 1 remains explicit, as do the original
7.0.1 and 3.2.5 inputs there. Its maximal-envelope/FF proof, common-normal
existence, source SL₃(4) exclusion, both final orientations and full 11.1.2
assembly remain with qt-d-1222-natural-relative-components. Earlier-source
discharge remains with qt-d-1222-natural-local-geometry.
Source: Aschbacher--Smith, 11.1.2, printed p.764, using 1.2.7(3).
-/

set_option backward.isDefEq.respectTransparency false
open Subgroup Theory.GroupTheory Representation
open CFSG.Quasithin.Chapter12.Section02 CFSG.Quasithin.ChapterB.QuasisimpleSource
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components.Triangle
open ShadowReduction.ComponentGeometry ShadowReduction.ComponentGeometry.Triangle.Reselection
public noncomputable section
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G}
    {L V I U : Subgroup G}

/-- The original nonsolvable uniqueness argument kills the reselected fixed
layer once the strict first component centralizes the Sylow omega-center. -/
theorem reselected_fixed_eq_bot_of_component_centralizes_omega
    (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)
    {c : Coordinates D S.field} (f : InvariantFlag c)
    (hm : ClassicalGroup.IsPSL (f.Li 0 ⧸ pCore 2 (f.Li 0)) 2 (2^S.field.degree))
    (hgen : f.Li 0 ⊔ f.Li 1 = L)
    {K : Subgroup G} (hK : Source.ComponentIn (normalizer (f.Vi 0 : Set G)) K)
    (hLK : f.Li 0 < K)
    (hKZ : K ≤ centralizer
      (omegaOneAmbient ((center (T : Subgroup G)).map (T : Subgroup G).subtype) : Set G))
    (D_I : ChosenModule T I U) (S_I : D_I.NonbinaryNaturalInput)
    (hLI : f.Li 1 ≤ I) : U ⊓ centralizer (I : Set G) = ⊥ := by
  by_contra hne
  let C := U ⊓ centralizer (I : Set G)
  let Z := omegaOneAmbient ((center (T : Subgroup G)).map (T : Subgroup G).subtype)
  have hTC : (T : Subgroup G) ≤ normalizer (C : Set G) :=
    (le_inf S_I.sylow_normalizes (D_I.sylow_normalizes_component.trans
      (normalizer_le_normalizer_centralizer I))).trans inf_normalizer_le_normalizer_inf
  have hPne : Z ⊓ C ≠ ⊥ := fun he => hne
    (eq_bot_of_normalized_of_omega_center_disjoint (T : Subgroup G) C
      T.isPGroup' (inf_le_left.trans D_I.le_sylow) hTC he)
  have hZT : Z ≤ centralizer (T : Set G) := by
    rintro z hz t ht
    obtain ⟨a,ha,rfl⟩ := omegaOneAmbient_le _ hz
    exact congrArg (T : Subgroup G).subtype (mem_center_iff.mp ha ⟨t,ht⟩)
  have hIP : I ⊔ (T : Subgroup G) ≤ normalizer ((Z ⊓ C : Subgroup G) : Set G) :=
    (sup_le (le_centralizer_iff.mp (inf_le_right.trans inf_le_right))
      (le_centralizer_iff.mp (inf_le_left.trans hZT))).trans
        (Subgroup.centralizer_le_normalizer _)
  have htwo : IsPGroup 2 (Z ⊓ C : Subgroup G) :=
    T.isPGroup'.to_le (inf_le_right.trans (inf_le_left.trans D_I.le_sylow))
  have huI := Chapter1.Section02.nonsolvable_uniqueness_knownSimple
    S_I.source.simpleQTKE T S_I.source.maximal_faithful.1
  have huL := Chapter1.Section02.nonsolvable_uniqueness_knownSimple
    S.source.simpleQTKE T S.source.maximal_faithful.1
  have huniq : ∀ M : Subgroup G, IsMaximalTwoLocal M →
      I ⊔ (T : Subgroup G) ≤ M → M = normalizer (I : Set G) := by
    simpa only [D_I.localOrbit_eq] using huI.normalizer_unique
  have hbound := normalizer_le_of_unique_maximalTwoLocal huniq htwo hPne hIP
  have hKN : K ≤ normalizer (I : Set G) :=
    ((hKZ.trans (centralizer_le inf_le_left)).trans
      (Subgroup.centralizer_le_normalizer _)).trans hbound
  have hLN : L ≤ normalizer (I : Set G) := by
    rw [← hgen]
    exact sup_le (hLK.le.trans hKN) (hLI.trans I.le_normalizer)
  have hmax : IsMaximalTwoLocal (normalizer (I : Set G)) := by
    simpa only [D_I.localOrbit_eq] using huI.normalizer_maximal
  have hsame : normalizer (I : Set G) = normalizer (L : Set G) := by
    simpa only [D.localOrbit_eq] using huL.normalizer_unique _ hmax
      (sup_le hLN D_I.sylow_normalizes_component)
  exact hLK.ne (flag_component_eq_of_le_component_normalizer D S f 0 hm hK hLK.le
    (hsame ▸ hKN))

/-- Full-Sylow placement in either simple natural field-four model does not
require a prior orientation relative to the original vertex. -/
theorem simple_four_local_eq_flag_residual
    (D : ChosenModule T I U) (S : D.NonbinaryNaturalInput)
    (hd : S.field.degree = 2)
    (hm : Source.IsSp (I ⧸ pCore 2 I) 2 4 ∨
      ClassificationModels.IsG2At (I ⧸ pCore 2 I) 4)
    {c : Coordinates D S.field} (f : InvariantFlag c) (hu : f.IsInnerUnique)
    (A : Subgroup G) (hA : A ∈ Chapter1.L G T) (hAI : A < I)
    (hTA : (T : Subgroup G) ≤ normalizer (A : Set G)) :
    A = f.Li 0 ∨ A = f.Li 1 := by
  cases c with
  | sp4 m => exact symplectic_local_eq_flag_residual D S m f hu A hA hAI hTA
  | g2 m => exact g2_local_eq_flag_residual D S m f hu A hA hAI hTA
  | sl3 m =>
    have hc := (simple_four_model_data hm).2
    have hF : Nat.card S.field.Carrier = 4 := by simpa [hd] using S.field.card_eq
    rw [Nat.card_congr m.groupEquiv.toEquiv,
      Matrix.PSL3.LinearThree.DefiningSylow.card_specialLinear, hF] at hc
    norm_num [ShadowReduction.ComponentGeometry.Triangle.Reselection.Classification.FieldFourOrder] at hc

/-- The actual other residual is the new first residual and the original
second residual remains the second. The reselected fixed layer is killed by
nonsolvable uniqueness, not by a later shadow theorem. -/
theorem reselected_paired_flag_of_component_centralizes_omega
    (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)
    {c : Coordinates D S.field} (f : InvariantFlag c)
    (hm : ClassicalGroup.IsPSL (f.Li 0 ⧸ pCore 2 (f.Li 0)) 2 (2^S.field.degree))
    (hgen : f.Li 0 ⊔ f.Li 1 = L)
    {K K₀ : Subgroup G} (hK : Source.ComponentIn (normalizer (f.Vi 0 : Set G)) K)
    (hLK : f.Li 0 < K) (hK₀ : K₀ ∈ Chapter1.L G T) (hK₀K : K₀ ≤ K)
    (hK₀I : K₀ < K₀ ⊔ f.Li 1) (hLI : f.Li 1 < K₀ ⊔ f.Li 1)
    (hKZ : K ≤ centralizer
      (omegaOneAmbient ((center (T : Subgroup G)).map (T : Subgroup G).subtype) : Set G))
    (D_I : ChosenModule T (K₀ ⊔ f.Li 1) U) (S_I : D_I.NonbinaryNaturalInput)
    (hd : S_I.field.degree = 2)
    (hmI : Source.IsSp ((K₀ ⊔ f.Li 1 : Subgroup G) ⧸ pCore 2 (K₀ ⊔ f.Li 1 : Subgroup G)) 2 4 ∨
      ClassificationModels.IsG2At
        ((K₀ ⊔ f.Li 1 : Subgroup G) ⧸ pCore 2 (K₀ ⊔ f.Li 1 : Subgroup G)) 4) :
    U ⊓ centralizer ((K₀ ⊔ f.Li 1 : Subgroup G) : Set G) = ⊥ ∧
      ∃ f_I : InvariantFlag (coordinates D_I S_I), f_I.IsInnerUnique ∧
        K₀ ≤ centralizer (f_I.Vi 0 : Set G) ∧
        f_I.Li 0 = K₀ ∧ f_I.Li 1 = f.Li 1 ∧ f_I.Ri 1 = f.Ri 1 := by
  have hf := reselected_fixed_eq_bot_of_component_centralizes_omega
    D S f hm hgen hK hLK hKZ D_I S_I le_sup_right
  obtain ⟨f_I,_,hu,_,_⟩ := exists_unique_marked_flag D_I S_I (coordinates D_I S_I)
  have hp := triangle_other_le_firstResidual D_I S_I f_I rfl hK₀ hK₀K hKZ hf
  have hfirst := triangle_other_eq_firstResidual D_I S_I f_I rfl hK₀ hK₀K hKZ hf
  have hsecond : f_I.Li 1 = f.Li 1 := by
    rcases simple_four_local_eq_flag_residual D_I S_I hd hmI f_I hu (f.Li 1)
      (flag_residual_mem_local D S f 1) hLI (f.sylow_normalizes_Li 1) with he | he
    · rw [hfirst] at he
      exact (hK₀I.ne (by rw [he,sup_idem])).elim
    · exact he.symm
  refine ⟨hf,f_I,hu,hp.1,hfirst,hsecond,?_⟩
  change (f_I.Li 1 ⊔ (T : Subgroup G)).pCoreIn 2 =
    (f.Li 1 ⊔ (T : Subgroup G)).pCoreIn 2
  rw [hsecond]

private theorem sp4_fixed_line
    (D : ChosenModule T I U) (S : D.NonbinaryNaturalInput)
    (m : ActionEquiv D.centralQuotientAction (binarySymplectic S.field))
    (hf : U ⊓ centralizer (I : Set G) = ⊥) :
    (Sp4.flag m S).Vi 0 = U ⊓ centralizer (((T : Subgroup G) ⊓ I : Subgroup G) : Set G) := by
  ext v
  constructor
  · intro hv
    have hvU := D.centralQuotientPreimage_le _ hv
    refine ⟨hvU,?_⟩
    intro t ht
    have hc := (Sp4.mem_preimage_succ_iff m 0 ⟨v,hvU⟩).mp hv ⟨t,ht.2⟩ ht.1
    change t * v * t⁻¹ * v⁻¹ ∈ (Coordinates.sp4 m).preimage (Sp4.space m 0) at hc
    rw [Sp4.space_zero,Coordinates.preimage_bot,hf] at hc
    have he := mem_bot.mp hc
    have he' : t * v * t⁻¹ = v := mul_inv_eq_one.mp he
    exact mul_inv_eq_iff_eq_mul.mp he'
  · rintro ⟨hvU,hv⟩
    apply (Sp4.mem_preimage_succ_iff m 0 ⟨v,hvU⟩).mpr
    intro t ht
    change (t : G) * v * (t : G)⁻¹ * v⁻¹ ∈ (Coordinates.sp4 m).preimage (Sp4.space m 0)
    rw [Sp4.space_zero,Coordinates.preimage_bot,hf]
    apply mem_bot.mpr
    rw [hv t ⟨ht,t.property⟩]
    group

private theorem g2_fixed_line
    (D : ChosenModule T I U) (S : D.NonbinaryNaturalInput)
    (m : ActionEquiv D.centralQuotientAction (binaryG2 S.field))
    (hf : U ⊓ centralizer (I : Set G) = ⊥) :
    (G2.flag S m).Vi 0 = U ⊓ centralizer (((T : Subgroup G) ⊓ I : Subgroup G) : Set G) := by
  apply le_antisymm _ (G2.inner_fixed_le_first S m)
  intro v hv
  have hvU := D.centralQuotientPreimage_le _ hv
  refine ⟨hvU,?_⟩
  intro t ht
  let a : I := ⟨t,ht.2⟩
  let u : U := ⟨v,hvU⟩
  let c := Coordinates.g2 m
  have hinj : Function.Injective c.projection :=
    c.linearEquiv.toAddEquiv.toMultiplicative.injective.comp (centralQuotient_injective D hf)
  have hp := (c.mem_preimage _ u).mp hv
  have ha : G2.derivedMap S m a ∈ (G2.modelSylow S m : Subgroup _) := by
    apply mem_map_of_mem
    rw [G2.innerSylow_coe]
    exact ht.1
  have he := ((G2.modelFlag S m).first _).mp hp ⟨G2.derivedMap S m a,ha⟩
  have he' : c.modelAction (c.quotientMap a) (c.projection u).toAdd =
      (c.projection u).toAdd := he
  have hconj : U.normalizerMonoidHom (inclusion D.normalizes a) u = u := by
    apply hinj
    apply Multiplicative.toAdd.injective
    exact (c.projection_component_conjugation a u).trans he'
  have heq : t * v * t⁻¹ = v := congrArg Subtype.val hconj
  exact mul_inv_eq_iff_eq_mul.mp heq

/-- With its central layer removed, the actual first preimage is the fixed
subgroup of the source T_I, including O₂(IT). No later flag identity is assumed. -/
theorem simple_four_fixed_line
    (D : ChosenModule T I U) (S : D.NonbinaryNaturalInput)
    (hd : S.field.degree = 2)
    (hm : Source.IsSp (I ⧸ pCore 2 I) 2 4 ∨
      ClassificationModels.IsG2At (I ⧸ pCore 2 I) 4)
    (hf : U ⊓ centralizer (I : Set G) = ⊥)
    {c : Coordinates D S.field} (f : InvariantFlag c) :
    f.Vi 0 = U ⊓ centralizer (sourceTL T I : Set G) := by
  have hi : f.Vi 0 = U ⊓ centralizer (((T : Subgroup G) ⊓ I : Subgroup G) : Set G) := by
    cases c with
    | sp4 m =>
      have he : f.space 0 = (Sp4.flag m S).space 0 :=
        Sp4.flag_inner_unique m S 0 (f.space 0) (f.dimension 0)
          (inf_le_left.trans (f.invariant 0))
      change (Coordinates.sp4 m).preimage (f.space 0) = _
      rw [he]
      exact sp4_fixed_line D S m hf
    | g2 m =>
      have he : f.space 0 = (G2.flag S m).space 0 :=
        G2.flag_inner_unique S m 0 (f.space 0) (f.dimension 0)
          (inf_le_left.trans (f.invariant 0))
      change (Coordinates.g2 m).preimage (f.space 0) = _
      rw [he]
      exact g2_fixed_line D S m hf
    | sl3 m =>
      have hc := (simple_four_model_data hm).2
      have hF : Nat.card S.field.Carrier = 4 := by simpa [hd] using S.field.card_eq
      rw [Nat.card_congr m.groupEquiv.toEquiv,
        Matrix.PSL3.LinearThree.DefiningSylow.card_specialLinear,hF] at hc
      norm_num [ShadowReduction.ComponentGeometry.Triangle.Reselection.Classification.FieldFourOrder] at hc
  apply le_antisymm
  · refine le_inf (D.centralQuotientPreimage_le _) ?_
    apply le_centralizer_iff.mp
    rw [sourceTL_eq_sup_core]
    exact sup_le (le_centralizer_iff.mp (hi ▸ inf_le_right))
      (D.core_centralizes.trans (centralizer_le (D.centralQuotientPreimage_le _)))
  · rw [hi]
    exact inf_le_inf_left _ (centralizer_le sylow_intersection_le_sourceTL)

end
end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components.Triangle
