module

public import CFSG.Quasithin.Chapter13.Section07.ModelExclusions.Theta
public import CFSG.Quasithin.Chapter13.Section07.ModelExclusions.ComponentNormality
public import CFSG.Quasithin.Chapter13.Section08.SourceCompletion.Fitting.Standing

/-!
# The original component exclusion from the local normalizer

The genuine earlier13.3.9 forces a normal two-perfect subgroup in M,
centralizing the prescribed point, to be trivial or one of the soluble
point residuals. A C-component is nonsoluble, so it cannot lie in M.
All marked models and point-action hypotheses are built from NaturalSetup,
before any abelian conjugate-span conclusion. The universal earlier13.3.9
is retained for its source owner; no component-exclusion conclusion is input.

Source: Aschbacher–Smith,13.3.9, p.887;13.7.5(7), p.938.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section07.ModelExclusions
open Section08.SourceCompletion
open Section08.TransvectionRecognition.Component.ModelExtension
open Section08.ComponentSieve.FieldComponents.LinearThree.Geometry.CoveredProduct.ResidualPlacement
open Section08.SolvableExclusion.Residual
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ M G₁ H K : Subgroup G}
  (d : NaturalSetup T L V V₁ V₂ V₃ M G₁)
include d

/-- Both actual local point residuals are soluble, including the covered case. -/
theorem point_residual_solvable : Group.IsSolvable (sourceOne L T V₁) := by
  have hp : IsPGroup 3 (sourceOne L T V₁ ⧸ pCore 2 (sourceOne L T V₁)) :=
    fun x => ⟨1, by simpa using point_residual_quotient_cube d x⟩
  let : Group.IsNilpotent (sourceOne L T V₁ ⧸ pCore 2 (sourceOne L T V₁)) := hp.isNilpotent
  let : Group.IsNilpotent (pCore 2 (sourceOne L T V₁)) := pCore_isNilpotent
  exact (Group.isSolvable_iff_subgroup_quotient (pCore 2 (sourceOne L T V₁))).mpr
    ⟨inferInstance, inferInstance⟩

private theorem centralCore_eq_point_action_kernel :
    centralCore L = (centralizer (V : Set G)).subgroupOf L := by
  ext l
  change l ∈ centralCore L ↔ l.val ∈ centralizer (V : Set G)
  constructor
  · intro hl
    have hq : QuotientGroup.mk' (centralCore L) l = 1 := (QuotientGroup.eq_one_iff l).mpr hl
    apply mem_centralizer_iff.mpr
    intro v hv
    have he := d.conjugation l ⟨v, hv⟩
    rw [hq, map_one, map_one, Module.End.one_apply] at he
    have he' := congrArg Subtype.val (d.coordinate.injective he)
    change l.val * v * l.val⁻¹ = v at he'
    exact (mul_inv_eq_iff_eq_mul.mp he').symm
  · intro hl
    apply (QuotientGroup.eq_one_iff l).mp
    apply d.local_quotient.injective
    rw [map_one]
    apply Section08.ComponentSieve.SixAndG2.NaturalSix.alternatingAction_injective
    apply LinearMap.ext
    intro w
    obtain ⟨v, hv⟩ := d.coordinate.surjective (Multiplicative.ofAdd w)
    have hv' : (d.coordinate v).toAdd = w := hv
    have hc : V.normalizerMonoidHom
        ⟨l.val, d.normalizes_V (mem_sup_left l.property)⟩ v = v := by
      apply Subtype.ext
      change l.val * v.val * l.val⁻¹ = v.val
      rw [← mem_centralizer_iff.mp hl v.val v.property, mul_inv_cancel_right]
    have he := d.conjugation l v
    rw [hc, hv'] at he
    simpa only [Section08.ComponentSieve.SixAndG2.NaturalSix.alternatingAction,
      QuotientGroup.mk'_apply, map_one, Module.End.one_apply] using he.symm

/-- The actual barred A₆ model required by13.3.9, without abelian span. -/
theorem barred_model : Nonempty (barImage M V L ≃* alternatingGroup (Fin 6)) := by
  have hLM : L ≤ M := d.local_normalizer ▸ L.le_normalizer
  have hLV : L ≤ normalizer (V : Set G) := le_sup_left.trans d.normalizes_V
  let J := M ⊓ normalizer (V : Set G)
  let f : J →* MulAut V := V.normalizerMonoidHom.comp (inclusion inf_le_right)
  let a : L →* MulAut V := f.comp (inclusion (le_inf hLM hLV))
  have hk : a.ker = centralCore L := by
    rw [centralCore_eq_point_action_kernel d]
    ext l
    change V.normalizerMonoidHom ⟨l.val, hLV l.property⟩ = 1 ↔ _
    rw [← MonoidHom.mem_ker, normalizerMonoidHom_ker]
    rfl
  have hr : a.range = barImage M V L := by
    change (f.comp (inclusion (le_inf hLM hLV))).range = (L.subgroupOf J).map f
    ext x
    constructor
    · rintro ⟨l, rfl⟩
      exact ⟨inclusion (le_inf hLM hLV) l, l.property, rfl⟩
    · rintro ⟨j, hj, rfl⟩
      exact ⟨⟨j.val, hj⟩, rfl⟩
  let eq : (L ⧸ centralCore L) ≃* a.range :=
    (QuotientGroup.quotientMulEquivOfEq hk.symm).trans (QuotientGroup.quotientKerEquivRange a)
  exact ⟨(MulEquiv.subgroupCongr hr).symm.trans (eq.symm.trans d.local_quotient)⟩

omit d in
private theorem perfect_twoPerfect {X : Type*} [Group X] [Finite X]
    [Group.IsPerfect X] : IsPPerfect 2 X := by
  intro N hN hp
  let := hN
  have hsub : Subsingleton (X ⧸ N) := by
    by_contra! hn
    exact Group.IsPerfect.not_isNilpotent (X ⧸ N) hp.isNilpotent
  apply eq_top_iff.mpr
  intro g _
  exact (QuotientGroup.eq_one_iff g).mp (Subsingleton.elim _ _)

/-- The original13.3.9 implication excludes every normal source component from M. -/
theorem normal_component_not_le_local
    (h1339 : Source1339 L (sourceOne L T V₁) (plus L T V₁) T M V V₁)
    (hH : H ∈ Section08.Source.Hz (sourceOne L T V₁) T G₁ M)
    (hKH : K ≤ H) (hK : (K.subgroupOf H).IsCComponent)
    (hKn : H ≤ normalizer (K : Set G)) : ¬ K ≤ M := by
  intro hKM
  let := hK.perfect
  let : Group.IsPerfect K := Group.IsPerfect.ofSurjective
    (f := (subgroupOfEquivOfLe hKH).toMonoidHom) (subgroupOfEquivOfLe hKH).surjective
  have hn : (K.subgroupOf H).Normal := (normal_subgroupOf_iff_le_normalizer hKH).mpr hKn
  have hJ : H ∈ Chapter1.HOutside G (T : Set G) (M : Set G) :=
    ⟨⟨hH.1.1, (show (T : Subgroup G) ≤ H from le_sup_right.trans hH.1.2)⟩, hH.2.2⟩
  obtain ⟨z, hz, _⟩ := (Nat.card_eq_two_iff' (1 : V₁)).mp d.line_card
  have hzV : (z : G) ∈ V := (d.line_le_plane.trans (d.plane_le_seed.trans d.seed_le)) z.property
  have hzc : (z : G) ∉ V ⊓ centralizer (L : Set G) := by
    intro hc
    have hm : (⟨z, hzV⟩ : V) ∈ (centralizer (L : Set G)).comap V.subtype := hc.2
    rw [NaturalModels.centralizer_bot d] at hm
    have heV : (⟨z, hzV⟩ : V) = 1 := mem_bot.mp hm
    have heG : (z : G) = 1 := congrArg (fun v : V => (v : G)) heV
    exact hz (Subtype.ext heG)
  have hc : K ≤ centralizer ({(z : G)} : Set G) := by
    have hg : G₁ ≤ centralizer (V₁ : Set G) := by
      rw [d.first_normalizer]
      exact normalizer_le_centralizer_of_card_two V₁ d.line_card
    exact ((hKH.trans hH.2.1).trans hg).trans
      (centralizer_le (Set.singleton_subset_iff.mpr z.property))
  have hs := h1339 (barred_model d) H K hJ hKH perfect_twoPerfect hn
    ⟨z, z.property, hzc, le_inf hKM hc⟩
  have hKL : K ≤ sourceOne L T V₁ := by
    rcases hs with hb | ⟨_, _, ho, hcov⟩
    · rw [hb]; exact bot_le
    · rcases NaturalModels.quotient_alternatives d with ⟨e, _⟩ | ⟨e, _⟩
      · exact (ho ⟨e⟩).le
      · have htr : Section08.SolvableExclusion.IsTripleCoverSix (L ⧸ pCore 2 L) :=
          ⟨source_core_quotient_quasisimple d,
            (Nat.card_congr (centerCongr e).toEquiv).trans Representation.Hexacode.even_center_card,
            ⟨source_central_quotient d⟩⟩
        rw [hcov htr]
        exact plus_le_one L T V₁ d.line_stable
  let := point_residual_solvable d
  let : Group.IsSolvable K := Group.isSolvable_of_isSolvable_injective
    (inclusion_injective hKL)
  exact hK.not_isSolvable (Group.isSolvable_of_isSolvable_injective
    (f := (subgroupOfEquivOfLe hKH).toMonoidHom) (subgroupOfEquivOfLe hKH).injective)

end CFSG.Quasithin.Chapter13.Section07.ModelExclusions
