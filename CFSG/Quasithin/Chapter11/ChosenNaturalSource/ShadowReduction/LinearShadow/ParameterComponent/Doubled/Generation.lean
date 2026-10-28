module

public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.LinearShadow.ParameterComponent
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Preliminary.Module
public import Theory.Representation.BinaryConjugationSection
public import Theory.Representation.BinaryGroupAction

/-!
# E-generation for the actual doubled module

The preceding doubled-natural marking is a faithful coordinate map on the
literal subgroup V_M, so it gives elementarity and order 2^(6n). The E.3.20
argument works on this module while keeping the original D, S, H and omega
orbit. Once the doubled weak-closure and s-value have been proved, it forces
k = 2n and collapses the component supplied by 11.3.5 to the actual O²(H).

The two geometric inputs remain explicit here. In particular this module
does not assert weak-closure escape or the full exclusion in 11.3.6.
Source: Aschbacher--Smith, 11.3.6, printed p.772.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory Representation
open CFSG.Quasithin.ChapterB.QuasisimpleSource
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ParameterComponent.Doubled
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    {D : Chapter12.Section02.ChosenModule T L V} {S : D.NonbinaryNaturalInput}
    {U₁ : Submodule (ZMod 2) D.chosenCentralQuotient} {H : Subgroup G}

/-- The exact coordinate proposition underlying the preceding
`LocalGeometry.WeakClosure.Generation.DoubledNatural`. It is written here with
its exposed body so that the original source witness can be supplied by
reduction, without importing the unrelated bounds in its statement bundle.
The original quotient, field and full subgroup are unchanged. -/
abbrev Coordinates (D : Chapter12.Section02.ChosenModule T L V)
    (S : D.NonbinaryNaturalInput) : Prop :=
  ∃ m : ActionEquiv D.centralQuotientAction (linearNatural S.field 3),
    Nonempty (BinaryConjugationSection L
      (Source.conjugateSpan (normalizer (L : Set G)) V) ⊥
      ((repeated (linearNatural S.field 3) 2).comp
        (m.groupEquiv.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L)))))

/-- The full module in 11.3.6, with the original normalizer and seed. -/
def fullModule (L V : Subgroup G) : Subgroup G :=
  Source.conjugateSpan (normalizer (L : Set G)) V

omit [Finite G] in
theorem normalizes_fullModule :
    normalizer (L : Set G) ≤ normalizer (fullModule L V : Set G) := by
  rw [fullModule, Source.conjugateSpan, ← conjugateSpanBy_eq_iSup_conj]
  exact le_normalizer_conjugateSpanBy _ _

instance fullModule_relative_normal :
    ((fullModule L V).subgroupOf (normalizer (L : Set G))).Normal :=
  normal_subgroupOf_of_le_normalizer normalizes_fullModule

/-- Faithful doubled coordinates give elementarity of V_M itself. -/
theorem fullModule_elementary (d : Coordinates D S) :
    IsElementaryAbelian 2 (fullModule L V) := by
  obtain ⟨m,⟨c⟩⟩ := d
  let : IsElementaryAbelian 2 (Multiplicative (Fin 2 → Fin 3 → S.field.Carrier)) :=
    BinaryGroupAction.elementary
  apply IsElementaryAbelian.of_injective c.coordinates
  apply c.coordinates.ker_eq_bot_iff.mp
  rw [c.kernel_eq, bot_subgroupOf]

/-- The marking covers all of V_M, including any possible central part. -/
theorem fullModule_card (d : Coordinates D S) :
    Nat.card (fullModule L V) = 2 ^ (6 * S.field.degree) := by
  obtain ⟨m,⟨c⟩⟩ := d
  have he := c.card_section
  change Nat.card (fullModule L V) = _ at he
  have hc : Nat.card (fullModule L V) = 2 ^ (S.field.degree * 3 * 2) := by
    simpa only [Nat.card_fun, Nat.card_fin, Subgroup.card_bot, mul_one,
      S.field.card_eq, ← pow_mul] using he
  convert hc using 1
  congr 1
  omega

/-- The normalizer is exactly M, by maximality among genuine two-locals. -/
theorem fullModule_normalizer (d : Coordinates D S) :
    normalizer (fullModule L V : Set G) = normalizer (L : Set G) := by
  let := fullModule_elementary d
  have hne : fullModule L V ≠ ⊥ := by
    intro hz
    have he := fullModule_card d
    rw [hz,Subgroup.card_bot] at he
    have hb : 2 ≤ 2 ^ (6 * S.field.degree) := by
      calc
        2 = 2 ^ 1 := by decide
        _ ≤ _ := Nat.pow_le_pow_right (by decide) (by have := S.nonbinary; omega)
    omega
  have hlocal : IsTwoLocal (normalizer (fullModule L V : Set G)) :=
    ⟨fullModule L V,hne,IsElementaryAbelian.isPGroup 2 _,rfl⟩
  exact le_antisymm
    ((LocalGeometry.Preliminary.normalizer_maximal D S).2 hlocal normalizes_fullModule)
    normalizes_fullModule

/-- Normality is relative to M; the module then lies in its prescribed Sylow. -/
theorem fullModule_le_sylow (d : Coordinates D S) :
    fullModule L V ≤ (T : Subgroup G) := by
  let := fullModule_elementary d
  let M := normalizer (L : Set G)
  have hWM : fullModule L V ≤ M := by
    obtain ⟨_,⟨c⟩⟩ := d
    exact c.section_le.trans L.le_normalizer
  let : ((fullModule L V).subgroupOf M).Normal :=
    normal_subgroupOf_of_le_normalizer normalizes_fullModule
  have hp : IsPGroup 2 ((fullModule L V).subgroupOf M) :=
    (IsElementaryAbelian.isPGroup 2 (fullModule L V)).comap_subtype (K := M)
  have he := map_mono (f := M.subtype)
    (hp.le_sylow_of_normal (T.subtype D.sylow_normalizes_component))
  have hTM : ((T : Subgroup G).subgroupOf M).map M.subtype = T :=
    map_subgroupOf_eq_of_le (show (T : Subgroup G) ≤ M from D.sylow_normalizes_component)
  simpa only [Sylow.coe_subtype, map_subgroupOf_eq_of_le hWM, hTM] using he

/-- E.3.20 applied to V_M, without changing the original chosen seed. -/
theorem parameter_lower (h : Hypothesis1131At D S U₁ H)
    (d : Coordinates D S)
    (hw : ¬ ChapterE.indexedWeakClosure (fullModule L V) (T : Subgroup G) 0 ≤
      H.pCoreIn 2) :
    letI := fullModule_elementary d
    ChapterE.globalS (fullModule L V) ≤ (ChapterE.generationParameter H : ℕ∞) := by
  let := fullModule_elementary d
  exact globalS_le_parameter_for h (fullModule L V) hw

/-- The source rank comparison forces k=2n, before the final contradiction. -/
theorem parameter_eq_twice (h : Hypothesis1131At D S U₁ H)
    (d : Coordinates D S)
    (hw : ¬ ChapterE.indexedWeakClosure (fullModule L V) (T : Subgroup G) 0 ≤
      H.pCoreIn 2)
    (hs : @ChapterE.globalS G _ (fullModule L V) (fullModule_elementary d) =
      (2 * S.field.degree : ℕ∞))
    (hu : ChapterE.generationParameter H ≤ 2 * S.field.degree) :
    ChapterE.generationParameter H = 2 * S.field.degree := by
  have hl := parameter_lower h d hw
  rw [hs] at hl
  exact Nat.le_antisymm hu (ENat.natCast_le_natCast.mp hl)

/-- 11.3.5 now identifies the literal residual, with relative normality and
its own two-core quotient. No residual equality is assumed. -/
theorem residual_component (h : Hypothesis1131At D S U₁ H)
    (d : Coordinates D S) (r : RankOneReduction S H)
    (hw : ¬ ChapterE.indexedWeakClosure (fullModule L V) (T : Subgroup G) 0 ≤
      H.pCoreIn 2)
    (hs : @ChapterE.globalS G _ (fullModule L V) (fullModule_elementary d) =
      (2 * S.field.degree : ℕ∞))
    (hu : ChapterE.generationParameter H ≤ 2 * S.field.degree) :
    Source.NormalComponentIn H (residual H) ∧
      ClassicalGroup.IsPSL ((residual H) ⧸ pCore 2 (residual H))
        2 (2 ^ (2 * S.field.degree)) := by
  have hk := parameter_eq_twice h d hw hs hu
  obtain ⟨K,hK,_,hm,hcollapse⟩ := r
  have he := hcollapse (.inr hk)
  subst K
  exact ⟨⟨hK,residual_normal H⟩,by simpa only [hk] using hm⟩

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ParameterComponent.Doubled
