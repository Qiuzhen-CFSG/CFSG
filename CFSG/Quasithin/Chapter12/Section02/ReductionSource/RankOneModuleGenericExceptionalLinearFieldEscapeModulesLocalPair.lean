module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalLinearFieldEscapeModulesLocalPair
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericExceptionalLinearFieldEscapeModulesLocalSpan
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.WeakClosureBounds.ModuleBound.OriginalF916

/-!
# The original local span and its cubic conjugates

Under the contrary nonabelian centralizer-span hypothesis, the original
H-span lies in W. Mutual containment and its already proved strict ratio
force its moving cubic conjugates into O₂(H). Their commutators lie in
two disjoint point lines, so they commute. Since C has order three and
moves the point, this covers every nonidentity element of C. Consequently
the C-span of the original H-span is elementary and lies in O₂(H).

All actions, conjugators and kernels are the original ones, and both
opposite-image factors remain allowed. This supplies additional ambient
constraints; it does not yet exclude the contrary centralizer span.

Source: Aschbacher--Smith 5.1.23 and the final paragraph of 5.1.14,
printed pp.645--646, refs/quasithin.pdf. Final source assembly remains
qt-d-1222-linear-field-cubic-escape; existence of the earlier cubic local
data retains its separate producer.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation.BinaryOffender
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source.RankOneGeneric CubicEscape ChapterG.Section02.Setup
open Chapter13.Section08
open Chapter15.Section03.AbelianAmalgam.ModuleBound
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V H A B C : Subgroup G} {n : ℕ} {z : G}

/-- The original elementary H-span commutes with its moving cubic conjugate,
which lies in the original O₂(H). Both opposite factors remain allowed. -/
theorem linear_cubic_nonabelian_local_pair
    (D : ChosenModule T L V)
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hK : residual H ∈ Chapter1.LStar G (T : Subgroup G))
    (hnf : ¬ ChapterA.Section04.IsFaithfulSignalizerType (residual H))
    (hlinear : ClassicalGroup.IsPSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 3 4)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    (c : LinearFieldCartan T L H A B C n)
    (d : CubicEscape.LocalData T H C z) (hn : 1 < n)
    (hne : ¬ IsMulCommutative (conjugateSpanBy (CubicEscape.plane C z)
      (centralizer ({z} : Set G))))
    (g : G) (hg : g ∈ C) (hgn : g ∉ normalizer (zpowers z : Set G)) :
    let U₀ := (setup T H C z).U
    ⁅U₀, conjugate U₀ g⁆ = ⊥ ∧ conjugate U₀ g ≤ H.pCoreIn 2 := by
  intro U₀
  let s := linear_cubic_centralizer_setup h d
  let b := d.binaryNaturalData c D.sylow_normalizes_component hpsl s hne
  let : IsElementaryAbelian 2 U₀ :=
    linear_cubic_local_span_elementary D h hH hK hnf hlinear hpsl c d hn
  let a := d.localSpanAction
  let q := OriginalF916.conjugationSection a d.H_centralizes_point
  obtain ⟨hf, hr⟩ := d.local_pair_containment s b g hg hgn
    (linear_cubic_nonabelian_local_span_le_W D h hH hK hnf hlinear hpsl c d hn hne g hg hgn)
  obtain ⟨he, _, hc⟩ := conjugate_pair_trivial_of_strict_ratio q d.point_card a.faithful
    (linear_cubic_quadraticRatio_gt_two (C := C) h hH hlinear z
      (show IsElementaryAbelian 2 (conjugateSpanBy (plane C z) H) from
        ‹IsElementaryAbelian 2 U₀›) a) g⁻¹ hf hr
  refine ⟨bot_unique (hc.trans (disjoint_iff.mp (b.point_disjoint g hgn)).le), ?_⟩
  intro x hx
  let x' : H := ⟨x, hf hx⟩
  have hm : QuotientGroup.mk' (pCore 2 H) x' ∈
      Source.starImage H (conjugate U₀ g) := mem_map_of_mem _ hx
  have hπ : QuotientGroup.mk' (pCore 2 H) x' = 1 := by
    change Source.starImage H (conjugate U₀ g) = ⊥ at he
    simpa only [he, mem_bot] using hm
  exact mem_map_of_mem H.subtype ((QuotientGroup.eq_one_iff x').mp hπ)

/-- The cubic closure of the original H-span is elementary and stays in O₂(H). -/
theorem linear_cubic_nonabelian_local_cubic_span
    (D : ChosenModule T L V)
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hK : residual H ∈ Chapter1.LStar G (T : Subgroup G))
    (hnf : ¬ ChapterA.Section04.IsFaithfulSignalizerType (residual H))
    (hlinear : ClassicalGroup.IsPSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 3 4)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    (c : LinearFieldCartan T L H A B C n)
    (d : CubicEscape.LocalData T H C z) (hn : 1 < n)
    (hne : ¬ IsMulCommutative (conjugateSpanBy (CubicEscape.plane C z)
      (centralizer ({z} : Set G)))) :
    IsElementaryAbelian 2 (conjugateSpanBy (setup T H C z).U C) ∧
      conjugateSpanBy (setup T H C z).U C ≤ H.pCoreIn 2 := by
  let U₀ := (setup T H C z).U
  let : IsElementaryAbelian 2 U₀ :=
    linear_cubic_local_span_elementary D h hH hK hnf hlinear hpsl c d hn
  have hUQ : U₀ ≤ H.pCoreIn 2 :=
    le_pCoreIn_of_normalizes d.g2.U_isPGroup d.g2.U_le_H
      (le_normalizer_conjugateSpanBy _ _)
  have hpairs (g : G) (hg : g ∈ C) :
      ⁅U₀, conjugate U₀ g⁆ = ⊥ ∧ conjugate U₀ g ≤ H.pCoreIn 2 := by
    by_cases he : g = 1
    · subst g
      have hid : (MulAut.conj (1 : G)).toMonoidHom = MonoidHom.id G := by
        ext x
        simp
      rw [conjugate, inv_one, hid, map_id]
      exact ⟨commutator_self_eq_bot_iff.mpr inferInstance, hUQ⟩
    have hmove : g ∉ normalizer (zpowers z : Set G) := by
      intro hnz
      let : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
      have hzgen : zpowers (⟨g, hg⟩ : C) ≤ (normalizer (zpowers z : Set G)).subgroupOf C :=
        zpowers_le.mpr hnz
      obtain ⟨x, hx, hxn⟩ := d.exists_moving_cubic
      exact hxn (hzgen (mem_zpowers_of_prime_card c.cubic_card
        (by exact fun hh => he (congrArg Subtype.val hh)) (g' := ⟨x, hx⟩)))
    exact linear_cubic_nonabelian_local_pair D h hH hK hnf hlinear hpsl c d hn hne
      g hg hmove
  have hgen (g : G) (hg : g ∈ C) (u : G) (hu : u ∈ U₀) :
      g * u * g⁻¹ ∈ centralizer (U₀ : Set G) ⊓ H.pCoreIn 2 := by
    have hp := hpairs g⁻¹ (C.inv_mem hg)
    have hm : g * u * g⁻¹ ∈ conjugate U₀ g⁻¹ := by
      simp only [conjugate, inv_inv]
      exact ⟨u, hu, rfl⟩
    exact ⟨(le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hp.1)) hm,
      hp.2 hm⟩
  have hspan : conjugateSpanBy U₀ C ≤ centralizer (U₀ : Set G) ⊓ H.pCoreIn 2 := by
    apply (closure_le _).mpr
    rintro x ⟨g, hg, u, hu, rfl⟩
    exact hgen g hg u hu
  let : IsMulCommutative (conjugateSpanBy U₀ C) :=
    (conjugateSpanBy_commutative_iff U₀ C).mpr
      (le_centralizer_iff.mp (hspan.trans inf_le_left))
  exact ⟨conjugateSpanBy_elementary_of_commutative U₀ C, hspan.trans inf_le_right⟩

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
