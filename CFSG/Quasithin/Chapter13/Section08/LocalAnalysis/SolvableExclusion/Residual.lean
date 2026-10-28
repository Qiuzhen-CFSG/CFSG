module

public import CFSG.Quasithin.Chapter13.Section08.SourceDefs
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.Elementary
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.SolvableExclusion.Basic
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.SolvableExclusion.Residual.Normalizer
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.SolvableExclusion.Residual.Components

/-!
# Component overgroups and the intersection residual: 13.8.12

This is an independent conditional deduction from the actual earlier source
statements. The local data records precisely the standing consequences used
here. It contains no conclusion of 13.8.12. The universal input 13.3.9 keeps
its outside-overgroup, relative-normality, centralizer and exceptional clauses;
the component input is the normal-or-index-two alternative of 1.2.1(3).
No conclusion of 13.8.4–11 is needed in this particular deduction.

For clause (1), the T-conjugate span of a C-component is normal in H and
perfect; if contained in M, 13.3.9 would make it solvable. The same normality
identifies the generated overgroup with the literal product ⟨K,T⟩L₁.

For clause (2), failure of the alternatives forces O²(O₂,F(H)) **outside** M,
correcting the reversed containment printed on p.950. Choose the minimal
T-invariant two-perfect F as in the source. Its intersection E = F ∩ M has
O²(E) = X. The map from F into the ordinary Fitting subgroup of H/O₂(H)
has kernel F ∩ O₂(H) ≤ E, so the nilpotent normalizer condition gives
E < N_F(E). This larger normalizer preserves X. Its join with T is the
outside overgroup to which 13.3.9 applies. Using this overgroup directly
makes further minimization unnecessary and avoids the unsupported printed
identity F ∩ M = X; neither that identity nor its normalizer-residual
consequence is assumed.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), 13.3.9 on
printed p.887, the standing setup on pp.946–947, and 13.8.12 on p.950.
The parent source-theorem assembly must discharge the earlier inputs.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
open scoped Pointwise
namespace CFSG.Quasithin.Chapter13.Section08.SolvableExclusion.Residual
variable {G : Type*} [Group G] [Finite G]

/-- Standing local consequences used by this deduction. The actual source
has G₁ = C_G(z), z generating V₁, and the solvable parabolics L₁ and L₁,+.
The earlier theorem inputs are passed separately below. -/
structure LocalData (L L₁ L₁plus M V V₁ G₁ H : Subgroup G) (T : Sylow 2 G)
    (z : G) : Prop where
  mem_Hz : H ∈ Source.Hz L₁ T G₁ M
  sylow_le : (T : Subgroup G) ≤ M
  involution : orderOf z = 2
  involution_mem : z ∈ T
  line_mem : z ∈ V₁
  noncentral : z ∉ V ⊓ centralizer (L : Set G)
  centralizer : G₁ ≤ centralizer ({z} : Set G)
  barred_model : Nonempty (barImage M V L ≃* alternatingGroup (Fin 6))
  quotient_models : Nonempty ((L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6)) ∨
    IsTripleCoverSix (L ⧸ pCore 2 L)
  solvable_first : Group.IsSolvable L₁
  solvable_plus : Group.IsSolvable L₁plus
  normalizes_first : (T : Subgroup G) ≤ normalizer (L₁ : Set G)

variable {L L₁ L₁plus M V V₁ G₁ H : Subgroup G} {T : Sylow 2 G} {z : G}

omit [Finite G] in
private theorem mem_outside (J : Subgroup G) (hTJ : (T : Subgroup G) ≤ J)
    (hJz : J ≤ centralizer ({z} : Set G)) (hz : orderOf z = 2)
    (hzT : z ∈ T) (hout : ¬ J ≤ M) :
    J ∈ Chapter1.HOutside G (T : Set G) (M : Set G) := by
  have hp : IsPGroup 2 (zpowers z) :=
    IsPGroup.of_card (n := 1) (by simpa only [Nat.card_zpowers, pow_one] using hz)
  have hzJ : zpowers z ≤ J := zpowers_le.mpr (hTJ hzT)
  have hJN : J ≤ normalizer (zpowers z : Set G) := by
    have hn : centralizer ({z} : Set G) ≤ normalizer (zpowers z : Set G) := by
      rw [← centralizer_closure, ← zpowers_eq_closure]
      exact centralizer_le_normalizer _
    exact hJz.trans hn
  refine ⟨⟨?_, hTJ⟩, hout⟩
  intro he
  have hm := le_pCoreIn_of_normalizes hp hzJ hJN (mem_zpowers z)
  rw [he] at hm
  have hez : z = 1 := hm
  simp [hez] at hz

omit [Finite G] in
private theorem apply_1339 (d : LocalData L L₁ L₁plus M V V₁ G₁ H T z)
    (hsource : Source1339 L L₁ L₁plus T M V V₁)
    (J Y : Subgroup G) (hTJ : (T : Subgroup G) ≤ J) (hJH : J ≤ H)
    (hout : ¬ J ≤ M) (hYJ : Y ≤ J) (hp : IsPPerfect 2 Y)
    (hn : J ≤ normalizer (Y : Set G)) (hYM : Y ≤ M) :
    ResidualAlternative L L₁ L₁plus Y := by
  have hJz := hJH.trans (d.mem_Hz.2.1.trans d.centralizer)
  apply alternative_of_1339 d.quotient_models
  exact hsource d.barred_model J Y
    (mem_outside J hTJ hJz d.involution d.involution_mem hout)
    hYJ hp ((normal_subgroupOf_iff_le_normalizer hYJ).mpr hn)
    ⟨z, d.line_mem, d.noncentral, le_inf hYM (hYJ.trans hJz)⟩

omit [Finite G] in
private theorem norm_residualInM (d : LocalData L L₁ L₁plus M V V₁ G₁ H T z) :
    (T : Subgroup G) ≤ normalizer (residualInM H M : Set G) := by
  apply le_trans _ (normalizer_le_normalizer_twoResidual (twoFitting H ⊓ M))
  apply le_normalizer_iff.mpr
  intro t ht x hx
  exact ⟨le_normalizer_iff.mp (le_normalizer_twoFitting H) t
    ((le_sup_right.trans d.mem_Hz.1.2 : (T : Subgroup G) ≤ H) ht) x hx.1,
    le_normalizer_iff.mp M.le_normalizer t (d.sylow_le ht) x hx.2⟩

omit [Finite G] in
private theorem core_le_M (d : LocalData L L₁ L₁plus M V V₁ G₁ H T z) :
    Source.QH H ≤ M := by
  have hTH : (T : Subgroup G) ≤ H := le_sup_right.trans d.mem_Hz.1.2
  have h := pCoreIn_le_sylow H (T.subtype hTH)
  rw [Sylow.coe_subtype, map_subgroupOf_eq_of_le hTH] at h
  exact h.trans d.sylow_le

/-- Corrects the reversed containment in the first paragraph of the printed proof. -/
theorem wholeResidual_outside_of_failure
    (d : LocalData L L₁ L₁plus M V V₁ G₁ H T z)
    (hsource : Source1339 L L₁ L₁plus T M V V₁)
    (hfail : ¬ ResidualAlternative L L₁ L₁plus (residualInM H M)) :
    ¬ residualWhole H ≤ M := by
  intro hRM
  have he : residualInM H M = residualWhole H := by
    apply le_antisymm ((residualInM_le H M).trans inf_le_left)
    have hp := isPPerfect_embedded_pResidual 2 (twoFitting H)
    rw [← twoResidual_eq_self (residualWhole H) hp]
    exact twoResidual_mono (le_inf (twoResidual_le _) hRM)
  have hn : H ≤ normalizer (residualWhole H : Set G) :=
    (le_normalizer_twoFitting H).trans (normalizer_le_normalizer_twoResidual _)
  apply hfail
  rw [he]
  exact apply_1339 d hsource H _ (le_sup_right.trans d.mem_Hz.1.2) le_rfl
    d.mem_Hz.2.2 ((twoResidual_le _).trans (twoFitting_le H))
    (isPPerfect_embedded_pResidual 2 _) hn hRM

/-- The minimal two-perfect T-invariant subgroup required in the source proof. -/
theorem exists_minimal_residual_subgroup
    (d : LocalData L L₁ L₁plus M V V₁ G₁ H T z)
    (hout : ¬ residualWhole H ≤ M) :
    ∃ F : Subgroup G, F ≤ twoFitting H ∧
      Minimal (fun F : Subgroup G => residualInM H M ≤ F ∧
        IsPPerfect 2 F ∧ (T : Subgroup G) ≤ normalizer (F : Set G) ∧ ¬ F ≤ M) F ∧
      F ⊔ (T : Subgroup G) ∈ Chapter1.HOutside G (T : Set G) (M : Set G) := by
  have hp : IsPPerfect 2 (residualWhole H) := isPPerfect_embedded_pResidual 2 _
  have hn : (T : Subgroup G) ≤ normalizer (residualWhole H : Set G) :=
    (le_sup_right.trans d.mem_Hz.1.2).trans
      ((le_normalizer_twoFitting H).trans (normalizer_le_normalizer_twoResidual _))
  obtain ⟨F, hFR, hF⟩ := exists_minimal_le_of_wellFoundedLT
    (fun F : Subgroup G => residualInM H M ≤ F ∧ IsPPerfect 2 F ∧
      (T : Subgroup G) ≤ normalizer (F : Set G) ∧ ¬ F ≤ M)
    (residualWhole H) ⟨(residualInM_le H M).trans inf_le_left, hp, hn, hout⟩
  have hFH : F ≤ H := hFR.trans ((twoResidual_le _).trans (twoFitting_le H))
  have hJH : F ⊔ (T : Subgroup G) ≤ H :=
    sup_le hFH (le_sup_right.trans d.mem_Hz.1.2)
  exact ⟨F, hFR.trans (twoResidual_le _), hF,
    mem_outside _ le_sup_right (hJH.trans (d.mem_Hz.2.1.trans d.centralizer))
      d.involution d.involution_mem (fun h => hF.prop.2.2.2 (le_sup_left.trans h))⟩

/-- Clause (2), using the ordinary Fitting preimage and genuine relative normalizers. -/
theorem residual_alternative
    (d : LocalData L L₁ L₁plus M V V₁ G₁ H T z)
    (hsource : Source1339 L L₁ L₁plus T M V V₁) :
    ResidualAlternative L L₁ L₁plus (residualInM H M) := by
  by_contra hfail
  obtain ⟨F, hFR, hF, _⟩ := exists_minimal_residual_subgroup d
    (wholeResidual_outside_of_failure d hsource hfail)
  let E := F ⊓ M
  let N := F ⊓ normalizer (E : Set G)
  have hEF : E < F := lt_of_le_of_ne inf_le_left
    (fun he => hF.prop.2.2.2 (he.symm.le.trans inf_le_right))
  obtain ⟨f, hf⟩ := exists_fittingMap H F hFR
  have hk : f.ker ≤ E.subgroupOf F := by
    rw [hf]
    intro x hx
    exact ⟨x.property, core_le_M d hx⟩
  have hEN : E < N := lt_relative_normalizer_of_nilpotent_image F E hEF f hk
  have hNM : ¬ N ≤ M := by
    intro hn
    exact hEN.not_ge (le_inf inf_le_left hn)
  have hNX : N ≤ normalizer (residualInM H M : Set G) := by
    rw [← intersection_residual_eq H M F hF.prop.1 hFR]
    exact inf_le_right.trans (normalizer_le_normalizer_twoResidual E)
  have hXE : residualInM H M ≤ E :=
    le_inf hF.prop.1 ((residualInM_le H M).trans inf_le_right)
  have hFH : F ≤ H := hFR.trans (twoFitting_le H)
  exact hfail (apply_1339 d hsource (N ⊔ (T : Subgroup G)) (residualInM H M)
    le_sup_right (sup_le (inf_le_left.trans hFH) (le_sup_right.trans d.mem_Hz.1.2))
    (fun h => hNM (le_sup_left.trans h)) (hXE.trans (hEN.le.trans le_sup_left))
    (isPPerfect_embedded_pResidual 2 _) (sup_le hNX (norm_residualInM d))
    ((residualInM_le H M).trans inf_le_right))


/-- Source 13.8.12(1), with the precise earlier normal-or-index-two
alternative for the genuine C-component. -/
theorem component_outside
    (d : LocalData L L₁ L₁plus M V V₁ G₁ H T z)
    (hsource : Source1339 L L₁ L₁plus T M V V₁)
    (K : Subgroup G) (hKH : K ≤ H) (hK : (K.subgroupOf H).IsCComponent)
    (horbit : (K.subgroupOf H).Normal ∨
      (normalizer (K.subgroupOf H : Set H)).index = 2) : ¬ K ≤ M := by
  intro hKM
  let Y := conjugateSpanBy K (T : Subgroup G)
  have hTH : (T : Subgroup G) ≤ H := le_sup_right.trans d.mem_Hz.1.2
  have he : Y = conjugateSpanBy K H := component_span_eq_full H K T hKH hTH horbit
  have hYH : Y ≤ H := he ▸ conjugateSpanBy_le_self hKH
  have hYN : H ≤ normalizer (Y : Set G) := he ▸ le_normalizer_conjugateSpanBy K H
  have hp : IsPPerfect 2 Y := span_isPPerfect K T (component_isPPerfect H K hKH hK)
  have hYM : Y ≤ M := conjugateSpanBy_le hKM (d.sylow_le.trans M.le_normalizer)
  have halt := apply_1339 d hsource H Y hTH le_rfl d.mem_Hz.2.2 hYH hp hYN hYM
  have hs : Group.IsSolvable Y := by
    rcases halt with hb | ⟨_, heq⟩ | ⟨_, heq⟩
    · rw [hb]; infer_instance
    · rw [heq]; exact d.solvable_first
    · rw [heq]; exact d.solvable_plus
  let := hs
  let : Group.IsSolvable K := Group.isSolvable_of_isSolvable_injective
    (f := inclusion (le_conjugateSpanBy K (T : Subgroup G)))
    (inclusion_injective (le_conjugateSpanBy K (T : Subgroup G)))
  exact hK.not_isSolvable (Group.isSolvable_of_isSolvable_injective
    (f := (subgroupOfEquivOfLe hKH).toMonoidHom) (subgroupOfEquivOfLe hKH).injective)

/-- The join is the literal source product ⟨K,T⟩L₁ and is in the actual Hz
family. The normalizer assertion records why the product calculation works. -/
theorem component_overgroup
    (d : LocalData L L₁ L₁plus M V V₁ G₁ H T z)
    (hsource : Source1339 L L₁ L₁plus T M V V₁)
    (K : Subgroup G) (hKH : K ≤ H) (hK : (K.subgroupOf H).IsCComponent)
    (horbit : (K.subgroupOf H).Normal ∨
      (normalizer (K.subgroupOf H : Set H)).index = 2) :
    ¬ K ≤ M ∧ ((K ⊔ (T : Subgroup G)) ⊔ L₁) ∈ Source.Hz L₁ T G₁ M ∧
      H ≤ normalizer (conjugateSpanBy K (T : Subgroup G) : Set G) ∧
      ((((K ⊔ (T : Subgroup G)) ⊔ L₁) : Subgroup G) : Set G) =
        ((K ⊔ (T : Subgroup G) : Subgroup G) : Set G) * (L₁ : Set G) := by
  have hKM := component_outside d hsource K hKH hK horbit
  have hTH : (T : Subgroup G) ≤ H := le_sup_right.trans d.mem_Hz.1.2
  have hn : H ≤ normalizer (conjugateSpanBy K (T : Subgroup G) : Set G) := by
    rw [component_span_eq_full H K T hKH hTH horbit]
    exact le_normalizer_conjugateSpanBy K H
  let J := (K ⊔ (T : Subgroup G)) ⊔ L₁
  have hTJ : (T : Subgroup G) ≤ J := le_sup_right.trans le_sup_left
  have hJH : J ≤ H := sup_le (sup_le hKH hTH) (le_sup_left.trans d.mem_Hz.1.2)
  have hout : ¬ J ≤ M := fun h => hKM (le_sup_left.trans (le_sup_left.trans h))
  have hJO := mem_outside J hTJ (hJH.trans (d.mem_Hz.2.1.trans d.centralizer))
    d.involution d.involution_mem hout
  refine ⟨hKM, ⟨⟨hJO.1.1, sup_le le_sup_right hTJ⟩, hJH.trans d.mem_Hz.2.1, hout⟩,
    hn, ?_⟩
  exact component_overgroup_product H K L₁ T d.mem_Hz.1.2 hn d.normalizes_first

/-- Both clauses of 13.8.12 as an independent conditional deduction from
the earlier source results. No residual alternative or component exclusion
is an input. The source assembly supplies the standing local data, 13.3.9,
and the normal-or-index-two conclusion of 1.2.1(3). -/
theorem lemma_13_8_12
    (d : LocalData L L₁ L₁plus M V V₁ G₁ H T z)
    (hsource : Source1339 L L₁ L₁plus T M V V₁)
    (h121 : ∀ K : Subgroup G, K ≤ H → (K.subgroupOf H).IsCComponent →
      (K.subgroupOf H).Normal ∨ (normalizer (K.subgroupOf H : Set H)).index = 2) :
    (∀ K : Subgroup G, K ≤ H → (K.subgroupOf H).IsCComponent →
      ¬ K ≤ M ∧ ((K ⊔ (T : Subgroup G)) ⊔ L₁) ∈ Source.Hz L₁ T G₁ M ∧
        H ≤ normalizer (conjugateSpanBy K (T : Subgroup G) : Set G) ∧
        ((((K ⊔ (T : Subgroup G)) ⊔ L₁) : Subgroup G) : Set G) =
          ((K ⊔ (T : Subgroup G) : Subgroup G) : Set G) * (L₁ : Set G)) ∧
      ResidualAlternative L L₁ L₁plus (residualInM H M) := by
  exact ⟨fun K hKH hK => component_overgroup d hsource K hKH hK (h121 K hKH hK),
    residual_alternative d hsource⟩

end CFSG.Quasithin.Chapter13.Section08.SolvableExclusion.Residual
end
