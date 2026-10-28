module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Outside.Generation.Equal
public import Theory.GroupTheory.Commutator.PerfectCoreKernel

/-!
# Generation one from the literal point-section kernel

The two-core of K lies in T, which normalizes the original perfect L₁.
The perfect-subgroup commutator theorem therefore restricts the action
kernel on K/O₂(K) to the actual kernel on L₁/O₂(L₁), proving normalization
as well as the commutator bound. This works for strict components too.

The original E.2.2 Hall actor lies in O²(H). If that residual centralizes
the point section, the three proved natural-action calculations and the
split-torus coprimality theorem make the Hall actor fix V. Faithfulness
then contradicts its nontrivial cyclic subgroup when n(H)>1. We obtain
generation one for the quotient-centralizing alternative, and construct
an actual selected H whenever the quotient centralizer escapes M.
For arbitrary H, the genuine E.2.2 construction now leaves only an
escaping local component I contained in K; the commuting branch is closed.

The exact OddKernelNormalizer input is used only for Hall faithfulness;
its producer remains qt-d-1222-natural-odd-kernel-normalizer. Earlier
geometry, the linear fixed-space input, 11.3.2 and Kz=K retain the producers
qt-d-1222-natural-local-geometry, qt-d-1222-shadow-linear-geometry,
qt-d-1222-shadow-component-triangle and qt-d-1222-shadow-component-comparison,
with final discharge by qt-d-1222-shadow-components. Excluding the contained
component and proving generation one for the smaller R₁O²(H) carrier
remain with qt-d-1222-shadow-component-witness. No complete 11.4.4 or
11.5.1 is asserted here.

Source: Aschbacher--Smith, E.2.2 and 11.4.4--11.5.1,
printed pp.215--216 and778--779 of refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation
open CFSG.Quasithin.Chapter12.Section02 CFSG.Quasithin.ChapterB.QuasisimpleSource
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Outside.Generation
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    {D : ChosenModule T L V} (S : D.NonbinaryNaturalInput)
    {c : LocalGeometry.Coordinates D S.field} (f : LocalGeometry.InvariantFlag c)
    (X : Subgroup G) (z : G) (H : Subgroup G)

/-- Restriction of the literal component-quotient kernel to the original
perfect flag residual. Normalization of that residual is proved internally. -/
theorem ofFlag_coreCentralizer_le_first :
    Closure.coreQuotientCentralizer (ofFlag S f X z H).K ≤
      Closure.coreQuotientCentralizer (f.Li 0) := by
  let E := ofFlag S f X z H
  let B := Closure.coreQuotientCentralizer E.K
  have hTA := f.sylow_normalizes_Li 0
  have hTK := (f.invariant 0).trans E.G₁_normalizes_K
  have hcore : E.K.pCoreIn 2 ≤ (T : Subgroup G) := by
    have hh := pCoreIn_mono_of_normalizes (p := 2) (Y := E.K)
      (L := E.K ⊔ (T : Subgroup G)) le_sup_left (sup_le E.K.le_normalizer hTK)
    apply hh.trans
    simpa only [Sylow.coe_subtype,map_subgroupOf_eq_of_le le_sup_right] using
      pCoreIn_le_sylow (E.K ⊔ (T : Subgroup G)) (T.subtype le_sup_right)
  let : Group.IsPerfect (f.Li 0) := LocalGeometry.localResidual_perfect _
  have hcK : ⁅E.K,B⁆ ≤ E.K.pCoreIn 2 := by
    rw [commutator_comm]
    exact commutator_le.mpr (fun b hb k hk =>
      Closure.coreQuotientCentralizer_commutator hb hk)
  have hc := perfect_subgroup_core_commutator (f.Li 0) E.K B
    (le_conjugateSpanBy _ _) (hcore.trans hTA) hcK
  exact coreCentralizer_of_commutator
    (le_normalizer_iff_commutator_le_left.mpr (hc.trans (pCoreIn_le 2 _)))
    (by simpa only [commutator_comm] using hc)

/-- The natural-action calculation in all three original source rows. -/
theorem ofFlag_odd_point_section_centralizes
    (h : Comparison.EarlierGeometry (ofFlag S f X z H))
    (hf : V ⊓ centralizer (L : Set G) = ⊥)
    (B : Subgroup G) (ho : Odd (Nat.card B))
    (hBV : B ≤ normalizer (V : Set G)) (hBz : B ≤ Gz (ofFlag S f X z H))
    (hc : ⁅B,f.Li 0⁆ ≤ (f.Li 0).pCoreIn 2)
    (hco : Nat.Coprime (Nat.card B) (2 ^ S.field.degree - 1)) :
    B ≤ centralizer (V : Set G) := by
  cases c with
  | sl3 m => exact ofFlag_sl3_odd_section_centralizes S m f B ho hBV hc hco
  | sp4 m => exact ofFlag_sp4_odd_section_centralizes S m f B ho hBV hc hco
  | g2 m =>
    let E := ofFlag S f X z H
    let c := LocalGeometry.Coordinates.g2 m
    let v : V := ⟨z,E.V₁_le h.point_mem⟩
    have hv0 : (c.projection v).toAdd ≠ 0 := by
      intro hz0
      have hv1 : v=1 := Closure.Nonabelian.PointModels.projection_injective c hf
        (hz0.trans (map_one c.projection).symm)
      exact h.point_ne_one (congrArg Subtype.val hv1)
    exact ofFlag_g2_odd_section_centralizes S m f v
      ((c.mem_preimage _ v).mp h.point_mem) hv0 hf B ho hBV hBz hc hco

/-- The Hall argument proves generation one whenever the actual two-residual
centralizes the original point section, with no equal-component hypothesis. -/
theorem ofFlag_generation_eq_one_of_residual_first_kernel
    (h : Comparison.EarlierGeometry (ofFlag S f X z H))
    (hf : V ⊓ centralizer (L : Set G) = ⊥)
    (hcontrol : LocalGeometry.WeakClosure.Generation.OddKernelNormalizer
      (T := T) (L := L) (V := V))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hHz : H ≤ Gz (ofFlag S f X z H))
    (hr : (pResidual 2 H).map H.subtype ≤ Closure.coreQuotientCentralizer (f.Li 0)) :
    ChapterE.generationParameter H = 1 := by
  apply Nat.le_antisymm ?_ (selected_generation_spec (ofFlag S f X z H) h hH hHz).1
  change ChapterE.generationParameter H ≤ 1
  by_contra! hn
  obtain ⟨hP,n,_,hb,d,hm,_⟩ := LocalGeometry.WeakClosure.Generation.hall_data D S hH hn
  have hBN : d.witness.abelianGroup ≤ pResidual 2 H := by
    intro b hb
    exact mem_pResidual_of_orderOf_coprime
      (d.witness.odd.coprime_two_left.of_dvd_right
        (d.witness.abelianGroup.orderOf_dvd_natCard hb))
  let B := d.witness.abelianGroup.map H.subtype
  have hBc : B ≤ Closure.coreQuotientCentralizer (f.Li 0) := (map_mono hBN).trans hr
  have hBz : B ≤ Gz (ofFlag S f X z H) := (map_subtype_le _).trans hHz
  have hBM : B ≤ normalizer (L : Set G) :=
    map_le_iff_le_comap.mpr (d.hall_le.trans hm.le)
  have ho : Odd (Nat.card B) := d.witness.odd.of_dvd_nat (card_map_dvd _ _)
  have hBV : B ≤ normalizer (V : Set G) := (le_inf hBM hBz).trans
    (point_intersection_normalizes_seed (ofFlag S f X z H)
      ((ofFlag S f X z H).V₁_le h.point_mem) h.point_ne_one)
  have hc : ⁅B,f.Li 0⁆ ≤ (f.Li 0).pCoreIn 2 :=
    commutator_le.mpr (fun b hb k hk =>
      Closure.coreQuotientCentralizer_commutator (hBc hb) hk)
  have hcop := ofFlag_odd_point_section_coprime S f X z H h hf B ho hBM hBz hBc
  have hfix := ofFlag_odd_point_section_centralizes S f X z H h hf B ho hBV hBz hc hcop
  have hfaith := LocalGeometry.WeakClosure.Generation.hall_faithful D S hcontrol hH hn hP d hm
  have hz : B = ⊥ := by rwa [inf_eq_left.mpr hfix] at hfaith
  have hB : d.witness.abelianGroup = ⊥ :=
    (map_eq_bot_iff_of_injective _ H.subtype_injective).mp hz
  have hC : d.witness.cyclicGroup = ⊥ := bot_unique (d.witness.cyclic_le.trans hB.le)
  have hc1 := d.witness.card
  rw [Subgroup.card_eq_one.mpr hC] at hc1
  have hn2 : 2 ≤ n := by omega
  have hp : 2 ^ 2 ≤ 2 ^ n := Nat.pow_le_pow_right (by decide) hn2
  omega

/-- The quotient-centralizing source residual alternative has generation one
in every surviving model, including both strict odd-extension rows. -/
theorem ofFlag_generation_eq_one_of_centralizing_alternative
    (h : Comparison.EarlierGeometry (ofFlag S f X z H))
    (he : (ofFlag S f X z H).Kz = (ofFlag S f X z H).K)
    (hlinear : Source.IsSL (L ⧸ pCore 2 L) 3 (2 ^ S.field.degree) →
      V ⊓ centralizer (L : Set G) = ⊥)
    (h1132 : ∀ J, Hypothesis1131At D S (ofFlag S f X z H).point J →
      Proposition1132At D S (ofFlag S f X z H).point J)
    (hcontrol : LocalGeometry.WeakClosure.Generation.OddKernelNormalizer
      (T := T) (L := L) (V := V))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hHz : H ≤ Gz (ofFlag S f X z H))
    (hr : ⁅(ofFlag S f X z H).K,(pResidual 2 H).map H.subtype⁆ ≤
      (ofFlag S f X z H).K.pCoreIn 2) : ChapterE.generationParameter H = 1 := by
  apply ofFlag_generation_eq_one_of_residual_first_kernel S f X z H h
    (fixed_and_transitive D S _ hlinear h1132).1 hcontrol hH hHz
  apply le_trans _ (ofFlag_coreCentralizer_le_first S f X z H)
  exact coreCentralizer_of_commutator
    ((map_subtype_le _).trans (hHz.trans (point_normalizes_component _ he)))
    (by simpa only [commutator_comm] using hr)

/-- After the full Hall calculation, large generation can only come from
an actual escaping E.2.2 component contained in K. The commutation branch
is discharged, rather than retained as an action hypothesis. -/
theorem ofFlag_large_generation_component_le
    (h : Comparison.EarlierGeometry (ofFlag S f X z H))
    (he : (ofFlag S f X z H).Kz = (ofFlag S f X z H).K)
    (hlinear : Source.IsSL (L ⧸ pCore 2 L) 3 (2 ^ S.field.degree) →
      V ⊓ centralizer (L : Set G) = ⊥)
    (h1132 : ∀ J, Hypothesis1131At D S (ofFlag S f X z H).point J →
      Proposition1132At D S (ofFlag S f X z H).point J)
    (hcontrol : LocalGeometry.WeakClosure.Generation.OddKernelNormalizer
      (T := T) (L := L) (V := V))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hHz : H ≤ Gz (ofFlag S f X z H))
    (hn : 1 < ChapterE.generationParameter H) :
    ∃ I : Subgroup G, I ≤ H ∧ (I.subgroupOf H).IsCComponent ∧
      I ∈ Chapter1.L G (T : Subgroup G) ∧ ¬ I ≤ normalizer (L : Set G) ∧
      I ⊔ (T : Subgroup G) = H ∧
      conjugateSpanBy I (T : Subgroup G) = (pResidual 2 H).map H.subtype ∧
      I ≤ (ofFlag S f X z H).K := by
  let E := ofFlag S f X z H
  obtain ⟨I,hIH,hI,hlocal,hout,hjoin,hres⟩ := component_of_large_generation E h hH hHz hn
  refine ⟨I,hIH,hI,hlocal,hout,hjoin,hres,?_⟩
  rcases local_component_alternative E h he hlocal (hIH.trans hHz) with hIK | hc
  · exact hIK
  have hIc : I ≤ Closure.coreQuotientCentralizer E.K :=
    coreCentralizer_of_commutator ((hIH.trans hHz).trans (point_normalizes_component E he))
      (by simpa only [commutator_comm] using hc)
  have hr : (pResidual 2 H).map H.subtype ≤ Closure.coreQuotientCentralizer E.K := by
    change (pResidual 2 E.H).map E.H.subtype ≤ _
    rw [←hres]
    exact conjugateSpanBy_le hIc
      (((f.invariant 0).trans E.G₁_normalizes_K).trans
        (Closure.normalizer_normalizes_coreQuotientCentralizer E.K))
  have hn1 := ofFlag_generation_eq_one_of_residual_first_kernel S f X z H h
    (fixed_and_transitive D S _ hlinear h1132).1 hcontrol hH hHz
    (hr.trans (ofFlag_coreCentralizer_le_first S f X z H))
  omega

/-- Select an actual outside H in the escaping quotient centralizer, and
prove its residual alternative and generation one on the unchanged flag. -/
theorem ofFlag_selected_generation_one_of_kernel_escape
    (h : Comparison.EarlierGeometry (ofFlag S f X z H))
    (he : (ofFlag S f X z H).Kz = (ofFlag S f X z H).K)
    (hlinear : Source.IsSL (L ⧸ pCore 2 L) 3 (2 ^ S.field.degree) →
      V ⊓ centralizer (L : Set G) = ⊥)
    (h1132 : ∀ J, Hypothesis1131At D S (ofFlag S f X z H).point J →
      Proposition1132At D S (ofFlag S f X z H).point J)
    (hcontrol : LocalGeometry.WeakClosure.Generation.OddKernelNormalizer
      (T := T) (L := L) (V := V))
    (hout : ¬ Yz (ofFlag S f X z H) ≤ normalizer (L : Set G)) :
    ∃ J, J ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)) ∧
      J ≤ Gz (ofFlag S f X z J) ∧ SelectedResidualAlternative (ofFlag S f X z J) ∧
      ChapterE.generationParameter J = 1 ∧
      (pResidual 2 J).map J.subtype ≤ Yz (ofFlag S f X z J) := by
  let E := ofFlag S f X z H
  have hJz : Yz E ⊔ (T : Subgroup G) ≤ Gz E := sup_le inf_le_left h.sylow_le_pointCentralizer
  obtain ⟨J,hJ,hJY⟩ := exists_HStar_below_point E h _ le_sup_right hJz
    (fun hh => hout (le_sup_left.trans hh))
  have hJz' := hJY.trans hJz
  have hr := residual_le_factor (Yz E) J
    (h.sylow_le_pointCentralizer.trans (point_normalizes_kernel E he)) hJY
  have hc : ⁅E.K,(pResidual 2 J).map J.subtype⁆ ≤ E.K.pCoreIn 2 := by
    rw [commutator_comm]
    exact commutator_le.mpr (fun b hb k hk =>
      Closure.coreQuotientCentralizer_commutator (hr hb).2 hk)
  refine ⟨J,hJ,hJz',Or.inl hc,?_,hr⟩
  exact ofFlag_generation_eq_one_of_centralizing_alternative S f X z J
    ⟨h.point_mem,h.point_fixed,h.point_ne_one,h.seed_centralizes,
      h.line_component,h.point_component,h.normalizer_split⟩
    he hlinear h1132 hcontrol hJ hJz' hc

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Outside.Generation
