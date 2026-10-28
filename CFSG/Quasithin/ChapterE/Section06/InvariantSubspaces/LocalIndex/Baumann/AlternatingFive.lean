module

public import CFSG.Quasithin.ChapterE.Section06.InvariantSubspaces.LocalIndex.Baumann.Reduction
public import CFSG.Quasithin.ChapterE.Section06.InvariantSubspaces.LocalIndex.Baumann.AlternatingFive.Transport
public import CFSG.Quasithin.ChapterE.Section06.InvariantSubspaces.LocalIndex.Baumann.AlternatingFive.NaturalAction
public import CFSG.Quasithin.ChapterE.Section06.InvariantSubspaces.LocalIndex.Baumann.AlternatingFive.ThompsonImage
public import CFSG.Quasithin.ChapterB.Section02.Baumann
public import Theory.GroupTheory.NormalClosureCentralizerCore
public import Theory.GroupTheory.SylowKernelCore
public import Stellmacher.OmegaOneCenterMap

/-!
# Alpha decomposition for an alternating-five block

The supplied C_H(U) = O₂(H) identifies C_R(U) with O₂(H). Relative normality
of L in H then identifies C_L(U) with O₂(L), giving the subgroup conditions
(a) and (b) of Baumann's Argument inside H, where L is the actual two-residual.

The natural-action construction identifies U itself with the natural A₅ module,
retaining possible central extensions in O₂(L). The offender calculation identifies
the actual image of J(R) with two commuting transpositions. The concrete geometry
then supplies g in L such that J(R) and J(R)^g generate the full action image,
with fixed codimensions 2 + 2 = 4. Transport through H/C_H(U) verifies the
no-strong-offender condition and all remaining hypotheses of B.2.18.

Part (2) of that theorem gives the exact alpha decomposition, transported back
to the original ambient group. Its weaker consequence `alternatingFiveAlphaInput`
feeds the parent's proof of Q ≤ Baum(R). The centralizer equality remains the
explicit earlier input of this conditional helper.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), C.5.4(3),
printed p.155; B.2.18(2), pp.80–81; B.3.2(4), pp.83–84; C.1.13(c), pp.124–125.
-/

public section

namespace CFSG.Quasithin.ChapterE.Section06.InvariantSubspaces.LocalIndex.Baumann.AlternatingFive
open Subgroup Stellmacher ChapterB
universe u
variable {G : Type u} [Group G] [Finite G]
variable {K : GroupClass.{u}} {A H R L : Subgroup G}

/-- C_R(U) is the full local two-core, using Sylow containment. -/
theorem sylow_centralizer_eq (h : Configuration K A H R L)
    (hc : H ⊓ centralizer (U L : Set G) = pCoreIn 2 H) :
    R ⊓ centralizer (U L : Set G) = pCoreIn 2 H := by
  apply le_antisymm
  · rw [← hc]
    exact inf_le_inf_right _ (h.join_eq ▸ le_sup_right)
  · exact le_inf (HCore_le_R h) (hc ▸ inf_le_right)

/-- Relative normality gives the exact intersection of the two intrinsic cores. -/
theorem blockCore_eq_inter (h : Configuration K A H R L) :
    pCoreIn 2 L = L ⊓ pCoreIn 2 H := by
  have hc : pCoreIn 2 L ≤ pCoreIn 2 H :=
    le_pCoreIn_of_normalizes (isPGroup_pCoreIn 2 L)
      ((pCoreIn_le 2 L).trans (h.join_eq ▸ le_sup_left))
      (h.normalizes_L.trans (normalizer_le_normalizer_characteristic_image L (pCore 2 L)))
  exact le_antisymm (le_inf (pCoreIn_le 2 L) hc)
    (inf_pCoreIn_le_of_le 2 (h.join_eq ▸ le_sup_left))

/-- C_L(U) is exactly O₂(L), stronger than the bound in B.2.18(b). -/
theorem block_centralizer_eq (h : Configuration K A H R L)
    (hc : H ⊓ centralizer (U L : Set G) = pCoreIn 2 H) :
    L ⊓ centralizer (U L : Set G) = pCoreIn 2 L := by
  have hLH : L ≤ H := h.join_eq ▸ le_sup_left
  rw [blockCore_eq_inter h, ← hc, ← inf_assoc, inf_eq_left.mpr hLH]

/-- The first containment required in B.2.18(a). -/
theorem blockCore_le_sylow_centralizer (h : Configuration K A H R L)
    (hc : H ⊓ centralizer (U L : Set G) = pCoreIn 2 H) :
    pCoreIn 2 L ≤ R ⊓ centralizer (U L : Set G) := by
  rw [sylow_centralizer_eq h hc, blockCore_eq_inter h]
  exact inf_le_right

/-- The relative normalizer condition in B.2.18(a). -/
theorem block_normalizes_sylow_centralizer (h : Configuration K A H R L)
    (hc : H ⊓ centralizer (U L : Set G) = pCoreIn 2 H) :
    L ≤ normalizer ((R ⊓ centralizer (U L : Set G) : Subgroup G) : Set G) := by
  rw [sylow_centralizer_eq h hc]
  exact (show L ≤ H from h.join_eq ▸ le_sup_left).trans
    (H.le_normalizer.trans (normalizer_le_normalizer_characteristic_image H (pCore 2 H)))

omit [Finite G] in
private theorem map_fixed (B C : Subgroup H) :
    (B ⊓ centralizer (C : Set H)).map H.subtype =
      B.map H.subtype ⊓ centralizer (C.map H.subtype : Set G) := by
  rw [map_inf _ _ _ H.subtype_injective, map_centralizer_subtype,
    ← inf_assoc, inf_eq_left.mpr (map_subtype_le B)]

private theorem self_thompson (T : Subgroup G) :
    elementaryAbelianMaxJ (elementaryAbelianMaxJ T) = elementaryAbelianMaxJ T := by
  have hJT : elementaryAbelianMaxJ T ≤ T := sSup_le fun _ hE => hE.1
  have h₁ := elementaryAbelianMaxOrder_le_and_j_le_of_eq (elementaryAbelianMaxJ T) T hJT
  have h₂ := elementaryAbelianMaxOrder_le_and_j_le_of_maxJ_le T (elementaryAbelianMaxJ T) le_rfl
  exact le_antisymm (h₁.2 (le_antisymm h₁.1 h₂.1))
    (h₂.2 (le_antisymm h₂.1 h₁.1))

omit [Finite G] in
private theorem core_le_frattini (B : Subgroup G) :
    pCoreIn 2 B ≤ BaumannArgument.coreFrattini B := by
  rintro x ⟨y, hy, rfl⟩
  refine mem_map.mpr ⟨y, ?_, rfl⟩
  change (y : B ⧸ pCore 2 B) ∈ frattini (B ⧸ pCore 2 B)
  rw [(QuotientGroup.eq_one_iff y).mpr hy]
  exact one_mem _

omit [Finite G] in
private theorem native_fixedCodim (hVH : U L ≤ H) (B : Subgroup H) :
    BaumannArgument.fixedCodim ((U L).subgroupOf H) B =
      Nat.log 2 (Nat.card (U L)) -
        Nat.log 2 (Nat.card (U L ⊓ centralizer (B.map H.subtype : Set G) : Subgroup G)) := by
  unfold BaumannArgument.fixedCodim
  rw [← card_map_of_injective (K := (U L).subgroupOf H) H.subtype_injective,
    ← card_map_of_injective
      (K := (U L).subgroupOf H ⊓ centralizer (B : Set H)) H.subtype_injective,
    map_fixed, map_subgroupOf_eq_of_le hVH]

omit [Finite G] in
private theorem no_strong_of_model (m : NaturalActionModel H L) (hVH : U L ≤ H)
    [((U L).subgroupOf H).Normal]
    (e : (H ⧸ centralizer ((U L).subgroupOf H : Set H)) ≃* Equiv.Perm (Fin 5))
    (he : e.toMonoidHom.comp (BaumannArgument.actionMap ((U L).subgroupOf H)) = m.quotient)
    (T : Subgroup H) : BaumannArgument.NoStrongOffenders ((U L).subgroupOf H) T := by
  let V := (U L).subgroupOf H
  have hmap (B : Subgroup H) : (B.map (BaumannArgument.actionMap V)).map e.toMonoidHom =
      B.map m.quotient := by rw [map_map, he]
  intro B _ hBe hne
  let _ := hBe
  have hBe' : IsElementaryAbelian 2 (B.map m.quotient) := by
    rw [← hmap]
    exact IsElementaryAbelian.map e.toMonoidHom
  have hne' : B.map m.quotient ≠ ⊥ := by
    rw [← hmap]
    exact fun hz => hne ((map_eq_bot_iff_of_injective _ e.injective).mp hz)
  have hb := image_rank_le_fixed_codimension m B ⟨hne', hBe'⟩
  rw [← native_fixedCodim hVH B] at hb
  have hcard : Nat.card (B.map m.quotient) = Nat.card (B.map (BaumannArgument.actionMap V)) := by
    rw [← hmap, card_map_of_injective e.injective]
  simpa only [Representation.BinaryOffender.rank, hcard] using hb

private theorem alpha_decomposition_of_model (h : Configuration K A H R L)
    (hc : H ⊓ centralizer (U L : Set G) = pCoreIn 2 H)
    (m : NaturalActionModel H L)
    (himage : Offenders.IsConjugateTo
      ((elementaryAbelianMaxJ R).subgroupOf H |>.map m.quotient) (Offenders.D 5)) :
    thompsonAlpha R = (thompsonAlpha R ⊓ centralizer (L : Set G)) ⊔
      (U L ⊓ centralizer (elementaryAbelianMaxJ R : Set G)) := by
  classical
  have hRH : R ≤ H := h.join_eq ▸ le_sup_right
  have hLH : L ≤ H := h.join_eq ▸ le_sup_left
  have hVH : U L ≤ H := module_le_L.trans hLH
  let V := (U L).subgroupOf H
  let T := R.subgroupOf H
  let J := elementaryAbelianMaxJ T
  let _ : V.Normal := (normal_subgroupOf_iff_le_normalizer hVH).mpr (normalizes_module h)
  let _ : IsElementaryAbelian 2 (U L) := module_elementary h
  let _ : IsElementaryAbelian 2 V := IsElementaryAbelian.subgroupOf hVH
  have hVmap : V.map H.subtype = U L := map_subgroupOf_eq_of_le hVH
  have hTmap : T.map H.subtype = R := map_subgroupOf_eq_of_le hRH
  have hres : (pResidual 2 H).map H.subtype = L := h.residual
  have hC : centralizer (V : Set H) = pCore 2 H := by
    apply map_injective H.subtype_injective
    rw [map_centralizer_subtype, hVmap]
    exact hc
  have hker : m.quotient.ker = centralizer (V : Set H) := m.kernel.trans hC.symm
  have hJimage : Offenders.IsConjugateTo (J.map m.quotient) (Offenders.D 5) := by
    simpa only [J, T, intrinsic_thompson hRH] using himage
  obtain ⟨g, hg, hgen, hdim⟩ := exists_local_conjugate_pair m J hJimage
  have hgres : g ∈ pResidual 2 H := by
    have he : L.subgroupOf H = pResidual 2 H := by
      rw [← hres]
      exact comap_map_eq_self_of_injective H.subtype_injective _
    rwa [← he]
  let X : Fin 2 → Subgroup H := ![J, J.map (MulAut.conj g).toMonoidHom]
  have hXsup : (⨆ i, X i) = J ⊔ J.map (MulAut.conj g).toMonoidHom := by
    apply le_antisymm
    · apply iSup_le
      intro i
      fin_cases i
      · exact le_sup_left
      · exact le_sup_right
    · exact sup_le (le_iSup X 0) (le_iSup X 1)
  have hJT : J ≤ T := sSup_le fun _ hE => hE.1
  have hJself : elementaryAbelianMaxJ J = J := self_thompson T
  have hJrank : twoRank J = twoRank T := twoRank_eq_of_intermediate T J le_rfl hJT
  have hfixed := native_fixedCodim hVH
  let e : (H ⧸ centralizer (V : Set H)) ≃* Equiv.Perm (Fin 5) :=
    (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective m.quotient
        (quotient_surjective_of_image m J hJimage))
  have he : e.toMonoidHom.comp (BaumannArgument.actionMap V) = m.quotient := by
    ext x
    rfl
  have hmap (B : Subgroup H) : (B.map (BaumannArgument.actionMap V)).map e.toMonoidHom =
      B.map m.quotient := by rw [map_map, he]
  have hno : BaumannArgument.NoStrongOffenders V T := no_strong_of_model m hVH e he T
  have hQT : pCore 2 H ≤ T := by
    apply (map_le_map_iff_of_injective H.subtype_injective).mp
    exact hTmap ▸ HCore_le_R h
  have hQ : T ⊓ centralizer (V : Set H) = pCore 2 H := by
    rw [hC, inf_eq_right.mpr hQT]
  have hcore : pCoreIn 2 (pResidual 2 H) ≤ T ⊓ centralizer (V : Set H) := by
    apply (map_le_map_iff_of_injective H.subtype_injective).mp
    rw [map_pCoreIn_of_injective _ _ _ H.subtype_injective, hres, map_fixed, hTmap, hVmap]
    exact blockCore_le_sylow_centralizer h hc
  have hCL : pResidual 2 H ⊓ centralizer (V : Set H) = pCoreIn 2 (pResidual 2 H) := by
    apply map_injective H.subtype_injective
    rw [map_fixed, hres, hVmap, map_pCoreIn_of_injective _ _ _ H.subtype_injective, hres]
    exact block_centralizer_eq h hc
  have hAD : BaumannArgument.HypothesesAD V T X := by
    refine {
      R_two := ?_
      V_le_R := comap_mono (module_le_R h)
      core_le := hcore
      normalizes := ?_
      centralizer_le_frattini := ?_
      no_strong := hno
      conjugate_into := ?_
      self_thompson := ?_
      rank_eq := ?_
      image_generation := ?_
      codimension_sum := ?_ }
    · obtain ⟨P, hP⟩ := h.sylow
      have hPT : (P : Subgroup H) = T := map_injective H.subtype_injective (hP.trans hTmap.symm)
      exact hPT ▸ P.isPGroup'
    · change pResidual 2 H ≤ normalizer ((T ⊓ centralizer (V : Set H) : Subgroup H) : Set H)
      rw [hQ, normalizer_eq_top]
      exact le_top
    · rw [hCL]
      exact core_le_frattini _
    · intro i
      fin_cases i
      · refine ⟨1, one_mem _, ?_⟩
        change J.conjBy 1 ≤ T
        rwa [conjBy_one]
      · refine ⟨g⁻¹, inv_mem hgres, ?_⟩
        change (J.conjBy g).conjBy g⁻¹ ≤ T
        rwa [conjBy_inv]
    · intro i
      fin_cases i
      · exact hJself
      · change elementaryAbelianMaxJ (J.map (MulAut.conj g).toMonoidHom) = _
        exact (elementaryAbelianMaxJ_map_equiv (MulAut.conj g) J).trans
          (congrArg (fun B => B.map (MulAut.conj g).toMonoidHom) hJself)
    · intro i
      fin_cases i
      · exact hJrank
      · exact (twoRank_map_equiv (MulAut.conj g) J).trans hJrank
    · rw [← Subgroup.map_iSup]
      have hi : (⨆ i, X i).map (BaumannArgument.actionMap V) = ⊤ := by
        apply map_injective (f := e.toMonoidHom) e.injective
        rw [hmap, hXsup, hgen, map_top_of_surjective _ e.surjective]
      rw [hi]
      exact le_top
    · rw [Fin.sum_univ_two]
      change BaumannArgument.fixedCodim V J +
        BaumannArgument.fixedCodim V (J.map (MulAut.conj g).toMonoidHom) ≤ _
      rw [hfixed, hfixed, hfixed, hres, hdim, block_fixed_codimension m hLH]
  have halpha := lemma_B_2_18_2 V T X hAD (hXsup ▸ le_sup_left)
  have halphamap : (thompsonAlpha T).map H.subtype = thompsonAlpha R := by
    unfold thompsonAlpha
    rw [← omegaOneCenterAmbient_map_injective H.subtype H.subtype_injective,
      ← elementaryAbelianMaxJ_map_injective H.subtype H.subtype_injective, hTmap]
  have hm := congrArg (fun B : Subgroup H => B.map H.subtype) halpha
  rwa [Subgroup.map_sup, map_fixed, map_fixed, halphamap, hres, hVmap,
    ← elementaryAbelianMaxJ_map_injective H.subtype H.subtype_injective, hTmap] at hm

/-- B.2.18(2) applied to the actual natural A₅-block action and the pair
J(R), J(R)^g. The centralizer theorem remains the explicit earlier input. -/
theorem alpha_decomposition (h : Configuration K A H R L)
    (hc : H ⊓ centralizer (U L : Set G) = pCoreIn 2 H)
    (hL : ChapterC.IsAlternatingBlock L 5) :
    thompsonAlpha R = (thompsonAlpha R ⊓ centralizer (L : Set G)) ⊔
      (U L ⊓ centralizer (elementaryAbelianMaxJ R : Set G)) := by
  obtain ⟨m⟩ := naturalActionInput A H R L h hc hL
  exact alpha_decomposition_of_model h hc m (thompsonImageInput A H R L h hc hL m)

end CFSG.Quasithin.ChapterE.Section06.InvariantSubspaces.LocalIndex.Baumann.AlternatingFive

namespace CFSG.Quasithin.ChapterE.Section06.InvariantSubspaces.LocalIndex.Baumann
open Subgroup
universe u
variable {G : Type u} [Group G] [Finite G] {K : GroupClass.{u}}

/-- The alternating-five alpha input, with the actual action, offenders,
and all hypotheses of Baumann's Argument discharged. -/
theorem alternatingFiveAlphaInput : AlternatingFiveAlphaInput (G := G) K := by
  intro A H R L h hc hL
  calc
    ChapterB.thompsonAlpha R = _ := AlternatingFive.alpha_decomposition h hc hL
    _ ≤ _ := sup_le_sup_left inf_le_left _

end CFSG.Quasithin.ChapterE.Section06.InvariantSubspaces.LocalIndex.Baumann

end
