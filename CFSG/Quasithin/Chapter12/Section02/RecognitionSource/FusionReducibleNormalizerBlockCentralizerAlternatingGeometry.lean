module
public import CFSG.Quasithin.Chapter12.Section02.RecognitionSource.FusionReducibleNormalizerBlockCentralizerContracts
public import CFSG.Quasithin.ChapterC.Section01.BlockStructure.CoreAction
public import CFSG.Quasithin.ChapterC.Section01.BlockStructure.NormalizedTwoGroups
public import Theory.Frattini.BinarySquares
public import Theory.GroupTheory.ReducedNormal.SylowCenterClosure

/-!
# The actual omega module and the invariant-core source contract

The omega module is the normal closure of Ω₁Z(T) inside LT, mapped back
into G. Characteristic two makes it elementary, puts it in the local core,
and makes that core centralize it. No identification with chosen V is made.
The square argument also proves Φ(O₂(LT)) ≤ C_T(L) directly from shortness.

In an escaping configuration W contains the intrinsic layer U(L), so the
Sylow centralizer of W is exactly Q. This proves Q=C_S(W) for S=QWᵈ and
transfers the proved movement of U(L) to the actual W. The remaining source
obligations are d-invariance of S, Q=W C_Q(Wᵈ), and |S:Q|=2.

Source: Aschbacher–Smith B.2.14, C.1.13(a), and 3.3.31, printed pp.78,
124–125, and602. The next module proves the contradiction from these facts.
-/

public section
open Subgroup Theory.GroupTheory
open scoped commutatorElement
namespace CFSG.Quasithin.Chapter12.Section02.RecognitionSource.FusionReducibleNormalizer
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

/-- The actual omega-center-generated module of LT. -/
@[expose] def blockOmegaModule (T : Sylow 2 G) (L : Subgroup G) : Subgroup G :=
  let H := L ⊔ (T : Subgroup G)
  let P : Sylow 2 H := T.subtype le_sup_right
  (normalClosure (Stellmacher.omegaOneCenterAmbient (P : Subgroup H) : Set H)).map H.subtype

omit [Finite G] in
private theorem core_le_sylow : (L ⊔ (T : Subgroup G)).pCoreIn 2 ≤ (T : Subgroup G) := by
  simpa only [Sylow.coe_subtype, map_subgroupOf_eq_of_le le_sup_right] using
    pCoreIn_le_sylow (L ⊔ (T : Subgroup G)) (T.subtype le_sup_right)

omit [Finite G] in
private theorem join_normalizes_core : L ⊔ (T : Subgroup G) ≤
    normalizer ((L ⊔ (T : Subgroup G)).pCoreIn 2 : Set G) :=
  (L ⊔ (T : Subgroup G)).le_normalizer.trans
    (normalizer_le_normalizer_characteristic_image _ (pCore 2 _))

theorem blockOmegaModule_elementary
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) :
    IsElementaryAbelian 2 (blockOmegaModule T L) :=
  (omegaCenter_normalClosure_reduced (T.subtype le_sup_right)
    (join_characteristicTwo h)).elementary.map _

theorem blockOmegaModule_le_core
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) :
    blockOmegaModule T L ≤ (L ⊔ (T : Subgroup G)).pCoreIn 2 :=
  map_mono ((omegaCenter_normalClosure_reduced (T.subtype le_sup_right)
    (join_characteristicTwo h)).le_reducedPSubgroup.trans (reducedPSubgroup_le_pCore 2 _))

private theorem short_residual (hb : ChapterC.IsShort L) :
    Stellmacher.twoResidualAmbient L = L := by
  have hi : Stellmacher.twoResidualSubgroup L = ⊤ := by
    apply top_unique
    apply le_sInf
    rintro N ⟨hn, n, hi⟩
    let := hn
    have hp : IsPGroup 2 (L ⧸ N) := IsPGroup.iff_card.mpr
      ⟨n, by simpa only [index_eq_card] using hi⟩
    rw [hb.twoPerfect N hn hp]
  rw [Stellmacher.twoResidualAmbient, hi, ← MonoidHom.range_eq_map, range_subtype]

omit [Finite G] in
/-- The source omega-center is contained in its literal orbit closure. -/
theorem omegaCenter_le_blockOmegaModule :
    omegaCenterIn (T : Subgroup G) ≤ blockOmegaModule T L := by
  let H := L ⊔ (T : Subgroup G)
  let P := T.subtype (show (T : Subgroup G) ≤ H from le_sup_right)
  have he : (Stellmacher.omegaOneCenterAmbient (P : Subgroup H)).map H.subtype =
      omegaCenterIn (T : Subgroup G) := by
    rw [← Stellmacher.omegaOneCenterAmbient_map_injective H.subtype H.subtype_injective,
      Sylow.coe_subtype, map_subgroupOf_eq_of_le le_sup_right]
    rfl
  rw [← he]
  exact map_mono (f := H.subtype) le_normalClosure

/-- The local two-core fixes the entire source module. -/
theorem local_core_centralizes_blockOmegaModule
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) :
    (L ⊔ (T : Subgroup G)).pCoreIn 2 ≤ centralizer (blockOmegaModule T L : Set G) := by
  apply le_centralizer_iff.mp
  exact (map_mono (f := (L ⊔ (T : Subgroup G)).subtype) ((omegaCenter_normalClosure_reduced (T.subtype le_sup_right)
    (join_characteristicTwo h)).le_reducedPSubgroup.trans
      (reducedPSubgroup_le_centralizer_pCore 2 _))).trans
        (map_centralizer_le_centralizer_image _ _)

/-- C.1.13(a) on the literal local core, with all normality relative to LT. -/
theorem local_core_frattini_le_sylow_centralizer (D : ChosenModule T L V)
    (hb : ChapterC.IsShort L) :
    (frattini ((L ⊔ (T : Subgroup G)).pCoreIn 2)).map
      ((L ⊔ (T : Subgroup G)).pCoreIn 2).subtype ≤
        (T : Subgroup G) ⊓ centralizer (L : Set G) := by
  let Q := (L ⊔ (T : Subgroup G)).pCoreIn 2
  let U := (ChapterC.blockU L).map L.subtype
  let : IsElementaryAbelian 2 U := hb.elementary.map L.subtype
  have hQU : Q ≤ centralizer (U : Set G) :=
    hb.normalizing_twoGroup_centralizes_blockU (isPGroup_pCoreIn 2 _)
      (le_sup_left.trans join_normalizes_core)
      (core_le_sylow.trans D.sylow_normalizes_component)
  have hcomm : ⁅L, Q⁆ ≤ U := by
    rw [show U = ⁅L.pCoreIn 2, L⁆ from block_module_eq_commutator]
    exact (ChapterC.c6_3_commutator_core_bound L (T : Subgroup G)
      D.sylow_normalizes_component (short_residual hb)).1
  have hsq (q : Q) : (q : G) ^ 2 ∈ centralizer (L : Set G) := by
    intro l hl
    let c := l * q * l⁻¹ * (q : G)⁻¹
    have hc : c ∈ U := hcomm (commutator_mem_commutator hl q.property)
    have hcq : Commute c (q : G) := hQU q.property c hc
    have hc2 : c ^ 2 = 1 := elemPow_eq_one_of_isElementaryAbelian c hc
    have he : (l * q * l⁻¹) ^ 2 = (q : G) ^ 2 := by
      calc
        (l * q * l⁻¹) ^ 2 = (c * q) ^ 2 := by congr 1; dsimp [c]; group
        _ = c ^ 2 * (q : G) ^ 2 := hcq.mul_pow 2
        _ = (q : G) ^ 2 := by rw [hc2, one_mul]
    calc
      l * (q : G) ^ 2 = (l * q * l⁻¹) ^ 2 * l := by simp only [pow_two]; group
      _ = (q : G) ^ 2 * l := by rw [he]
  apply le_inf ((map_subtype_le _).trans core_le_sylow)
  rw [(isPGroup_pCoreIn 2 (L ⊔ (T : Subgroup G))).frattini_eq_closure_squares,
    map_le_iff_le_comap]
  apply (closure_le _).mpr
  rintro _ ⟨q, rfl⟩
  exact hsq q

omit [Finite G] in
/-- The orbit closure is normal in its defining local join. -/
theorem join_normalizes_blockOmegaModule :
    L ⊔ (T : Subgroup G) ≤ normalizer (blockOmegaModule T L : Set G) := by
  let H := L ⊔ (T : Subgroup G)
  let P : Sylow 2 H := T.subtype le_sup_right
  let W := normalClosure (Stellmacher.omegaOneCenterAmbient (P : Subgroup H) : Set H)
  simpa only [blockOmegaModule, H, P, W, normalizer_eq_top,
    ← MonoidHom.range_eq_map, range_subtype] using
    W.le_normalizer_map H.subtype

/-- In an escaping configuration the actual omega orbit is moved by L. -/
theorem blockOmegaModule_not_centralizes
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (hescape : ¬ normalizer (T : Set G) ≤ normalizer (L : Set G)) :
    ¬ blockOmegaModule T L ≤ centralizer (L : Set G) := by
  intro hc
  let Z := omegaCenterIn (T : Subgroup G)
  have hZT : Z ≤ (T : Subgroup G) := fun z hz =>
    ((mem_omegaCenterIn_iff _ _).mp hz).1
  have hTne : (T : Subgroup G) ≠ ⊥ := fun he => D.ne_bot
    (bot_unique (D.le_sylow.trans_eq he))
  have hZne : Z ≠ ⊥ := by
    have hh := inf_omegaCenterIn_ne_bot_of_normalized_twoGroup
      (T : Subgroup G) (T : Subgroup G) le_rfl T.isPGroup'
      (T : Subgroup G).le_normalizer hTne
    exact fun he => hh (by rw [show omegaCenterIn (T : Subgroup G) = ⊥ from he, inf_bot_eq])
  have hLZ : L ≤ normalizer (Z : Set G) :=
    (le_centralizer_iff.mp (omegaCenter_le_blockOmegaModule.trans hc)).trans
      (Subgroup.centralizer_le_normalizer _)
  have hNZ : normalizer (T : Set G) ≤ normalizer (Z : Set G) :=
    normalizer_le_normalizer_omegaCenterIn _
  exact hescape (hNZ.trans (D.normal_subgroup_normalizer_le h.toHypothesis1221
    (hZT.trans le_sup_right) hZne
    (sup_le hLZ ((T : Subgroup G).le_normalizer.trans hNZ))))
/-- The source omega module contains the intrinsic block layer, without identifying it with chosen V. -/
theorem blockU_le_blockOmegaModule
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (hescape : ¬ normalizer (T : Set G) ≤ normalizer (L : Set G))
    (hb : ChapterC.IsShort L) :
    (ChapterC.blockU L).map L.subtype ≤ blockOmegaModule T L := by
  exact (hb.blockU_le_or_centralizes_of_normalizing_twoGroup
    ((isPGroup_pCoreIn 2 _).to_le (blockOmegaModule_le_core h))
    (le_sup_left.trans join_normalizes_blockOmegaModule)
    ((blockOmegaModule_le_core h).trans
      (core_le_sylow.trans D.sylow_normalizes_component))).resolve_right
    (blockOmegaModule_not_centralizes h D hescape)

/-- The literal omega module has Sylow centralizer exactly O₂(LT). -/
theorem sylow_centralizer_blockOmegaModule_eq_local_core
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (hescape : ¬ normalizer (T : Set G) ≤ normalizer (L : Set G))
    (hb : ChapterC.IsShort L) :
    (T : Subgroup G) ⊓ centralizer (blockOmegaModule T L : Set G) =
      (L ⊔ (T : Subgroup G)).pCoreIn 2 := by
  apply le_antisymm
  · exact (inf_le_inf_left _ (centralizer_le
      (blockU_le_blockOmegaModule h D hescape hb))).trans
      (hb.sylow_centralizer_blockU_eq_pCoreIn D.sylow_normalizes_component).le
  · exact le_inf core_le_sylow (local_core_centralizes_blockOmegaModule h)

/-- The source subgroup S=QWᵈ, with the printed right-conjugation convention. -/
@[expose] def alternatingCoreJoin (T : Sylow 2 G) (L : Subgroup G) (d : G) : Subgroup G :=
  (L ⊔ (T : Subgroup G)).pCoreIn 2 ⊔
    (blockOmegaModule T L).map (MulAut.conj d⁻¹).toMonoidHom

/-- The four geometric facts used from the first half of source 3.3.31.
These do not assert triviality of C_T(L), preservation of Q, or any terminal contradiction. -/
structure AlternatingInvariantCoreGeometry (T : Sylow 2 G) (L : Subgroup G) (d : G) : Prop where
  invariant : d ∈ normalizer (alternatingCoreJoin T L d : Set G)
  centralizer : (L ⊔ (T : Subgroup G)).pCoreIn 2 =
    alternatingCoreJoin T L d ⊓ centralizer (blockOmegaModule T L : Set G)
  factorization : (L ⊔ (T : Subgroup G)).pCoreIn 2 = blockOmegaModule T L ⊔
    ((L ⊔ (T : Subgroup G)).pCoreIn 2 ⊓ Subgroup.centralizer
      ((blockOmegaModule T L).map (MulAut.conj d⁻¹).toMonoidHom : Set G))
  index : ((L ⊔ (T : Subgroup G)).pCoreIn 2).relIndex (alternatingCoreJoin T L d) = 2

/-- The centralizer clause of 3.3.31 holds for every actor normalizing T. -/
theorem alternatingCoreJoin_centralizer
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (hescape : ¬ normalizer (T : Set G) ≤ normalizer (L : Set G))
    (hb : ChapterC.IsShort L) {d : G} (hd : d ∈ normalizer (T : Set G)) :
    (L ⊔ (T : Subgroup G)).pCoreIn 2 =
      alternatingCoreJoin T L d ⊓ centralizer (blockOmegaModule T L : Set G) := by
  have hWT := (blockOmegaModule_le_core h).trans core_le_sylow
  have hWdT : (blockOmegaModule T L).map (MulAut.conj d⁻¹).toMonoidHom ≤
      (T : Subgroup G) := by
    rw [← mem_normalizer_iff_map_conj_eq.mp ((normalizer (T : Set G)).inv_mem hd)]
    exact map_mono hWT
  apply le_antisymm (le_inf le_sup_left (local_core_centralizes_blockOmegaModule h))
  exact (inf_le_inf_right _ (sup_le core_le_sylow hWdT)).trans
    (sylow_centralizer_blockOmegaModule_eq_local_core h D hescape hb).le

/-- Source 3.3.26 on the actual omega module, with its local normality and
centralizer clause. The invariant-core, factorization and index claims remain separate. -/
theorem exists_odd_alternating_omega_movement
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (hescape : ¬ normalizer (T : Set G) ≤ normalizer (L : Set G))
    (hi : BlockLocalInvariance T L) (hb : ChapterC.IsAlternatingBlock L 6) :
    ∃ d : G, Odd (orderOf d) ∧ d ∈ normalizer (T : Set G) ∧
      d ∉ normalizer (L : Set G) ∧
      ¬ (blockOmegaModule T L).map (MulAut.conj d⁻¹).toMonoidHom ≤
        (L ⊔ (T : Subgroup G)).pCoreIn 2 ∧
      blockLocalResidual T L ⊔ (T : Subgroup G) ≤ normalizer
        ((blockOmegaModule T L).map (MulAut.conj d⁻¹).toMonoidHom : Set G) ∧
      (L ⊔ (T : Subgroup G)).pCoreIn 2 =
        alternatingCoreJoin T L d ⊓ centralizer (blockOmegaModule T L : Set G) := by
  obtain ⟨A, hA, ho, _, _, d, hd, hout, hmove⟩ :=
    exists_odd_block_movement h D hescape (Or.inl hb)
  have hdT := hA hd
  have hdX := (hi.1 (Or.inl hb)).1 hdT
  have hXL : blockLocalResidual T L ≤ L := (map_subtype_le _).trans inf_le_left
  have hNW : blockLocalResidual T L ⊔ (T : Subgroup G) ≤
      normalizer (blockOmegaModule T L : Set G) :=
    (sup_le_sup_right hXL _).trans join_normalizes_blockOmegaModule
  have hn := (map_mono (f := (MulAut.conj d⁻¹).toMonoidHom) hNW).trans
    ((blockOmegaModule T L).le_normalizer_map (MulAut.conj d⁻¹).toMonoidHom)
  have hXd : (blockLocalResidual T L).map (MulAut.conj d⁻¹).toMonoidHom =
      blockLocalResidual T L := mem_normalizer_iff_map_conj_eq.mp
    ((normalizer (blockLocalResidual T L : Set G)).inv_mem hdX)
  have hTd : (T : Subgroup G).map (MulAut.conj d⁻¹).toMonoidHom = (T : Subgroup G) :=
    mem_normalizer_iff_map_conj_eq.mp ((normalizer (T : Set G)).inv_mem hdT)
  rw [Subgroup.map_sup, hXd, hTd] at hn
  refine ⟨d, ho.of_dvd_nat (A.orderOf_dvd_natCard hd), hdT, hout, ?_, hn,
    alternatingCoreJoin_centralizer h D hescape hb.2.1 hdT⟩
  exact fun hw => hmove ((map_mono (blockU_le_blockOmegaModule h D hescape hb.2.1)).trans hw)

/-- Remaining source construction, with the alternating natural marking and
local invariance unchanged. The chosen V is not substituted for the omega module. -/
@[expose] def AlternatingInvariantCoreGeometrySource
    (T : Sylow 2 G) (L V : Subgroup G) : Prop :=
  Hypothesis1223 KnownSimple.IsKnownSimple T L → ChosenModule T L V →
    Structural1222.{u} KnownSimple.IsKnownSimple → NoEscape L V →
    V ⊓ centralizer (L : Set G) ≠ ⊥ →
    ¬ normalizer (T : Set G) ≤ normalizer (L : Set G) →
    BlockLocalInvariance T L → ChapterC.IsAlternatingBlock L 6 →
    ∃ d : G, Odd (orderOf d) ∧ d ∈ normalizer (T : Set G) ∧
      d ∉ normalizer (L : Set G) ∧ AlternatingInvariantCoreGeometry T L d

end CFSG.Quasithin.Chapter12.Section02.RecognitionSource.FusionReducibleNormalizer
