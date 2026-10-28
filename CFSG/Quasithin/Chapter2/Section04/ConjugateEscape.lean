module
public import CFSG.Quasithin.Chapter2.Section04.BlockResidual
public import CFSG.Quasithin.ChapterC.Section01.BlockBasics
public import Theory.GroupTheory.PResidual.SubnormalCoreAction
public import Theory.GroupTheory.PGroup.SubnormalCore
public import Theory.GroupTheory.ConjugateEscape
public import Mathlib.GroupTheory.IndexNormal
public import Theory.GroupTheory.IndexTwoConjugatePair
public import Theory.GroupTheory.CharacteristicCentralizerFusion

/-!
# The escaping conjugates in source Lemma 2.4.5

For the selected minimal parabolic H = ⟨L,S⟩, the genuine block module
U₀ = ⟨U(L)^S⟩ is nontrivial and lies in O₂(H). Subnormality and
2-perfection give [L,O₂(H)] ≤ U(L) ≤ U₀. If every M₀-conjugate of U₀
lay in O₂(H), their join would be a nontrivial subgroup of S normalized
by both H and M₀. The original normalizer equality 2.4.4 excludes this
whenever S < M₀ ≤ T and M₀ normalizes S.

If |M₀:S| = 2, every element of M₀−S gives the same conjugate of U₀,
so every such conjugate escapes O₂(H). This proves the escape assertion
of Aschbacher–Smith 2.4.5(2b), printed p.528 of the combined manuscript
(1 March 2004), on the actual selected block and Sylow maps. It uses no
unproved C.5 pushing-up implication; the corresponding centralizer factor D=C_S(L₀) also has trivial intersection
with its outside conjugate: their intersection is H-normal and M₀-invariant,
so the same normalizer equality excludes it. Thus both assertions in
2.4.5(2b) are proved; the core factorization in (2a) remains separate.
-/

@[expose] public section
open Subgroup
namespace CFSG.Quasithin.Chapter2
variable {G : Type*} [Group G] [Finite G] {M : Subgroup G}

omit [Finite G] in
/-- The generated module retains the nonzero module of the original short block. -/
theorem MinimalBlockSetup.U0_ne_bot (d : MinimalBlockSetup M) : d.U0 ≠ ⊥ := by
  intro he
  have h := le_iSup_conjugates ((ChapterC.blockU d.block).map d.block.subtype)
    (d.S : Subgroup d.H)
  change (ChapterC.blockU d.block).map d.block.subtype ≤ d.U0 at h
  have hb := map_eq_bot_iff_of_injective (ChapterC.blockU d.block) d.block.subtype_injective
  exact d.block_type.1.short.blockU_ne_bot (hb.mp (bot_unique (he ▸ h)))

/-- The module and its Sylow conjugates lie in the actual two-core of H. -/
theorem MinimalBlockSetup.U0_le_core (d : MinimalBlockSetup M) : d.U0 ≤ pCore 2 d.H := by
  apply iSup_conjugates_le_of_le_normalizer
  · apply (map_mono ChapterC.blockU_le_core).trans
    have h := pCoreAmbient_mono_of_isSubnormalIn d.block ⊤ 2 le_top
      d.block_type.1.subnormal.subgroupOf
    change (pCore 2 d.block).map d.block.subtype ≤
      (pCore 2 (⊤ : Subgroup d.H)).map (Subgroup.topEquiv.toMonoidHom) at h
    rwa [pCore_map_iso] at h
  · rw [normalizer_eq_top]
    exact le_top

omit [Finite G] in
/-- The selected Sylow subgroup normalizes the source conjugate-generated module. -/
theorem MinimalBlockSetup.sylow_normalizes_U0 (d : MinimalBlockSetup M) :
    (d.S : Subgroup d.H) ≤ normalizer (d.U0 : Set d.H) :=
  le_normalizer_iSup_conjugates _ _

/-- The subnormal short block acts on the local two-core through U₀. -/
theorem MinimalBlockSetup.block_commutator_core_le_U0 (d : MinimalBlockSetup M) : ⁅d.block, pCore 2 d.H⁆ ≤ d.U0 := by
  rw [commutator_comm]
  exact (commutator_le_core_commutator_of_isSubnormal d.block (pCore 2 d.H)
    d.block_type.1.subnormal d.block_type.1.short.twoPerfect pCore_isPGroup
    (by rw [normalizer_eq_top]; exact le_top)).trans
      (le_iSup_conjugates _ _)



/-- Any proper normalizing two-overgroup of S contains an escaping conjugator.
All normalizer-barrier hypotheses are discharged by the literal source 2.4.4. -/
theorem MinimalBlockSetup.exists_U0_conjugate_escape
    (d : MinimalBlockSetup M) (T : Sylow 2 G)
    (hST : (d.S : Subgroup d.H).map d.H.subtype ≤ (T : Subgroup G))
    (M₀ : Subgroup G)
    (hSM₀ : (d.S : Subgroup d.H).map d.H.subtype < M₀)
    (hM₀T : M₀ ≤ (T : Subgroup G))
    (hM₀S : M₀ ≤ normalizer ((d.S : Subgroup d.H).map d.H.subtype : Set G)) :
    ∃ x ∈ M₀, x ∉ (d.S : Subgroup d.H).map d.H.subtype ∧
      ¬ (d.U0.map d.H.subtype).map (MulAut.conj x⁻¹ : G →* G) ≤ twoCore d.H := by
  let S : Subgroup G := (d.S : Subgroup d.H).map d.H.subtype
  let U₀ : Subgroup G := d.U0.map d.H.subtype
  let B : Subgroup G := d.block.map d.H.subtype
  have hU : U₀ ≠ ⊥ := by
    exact fun h => d.U0_ne_bot ((map_eq_bot_iff_of_injective _ d.H.subtype_injective).mp h)
  have hUQ : U₀ ≤ twoCore d.H := map_mono d.U0_le_core
  have hUS : U₀ ≤ S := hUQ.trans (pCoreIn_le_sylow d.H d.S)
  have hSN : S ≤ normalizer (U₀ : Set G) :=
    (map_mono d.sylow_normalizes_U0).trans (d.U0.le_normalizer_map d.H.subtype)
  have hcomm : ⁅B, twoCore d.H⁆ ≤ U₀ := by
    change ⁅d.block.map d.H.subtype, (pCore 2 d.H).map d.H.subtype⁆ ≤
      d.U0.map d.H.subtype
    simpa only [map_commutator] using map_mono (f := d.H.subtype)
      d.block_commutator_core_le_U0
  obtain ⟨y, hy, hyescape⟩ := exists_conjugate_not_le_of_no_common_normal
    U₀ S (twoCore d.H) B M₀ hU hUS hM₀S hcomm (by
      intro W hW hWS hBW hM₀W
      have hgen : B ⊔ S = d.H := by
        rw [← Subgroup.map_sup, d.generated, ← MonoidHom.range_eq_map, range_subtype]
      have hHW : d.H ≤ normalizer (W : Set G) := by
        rw [← hgen]
        exact sup_le hBW (hSM₀.le.trans hM₀W)
      have hn : (W.subgroupOf d.H).Normal :=
        (normal_subgroupOf_iff_le_normalizer (hWS.trans (map_subtype_le _))).mpr hHW
      have he := lemma_2_4_4 d.mem_gammaEvenZero.1 d.full_pair d.S le_rfl T hST
        W hW hWS hn
      exact hSM₀.not_ge ((le_inf hM₀T hM₀W).trans he.le))
  refine ⟨y⁻¹, M₀.inv_mem hy, ?_, ?_⟩
  · intro hys
    have hyS : y ∈ S := by simpa using S.inv_mem hys
    exact hyescape ((mem_normalizer_iff_map_conj_eq.mp (hSN hyS)).le.trans hUQ)
  · simpa using hyescape



/-- The escape assertion of 2.4.5(2b): every element outside S in an index-two
overgroup moves the actual U₀ outside the original O₂(H). -/
theorem MinimalBlockSetup.U0_conjugate_escape_of_index_two
    (d : MinimalBlockSetup M) (T : Sylow 2 G)
    (hST : (d.S : Subgroup d.H).map d.H.subtype ≤ (T : Subgroup G))
    (M₀ : Subgroup G)
    (hSM₀ : (d.S : Subgroup d.H).map d.H.subtype ≤ M₀)
    (hM₀T : M₀ ≤ (T : Subgroup G))
    (hindex : ((d.S : Subgroup d.H).map d.H.subtype).relIndex M₀ = 2)
    (x : G) (hx : x ∈ M₀) (hxS : x ∉ (d.S : Subgroup d.H).map d.H.subtype) :
    ¬ (d.U0.map d.H.subtype).map (MulAut.conj x⁻¹ : G →* G) ≤ twoCore d.H := by
  let S : Subgroup G := (d.S : Subgroup d.H).map d.H.subtype
  let U₀ : Subgroup G := d.U0.map d.H.subtype
  have hn : (S.subgroupOf M₀).Normal := normal_of_index_eq_two hindex
  have hM₀S : M₀ ≤ normalizer (S : Set G) :=
    (normal_subgroupOf_iff_le_normalizer hSM₀).mp hn
  have hlt : S < M₀ := lt_of_le_of_ne hSM₀ (by
    intro he
    have hi : S.relIndex M₀ = 1 := relIndex_eq_one.mpr he.ge
    have hi2 : S.relIndex M₀ = 2 := hindex
    omega)
  obtain ⟨y, hy, hyS, hyescape⟩ := d.exists_U0_conjugate_escape T hST M₀ hlt hM₀T hM₀S
  have hSN : S ≤ normalizer (U₀ : Set G) :=
    (map_mono d.sylow_normalizes_U0).trans (d.U0.le_normalizer_map d.H.subtype)
  have hxinv : x⁻¹ ∉ S := by
    intro hi
    exact hxS (show x ∈ S from by simpa only [inv_inv] using S.inv_mem hi)
  have hmul : y * x⁻¹ ∈ S := by
    have hi : (S.subgroupOf M₀).index = 2 := hindex
    exact (mul_mem_iff_of_index_two hi (a := (⟨y, hy⟩ : M₀))
      (b := (⟨x⁻¹, M₀.inv_mem hx⟩ : M₀))).mpr
      (by change (y ∈ S ↔ x⁻¹ ∈ S); exact iff_of_false hyS hxinv)
  have he : U₀.map (MulAut.conj y⁻¹ : G →* G) = U₀.map (MulAut.conj x⁻¹ : G →* G) := by
    have hfix := mem_normalizer_iff_map_conj_eq.mp
      ((normalizer (U₀ : Set G)).inv_mem (hSN hmul))
    calc
      U₀.map (MulAut.conj y⁻¹ : G →* G) =
          (U₀.map (MulAut.conj (y * x⁻¹)⁻¹ : G →* G)).map (MulAut.conj x⁻¹ : G →* G) := by
        rw [Subgroup.map_map U₀]
        apply congrArg (fun f : G →* G => U₀.map f)
        ext g
        simp [MulAut.conj_apply, mul_assoc]
      _ = U₀.map (MulAut.conj x⁻¹ : G →* G) := by rw [hfix]
  rwa [← he]



/-- The centralizer-disjointness assertion of 2.4.5(2b), proved from the
actual block closure and the original normalizer equality. -/
theorem MinimalBlockSetup.centralizer_disjoint_conjugate (d : MinimalBlockSetup M) (T : Sylow 2 G)
    (hST : (d.S : Subgroup d.H).map d.H.subtype ≤ (T : Subgroup G))
    (M₀ : Subgroup G)
    (hSM₀ : (d.S : Subgroup d.H).map d.H.subtype ≤ M₀)
    (hM₀T : M₀ ≤ (T : Subgroup G))
    (hindex : ((d.S : Subgroup d.H).map d.H.subtype).relIndex M₀ = 2)
    (x : G) (hx : x ∈ M₀) (hxS : x ∉ (d.S : Subgroup d.H).map d.H.subtype) :
    let D := (d.S : Subgroup d.H).map d.H.subtype ⊓
      centralizer (d.L0.map d.H.subtype : Set G)
    D ⊓ D.map (MulAut.conj x⁻¹ : G →* G) = ⊥ := by
  let S : Subgroup G := (d.S : Subgroup d.H).map d.H.subtype
  let L₀ : Subgroup G := d.L0.map d.H.subtype
  let D : Subgroup G := S ⊓ centralizer (L₀ : Set G)
  let W : Subgroup G := D ⊓ D.conjBy x⁻¹
  change W = ⊥
  have hn : (S.subgroupOf M₀).Normal := normal_of_index_eq_two hindex
  have hM₀S : M₀ ≤ normalizer (S : Set G) :=
    (normal_subgroupOf_iff_le_normalizer hSM₀).mp hn
  have hSL : S ≤ normalizer (L₀ : Set G) := by
    let := d.L0_normal
    exact (map_mono (show (d.S : Subgroup d.H) ≤ normalizer (d.L0 : Set d.H) by
      rw [normalizer_eq_top]; exact le_top)).trans (d.L0.le_normalizer_map d.H.subtype)
  have hSD : S ≤ normalizer (D : Set G) :=
    (le_inf S.le_normalizer (hSL.trans (normalizer_le_normalizer_centralizer L₀))).trans
      inf_normalizer_le_normalizer_inf
  have hMS : M₀ ≤ normalizer (W : Set G) :=
    index_two_normalizes_conjugate_inf hindex (M₀.inv_mem hx)
      (fun h => hxS (show x ∈ S from by simpa only [inv_inv] using S.inv_mem h))
      le_rfl (hM₀S (M₀.inv_mem hx)) hSD
  have hHW : d.H ≤ normalizer (W : Set G) := by
    rw [← d.ambient_L0_sup_sylow]
    refine sup_le ?_ (hSM₀.trans hMS)
    apply (le_centralizer_iff.mp (show W ≤ centralizer (L₀ : Set G) from
      inf_le_left.trans inf_le_right)).trans
    exact centralizer_le_normalizer _
  by_contra hW
  have he := lemma_2_4_4 d.mem_gammaEvenZero.1 d.full_pair d.S le_rfl T hST
    W hW (inf_le_left.trans inf_le_left)
    ((normal_subgroupOf_iff_le_normalizer
      (show W ≤ d.H from inf_le_left.trans (inf_le_left.trans (map_subtype_le _)))).mpr hHW)
  exact hxS (he.le ⟨hM₀T hx, hMS hx⟩)


/-- Both source assertions of Lemma 2.4.5(2b), with right conjugation and
all literal block, Sylow and core maps retained. -/
theorem MinimalBlockSetup.lemma_2_4_5_2b
    (d : MinimalBlockSetup M) (T : Sylow 2 G)
    (hST : (d.S : Subgroup d.H).map d.H.subtype ≤ (T : Subgroup G))
    (M₀ : Subgroup G)
    (hSM₀ : (d.S : Subgroup d.H).map d.H.subtype ≤ M₀)
    (hM₀T : M₀ ≤ (T : Subgroup G))
    (hindex : ((d.S : Subgroup d.H).map d.H.subtype).relIndex M₀ = 2)
    (x : G) (hx : x ∈ M₀) (hxS : x ∉ (d.S : Subgroup d.H).map d.H.subtype) :
    let D := (d.S : Subgroup d.H).map d.H.subtype ⊓
      centralizer (d.L0.map d.H.subtype : Set G)
    D ⊓ D.map (MulAut.conj x⁻¹ : G →* G) = ⊥ ∧
      ¬ (d.U0.map d.H.subtype).map (MulAut.conj x⁻¹ : G →* G) ≤ twoCore d.H :=
  ⟨d.centralizer_disjoint_conjugate T hST M₀ hSM₀ hM₀T hindex x hx hxS,
    d.U0_conjugate_escape_of_index_two T hST M₀ hSM₀ hM₀T hindex x hx hxS⟩

end CFSG.Quasithin.Chapter2
