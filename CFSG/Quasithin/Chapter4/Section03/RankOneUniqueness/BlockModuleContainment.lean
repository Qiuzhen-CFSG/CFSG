module
public import CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.BlockAlternativesPreparation
public import CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.BlockCrossing
public import Theory.GroupTheory.CommutatorPreimage

/-!
# The source full module inside the original block layer

Self-centralization of the generalized Fitting subgroup puts the source
module in O₂(K). Its commutator identity then puts it in U(K) and in
[U(K),L]. The original escaping inclusion makes the first containment strict.
Perfectness of L also removes a possible error in the K-fixed layer when
identifying [U(K),L]. That last lemma keeps its module-calculation premise
explicit; it is not an assertion of the unproved parabolic marking.

All subgroups use the original inclusions K ≤ H ≤ G. The full module is
Chapter4.Section02.Unitary.fullModule, exactly as in BlockCrossing.
Source: Aschbacher--Smith C.2.8, C.4.1 and the SL₃ step of original 4.3.7,
printed pp.147,151--153,615--616.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}

omit [Finite G] in
private theorem source_span (c : SourceConfiguration T L) :
    conjugateSpanBy L (c.H ⊓ normalizer (L : Set G)) = L :=
  le_antisymm (conjugateSpanBy_le le_rfl inf_le_right) (le_conjugateSpanBy _ _)

theorem SourceConfiguration.fullModule_le_blockLayer
    (c : SourceConfiguration T L) (hf : generalizedFitting c.K = pCore 2 c.K) :
    Section02.Unitary.fullModule L ((L ⊔ (T : Subgroup G)).pCoreIn 2) ≤
      c.blockLayer := by
  let W := Section02.Unitary.fullModule L ((L ⊔ (T : Subgroup G)).pCoreIn 2)
  let f : c.K →* G := c.H.subtype.comp c.K.subtype
  have hWL : W ≤ L := by simpa only [source_span c] using c.c28.module_le
  have hWcomm : W = ⁅W,L⁆ := by
    simpa only [source_span c] using c.c28.module_commutator
  have hQR : (pCore 2 c.K).map f ≤ c.I.pCoreIn 2 := by
    rw [← map_map]
    exact (map_mono (pCoreIn_le_of_subnormal 2 c.component.subnormal)).trans
      c.c28.ambient_core_le_radical
  have hWC : W ≤ centralizer ((pCore 2 c.K).map f : Set G) := by
    apply le_trans _ (centralizer_le hQR)
    intro w hw
    obtain ⟨v,hv,rfl⟩ := c.c28.module_le_center_radical hw
    intro r hr
    exact congrArg (fun x : c.I.pCoreIn 2 => (x : G)) (Subgroup.mem_center_iff.mp hv ⟨r,hr⟩)
  have hWQ : W ≤ (pCore 2 c.K).map f := by
    intro w hw
    obtain ⟨k,hk,hkw⟩ := c.le_component (hWL hw)
    let x : c.K := ⟨k,hk⟩
    have hx : x ∈ centralizer (pCore 2 c.K : Set c.K) := by
      intro y hy
      apply Subtype.ext
      apply Subtype.ext
      change f y * f x = f x * f y
      have he : f x = w := hkw
      rw [he]
      exact hWC hw (f y) (mem_map_of_mem f hy)
    have hxQ : x ∈ pCore 2 c.K := by
      rw [← hf] at hx ⊢
      exact centralizer_generalizedFitting_le c.K hx
    exact ⟨x,hxQ,hkw⟩
  have hLK : L ≤ (⊤ : Subgroup c.K).map f := by
    rw [← map_map,← MonoidHom.range_eq_map,range_subtype]
    exact c.le_component
  calc
    W = ⁅W,L⁆ := hWcomm
    _ ≤ ⁅(pCore 2 c.K).map f,(⊤ : Subgroup c.K).map f⁆ := commutator_mono hWQ hLK
    _ = c.blockLayer := by rw [← map_commutator,← map_map]; rfl

theorem SourceConfiguration.fullModule_le_block_commutator
    (c : SourceConfiguration T L) (hf : generalizedFitting c.K = pCore 2 c.K) :
    Section02.Unitary.fullModule L ((L ⊔ (T : Subgroup G)).pCoreIn 2) ≤
      ⁅c.blockLayer,L⁆ := by
  have hc := c.c28.module_commutator
  rw [source_span c] at hc
  calc
    _ = ⁅Section02.Unitary.fullModule L ((L ⊔ (T : Subgroup G)).pCoreIn 2),L⁆ := hc
    _ ≤ ⁅c.blockLayer,L⁆ := commutator_mono (c.fullModule_le_blockLayer hf) le_rfl

theorem SourceConfiguration.fullModule_lt_blockLayer
    (c : SourceConfiguration T L) (hf : generalizedFitting c.K = pCore 2 c.K) :
    Section02.Unitary.fullModule L ((L ⊔ (T : Subgroup G)).pCoreIn 2) <
      c.blockLayer := by
  apply lt_of_le_of_ne (c.fullModule_le_blockLayer hf)
  intro he
  have hn := c.blockLayer_normalized
  rw [← he] at hn
  have hHM := (le_inf le_rfl hn).trans c.c28.module_normalizer
  exact c.outside (hHM.trans inf_le_right)

/-- To identify the full commutator module, it suffices to do so modulo
the actual K-fixed layer. Perfectness removes any remaining central
displacement; no splitting of the block module is required. -/
theorem SourceConfiguration.block_commutator_eq_fullModule_of_fixed_layer
    (c : SourceConfiguration T L) (hf : generalizedFitting c.K = pCore 2 c.K)
    (hmod : ⁅c.blockLayer,L⁆ ≤
      Section02.Unitary.fullModule L ((L ⊔ (T : Subgroup G)).pCoreIn 2) ⊔
        (c.blockLayer ⊓ centralizer (c.K.map c.H.subtype : Set G))) :
    ⁅c.blockLayer,L⁆ =
      Section02.Unitary.fullModule L ((L ⊔ (T : Subgroup G)).pCoreIn 2) := by
  let W := Section02.Unitary.fullModule L ((L ⊔ (T : Subgroup G)).pCoreIn 2)
  let Z := c.blockLayer ⊓ centralizer (c.K.map c.H.subtype : Set G)
  have hW : W = ⁅W,L⁆ := by
    simpa only [source_span c] using c.c28.module_commutator
  have hWL : W ≤ L := by simpa only [source_span c] using c.c28.module_le
  have hZW : Z ≤ normalizer (W : Set G) :=
    (inf_le_right.trans (centralizer_le (hWL.trans c.le_component))).trans
      (Subgroup.centralizer_le_normalizer _)
  have hZ : ⁅Z,L⁆ = ⊥ := commutator_eq_bot_iff_le_centralizer.mpr
    (inf_le_right.trans (centralizer_le c.le_component))
  have hpre : W ⊔ Z ≤ commutatorPreimage (W ⊔ Z) L W :=
    sup_le (le_commutatorPreimage le_sup_left hW.ge)
      (le_commutatorPreimage le_sup_right (hZ.le.trans bot_le))
  have hiter : ⁅⁅c.blockLayer,L⁆,L⁆ ≤ W :=
    (commutator_mono (hmod.trans hpre) le_rfl).trans
      (commutator_commutatorPreimage_le _ _ _ (sup_le W.le_normalizer hZW))
  let : Group.IsPerfect L := source_span c ▸ c.c28.span_perfect
  have hp : IsPPerfect 2 L := by
    intro N hN hq
    let := hN
    have hs : Subsingleton (L ⧸ N) := by
      by_contra! hn
      exact Group.IsPerfect.not_isNilpotent (L ⧸ N) hq.isNilpotent
    apply eq_top_iff.mpr
    intro x _
    exact (QuotientGroup.eq_one_iff x).mp (Subsingleton.elim _ _)
  rw [commutator_isPPerfect_idempotent L c.blockLayer hp
    (T.isPGroup'.to_le (c.blockLayer_le_sylow.trans inf_le_left))
    ((c.le_I.trans c.I_le_H).trans c.blockLayer_normalized)] at hiter
  exact le_antisymm hiter (c.fullModule_le_block_commutator hf)

end CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness
