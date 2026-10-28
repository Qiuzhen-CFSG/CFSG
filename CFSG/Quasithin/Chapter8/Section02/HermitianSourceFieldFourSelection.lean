module
public import CFSG.Quasithin.Chapter8.Section02.HermitianSourceSelectedTorusBounds
public import Theory.Representation.HermitianTensorThree.NearOffenders
import all CFSG.Quasithin.Chapter8.Section02.HermitianSourceSelectedTorusBounds

/-!
# The field-four fixed subgroup from the selected parameter one

The central intersection bounds the selected actor's fixed codimension by
its rank plus k. At k = 1 the checked Hermitian near-offender classification
therefore forces half-degree one, actor rank four and fixed codimension five.
Rank additivity identifies the fixed subgroup with the original intersection.
The marked plane radical is normalized by the image of the original Sylow
subgroup, giving relative normality of that same fixed subgroup; the original
selected group centralizes it. No lower bound on r or w is assumed here.

The Chapter 12 consumer uses the literal chosen orbit and the selected
parameter obtained by the torus exclusion. Selection, the earlier E.2 inputs,
and the field-four normalizer/centralizer exclusion remain with the assembly.
This does not assert r = 5 or the complete source exclusion.

Source: Aschbacher–Smith 8.2.4–5, printed pp.716–717, using H.4.4
(1 March 2004 manuscript, refs/quasithin.pdf).
-/

public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open Representation.HermitianTensorThree Representation.HermitianTensorThree.ImageOuter
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter8.Section02.HermitianSource
open ChapterE Offenders.Parabolic Offenders.Parabolic.Construction
variable {G : Type*} [Group G] [Finite G]
  {V : Subgroup G} [IsElementaryAbelian 2 V] {T : Sylow 2 G}
  {H M I : Subgroup G} {k : ℕ} {i : I} {S : Sylow 2 I}

/-- The actual central intersection bounds the selected actor codimension. -/
theorem selected_actor_fixedCodim_le_rank_add_parameter
    (s : Selected H T M V I k i S) :
    let A := V.map (MulAut.conj i.val⁻¹).toMonoidHom ⊓ (pCore 2 I).map I.subtype
    fixedCodim (automizerRepresentation V) (inducedAutomizer V A) ≤
      rank (inducedAutomizer V A) + k := by
  let W := V.map (MulAut.conj i.val⁻¹).toMonoidHom
  let A := W ⊓ (pCore 2 I).map I.subtype
  let Z := V ⊓ W
  let U := V ⊓ centralizer (A : Set G)
  let : IsElementaryAbelian 2 W := IsElementaryAbelian.map _
  have hZU : Z ≤ U := le_inf inf_le_left
    (inf_le_right.trans (W.le_centralizer.trans (centralizer_le inf_le_left)))
  have hc := offender_corank_add hZU (show U ≤ V from inf_le_left)
  have hz := offender_corank_add (W := V) (A := Z) bot_le inf_le_left
  have hz' : subgroupCorank V Z + rank Z = rank V := by
    simpa only [subgroupCorank,relIndex_bot_left,rank] using hz.symm
  have hi := selected_actor_rank_identity s
  change rank Z + k + rank (inducedAutomizer V A) = rank V at hi
  change fixedCodim (automizerRepresentation V) (inducedAutomizer V A) ≤
    rank (inducedAutomizer V A) + k
  rw [fixedCodim_inducedAutomizer V A (selected_actor_normalizes s)]
  change subgroupCorank V U ≤ rank (inducedAutomizer V A) + k
  omega

/-- Parameter one gives the marked field-four actor and its original fixed subgroup,
without extending the higher-field r and w bounds. -/
theorem selected_one_fixed_subgroup
    (s : Selected H T M V I 1 i S) (hT : HypothesisE322 V T)
    (n : ℕ) [NeZero n]
    (e : Additive V ≃ₗ[ZMod 2] Space n)
    (j : Automizer V →* binaryNormalizer n) (hj : Function.Injective j)
    (he : ∀ a v, e (automizerRepresentation V a v) =
      overgroupAction n (binaryNormalizer n) (j a) (e v)) :
    let A := V.map (MulAut.conj i.val⁻¹).toMonoidHom ⊓ (pCore 2 I).map I.subtype
    let U := V ⊓ centralizer (A : Set G)
    n = 1 ∧ A ≤ T ∧ rank (inducedAutomizer V A) = 4 ∧ rank U = 4 ∧
      U = V ⊓ V.map (MulAut.conj i.val⁻¹).toMonoidHom ∧
      (U.subgroupOf T).Normal ∧ (T : Subgroup G) ≤ normalizer (U : Set G) ∧
      I ≤ centralizer (U : Set G) ∧ globalR V ≤ 5 ∧
      ∃ c : Cover n, ((inducedAutomizer V A).map ((binaryNormalizer n).subtype.comp j)).map
        (MulAut.conj (binaryActionHom n c)).toMonoidHom = UnipotentRadicals.plane n := by
  let W := V.map (MulAut.conj i.val⁻¹).toMonoidHom
  let A := W ⊓ (pCore 2 I).map I.subtype
  let U := V ⊓ centralizer (A : Set G)
  let Z := V ⊓ W
  let : IsElementaryAbelian 2 W := IsElementaryAbelian.map _
  let : IsElementaryAbelian 2 A := IsElementaryAbelian.of_le (show A ≤ W from inf_le_left)
  obtain ⟨hAT,hAC,_,_,_⟩ := selected_core_actor_data s hT
  have hAN : A ≤ normalizer (V : Set G) := hAT.trans hT.normalizes
  let : IsElementaryAbelian 2 (inducedAutomizer V A) := inducedAutomizer_elementary V A hAN
  have hA : IsElementaryTwo (inducedAutomizer V A) :=
    ⟨fun hz => hAC ((inducedAutomizer_eq_bot_iff hAN).mp hz),inferInstance⟩
  obtain ⟨hn,ha,hcod,_,hplane⟩ := NearOffenders.of_equivariant n
    (automizerRepresentation V) j hj e he (inducedAutomizer V A) hA
    (selected_actor_fixedCodim_le_rank_add_parameter s)
  have hdim : rank V = 9*n := by
    rw [rank,show Nat.card V = Nat.card (Additive V) from rfl,
      Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod,
      e.finrank_eq,finrank_binary,Nat.log_pow Nat.one_lt_two]
  have hi := selected_actor_rank_identity s
  change rank Z + 1 + rank (inducedAutomizer V A) = rank V at hi
  have hz : rank Z = 4 := by omega
  have hcor : subgroupCorank V U = 5 := by
    rwa [fixedCodim_inducedAutomizer V A hAN] at hcod
  have hu : rank U = 4 := by
    have hc := offender_corank_add (W := V) (A := U) bot_le inf_le_left
    have hc' : subgroupCorank V U + rank U = rank V := by
      simpa only [subgroupCorank,relIndex_bot_left,rank] using hc.symm
    omega
  have hZU : Z ≤ U := le_inf inf_le_left
    (inf_le_right.trans (W.le_centralizer.trans (centralizer_le inf_le_left)))
  have hU : U = Z := by
    let : IsElementaryAbelian 2 U := IsElementaryAbelian.of_le (show U ≤ V from inf_le_left)
    have hc := offender_corank_add (W := U) (A := Z) bot_le hZU
    have hc' : subgroupCorank U Z + rank Z = rank U := by
      simpa only [subgroupCorank,relIndex_bot_left,rank] using hc.symm
    exact (subgroup_eq_of_corank_zero hZU (by omega)).symm
  let f := (binaryNormalizer n).subtype.comp j
  have hf : Function.Injective f := (binaryNormalizer n).subtype_injective.comp hj
  let B := inducedAutomizer V A
  let P := inducedAutomizer V T
  let : IsElementaryAbelian 2 (B.map f) := IsElementaryAbelian.map f
  have hB : rank (B.map f) = 4*n := by
    rw [rank_map_injective f hf]
    simpa only [hn,Nat.mul_one] using ha
  have hfix : Module.finrank (ZMod 2)
      (fixedSpace (UnipotentRadicals.ambientAction n) (B.map f)) = 4*n := by
    have hc := fixedCodim_add_finrank (UnipotentRadicals.ambientAction n) (B.map f)
    have hec := fixedCodim_map_equivariant (automizerRepresentation V)
      (UnipotentRadicals.ambientAction n) f e he B
    have hc0 : fixedCodim (UnipotentRadicals.ambientAction n) (B.map f) = 5 :=
      hec.symm.trans hcod
    rw [hc0,finrank_binary] at hc
    omega
  have hp : IsPGroup 2 P := T.2.comap_subtype.map _
  have hBP : B ≤ P := map_mono (comap_mono hAT)
  have hPN : P.map f ≤ binaryNormalizer n := fun _ ⟨a,_,ha⟩ => ha ▸ (j a).property
  have hnorm := Chapter7.NormalizedSource.NonMathieuHermitian.saturated_actor_normalized n
    (P.map f) (hp.map f) hPN (B.map f) (map_mono hBP) hB hfix
  have hnorm' : P ≤ normalizer (B : Set (Automizer V)) := by
    intro a haP
    apply mem_normalizer_iff_map_conj_eq.mpr
    apply Subgroup.map_injective hf
    change (B.map (MulAut.conj a).toMonoidHom).map f = B.map f
    rw [map_map]
    have heq : f.comp (MulAut.conj a).toMonoidHom =
        (MulAut.conj (f a)).toMonoidHom.comp f := by
      ext b
      simp [MulAut.conj_apply]
    rw [heq,←map_map]
    exact mem_normalizer_iff_map_conj_eq.mp (hnorm (mem_map_of_mem f haP))
  have hIC : I ≤ centralizer (U : Set G) := by
    rw [hU,←s.generate]
    exact sup_le_centralizer_inf_of_abelian V W
  have hr : globalR V ≤ 5 := by
    have hh := selected_globalR_le_rank_sum s
    change globalR V ≤ ((1 + rank B : ℕ) : ℕ∞) at hh
    simpa [show rank B = 4 from ha] using hh
  exact ⟨hn,hAT,ha,hu,hU,
    Offenders.fixed_normal_in_sylow V A T hT.le_sylow hAN hT.normalizes hnorm',
    Offenders.fixed_normalized_of_image_normalized V A T hAN hT.normalizes hnorm',
    hIC,hr,hplane⟩

end CFSG.Quasithin.Chapter8.Section02.HermitianSource
