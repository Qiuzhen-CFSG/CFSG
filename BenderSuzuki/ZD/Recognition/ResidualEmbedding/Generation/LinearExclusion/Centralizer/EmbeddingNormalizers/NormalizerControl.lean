module

public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearExclusion.Centralizer.EmbeddingNormalizers.NormalizerCircle
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearExclusion.Centralizer.EmbeddingNormalizers.Action
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearRecognition.Centralizers.Counting.UniformCases.Numerics.LocalGeometry.BorelDegree
public import Theory.GroupTheory.PerfectCentralQuotientNormalizer

/-!
# Full normalizer control in the linear branch

For nontrivial Y ≤ C_G(L), the normalizer circle has the original field
parameter. Its PSL₂ quotient is filled by the injective image of L;
perfectness removes the central supplement. Its Suzuki alternative is
excluded by divisibility by three. In the remaining PSU₃ alternative,
the literal Borel index is q³+1, the full ambient degree. The circle is
therefore transitive, and the normal subgroup Y fixes every point because
it fixes the base point. Faithfulness contradicts Y ≠ 1.

This is the actual transitivity argument of GLS IV, Chapter 2, Lemma
15.2(c), refs/KGroup/GLS4/Chapter2.tex. No nonembedding of PSL₂ in PSU₃
is asserted or used.
-/

noncomputable section
namespace BenderSuzuki.ZD.LinearExclusion
open Subgroup Theory.GroupTheory PFAppendixIII PFchapter1section1
universe u
variable {G : Type u} [Group G] [Finite G] {Z : Set G} {M : Subgroup G}
  {z t : G} {n : ℕ} (d : Context Z M z t n)
include d

private theorem normalizerCircle_center_le_point (Y : Subgroup G)
    (hYJ : Y ≤ centralizer (residualGenerated M z t : Set G)) (hY : Y ≠ ⊥) :
    center (localCircle Z (normalizer (Y : Set G))) ≤
      M.comap (localCircleHom Z (normalizer (Y : Set G))) := by
  rw [← (d.normalizerCircle_structure Y hYJ hY).1]
  have hLN := residual_le_normalizer_of_le_centralizer Y hYJ
  have htL : t ∈ residualGenerated M z t :=
    (le_sup_right.trans le_sup_left : zpowers t ≤ _) (mem_zpowers t)
  have hzL : z ∈ residualGenerated M z t :=
    (le_sup_left.trans le_sup_left : zpowers z ≤ _) (mem_zpowers z)
  exact localCircle_oddCore_le d.minimal.disconnected d.reduction _
    (d.centralizerSubgroup_normalizer_ne_top Y hYJ hY)
    (fun hh => d.t_not_mem_M (hh (hLN htL)))
    ⟨z, d.z_mem, hLN hzL, d.z_mem_M⟩
    (d.normalizerCircle_not_solvable Y hYJ hY)

/-- A nontrivial centralizer subgroup prevents its normalizer circle from
having the full ambient coset degree. The proof uses the literal action. -/
public theorem Context.normalizerCircle_index_ne_degree (Y : Subgroup G)
    (hYJ : Y ≤ centralizer (residualGenerated M z t : Set G)) (hY : Y ≠ ⊥) :
    (M.comap (localCircleHom Z (normalizer (Y : Set G)))).index ≠ Nat.card (G ⧸ M) := by
  intro hindex
  let N := normalizer (Y : Set G)
  let C := localCircle Z N
  let f := localCircleHom Z N
  let alpha : G ⧸ M := QuotientGroup.mk 1
  let : MulAction C (G ⧸ M) := MulAction.compHom _ f
  have hstab : MulAction.stabilizer C alpha = M.comap f := by
    ext c
    change f c ∈ MulAction.stabilizer G (QuotientGroup.mk 1 : G ⧸ M) ↔ f c ∈ M
    rw [baseCoset_stabilizer]
  have horbit : MulAction.orbit C alpha = Set.univ := by
    apply Set.eq_of_subset_of_ncard_le (Set.subset_univ _)
    · rw [Set.ncard_univ, ← Nat.card_coe_set_eq,
        Nat.card_congr (MulAction.orbitEquivQuotientStabilizer C alpha)]
      change Nat.card (G ⧸ M) ≤ (MulAction.stabilizer C alpha).index
      rw [hstab, hindex]
  have hYM : Y ≤ M := hYJ.trans
    ((centralizer_residualGenerated_le_pairStabilizer d.minimal.disconnected
      d.z_mem d.z_mem_M).trans inf_le_left)
  apply hY
  apply bot_unique
  intro y hy
  apply d.coset_action_faithful
  intro beta
  have hb : beta ∈ MulAction.orbit C alpha := horbit ▸ Set.mem_univ beta
  obtain ⟨c, rfl⟩ := MulAction.mem_orbit_iff.mp hb
  change y • (f c • alpha) = f c • alpha
  have hcN : f c ∈ N := c.val.property
  have hcY : (f c)⁻¹ * y * f c ∈ Y := by
    simpa only [inv_inv] using
      (mem_normalizer_iff.mp (N.inv_mem hcN) y).mp hy
  have hfix : ((f c)⁻¹ * y * f c) • alpha = alpha := by
    change (f c)⁻¹ * y * f c ∈ MulAction.stabilizer G (QuotientGroup.mk 1 : G ⧸ M)
    rw [baseCoset_stabilizer]
    exact hYM hcY
  calc
    _ = f c • (((f c)⁻¹ * y * f c) • alpha) := by
      simp only [mul_smul, smul_inv_smul]
    _ = _ := congrArg (fun b => f c • b) hfix

/-- The original L fills the distinguished circle of every nontrivial
centralizer-subgroup normalizer. -/
public theorem Context.normalizerCircleEmbedding_surjective (Y : Subgroup G)
    (hYJ : Y ≤ centralizer (residualGenerated M z t : Set G)) (hY : Y ≠ ⊥) :
    Function.Surjective (d.normalizerCircleEmbedding Y hYJ) := by
  let L := residualGenerated M z t
  let C := localCircle Z (normalizer (Y : Set G))
  let i := d.normalizerCircleEmbedding Y hYJ
  let q := QuotientGroup.mk' (center C)
  have hi := d.normalizerCircleEmbedding_injective Y hYJ
  obtain ⟨hc, hp, _, hB⟩ := d.normalizerCircle_structure Y hYJ hY
  have hsimple := (show IsSimpleBenderGroupAtExponent n L from
    .isPSL2 ⟨d.model⟩).isSimple d.parameter
  have hqi : Function.Injective (q.comp i) := by
    rcases hsimple.eq_bot_or_eq_top_of_normal (q.comp i).ker inferInstance with hb | ht
    · exact (q.comp i).ker_eq_bot_iff.mp hb
    · have hzL : z ∈ L := (le_sup_left.trans le_sup_left : zpowers z ≤ L) (mem_zpowers z)
      let zL : L := ⟨z, hzL⟩
      have hzI := IsInvolution.map_of_injective
        (IsInvolution.subtype (d.minimal.disconnected.involutions z d.z_mem) hzL) i hi
      have hodd : Odd (Nat.card q.ker) := by
        rw [QuotientGroup.ker_mk', ← hc]
        exact Nat.coprime_two_left.mp pPrimeCore_coprime_card
      have hn := (involution_map_of_odd_kernel q hodd hzI).ne_one
      have hzker : zL ∈ (q.comp i).ker := by rw [ht]; exact mem_top _
      exact (hn hzker).elim
  have hs : Function.Surjective (q.comp i) := by
    cases d.normalizerCircle_model_atExponent Y hYJ hY with
    | isPSL2 he =>
      obtain ⟨e⟩ := he
      exact ((Nat.bijective_iff_injective_and_card (q.comp i)).mpr
        ⟨hqi, (Nat.card_congr d.model.toEquiv).trans
          (Nat.card_congr e.toEquiv).symm⟩).surjective
    | isSuzuki he =>
      obtain ⟨k, _, ⟨e⟩⟩ := he
      have hf := (e.injective.comp hqi).comp d.model.symm.injective
      have hd := card_dvd_of_injective
        (e.toMonoidHom.comp ((q.comp i).comp d.model.symm.toMonoidHom)) hf
      exact (MatrixGroups.suzukiMatrixGroup_three_free k
        (by have := d.parameter; omega)
        ((MatrixGroups.three_dvd_card_psl2_char_two (BinaryGaloisField n)).trans hd)).elim
    | isPSU3 he =>
      obtain ⟨E, hE, hfin, J, hJ, hcard, hfixed, ⟨e⟩⟩ := he
      let : Field E := hE
      let : Finite E := hfin
      let : Finite (MatrixGroups.ProjectiveSpecialUnitaryMatrixGroup J) :=
        Finite.of_equiv (C ⧸ center C) e.toEquiv
      let B := M.comap (localCircleHom Z (normalizer (Y : Set G)))
      have hdegree : (B.map q).index = (2 ^ n) ^ 3 + 1 :=
        ((B.map q).index_map_equiv e).symm.trans
          (LocalGeometry.psu3_borel_index J d.parameter hJ hcard hfixed (hB.map_mulEquiv e))
      rw [B.index_map_eq (QuotientGroup.mk'_surjective _)
        (by rw [QuotientGroup.ker_mk']; exact normalizerCircle_center_le_point d Y hYJ hY)] at hdegree
      exact (d.normalizerCircle_index_ne_degree Y hYJ hY
        (hdegree.trans d.degree_and_fixed.1.symm)).elim
  have hmap : i.range.map q = ⊤ := by
    rw [← MonoidHom.range_comp, MonoidHom.range_eq_top.mpr hs]
  let : Group.IsPerfect C := ⟨hp⟩
  have hr := perfect_le_of_map_le_of_central_kernel q
    (by rw [QuotientGroup.ker_mk']) (⊤ : Subgroup C) i.range
    (by rw [hmap]; exact le_top)
  exact MonoidHom.range_eq_top.mp (top_le_iff.mp hr)

/-- The literal ambient distinguished closure of N_G(Y) is L. -/
public theorem Context.normalizerCircle_eq_residual (Y : Subgroup G)
    (hYJ : Y ≤ centralizer (residualGenerated M z t : Set G)) (hY : Y ≠ ⊥) :
    localCircleIn Z (normalizer (Y : Set G)) = residualGenerated M z t := by
  apply le_antisymm _ (d.residual_le_normalizerCircle Y hYJ)
  rintro x ⟨v, hv, rfl⟩
  obtain ⟨a, ha⟩ := d.normalizerCircleEmbedding_surjective Y hYJ hY ⟨v, hv⟩
  have he := congrArg (localCircleHom Z (normalizer (Y : Set G))) ha
  change (a : G) = (v : G) at he
  change (v : G) ∈ residualGenerated M z t
  rw [← he]
  exact a.property

/-- GLS IV, Chapter 2, Lemma 15.2(c), for every nontrivial subgroup of J. -/
public theorem Context.normalizer_control_of_le_centralizer (Y : Subgroup G)
    (hYJ : Y ≤ centralizer (residualGenerated M z t : Set G)) (hY : Y ≠ ⊥) :
    normalizer (Y : Set G) ≤ normalizer (residualGenerated M z t : Set G) := by
  rw [← d.normalizerCircle_eq_residual Y hYJ hY, localCircleIn_eq_closure]
  apply le_normalizer_closure_iff.mpr
  intro g hg x hx
  exact subset_closure ⟨d.minimal.disconnected.invariant g x hx.1,
    (normalizer (Y : Set G)).mul_mem
      ((normalizer (Y : Set G)).mul_mem hg hx.2)
      ((normalizer (Y : Set G)).inv_mem hg)⟩

end BenderSuzuki.ZD.LinearExclusion
