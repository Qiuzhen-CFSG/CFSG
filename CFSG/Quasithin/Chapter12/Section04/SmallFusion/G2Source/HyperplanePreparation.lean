module

public import CFSG.Quasithin.Chapter12.Section04.SmallFusion.G2Source.NormalizerAction
public import CFSG.Quasithin.Chapter1.Section02.Uniqueness.SourceKnownSimple
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.Actor.Orbit.Source318
public import CFSG.Quasithin.ChapterE.Section06.Obstructions
public import CFSG.Quasithin.ChapterE.Section06.CentralizerStructure.Sylow
public import Theory.Representation.G2OrthogonalCover.BinaryHyperplaneFixers

/-!
# The E.6.1 and Sylow setup for binary G₂ cover hyperplanes

The actual chosen-module orbit-centralizer identity identifies C_T(V) with
O₂(LT), so LT normalizes this literal subgroup. Source uniqueness and the
fixed-involution setup then establish E.6.1 at N_G(V).

The full normalizer actor and the cover pointwise-fixer theorem are used below
on the original ambient subgroups. The cover has dimension seven; its escaping
hyperplanes and their hyperplanes have dimensions six and five.

Source: Aschbacher--Smith, Lemma 12.4.8, first paragraph, printed p.815,
and E.6.1, E.6.4--5, printed pp.244--246.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Module
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section04.SmallFusion.G2Source
open Chapter12.Section02 ChapterE ChapterE.Section06 Atlas.G2.Natural
open ChapterB.QuasisimpleSource
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {L V : Subgroup G}
local notation "F" => ZMod 2
local notation "E" => TraceZero F

theorem cover_source_hypothesisE61
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (D : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (e : ActionEquiv D.quotientAction
      (OrthogonalCover.action F))
    (hne : fixedSubgroup L V ≠ ⊥) :
    HypothesisE61 KnownSimple.IsKnownSimple T (normalizer (V : Set G)) V := by
  have hs := structural L h
  have hOrbit : componentOrbit L (T : Subgroup G) = L := by
    apply le_antisymm _ (le_componentOrbit L _)
    exact iSup_conjugates_le_of_le_normalizer L (T : Subgroup G) L le_rfl hs.1
  have hu := Chapter1.Section02.nonsolvable_uniqueness_knownSimple
    h.simpleQTKE T h.maximal_faithful.1
  obtain ⟨_, _, _, _, hMV, _, _⟩ :=
    exists_fixed_involution_setup h D structural e hne
  have hmax : IsMaximalTwoLocal (normalizer (V : Set G)) := by
    simpa only [hOrbit, hMV] using hu.normalizer_maximal
  have hTV := (hs.2.2 V D).1
  have hVOrbit : componentOrbit V (T : Subgroup G) = V :=
    le_antisymm (iSup_conjugates_le_of_le_normalizer V T V le_rfl hTV)
      (le_componentOrbit V T)
  have hQ : sylowCentralizer (T : Subgroup G) V =
      (L ⊔ (T : Subgroup G)).pCoreIn 2 := by
    change (T : Subgroup G) ⊓ centralizer (V : Set G) = _
    simpa only [hVOrbit] using D.orbit_centralizer h.toHypothesis1221
  have hNQ : L ⊔ (T : Subgroup G) ≤
      normalizer (sylowCentralizer (T : Subgroup G) V : Set G) := by
    rw [hQ]
    exact (L ⊔ (T : Subgroup G)).le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image _ (pCore 2 _))
  refine ⟨h.simpleQTKE, hmax, hTV, D.ne_bot, D.elementary, D.le_sylow,
    (normal_subgroupOf_iff_le_normalizer D.le_sylow).mpr hTV, ?_, ?_⟩
  · intro g hg
    exact Or.inr (mem_normalizer_iff_map_conj_eq.mp hg)
  · intro N hN hle
    have he : N = normalizer (L : Set G) := by
      simpa only [hOrbit] using hu.normalizer_unique N hN
        ((le_inf (le_inf (sup_le D.normalizes hTV) (sup_le D.normalizes hTV)) hNQ).trans hle)
    exact he.trans hMV

private def coverCoordinates [IsElementaryAbelian 2 V]
    (b : V ≃* Multiplicative E) : Additive V ≃ₗ[F] E := by
  let ca : Additive V ≃+ E := {
    toFun v := (b v.toMul).toAdd
    invFun w := Additive.ofMul (b.symm (Multiplicative.ofAdd w))
    left_inv v := congrArg Additive.ofMul (b.symm_apply_apply v.toMul)
    right_inv w := congrArg Multiplicative.toAdd (b.apply_symm_apply _)
    map_add' v w := congrArg Multiplicative.toAdd (map_mul b v.toMul w.toMul) }
  exact { ca with map_smul' := ZMod.map_smul ca }

private def coverSubspace [IsElementaryAbelian 2 V]
    (b : V ≃* Multiplicative E) (U : Subgroup G) : Submodule F E :=
  (AddSubgroup.toZModSubmodule 2 (U.subgroupOf V).toAddSubgroup).map
    (coverCoordinates b).toLinearMap

private theorem coverSubspace_dimension [IsElementaryAbelian 2 V]
    (b : V ≃* Multiplicative E) {U : Subgroup G}
    (hUV : U ≤ V) (hcard : 32 ≤ Nat.card U) :
    5 ≤ finrank F (coverSubspace b U) := by
  let S := AddSubgroup.toZModSubmodule 2 (U.subgroupOf V).toAddSubgroup
  have hc : Nat.card U = 2 ^ finrank F S := by
    have hc' := Module.natCard_eq_pow_finrank (K := F) (V := S)
    have he : Nat.card S = Nat.card (U.subgroupOf V) := rfl
    rw [he, Nat.card_congr (subgroupOfEquivOfLe hUV).toEquiv, Nat.card_zmod] at hc'
    exact hc'
  change 5 ≤ finrank F (S.map (coverCoordinates b).toLinearMap)
  rw [(coverCoordinates b).finrank_map_eq]
  by_contra! hsmall
  have hp : 2 ^ finrank F S ≤ 2 ^ 4 :=
    Nat.pow_le_pow_right (by decide) (by omega)
  rw [← hc] at hp
  norm_num at hp
  omega

private theorem local_centralizer_of_cover_subspace [IsElementaryAbelian 2 V]
    (b : V ≃* Multiplicative E)
    (φ : normalizer (L : Set G) →* Atlas.G2.Model F)
    (hφ : ∀ (n : normalizer (L : Set G)) (x : E),
      (b.symm (Multiplicative.ofAdd (traceZeroAction F (φ n) x)) : G) =
        (n : G) * (b.symm (Multiplicative.ofAdd x) : G) * (n : G)⁻¹)
    (hMV : normalizer (L : Set G) = normalizer (V : Set G))
    {U : Subgroup G} (hUV : U ≤ V) (hcard : 32 ≤ Nat.card U)
    (hi : identity F ∉ coverSubspace b U) :
    normalizer (V : Set G) ⊓ centralizer (U : Set G) = centralizer (V : Set G) := by
  apply le_antisymm
  · rintro n ⟨hn, hc⟩
    let m : normalizer (L : Set G) := ⟨n, hMV.symm.le hn⟩
    have hg : φ m = 1 := by
      apply OrthogonalCover.pointwise_large_subspace_trivial (coverSubspace b U)
        (coverSubspace_dimension b hUV hcard) hi
      rintro x ⟨v, hv, rfl⟩
      apply Multiplicative.ofAdd.injective
      apply b.symm.injective
      apply Subtype.ext
      rw [hφ]
      change n * (b.symm (b v.toMul) : G) * n⁻¹ = (b.symm (b v.toMul) : G)
      rw [b.symm_apply_apply, ← hc v.toMul hv, mul_inv_cancel_right]
    intro v hv
    have hh := hφ m (b ⟨v, hv⟩).toAdd
    rw [hg, map_one, Module.End.one_apply] at hh
    have hh' : v = n * v * n⁻¹ := by
      change (b.symm (b ⟨v, hv⟩) : G) = n * (b.symm (b ⟨v, hv⟩) : G) * n⁻¹ at hh
      simpa only [b.symm_apply_apply] using hh
    exact (mul_inv_eq_iff_eq_mul.mp hh'.symm).symm
  · exact le_inf (Subgroup.centralizer_le_normalizer _) (centralizer_le hUV)

/-- The first paragraph of 12.4.8 on the actual chosen cover, including all
its codimension-two sections. No orbit or component premise is assumed. -/
theorem escaping_cover_subspaces
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (D : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (e : ActionEquiv D.quotientAction (OrthogonalCover.action F))
    (hne : fixedSubgroup L V ≠ ⊥)
    {U : Subgroup G} (hUV : U ≤ V) (hcor : subgroupCorank V U = 1)
    (hescape : ¬ centralizer (U : Set G) ≤ normalizer (V : Set G)) :
    Nat.card U = 64 ∧ ¬ fixedSubgroup L V ≤ U ∧
      normalizer (V : Set G) ⊓ centralizer (U : Set G) = centralizer (V : Set G) ∧
      U ∈ obstructionFamily (normalizer (V : Set G)) V ∧
      ∀ U₀ ≤ U, subgroupCorank U U₀ = 1 →
        Nat.card U₀ = 32 ∧ ¬ fixedSubgroup L V ≤ U₀ ∧
        normalizer (V : Set G) ⊓ centralizer (U₀ : Set G) = centralizer (V : Set G) ∧
        U₀ ∈ obstructionFamily (normalizer (V : Set G)) V := by
  classical
  let _ := D.elementary
  let _ : IsElementaryAbelian 2 U := IsElementaryAbelian.of_le hUV
  obtain ⟨z, hz, hfix, hM, hMV, _, _⟩ :=
    exists_fixed_involution_setup h D structural e hne
  change fixedSubgroup L V = zpowers z at hfix
  obtain ⟨b, φ, hφ⟩ := exists_normalizer_full_g2_actor h D structural e hne
  have hcardV : Nat.card V = 128 := by
    rw [Nat.card_congr b.toEquiv]
    change Nat.card E = 128
    rw [Module.natCard_eq_pow_finrank (K := F), Nat.card_zmod,
      OrthogonalCover.finrank_traceZero]
    norm_num
  have hindex : U.relIndex V = 2 := by
    rw [relIndex_eq_two_pow_quotient_finrank, ← subgroupCorank_eq_quotient_finrank,
      hcor, pow_one]
  have hcardU : Nat.card U = 64 := by
    have hc := relIndex_mul_relIndex (⊥ : Subgroup G) U V bot_le hUV
    rw [relIndex_bot_left, relIndex_bot_left, hindex, hcardV] at hc
    omega
  have hZC : centralizer (fixedSubgroup L V : Set G) ≤ normalizer (V : Set G) := by
    rw [← hMV, hM]
    intro x hx
    exact mem_centralizer_singleton_iff.mpr
      ((hx z (hfix ▸ mem_zpowers z)).symm)
  have hout : ¬ fixedSubgroup L V ≤ U :=
    fun hin => hescape ((centralizer_le hin).trans hZC)
  let zi : V := b.symm (Multiplicative.ofAdd (identity F))
  have hzi1 : (zi : G) ≠ 1 := by
    intro heq
    have hh : zi = 1 := Subtype.ext heq
    have hh' := congrArg (fun v : V => (b v).toAdd) hh
    have hi : identity F = 0 := by
      change (b (b.symm (Multiplicative.ofAdd (identity F)))).toAdd = (b 1).toAdd at hh'
      rw [b.apply_symm_apply, map_one] at hh'
      exact hh'
    exact Atlas.SplitOctonion.unit_ne_zero (congrArg Subtype.val hi)
  have hziL : (zi : G) ∈ centralizer (L : Set G) := by
    intro l hl
    have hh := hφ ⟨l, L.le_normalizer hl⟩ (identity F)
    rw [traceZeroAction_identity] at hh
    exact mul_inv_eq_iff_eq_mul.mp hh.symm
  have hzieq : (zi : G) = z := by
    have hmem : (zi : G) ∈ zpowers z := hfix ▸ ⟨zi.property, hziL⟩
    rw [mem_zpowers_iff_mem_range_orderOf, hz] at hmem
    obtain ⟨n, hn, hnzi⟩ := Finset.mem_image.mp hmem
    have hnlt : n < 2 := Finset.mem_range.mp hn
    interval_cases n
    · exact (hzi1 (by simpa using hnzi.symm)).elim
    · simpa using hnzi.symm
  have hno (W : Subgroup G) (hWU : W ≤ U) : identity F ∉ coverSubspace b W := by
    rintro ⟨v, hv, hvi⟩
    have hvz : (v.toMul : G) = z := by
      have hvi' : b v.toMul = Multiplicative.ofAdd (identity F) :=
        congrArg Multiplicative.ofAdd hvi
      have hvzi : v.toMul = zi := b.injective (hvi'.trans (b.apply_symm_apply _).symm)
      exact (congrArg Subtype.val hvzi).trans hzieq
    have hzU : z ∈ U := hvz ▸ hWU hv
    apply hout
    rw [hfix]
    exact zpowers_le.mpr hzU
  have hCU := local_centralizer_of_cover_subspace b φ hφ hMV hUV
    (by omega) (hno U le_rfl)
  have hCV : normalizer (V : Set G) ⊓ centralizer (V : Set G) = centralizer (V : Set G) :=
    inf_eq_right.mpr (Subgroup.centralizer_le_normalizer _)
  refine ⟨hcardU, hout, hCU, ⟨hUV, ?_, hescape,
    oddCentralizerCondition_of_eq (hCU.trans hCV.symm)⟩, ?_⟩
  · intro he
    rw [he, card_bot] at hcardU
    omega
  · intro U₀ hU₀U hcor₀
    have hindex₀ : U₀.relIndex U = 2 := by
      rw [relIndex_eq_two_pow_quotient_finrank, ← subgroupCorank_eq_quotient_finrank,
        hcor₀, pow_one]
    have hcard₀ : Nat.card U₀ = 32 := by
      have hc := relIndex_mul_relIndex (⊥ : Subgroup G) U₀ U bot_le hU₀U
      rw [relIndex_bot_left, relIndex_bot_left, hindex₀, hcardU] at hc
      omega
    have hout₀ : ¬ fixedSubgroup L V ≤ U₀ := fun hin => hout (hin.trans hU₀U)
    have hCU₀ := local_centralizer_of_cover_subspace b φ hφ hMV (hU₀U.trans hUV)
      (by omega) (hno U₀ hU₀U)
    refine ⟨hcard₀, hout₀, hCU₀, hU₀U.trans hUV, ?_, ?_,
      oddCentralizerCondition_of_eq (hCU₀.trans hCV.symm)⟩
    · intro he
      rw [he, card_bot] at hcard₀
      omega
    · exact fun hin => hescape ((centralizer_le hU₀U).trans hin)

/-- E.6.5(1), with C_T(V) as the actual ambient image of both Sylow groups. -/
theorem cover_escaping_sylow_centralizers
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (D : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (e : ActionEquiv D.quotientAction (OrthogonalCover.action F))
    (hne : fixedSubgroup L V ≠ ⊥)
    {U : Subgroup G} (hUV : U ≤ V) (hcor : subgroupCorank V U = 1)
    (hescape : ¬ centralizer (U : Set G) ≤ normalizer (V : Set G)) :
    Chapter1.IsSylowIn 2 (sylowCentralizer (T : Subgroup G) V)
        (centralizer (U : Set G)) ∧
      ∀ U₀ ≤ U, subgroupCorank U U₀ = 1 →
        Chapter1.IsSylowIn 2 (sylowCentralizer (T : Subgroup G) V)
          (centralizer (U₀ : Set G)) := by
  have hE := cover_source_hypothesisE61 h D structural e hne
  have hg := escaping_cover_subspaces h D structural e hne hUV hcor hescape
  exact ⟨hE.sylow_obstruction hg.2.2.2.1, fun U₀ hU₀ hcor₀ =>
    hE.sylow_obstruction (hg.2.2.2.2 U₀ hU₀ hcor₀).2.2.2⟩

end CFSG.Quasithin.Chapter12.Section04.SmallFusion.G2Source
