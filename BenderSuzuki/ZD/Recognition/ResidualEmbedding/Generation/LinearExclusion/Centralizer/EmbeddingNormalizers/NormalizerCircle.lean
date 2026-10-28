module
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearExclusion.Centralizer.SourceInterfaces
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.LocalResidual.NormalComplements.RankOne.LocalRecognition.Source.Model
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.LocalResidual.NormalComplements.RankOne.LocalRecognition.Counts.Models

/-!
# The distinguished circle of a linear centralizer-subgroup normalizer

For nontrivial Y ≤ C_G(L), simplicity makes N_G(Y) proper. Its literal
distinguished circle contains L and has an odd central kernel. The common
root A identifies the exponent of its simple Bender quotient with the
original PSL₂ parameter. All three model alternatives are retained here.

The proof uses local recognition and counts the involutions in the actual
Borel through A. Normality remains relative to N_G(Y).

Source: GLS IV, Chapter 2, Corollary 7.13 and Lemma 15.2(c),
refs/KGroup/GLS4/Chapter2.tex. Adapted from the corresponding Suzuki
normalizer-circle construction; no Suzuki marking is used.
-/

noncomputable section
namespace BenderSuzuki.ZD.LinearExclusion
open Subgroup Theory.GroupTheory PFAppendixIII PFchapter1section1
universe u
variable {G : Type u} [Group G] [Finite G] {Z : Set G} {M : Subgroup G}
  {z t : G} {n : ℕ} (d : Context Z M z t n)
include d

omit [Finite G] d in
public theorem residual_le_normalizer_of_le_centralizer (Y : Subgroup G)
    (hYJ : Y ≤ centralizer (residualGenerated M z t : Set G)) :
    residualGenerated M z t ≤ normalizer (Y : Set G) := by
  apply le_trans _ (Subgroup.centralizer_le_normalizer _)
  intro x hx
  rw [mem_centralizer_iff]
  intro y hy
  exact (mem_centralizer_iff.mp (hYJ hy) x hx).symm

public theorem Context.centralizerSubgroup_normalizer_ne_top (Y : Subgroup G)
    (hYJ : Y ≤ centralizer (residualGenerated M z t : Set G)) (hY : Y ≠ ⊥) :
    normalizer (Y : Set G) ≠ ⊤ := by
  intro hn
  rcases d.reduction.simple.eq_bot_or_eq_top_of_normal Y (normalizer_eq_top_iff.mp hn) with h | h
  · exact hY h
  · have hYM : Y ≤ M := hYJ.trans
      ((centralizer_residualGenerated_le_pairStabilizer d.minimal.disconnected
        d.z_mem d.z_mem_M).trans inf_le_left)
    exact d.t_not_mem_M (hYM (h ▸ mem_top t))

public theorem Context.residual_le_normalizerCircle (Y : Subgroup G)
    (hYJ : Y ≤ centralizer (residualGenerated M z t : Set G)) :
    residualGenerated M z t ≤ localCircleIn Z (normalizer (Y : Set G)) := by
  rw [localCircleIn_eq_closure,
    ← closure_Z_inter_residualGenerated d.minimal.disconnected d.z_mem d.t_mem]
  apply Subgroup.closure_mono
  intro x hx
  exact ⟨hx.1, residual_le_normalizer_of_le_centralizer Y hYJ hx.2⟩

public theorem Context.normalizer_distinguishedClosure (Y : Subgroup G)
    (hYJ : Y ≤ centralizer (residualGenerated M z t : Set G)) :
    closure (Z ∩ ((M ⊓ normalizer (Y : Set G) : Subgroup G) : Set G)) =
      closure (Z ∩ (M : Set G)) := by
  apply le_antisymm
  · apply Subgroup.closure_mono
    rintro x ⟨hxZ, hxM, _⟩
    exact ⟨hxZ, hxM⟩
  apply (closure_le _).mpr
  intro x hx
  have hAL := proper_residualGenerated_contains_distinguishedClosure d.minimal
    d.reduction d.action d.z_mem d.z_mem_M d.t_mem d.t_not_mem_M d.proper d.even_pair
  exact subset_closure ⟨hx.1, hx.2,
    residual_le_normalizer_of_le_centralizer Y hYJ (hAL (subset_closure hx))⟩

@[expose] public def Context.normalizerCircleEmbedding (Y : Subgroup G)
    (hYJ : Y ≤ centralizer (residualGenerated M z t : Set G)) :
    residualGenerated M z t →* localCircle Z (normalizer (Y : Set G)) :=
  { toFun := fun x => ⟨⟨x, residual_le_normalizer_of_le_centralizer Y hYJ x.property⟩, by
      obtain ⟨v, hv, he⟩ := d.residual_le_normalizerCircle Y hYJ x.property
      exact (show v = ⟨(x : G), residual_le_normalizer_of_le_centralizer Y hYJ x.property⟩
        from Subtype.ext he) ▸ hv⟩
    map_one' := rfl
    map_mul' _ _ := rfl }

public theorem Context.normalizerCircleEmbedding_apply (Y : Subgroup G)
    (hYJ : Y ≤ centralizer (residualGenerated M z t : Set G)) (x : residualGenerated M z t) :
    localCircleHom Z (normalizer (Y : Set G)) (d.normalizerCircleEmbedding Y hYJ x) = x := by
  rfl

public theorem Context.normalizerCircleEmbedding_injective (Y : Subgroup G)
    (hYJ : Y ≤ centralizer (residualGenerated M z t : Set G)) :
    Function.Injective (d.normalizerCircleEmbedding Y hYJ) := by
  intro x y he
  exact Subtype.ext (congrArg (localCircleHom Z (normalizer (Y : Set G))) he)

private theorem normalizer_inputs (Y : Subgroup G)
    (hYJ : Y ≤ centralizer (residualGenerated M z t : Set G)) :
    ¬ normalizer (Y : Set G) ≤ M ∧
      ∃ x ∈ Z, x ∈ normalizer (Y : Set G) ∧ x ∈ M := by
  have hLN := residual_le_normalizer_of_le_centralizer Y hYJ
  have htL : t ∈ residualGenerated M z t :=
    (le_sup_right.trans le_sup_left : zpowers t ≤ _) (mem_zpowers t)
  have hzL : z ∈ residualGenerated M z t :=
    (le_sup_left.trans le_sup_left : zpowers z ≤ _) (mem_zpowers z)
  exact ⟨fun h => d.t_not_mem_M (h (hLN htL)), z, d.z_mem, hLN hzL, d.z_mem_M⟩

public theorem Context.normalizerCircle_not_solvable (Y : Subgroup G)
    (hYJ : Y ≤ centralizer (residualGenerated M z t : Set G)) (hY : Y ≠ ⊥) :
    ¬ Group.IsSolvable (localCircle Z (normalizer (Y : Set G))) := by
  intro hs
  obtain ⟨hNM, hne⟩ := normalizer_inputs d Y hYJ
  obtain ⟨v, hv, hvN, hvM, huniq, _⟩ := localCircle_solvable_alternative
    d.minimal.disconnected d.reduction d.action _
    (d.centralizerSubgroup_normalizer_ne_top Y hYJ hY) hNM hne hs
  obtain ⟨w, hw, hwM, hvw, _⟩ :=
    exists_commuting_distinguished_of_minimal d.minimal d.reduction hv hvM
  have hAL := proper_residualGenerated_contains_distinguishedClosure d.minimal
    d.reduction d.action d.z_mem d.z_mem_M d.t_mem d.t_not_mem_M d.proper d.even_pair
  exact hvw (huniq w hw (residual_le_normalizer_of_le_centralizer Y hYJ
    (hAL (subset_closure ⟨hw, hwM⟩))) hwM).symm

public theorem Context.normalizerCircle_structure (Y : Subgroup G)
    (hYJ : Y ≤ centralizer (residualGenerated M z t : Set G)) (hY : Y ≠ ⊥) :
    let C := localCircle Z (normalizer (Y : Set G))
    pPrimeCore 2 C = center C ∧ commutator C = ⊤ ∧
      IsSimpleBenderGroup (C ⧸ center C) ∧
      IsBorelSubgroup ((M.comap (localCircleHom Z (normalizer (Y : Set G)))).map
        (QuotientGroup.mk' (center C))) := by
  obtain ⟨hNM, hne⟩ := normalizer_inputs d Y hYJ
  exact localCircle_nonsolvable_structure d.minimal d.reduction d.action _
    (d.centralizerSubgroup_normalizer_ne_top Y hYJ hY) hNM hne
    (d.normalizerCircle_not_solvable Y hYJ hY)

private theorem normalizerCircle_involution_card (Y : Subgroup G)
    (hYJ : Y ≤ centralizer (residualGenerated M z t : Set G)) (hY : Y ≠ ⊥) :
    Nat.card {x : M.comap (localCircleHom Z (normalizer (Y : Set G))) //
      PFAppendixIII.IsInvolution x} = 2 ^ n - 1 := by
  let N := normalizer (Y : Set G)
  let C := localCircle Z N
  let B := M.comap (localCircleHom Z N)
  let A := closure (Z ∩ (M : Set G))
  let i := d.normalizerCircleEmbedding Y hYJ
  have hi := d.normalizerCircleEmbedding_injective Y hYJ
  have hAL := proper_residualGenerated_contains_distinguishedClosure d.minimal
    d.reduction d.action d.z_mem d.z_mem_M d.t_mem d.t_not_mem_M d.proper d.even_pair
  obtain ⟨hNM, hne⟩ := normalizer_inputs d Y hYJ
  have hN := d.centralizerSubgroup_normalizer_ne_top Y hYJ hY
  let f : {x : B // PFAppendixIII.IsInvolution x} → {x : A // PFAppendixIII.IsInvolution x} :=
    fun x => ⟨⟨localCircleHom Z N x.val.val, subset_closure
      ⟨localCircle_involution_mem d.minimal.disconnected d.reduction N hN hNM hne
        (IsInvolution.map_of_injective x.property B.subtype Subtype.val_injective),
        x.val.property⟩⟩,
      IsInvolution.subtype (IsInvolution.map_of_injective
        (IsInvolution.map_of_injective x.property B.subtype Subtype.val_injective)
        (localCircleHom Z N) (localCircleHom_injective Z N)) _⟩
  have hf : Function.Bijective f := by
    constructor
    · intro x y he
      apply Subtype.ext
      apply Subtype.ext
      apply localCircleHom_injective Z N
      exact congrArg (fun a => a.val.val) he
    · intro a
      let aL : residualGenerated M z t := ⟨a.val.val, hAL a.val.property⟩
      have haL : PFAppendixIII.IsInvolution aL :=
        IsInvolution.subtype (IsInvolution.map_of_injective a.property A.subtype
          Subtype.val_injective) aL.property
      have hai : i aL ∈ B := distinguishedClosure_le (Z := Z) (M := M) a.val.property
      refine ⟨⟨⟨i aL, hai⟩, IsInvolution.subtype
        (IsInvolution.map_of_injective haL i hi) hai⟩, ?_⟩
      rfl
  have hc := Nat.card_congr (Equiv.ofBijective f hf)
  obtain ⟨hA, hAc⟩ := d.distinguished_elementary_card
  let := hA
  exact hc.trans ((involution_card_eq_of_exponent_two
    (fun x : A => Subtype.ext (elemPow_eq_one_of_isElementaryAbelian (x : G) x.property))).trans (congrArg (· - 1) hAc))

/-- The actual quotient model has the same exponent as L, because both
Borel involution sets are the nonidentity elements of the common A. -/
public theorem Context.normalizerCircle_model_atExponent (Y : Subgroup G)
    (hYJ : Y ≤ centralizer (residualGenerated M z t : Set G)) (hY : Y ≠ ⊥) :
    IsSimpleBenderGroupAtExponent n
      (localCircle Z (normalizer (Y : Set G)) ⧸
        center (localCircle Z (normalizer (Y : Set G)))) := by
  let N := normalizer (Y : Set G)
  let C := localCircle Z N
  let B := M.comap (localCircleHom Z N)
  let q := QuotientGroup.mk' (center C)
  obtain ⟨hc, _, hmodel, hB⟩ := d.normalizerCircle_structure Y hYJ hY
  obtain ⟨k, hk, hm⟩ := hmodel.exists_exponent
  have hcount := bender_borel_involution_card_atExponent hk hm hB
  have hodd : Odd (Nat.card q.ker) := by
    rw [QuotientGroup.ker_mk', ← hc]
    exact Nat.coprime_two_left.mp pPrimeCore_coprime_card
  obtain ⟨hNM, hne⟩ := normalizer_inputs d Y hYJ
  have hker : q.ker ≤ B := by
    rw [QuotientGroup.ker_mk', ← hc]
    exact localCircle_oddCore_le d.minimal.disconnected d.reduction N
      (d.centralizerSubgroup_normalizer_ne_top Y hYJ hY) hNM hne
      (d.normalizerCircle_not_solvable Y hYJ hY)
  have hh := involution_card_map_of_central_odd_kernel q
    (QuotientGroup.mk'_surjective _) hodd (by rw [QuotientGroup.ker_mk']) B hker
  have heq : 2 ^ n - 1 = 2 ^ k - 1 :=
    (normalizerCircle_involution_card d Y hYJ hY).symm.trans (hh.trans hcount)
  have hp : 2 ^ n = 2 ^ k := by
    have h1 : 1 ≤ 2 ^ n := Nat.one_le_two_pow
    have h2 : 1 ≤ 2 ^ k := Nat.one_le_two_pow
    omega
  have hn' := Nat.pow_right_injective (by decide : 2 ≤ 2) hp
  exact hn'.symm ▸ hm

end BenderSuzuki.ZD.LinearExclusion
