module

public import CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.SixAutomorphisms.ModelIdentification.QuotientRecognition.RankTwo.Exceptional.Transport
public import Theory.AtlasPort.LinearGroups.G2.LieShortParabolic.Quotient
public import Theory.AtlasPort.LinearGroups.G2.LieLongParabolic.Quotient
public import Theory.AtlasPort.LinearGroups.G2.EvenLocal.NormalizerCover
public import Theory.AtlasPort.LinearGroups.G2.LieAutomorphismExtensions.Semilinear
public import Theory.GroupTheory.PrimeRankHom
public import Theory.GroupTheory.PrimeRankZero
public import Theory.Representation.QuadraticFourGroup.Recognition.FactorSylows.Linear
public import Theory.GroupAction.AutomorphismFixedTransport

public import Theory.AtlasPort.LinearGroups.G2.Order
public import Theory.AtlasPort.LinearGroups.G2.Simplicity
public import Theory.AtlasPort.LinearGroups.G2.EvenFieldFixedResidual
public import Mathlib.Algebra.CharP.CharAndCard

/-!
# The G₂ branches of the fixed A₆ inspection

The proved normalizer cover places an inner involution centralizer in a full
root parabolic. A perfect subgroup has trivial torus character, and its
three-rank is at most one by the actual SL₂ projection with two-group kernel.
For an outer involution, a smaller-field fixed-group equivalence reduces the
component to a whole simple G₂ model. The binary endpoint is excluded by its
order, without identifying G₂(2)′ with a different model.

The parabolic argument follows the existing seven-component calculation in
`ComponentBalance/SevenLifting/Inspection/BinaryLie/G2/Inner.lean`, specialized
to the actual A₆ embedding. Coverage and field descent for outer involutions
remain explicit premises; this does not assert the full source inspection.
Source: Aschbacher–Smith E.6.23, printed p.254, and 16.1.4(1,4), p.1171,
`refs/quasithin.pdf`. The octonion imports retain their ATLAS attribution.
-/

public section
open Subgroup Theory.GroupTheory Atlas.G2 Atlas.G2.LieParabolicSetup
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.SixAutomorphisms.ModelIdentification.QuotientScreen.RankTwo.Exceptional.G2

private theorem perfect_hom_trivial {X C : Type*} [Group X] [Group.IsPerfect X]
    [CommMonoid C] (f : X →* C) : f = 1 := by
  let φ := f.toHomUnits
  let : Group.IsPerfect φ.range := Group.IsPerfect.range φ
  have : Subsingleton φ.range := inferInstance
  ext x
  exact congrArg (fun y : φ.range => (y.val : C))
    (Subsingleton.elim (⟨φ x, x, rfl⟩ : φ.range) 1)

variable {F : Type*} [Field F] [Finite F] [CharP F 2]

private theorem rank_of_two_kernel {X : Type*} [Group X] [Finite X]
    (f : X →* SL(2,F)) (hk : IsPGroup 2 f.ker) : primeRank 3 X ≤ 1 := by
  have hz : primeRank 3 f.ker = 0 := by
    apply PrimeRank.eq_zero_iff_not_dvd_card.mpr
    intro hd
    obtain ⟨n, hn⟩ := hk.exists_card_eq
    rw [hn] at hd
    exact (by decide : ¬ 3 ∣ 2) ((by decide : Nat.Prime 3).dvd_of_dvd_pow hd)
  have hsl : primeRank 3 SL(2,F) ≤ 1 := by
    let P : Sylow 3 SL(2,F) := default
    exact P.primeRank_le_one_of_isCyclic
      (Matrix.SL2.odd_pGroup_isCyclic_of_injective P.isPGroup' (by decide)
        (P : Subgroup SL(2,F)).subtype (P : Subgroup SL(2,F)).subtype_injective)
  have h := primeRank_le_ker_add (p := 3) f
  omega

private theorem rank_local_short : primeRank 3 (local₁ (F := F)) ≤ 1 := by
  apply rank_of_two_kernel (shortSLHom (F := F))
  rw [shortSLHom_ker]
  exact radical₁_isTwoGroup.comap_subtype

private theorem rank_local_long : primeRank 3 (local₂ (F := F)) ≤ 1 := by
  apply rank_of_two_kernel (longSLHom (F := F))
  rw [longSLHom_ker]
  exact radical₂_isTwoGroup.comap_subtype

omit [Finite F] in
private theorem perfect_le_short_local (L : Subgroup (Model F)) [Group.IsPerfect L]
    (hL : L ≤ parabolic₁) : L ≤ local₁ := by
  let f : L →* shortPlaneStabilizer (F := F) :=
    inclusion (hL.trans parabolic₁_le_shortPlaneStabilizer)
  have hχ := perfect_hom_trivial (shortDet.comp f)
  intro x hx
  rw [local₁_eq_shortSpecial]
  exact ⟨f ⟨x, hx⟩, congrArg (fun χ : L →* F => χ ⟨x, hx⟩) hχ, rfl⟩

omit [Finite F] in
private theorem perfect_le_long_local (L : Subgroup (Model F)) [Group.IsPerfect L]
    (hL : L ≤ parabolic₂) : L ≤ local₂ := by
  let f : L →* pointStabilizer (K := F) := inclusion (hL.trans parabolic_le_pointStabilizer)
  have hχ := perfect_hom_trivial (lineScalarHom.comp f)
  intro x hx
  have hm : f ⟨x, hx⟩ ∈ (lineScalarHom (K := F)).ker :=
    congrArg (fun χ : L →* Fˣ => χ ⟨x, hx⟩) hχ
  rw [lineScalarHom_kernel] at hm
  rwa [local₂_eq_fixingFirstVector]

/-- Every perfect subgroup of either full parabolic has three-rank at most one. -/
private theorem parabolic_perfect_rank (L : Subgroup (Model F)) [Group.IsPerfect L]
    (hL : L ≤ parabolic₁ ∨ L ≤ parabolic₂) : primeRank 3 L ≤ 1 := by
  rcases hL with hL | hL
  · exact (Theory.GroupTheory.primeRank_le_of_injective 3 (inclusion (perfect_le_short_local L hL))
      (inclusion_injective _)).trans rank_local_short
  · exact (Theory.GroupTheory.primeRank_le_of_injective 3 (inclusion (perfect_le_long_local L hL))
      (inclusion_injective _)).trans rank_local_long

/-- Every perfect subgroup centralizing an actual involution has no A₆ model. -/
theorem not_six_centralizing_involution (t : Model F) (ht : orderOf t = 2)
    (L : Subgroup (Model F)) [Group.IsPerfect L]
    (hL : L ≤ centralizer ({t} : Set (Model F))) : ¬ Nonempty (L ≃* alternatingGroup (Fin 6)) := by
  rintro ⟨e⟩
  have htn : t ≠ 1 := by intro h; simp [h] at ht
  have hp : IsPGroup 2 (zpowers t) := IsPGroup.of_card (n := 1) (by
    simpa only [Nat.card_zpowers, pow_one] using ht)
  obtain ⟨g, hg⟩ := Atlas.G2.EvenLocal.NormalizerCover.normalizer_conjugate_le_parabolic
    (zpowers t) (zpowers_ne_bot.mpr htn) hp
  have hLN : L ≤ normalizer (zpowers t : Set (Model F)) := by
    apply hL.trans
    have he : centralizer (zpowers t : Set (Model F)) =
        centralizer ({t} : Set (Model F)) := by
      rw [zpowers_eq_closure, centralizer_closure]
    rw [← he]
    exact centralizer_le_normalizer _
  let J := L.map (MulAut.conj g).toMonoidHom
  let : Group.IsPerfect J := Group.IsPerfect.map _
  have hJ : J ≤ parabolic₁ ∨ J ≤ parabolic₂ :=
    hg.imp ((map_mono hLN).trans ·) ((map_mono hLN).trans ·)
  have hu := parabolic_perfect_rank J hJ
  exact alternatingGroup.SixSubgroupObstructions.not_injective_of_three_rank_le_one hu
    (((MulAut.conj g).subgroupMap L).toMonoidHom.comp e.symm.toMonoidHom)
    (((MulAut.conj g).subgroupMap L).injective.comp e.symm.injective)

/-- Actual smaller-field fixed models for the non-inner branch. The existing
G₂ coverage and field-descent owners must construct these equivalences. -/
@[expose] def OuterFixedModels : Prop :=
  ∀ (K : Type) [Field K] [Finite K] (n : ℕ), 2 ≤ n → Nat.card K = 2 ^ n →
    ∀ a : MulAut (Model K), orderOf a = 2 →
      (∀ g : Model K, a ≠ MulAut.conj g) →
      ∃ (k : Type) (_ : Field k) (_ : Finite k),
        2 ≤ Nat.card k ∧ Nonempty (a.fixedSubgroup ≃* Model k)

/-- The full G₂(2) endpoint has no A₆ subgroup. Larger fixed models are simple,
so a component fills the fixed model and is excluded by the model order. -/
theorem not_six_of_fixed_model {D : Type*} [Group D]
    (a : MulAut D) (K : Type*) [Field K] [Finite K] (hK : 2 ≤ Nat.card K)
    (e : a.fixedSubgroup ≃* Model K) (S : Subgroup D)
    (hS : IsComponentIn S a.fixedSubgroup) :
    ¬ Nonempty (S ≃* alternatingGroup (Fin 6)) := by
  by_cases hb : Nat.card K = 2
  · rintro ⟨f⟩
    let j : S →* Model K := e.toMonoidHom.comp (inclusion hS.1)
    have hd := Subgroup.card_dvd_of_injective j (e.injective.comp (inclusion_injective _))
    rw [Nat.card_congr f.toEquiv, alternatingGroup.SixSubgroupObstructions.card_six,
      Atlas.G2.card_Model, hb] at hd
    norm_num at hd
  · let : IsSimpleGroup (Model K) := Atlas.G2.isSimple (by omega)
    apply not_six_of_simple_fixed_model (E := Model K) ?_ a e S hS
    have hlarge : 360 < Nat.card (Model K) := by
      rw [Atlas.G2.card_Model]
      calc
        360 < 3 ^ 6 * (3 ^ 6 - 1) * (3 ^ 2 - 1) := by norm_num
        _ ≤ Nat.card K ^ 6 * (Nat.card K ^ 6 - 1) * (Nat.card K ^ 2 - 1) := by
          gcongr <;> omega
    omega

/-- All G₂ cases reduce to the actual outer fixed-group descent.
The inner geometry and smaller-model component calculation are proved here. -/
theorem excludesFixedSix_of_outerFixedModels (hd : OuterFixedModels)
    (K : Type) [Field K] [Finite K] {n : ℕ} (hn : 2 ≤ n)
    (hc : Nat.card K = 2 ^ n) : ExcludesFixedSix (Model K) := by
  let : Fintype K := Fintype.ofFinite K
  let : CharP K 2 := charP_of_card_eq_prime_pow (p := 2) (f := n) (by
    simpa only [Nat.card_eq_fintype_card] using hc)
  have hq : 2 < Nat.card K := by
    rw [hc]
    have := Nat.pow_le_pow_right (by decide : 1 ≤ 2) hn
    omega
  intro a ha S hS
  by_cases hi : ∃ g : Model K, a = MulAut.conj g
  · obtain ⟨g, rfl⟩ := hi
    have hg : orderOf g = 2 := by
      rwa [orderOf_injective MulAut.conj
        (conj_injective_of_center_eq_bot
          (Atlas.G2.LieAutomorphismExtensions.model_center_eq_bot hq))] at ha
    let : IsQuasisimple S := hS.quasisimple
    exact not_six_centralizing_involution g hg S
      (by simpa only [MulAut.fixedSubgroup_conj] using hS.1)
  · obtain ⟨k, _, _, hk, ⟨e⟩⟩ := hd K n hn hc a ha (fun g hg => hi ⟨g, hg⟩)
    exact not_six_of_fixed_model a k hk e S hS

end CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.SixAutomorphisms.ModelIdentification.QuotientScreen.RankTwo.Exceptional.G2
