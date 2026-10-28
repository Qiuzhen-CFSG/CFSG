module
public import CFSG.Quasithin.Chapter7.NormalizedSource.DoubledBinaryCoverPlacement
public import Theory.SpecificGroups.PSL2.ThompsonBorel
public import Theory.SpecificGroups.Suzuki.ComponentThompson

open Subgroup Theory.GroupTheory PerfectCentralCovering Stellmacher
open scoped MatrixGroups
/-!
# Actual Borel control for the linear-two and Suzuki component rows

Ordinary multiplier triviality identifies the component itself with the
specified simple model. The intrinsic Thompson theorems then put its
original Sylow normalizer in N_G(J(Q)), even when Q exchanges two components.
The component orbit has at most two points by strong quasithinness.
The chosen-module consumer combines this containment with the existing
Cartan escape and thereby excludes both rows on the original plane.

Source: Aschbacher–Smith 7.7.6, printed p.706, using the Thompson Borel
calculations underlying 15.1.21(i), printed pp.1097–1098. This gives an
alternative to the local C(G,Q) argument for precisely these two rows.
-/
public noncomputable section
namespace CFSG.Quasithin.Chapter7.NormalizedSource.DoubledBinaryBenderExclusion
universe u v
private theorem center_eq_bot_of_identity {K : Type u} {S : Type v}
    [Group K] [Finite K] [IsQuasisimple K] [Group S] [Finite S] [IsQuasisimple S]
    (e : K ⧸ center K ≃* S)
    (hc : Covering.IsUniversal.{v,v,u} (Covering.id : Covering S S)) : center K = ⊥ := by
  let f : Covering K S := (centralQuotientCover e).toCovering
  have hd := kernel_card_dvd_of_surjective_factor (MonoidHom.id S) f.toMonoidHom
    (hc.lift f).toMonoidHom (hc.lift f).surjective
    (congrArg Covering.toMonoidHom (hc.lift_fac f))
  change Nat.card (centralQuotientCover e).toMonoidHom.ker ∣ _ at hd
  rw [centralQuotientCover_ker,MonoidHom.ker_id,card_bot] at hd
  exact card_eq_one.mp (Nat.dvd_one.mp hd)

private def wholeEquiv {K S : Type*} [Group K] [Group S]
    (hz : center K = ⊥) (e : K ⧸ center K ≃* S) : K ≃* S :=
  QuotientGroup.quotientBot.symm.trans ((QuotientGroup.quotientMulEquivOfEq hz.symm).trans e)

/-- The actual Borel normalizes J(Q) for a PSL₂ component in the surviving
field range, with no prior normalization assumption on Q. -/
theorem linearTwo_normalizer_thompson
    {G : Type*} [Group G] [Finite G] (H K Q : Subgroup G)
    (hK : IsComponentIn K H) (hQH : Q ≤ H) (hp : IsPGroup 2 Q)
    (hi : (normalizer (K : Set G)).relIndex Q ≤ 2)
    (P : Sylow 2 K) (hPQ : (P : Subgroup K).map K.subtype ≤ Q)
    {n : ℕ} (hn : 4 ≤ n) (hm : ClassicalGroup.IsPSL (K ⧸ center K) 2 (2^n)) :
    (normalizer (P : Set K)).map K.subtype ≤ normalizer (elementaryAbelianMaxJ Q : Set G) := by
  let := hK.quasisimple
  obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
  let : CharP F 2 := Theory.SpecificGroups.SymplecticFour.EvenProjective.charTwo_of_card hF
  have hbig : 8 ≤ Nat.card F := by
    rw [hF]
    exact (by decide : 8 ≤ 2^4).trans (Nat.pow_le_pow_right (by decide) hn)
  let : Fact (3 < Nat.card F) := ⟨by omega⟩
  have heven : Even (Nat.card F) := by
    rw [hF]
    exact even_iff_two_dvd.mpr (dvd_pow_self 2 (by omega))
  have hz := center_eq_bot_of_identity e
    (GorensteinWalter.PSL2Cover.identity_isUniversal_of_even F heven hbig)
  exact Theory.PSL2.OrdinaryBorel.component_normalizer_thompson_field
    H K Q hK.1 hQH hK.2 hp hi P hPQ (by omega) hF (wholeEquiv hz e)

/-- The actual Suzuki Borel normalizes J(Q), retaining the original Suzuki
parameter and allowing an exchanged pair of components. -/
theorem suzuki_normalizer_thompson
    {G : Type*} [Group G] [Finite G] (H K Q : Subgroup G)
    (hK : IsComponentIn K H) (hQH : Q ≤ H) (hp : IsPGroup 2 Q)
    (hi : (normalizer (K : Set G)).relIndex Q ≤ 2)
    (P : Sylow 2 K) (hPQ : (P : Subgroup K).map K.subtype ≤ Q)
    {m : ℕ} (hm : 2 ≤ m)
    (he : Nonempty ((K ⧸ center K) ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m)) :
    (normalizer (P : Set K)).map K.subtype ≤ normalizer (elementaryAbelianMaxJ Q : Set G) := by
  let := hK.quasisimple
  let : Fact (0 < m) := ⟨by omega⟩
  have hz := center_eq_bot_of_identity he.some
    (ChapterI.LieMultipliers.Suzuki.ordinary_identity_isUniversal m hm)
  exact BenderSuzuki.MatrixGroups.suzuki_component_borel_normalizes_thompson
    H K Q hK.1 hQH hK.2 hp hi P hPQ (by omega) (wholeEquiv hz he.some)

/-- Strong quasithinness bounds the actual Q-orbit of an ordinary component
by two. This is the relative normalizer index required above. -/
theorem component_normalizer_index
    {G : Type*} [Group G] [Finite G] (H K Q : Subgroup G)
    (hH : IsStronglyQuasithin H) (hK : IsComponentIn K H) (hQH : Q ≤ H) :
    (normalizer (K : Set G)).relIndex Q ≤ 2 := by
  have hb : (normalizer (K : Set G)).relIndex H ≤ 2 := by
    change ((normalizer (K : Set G)).subgroupOf H).index ≤ 2
    rw [subgroupOf_normalizer_eq hK.1]
    rcases hK.2.normal_or_index_two_of_odd_rank_le_two hH with hn | hi
    · let := hn
      rw [normalizer_eq_top,index_top]
      decide
    · exact hi.le
  exact (relIndex_le_of_le_right hQH index_ne_zero_of_finite).trans hb
end CFSG.Quasithin.Chapter7.NormalizedSource.DoubledBinaryBenderExclusion
