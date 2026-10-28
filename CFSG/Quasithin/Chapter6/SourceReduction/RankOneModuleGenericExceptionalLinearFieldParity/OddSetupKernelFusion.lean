module
public import CFSG.Quasithin.ChapterB.Section02.SolvableThreePrime
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalLinearFieldParity.OddSetupGeometry
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalLinearFieldEscapeModulesCentralizer
public import CFSG.Quasithin.Chapter5.RankOneBaumannSourceComplete
public import CFSG.Quasithin.Chapter6.SourceReduction.LocalCentralization.Geometry
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalLinearResidualReduction
public import Stellmacher.OmegaCenterCentralizer
public import Theory.GroupTheory.GeneralizedFitting.SylowOvergroup
public import Theory.GroupTheory.ComponentLocalPrimeFree

/-!
# Point TI under the solvable residual quotient-centralizer

The nonfaithful residual centralizes the Sylow omega-center. Uniqueness
therefore gives C_T(L) = 1, making the earlier Baumann point-centralizer
premise vacuous. Thus its Baumann normalizer lies in N_G(L).

Let C be the literal action kernel in N_G(O²(H)), embedded in G.
The group CT has order prime to three and, when C is solvable, is
solvable. Since it contains T inside the maximal residual normalizer,
it has characteristic two. Solvable Thompson factorization then shows
that every CT-conjugate of a subgroup of Ω₁Z(T) is already realized in
N_G(L). The proved natural-module point TI applies.

The final parity owner qt-d-1222-linear-field-parity retains source
5.1.16(2), extension to the full residual normalizer, and block exclusion.
Source: Aschbacher–Smith, 5.1.17, printed p.640 (refs/quasithin.pdf).
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.LinearParity
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L W H : Subgroup G} {n : ℕ}

/-- In this branch the source Baumann-control premise is vacuous. -/
theorem baumann_normalizer_le_of_nonfaithful_residual
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hK : residual H ∈ Chapter1.LStar G (T : Subgroup G))
    (hnf : ¬ ChapterA.Section04.IsFaithfulSignalizerType (residual H)) :
    normalizer (ChapterB.baumann (T : Subgroup G) : Set G) ≤ normalizer (L : Set G) := by
  have hHC : H ≤ omegaCentralizer T :=
    (residual_le_omegaCentralizer_iff hH.1.1.2).mp
      (residual_centralizes_omega_of_nonfaithful h.qtke hH.1.1 hK.1 hnf)
  have hz := h.centralOmega_disjoint_of_outside_centralizes hH hHC
  have ht := Stellmacher.inf_centralizer_eq_bot_of_omega_center
    (T : Subgroup G) L T.isPGroup' h.sylow_normalizes hz
  apply h.baumann_normalizer_of_point_centralizers
  intro x hx hne
  exact (hne (show x = 1 from mem_bot.mp (ht ▸ (show x ∈ (T : Subgroup G) ⊓
    centralizer (L : Set G) from ⟨hx.1.1,hx.2⟩)))).elim

/-- The literal quotient-centralizer and Sylow join has fusion controlled
on subgroups of the omega-center by N_G(L). -/
theorem residual_kernel_sylow_fusion
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hK : residual H ∈ Chapter1.LStar G (T : Subgroup G))
    (hnf : ¬ ChapterA.Section04.IsFaithfulSignalizerType (residual H))
    (hm : ClassicalGroup.IsPSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 3 4)
    (hsolv : Group.IsSolvable
      (normalizerQuotientAction (residual H) (pCore 2 (residual H))).ker)
    (Z : Subgroup G) (hZ : Z ≤ Stellmacher.omegaOneCenterAmbient (T : Subgroup G))
    {g : G} (hg : g ∈
      (normalizerQuotientAction (residual H) (pCore 2 (residual H))).ker.map
        (normalizer (residual H : Set G)).subtype ⊔ (T : Subgroup G)) :
    ∃ b ∈ normalizer (L : Set G),
      Z.map (MulAut.conj g).toMonoidHom = Z.map (MulAut.conj b).toMonoidHom := by
  let N := normalizer (residual H : Set G)
  let f := normalizerQuotientAction (residual H) (pCore 2 (residual H))
  let C := f.ker.map N.subtype
  let M := C ⊔ (T : Subgroup G)
  have hTN : (T : Subgroup G) ≤ N := hH.1.1.2.trans (le_normalizer_residual H)
  have hNC : N ≤ normalizer (C : Set G) := by
    simpa only [normalizer_eq_top,← MonoidHom.range_eq_map,range_subtype] using
      f.ker.le_normalizer_map N.subtype
  have hTC := hTN.trans hNC
  have hMN : M ≤ N := sup_le (map_subtype_le _) hTN
  let : Group.IsSolvable f.ker := hsolv
  let : Group.IsSolvable C := Group.isSolvable_of_surjective (N.subtype.subgroupMap_surjective f.ker)
  let : Group.IsNilpotent T := T.isPGroup'.isNilpotent
  have hsolM : Group.IsSolvable M := Group.isSolvable_sup_of_normalizes C (T : Subgroup G) hTC
  have hmax := (Chapter1.Section02.nonsolvable_uniqueness_knownSimple h.qtke T hK).normalizer_maximal
  have he : componentOrbit (residual H) (T : Subgroup G) = residual H :=
    le_antisymm (iSup_conjugates_le_of_le_normalizer _ _ _ le_rfl hTN)
      (le_componentOrbit _ _)
  rw [he] at hmax
  have hsq : IsStronglyQuasithin N := (h.qtke.twoLocal_sqtk hmax.1).stronglyQuasithin
  have hcN := h.qtke.evenCharacteristic T N hmax hTN
  have hchar : centralizer (pCore 2 M : Set M) ≤ pCore 2 M := by
    rw [← generalizedFitting_eq_pCore_of_sylow_overgroup T M N le_sup_right hMN hcN]
    exact centralizer_generalizedFitting_le M
  have h3C : ¬ 3 ∣ Nat.card C := by
    change ¬ 3 ∣ Nat.card (f.ker.map N.subtype)
    rw [card_map_of_injective N.subtype_injective]
    exact Nat.prime_three.coprime_iff_not_dvd.mp
      (CubicEscape.quotientAction_kernel_three_prime (residual H) hsq (linear_residual_quotient hm))
  have h3T : ¬ 3 ∣ Nat.card T := by
    obtain ⟨k,hk⟩ := T.isPGroup'.exists_card_eq
    rw [hk]
    exact Nat.prime_three.coprime_iff_not_dvd.mp ((by decide : Nat.Coprime 3 2).pow_right k)
  have h3M := not_dvd_card_sup_of_normalizes Nat.prime_three C (T : Subgroup G) hTC h3C h3T
  let Ω := Stellmacher.omegaOneCenterAmbient (T : Subgroup G)
  let : IsElementaryAbelian 2 Ω := Stellmacher.omegaOneCenterAmbient_elementaryAbelian _
  have hΩT : Ω ≤ (T : Subgroup G) := fun z hz =>
    ((Stellmacher.mem_omegaOneCenterAmbient_iff _ _).mp hz).1
  have hΩC : Ω ≤ centralizer (T : Set G) := fun z hz =>
    ((Stellmacher.mem_omegaOneCenterAmbient_iff _ _).mp hz).2.2
  obtain ⟨b,hb,heq⟩ := ChapterB.solvable_three_prime_central_seed_fusion T M Ω le_sup_right
    hΩT hΩC hchar hsolM h3M Z hZ hg
  exact ⟨b,baumann_normalizer_le_of_nonfaithful_residual h hH hK hnf hb.2,heq⟩

/-- The original natural point is TI under the quotient-centralizer joined with T. -/
theorem fundamental_point_ti_under_solvable_kernel
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hK : residual H ∈ Chapter1.LStar G (T : Subgroup G))
    (hnf : ¬ ChapterA.Section04.IsFaithfulSignalizerType (residual H))
    (hm : ClassicalGroup.IsPSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 3 4)
    (hsolv : Group.IsSolvable
      (normalizerQuotientAction (residual H) (pCore 2 (residual H))).ker)
    (D : Chapter3.Section02.FundamentalSetup KnownSimple.IsKnownSimple T L)
    (hodd : Odd n) (hnat : IsNaturalModule L D.moduleSubgroup n)
    {g : G} (hg : g ∈
      (normalizerQuotientAction (residual H) (pCore 2 (residual H))).ker.map
        (normalizer (residual H : Set G)).subtype ⊔ (T : Subgroup G)) :
    let Z := Stellmacher.omegaOneCenterAmbient (T : Subgroup G) ⊓ D.moduleSubgroup
    Z ⊓ Z.map (MulAut.conj g).toMonoidHom = ⊥ ∨
      Z.map (MulAut.conj g).toMonoidHom = Z := by
  obtain ⟨b,hb,he⟩ := residual_kernel_sylow_fusion h hH hK hnf hm hsolv
    (Stellmacher.omegaOneCenterAmbient (T : Subgroup G) ⊓ D.moduleSubgroup) inf_le_left hg
  dsimp only
  rw [he]
  exact fundamental_point_ti_under_normalizer D h.sylow_normalizes h.linear hodd hnat hb
end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.LinearParity
