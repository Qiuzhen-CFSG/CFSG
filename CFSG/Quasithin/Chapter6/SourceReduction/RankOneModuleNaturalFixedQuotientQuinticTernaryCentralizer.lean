module

public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleNaturalFixedQuotientQuinticTernarySubgroup
public import Theory.SpecificGroups.PSL3.QuinticSylowCentralizer
public import Theory.SpecificGroups.SU3.QuinticSylowCentralizer
public import FeitThompson.FinalTheorem

/-!
# The original quintic ternary action fixes a central Sylow involution

The subgroup inside the core-central quotient and its full Sylow are the
literal objects supplied by the original quintic action. Their two-five
product is preserved by every actor in (X ∨ T) ∩ N(K). The native ternary
Sylow theorem fixes the same central involution under all these actors.
No assertion that T already normalizes K is needed.

Source: Aschbacher--Smith 6.1.4, printed pp.665--666, and A.3.21(a).
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
open scoped MatrixGroups Pointwise
attribute [local instance] Representation.SL2.BinarySmall.spaceBinaryModule
namespace CFSG.Quasithin.Chapter6.Source.RankOneRecognition
open RankOneGeneric Chapter1.Section02.LocalModels

private theorem control_transport {C D : Type*} [Group C] [Finite C]
    [Group D] [Finite D] (e : C ≃* D)
    (native : ∀ (P : Sylow 2 D) (J : Subgroup D), (P : Subgroup D) ≤ J →
      ∀ (k : ℕ), Nat.card J ∣ 2^k*5 → ∀ (w : P), orderOf w = 2 → w ∈ center P →
      ∀ (a : MulAut D), J.map a.toMonoidHom = J → a (w : D) = w)
    (S : Sylow 2 C) (H : Subgroup C) (hSH : (S : Subgroup C) ≤ H)
    (k : ℕ) (hcard : Nat.card H ∣ 2^k*5)
    (z : S) (hz : orderOf z = 2) (hzc : z ∈ center S)
    (a : MulAut C) (ha : H.map a.toMonoidHom = H) : a (z : C) = z := by
  let P := S.mapSurjective (f := e.toMonoidHom) e.surjective
  let J := H.map e.toMonoidHom
  let eS : S ≃* P := (S : Subgroup C).equivMapOfInjective e.toMonoidHom e.injective
  have hw : orderOf (eS z) = 2 := (eS.orderOf_eq z).trans hz
  have hwc : eS z ∈ center P := by
    apply mem_center_iff.mpr
    intro x
    obtain ⟨y,rfl⟩ := eS.surjective x
    simpa only [←map_mul] using congrArg eS (mem_center_iff.mp hzc y)
  have hJ : Nat.card J ∣ 2^k*5 := by
    rwa [card_map_of_injective e.injective]
  have hmap : J.map ((MulAut.congr e) a).toMonoidHom = J := by
    dsimp [J]
    rw [map_map]
    have he : ((MulAut.congr e) a).toMonoidHom.comp e.toMonoidHom =
        e.toMonoidHom.comp a.toMonoidHom := by ext x; simp
    change H.map (((MulAut.congr e) a).toMonoidHom.comp e.toMonoidHom) = H.map e.toMonoidHom
    rw [he,←map_map,ha]
  have hh := native P J (map_mono hSH) k hJ (eS z) hw hwc ((MulAut.congr e) a) hmap
  apply e.injective
  have hv : (eS z : D) = e (z : C) :=
    coe_equivMapOfInjective_apply _ _ _ _
  rw [hv] at hh
  simpa only [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.symm_apply_apply] using hh

private theorem ternary_control {C : Type*} [Group C] [Finite C]
    (p : ℕ) (hp : p.Prime) (ho : Odd p) (unitary : Bool)
    (hc : IsPSLSign C unitary 3 p)
    (S : Sylow 2 C) (H : Subgroup C) (hSH : (S : Subgroup C) ≤ H)
    (k : ℕ) (hcard : Nat.card H ∣ 2^k*5)
    (z : S) (hz : orderOf z = 2) (hzc : z ∈ center S)
    (a : MulAut C) (ha : H.map a.toMonoidHom = H) : a (z : C) = z := by
  let : Fact p.Prime := ⟨hp⟩
  cases unitary with
  | false =>
    obtain ⟨F,_,_,hF,⟨e⟩⟩ := hc
    apply control_transport e _ S H hSH k hcard z hz hzc a ha
    intro P J hPJ k hk w hw hwc b hb
    exact Matrix.PSL3.TwoFiveSylow.automorphism_fixes_involution
      F (hF.symm ▸ ho) P J hPJ hk w hw hwc b hb
  | true =>
    obtain ⟨F,_,_,J,hF,hconj,⟨e⟩⟩ := hc
    let : Finite (BenderSuzuki.MatrixGroups.ProjectiveSpecialUnitaryMatrixGroup J) :=
      Finite.of_surjective J.specialToProjective J.specialToProjective_surjective
    apply control_transport e _ S H hSH k hcard z hz hzc a ha
    intro P H hPH k hk w hw hwc b hb
    exact Matrix.SU3.TwoFiveSylow.automorphism_fixes_involution
      p ho F J hF hconj P H hPH hk w hw hwc b hb

private theorem quintic_product_stabilized {G : Type*} [Group G] [Finite G]
    (K X T : Subgroup G) (hXN : X ≤ normalizer (K : Set G))
    (hTX : T ≤ normalizer (X : Set G))
    (S : Subgroup (coreCentralQuotient K))
    (hS : S = coreCentralIntersectionImage K T)
    (hY : ((coreCentralActorImage K X).comap MulAut.conj).map MulAut.conj =
      coreCentralActorImage K X) :
    let Y := (coreCentralActorImage K X).comap MulAut.conj
    coreCentralActorImage K (X ⊔ T) ≤
      MulAction.stabilizer (MulAut (coreCentralQuotient K)) (Y ⊔ S) := by
  let C := coreCentralQuotient K
  let B := coreCentralActorImage K X
  let Y : Subgroup C := B.comap MulAut.conj
  let H := Y ⊔ S
  let f := normalizerCoreCentralAction K
  have hTfix : coreCentralActorImage K T ≤ MulAction.stabilizer (MulAut C) H := by
    intro a ha
    have hSa : S.map a.toMonoidHom = S := by
      rw [hS]
      exact coreCentralActorImage_stabilizes K T T T.le_normalizer ha
    have hYa : Y.map a.toMonoidHom = Y := by
      apply eq_of_le_of_card_ge
      · rintro _ ⟨y,hy,rfl⟩
        obtain ⟨t,ht,rfl⟩ := ha
        have hn : f t ∈ normalizer (B : Set (MulAut C)) := by
          apply (X.subgroupOf (normalizer (K : Set G))).le_normalizer_map f
          apply mem_map_of_mem
          apply mem_normalizer_iff.mpr
          intro x
          exact mem_normalizer_iff.mp (hTX ht) (x : G)
        have hid : MulAut.conj (f t y) = f t * MulAut.conj y * (f t)⁻¹ := by
          ext x
          simp [MulAut.conj_apply]
        change MulAut.conj (f t y) ∈ B
        rw [hid]
        exact (mem_normalizer_iff.mp hn (MulAut.conj y)).mp hy
      · exact le_of_eq (card_map_of_injective a.injective).symm
    change H.map a.toMonoidHom = H
    exact (map_sup Y S a.toMonoidHom).trans (congrArg₂ (· ⊔ ·) hYa hSa)
  have hXfix : coreCentralActorImage K X ≤ MulAction.stabilizer (MulAut C) H := by
    intro a ha
    rw [←hY] at ha
    obtain ⟨y,hy,rfl⟩ := ha
    exact mem_normalizer_iff_map_conj_eq.mp (H.le_normalizer ((show Y ≤ H from le_sup_left) hy))
  change coreCentralActorImage K (X ⊔ T) ≤ MulAction.stabilizer (MulAut C) H
  rintro _ ⟨g,hg,rfl⟩
  have hgprod : (g : G) ∈ (X : Set G) * (T : Set G) := by
    rw [←coe_mul_of_right_le_normalizer_left X T hTX]
    exact hg
  obtain ⟨x,hx,t,ht,hxt⟩ := hgprod
  have htN : t ∈ normalizer (K : Set G) := by
    have hh := (normalizer (K : Set G)).mul_mem
      ((normalizer (K : Set G)).inv_mem (hXN hx)) g.property
    simpa [←hxt] using hh
  let xn : normalizer (K : Set G) := ⟨x,hXN hx⟩
  let tn : normalizer (K : Set G) := ⟨t,htN⟩
  have he : g = xn * tn := Subtype.ext hxt.symm
  rw [he,map_mul]
  exact (MulAction.stabilizer (MulAut C) H).mul_mem
    (hXfix (mem_map_of_mem f hx)) (hTfix (mem_map_of_mem f ht))

variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L M V M₁ K : Subgroup G} {n : ℕ}

/-- A central involution in the actual projected component Sylow centralizes
its quintic product and is fixed by every original (X ∨ T)-actor on K. -/
theorem original_hermitian_quintic_ternary_centralizer
    (h : Hypothesis611 KnownSimple.IsKnownSimple T L M V n)
    (hout : Chapter3.HasMaximalOutside T M)
    (hm : IsConjugationModel L (reducedSubgroup (L ⊔ (T : Subgroup G)))
      (Representation.SL2.BinarySmall.hermitian 2))
    (hM₁ : IsMaximalTwoLocal M₁) (hCM₁ : omegaCentralizer T ≤ M₁)
    (hK : K ∈ Chapter1.cComponentsIn M₁) (hnot : ¬ K ≤ M)
    (hq : IsQuasisimple (K ⧸ pCore 2 K))
    (p : ℕ) (hp : p.Prime) (ho : Odd p) (unitary : Bool)
    (hc : IsPSLSign (coreCentralQuotient K) unitary 3 p) :
    let C := coreCentralQuotient K
    let X := quinticResidual T L
    let Y := (coreCentralActorImage K X).comap (MulAut.conj : C →* MulAut C)
    Y.map MulAut.conj = coreCentralActorImage K X ∧
      IsPPerfect 2 Y ∧ Group.IsSolvable Y ∧ Nat.card (Y ⧸ pCore 2 Y) = 5 ∧
      ∃ (S : Sylow 2 C) (z : S),
        (S : Subgroup C) = coreCentralIntersectionImage K (T : Subgroup G) ∧
        (S : Subgroup C) ≤ normalizer (Y : Set C) ∧
        orderOf z = 2 ∧ z ∈ center S ∧
        (∃ a : ℕ, Nat.card (Y ⊔ (S : Subgroup C) : Subgroup C) = 2^a*5) ∧
        Y ⊔ (S : Subgroup C) ≤ centralizer ({(z : C)} : Set C) ∧
        ∀ a ∈ coreCentralActorImage K (X ⊔ (T : Subgroup G)), a (z : C) = z := by
  let := hq
  let C := coreCentralQuotient K
  let X := quinticResidual T L
  let Y := (coreCentralActorImage K X).comap (MulAut.conj : C →* MulAut C)
  let : IsSimpleGroup C := IsQuasisimple.simple
  let : Group.IsPerfect C := Group.IsPerfect.ofSurjective
    (QuotientGroup.mk'_surjective (center (K ⧸ pCore 2 K)))
  obtain ⟨hY,hperf,hsolv,hfive,S,hS,hSN,k,hcard⟩ :=
    original_hermitian_quintic_ternary_subgroup h hout hm hM₁ hCM₁ hK hnot hq p hp ho unitary hc
  have htwo : 2 ∣ Nat.card C := by
    by_contra hn
    exact Group.IsPerfect.not_isSolvable C
      (odd_order_theorem C (Nat.not_even_iff_odd.mp (by simpa only [even_iff_two_dvd] using hn)))
  let : Nontrivial S := (nontrivial_iff_ne_bot _).mpr (S.ne_bot_of_dvd_card htwo)
  let := S.isPGroup'.center_nontrivial
  have hZ := S.isPGroup'.to_subgroup (center S)
  obtain ⟨b,hb,hbcard⟩ := hZ.nontrivial_iff_card.mp inferInstance
  obtain ⟨z,hz⟩ := exists_prime_orderOf_dvd_card' (G := center S) 2
    (hbcard ▸ dvd_pow_self 2 (by omega : b ≠ 0))
  have hzS : orderOf z.val = 2 := by simpa only [Subgroup.orderOf_coe] using hz
  have hcontrol := ternary_control p hp ho unitary hc S (Y ⊔ (S : Subgroup C))
    le_sup_right k (hcard ▸ dvd_rfl) z.val hzS z.property
  have hcentral : Y ⊔ (S : Subgroup C) ≤ centralizer ({(z.val : C)} : Set C) := by
    intro y hy
    have he := hcontrol (MulAut.conj y)
      (mem_normalizer_iff_map_conj_eq.mp ((Y ⊔ (S : Subgroup C)).le_normalizer hy))
    apply mem_centralizer_singleton_iff.mpr
    simpa only [MulAut.conj_apply,mul_inv_eq_iff_eq_mul] using he
  have hstab := quintic_product_stabilized K X (T : Subgroup G)
    (original_hermitian_quintic_normalizes_component h hout hm hM₁ hCM₁ hK)
    (sylow_normalizes_quinticResidual (h.rankOneInput hout).sylow_normalizes)
    (S : Subgroup C) hS hY
  refine ⟨hY,hperf,hsolv,hfive,S,z.val,hS,hSN,hzS,z.property,⟨k,hcard⟩,hcentral,?_⟩
  intro a ha
  exact hcontrol a (hstab ha)

end CFSG.Quasithin.Chapter6.Source.RankOneRecognition
