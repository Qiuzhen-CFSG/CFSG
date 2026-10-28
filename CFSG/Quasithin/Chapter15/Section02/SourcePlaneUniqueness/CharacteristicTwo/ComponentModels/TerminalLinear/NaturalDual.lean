module

public import CFSG.Quasithin.Chapter15.Section02.SourcePlaneUniqueness.CharacteristicTwo.ComponentModels.TerminalLinear.Setup
public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceImplication.ParabolicConclusion
public import Theory.SpecificGroups.BinaryLinear.SmallLeviRank
public import Theory.GroupTheory.PrimeRankResidualCentralizer
public import Theory.GroupTheory.PrimeRankZero

/-!
# The rank obstruction to the terminal natural-plus-dual row

B.5.1(6) gives the actual Sylow-fixed centralizer a two-core quotient
PSL_{n-2}(2), for n = 4 or 5. This bounds its three-rank by one.
The original KS has three-rank two, as soon as its earlier source
quotient S₃ × S₃ is supplied. Taking O²(H) preserves odd rank, so K
also has three-rank at least two. Odd rank survives the two-core
quotient map of X, so the image of K cannot lie in that centralizer.

The last theorem applies this obstruction to M₁ = C_X(ZS). Its explicit
centralizer-image identity is an outstanding module-recognition premise,
not an assumed contradiction. The terminal recognition producer must
identify the original U-action and its Sylow-fixed space to discharge it.
The KS quotient is the earlier 15.2.21(1) input owned by SmallActions;
the actual K containment belongs to the terminal component preparation.

Source: Aschbacher--Smith, combined manuscript (1 March 2004),
15.2.23(b), printed p.1117, and B.5.1(6), printed pp.99 and 103.
-/

public section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section02.TerminalLinear
open ChapterB.QuasisimpleSource Section01

private theorem symmetricPair_threeRank :
    primeRank 3 (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3)) = 2 := by
  have hle : primeRank 3 (Equiv.Perm (Fin 3)) ≤ 1 := by
    apply primeRank_le_one_of_square_not_dvd
    rw [Nat.card_perm, Nat.card_fin]
    decide
  have hne : primeRank 3 (Equiv.Perm (Fin 3)) ≠ 0 := by
    intro h
    have hd := PrimeRank.eq_zero_iff_not_dvd_card.mp h
    rw [Nat.card_perm, Nat.card_fin] at hd
    exact hd (by decide)
  rw [primeRank_prod_eq_add]
  omega

variable {D W : Type*} [Group D] [Finite D] [AddCommGroup W] [Module (ZMod 2) W]
variable {ρ : Representation (ZMod 2) D W} {L : Subgroup D} {n : ℕ}

/-- Odd rank is measured on the literal centralizer, before taking its two-core quotient. -/
theorem sylowFixedCentralizer_threeRank_le_one (hn : n = 4 ∨ n = 5)
    {P : Sylow 2 D} (c : SylowFixedCentralizer ρ L n P) :
    primeRank 3 (subspaceKernel ρ (fixedSpace ρ P) L) ≤ 1 := by
  rw [← primeRank_quotient_eq_of_isTwoGroup 3 (by decide)
    (pCore 2 (subspaceKernel ρ (fixedSpace ρ P) L)) pCore_isPGroup,
    primeRank_equiv 3 c.quotientEquiv]
  exact BinaryLinear.SmallLeviRank.interior hn

variable [FiniteDimensional (ZMod 2) W]

/-- The whole natural-plus-dual action has the same small-rank centralizer,
without choosing an unrelated moved section. -/
theorem naturalDual_fixedCentralizer_threeRank (hn : n = 4 ∨ n = 5)
    (hnat : IsNaturalPlusDual ρ n) (P : Sylow 2 D) :
    primeRank 3 (subspaceKernel ρ (fixedSpace ρ P) ⊤) ≤ 1 := by
  obtain ⟨e⟩ := hnat
  let S := P.mapSurjective (f := e.groupEquiv.toMonoidHom) e.groupEquiv.surjective
  obtain ⟨c⟩ := NaturalDualCentralizer.sylowFixedCentralizer_naturalPlusDual hn S
  have c' : SylowFixedCentralizer (naturalPlusDual n)
      ((⊤ : Subgroup D).map e.groupEquiv.toMonoidHom) n S := by
    simpa only [map_top_of_surjective e.groupEquiv.toMonoidHom e.groupEquiv.surjective] using c
  obtain ⟨a⟩ := sylowFixedCentralizer_transport e ⊤ n P c'
  exact sylowFixedCentralizer_threeRank_le_one hn a

/-- B.5.1(6) excludes a three-rank-two subgroup in the Sylow-fixed centralizer. -/
theorem naturalDual_not_le_fixedCentralizer (s : MovedSection ρ L)
    (hn : n = 4 ∨ n = 5) (hL : L = ⊤)
    (hnat : IsNaturalPlusDual (s.space.toRepresentation.comp L.subtype) n)
    (P : Sylow 2 D) (A : Subgroup D) (hrank : 2 ≤ primeRank 3 A) :
    ¬ A ≤ subspaceKernel ρ (fixedSpace ρ P) L := by
  intro hA
  obtain ⟨c⟩ := s.sylowFixedCentralizer_of_naturalDual ρ hn hL hnat P
  have hb := (primeRank_mono 3 hA).trans (sylowFixedCentralizer_threeRank_le_one hn c)
  omega

variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc V H ZS X : Subgroup G}
variable {hsource : ChosenSmallSource T M Mc V}

/-- The actual S₃-square quotient supplies the rank of the original KS. -/
theorem KS_threeRank (hpair : Nonempty ((KS H T ZS ⧸ pCore 2 (KS H T ZS)) ≃*
    (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3)))) :
    primeRank 3 (KS H T ZS) = 2 := by
  obtain ⟨e⟩ := hpair
  rw [← primeRank_quotient_eq_of_isTwoGroup 3 (by decide)
    (pCore 2 (KS H T ZS)) pCore_isPGroup, primeRank_equiv 3 e]
  exact symmetricPair_threeRank

/-- The original K has at least the three-rank of KS. S need not lie in X. -/
theorem K_threeRank_ge_two (d : PlaneUniquenessPreceding hsource H ZS)
    (hpair : Nonempty ((KS H T ZS ⧸ pCore 2 (KS H T ZS)) ≃*
      (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3)))) :
    2 ≤ primeRank 3 ((pResidual 2 H).map H.subtype) := by
  have hKSH : KS H T ZS ≤ H := by
    exact (sup_le_sup_left inf_le_left _).trans_eq d.residual_sup_sylow
  have hr : primeRank 3 ((pResidual 2 H).map H.subtype) = primeRank 3 H := by
    rw [← primeRank_equiv 3 ((pResidual 2 H).equivMapOfInjective H.subtype H.subtype_injective)]
    exact ResidualCentralizerRank.primeRank_residual (by decide : Nat.Coprime 2 3)
  rw [hr, ← KS_threeRank hpair]
  exact primeRank_mono 3 hKSH

/-- The natural-plus-dual contradiction along any map with the literal two-core kernel.
The module-recognition owner must still supply the displayed centralizer identity. -/
theorem false_of_naturalDual_centralizer
    (d : PlaneUniquenessPreceding hsource H ZS)
    (hKX : (pResidual 2 H).map H.subtype ≤ X)
    (hpair : Nonempty ((KS H T ZS ⧸ pCore 2 (KS H T ZS)) ≃*
      (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3))))
    (q : X →* D) (hker : q.ker = pCore 2 X)
    (s : MovedSection ρ L) (hn : n = 4 ∨ n = 5) (hL : L = ⊤)
    (hnat : IsNaturalPlusDual (s.space.toRepresentation.comp L.subtype) n)
    (P : Sylow 2 D)
    (hcentralizer : ((M1 X ZS).subgroupOf X).map q =
      subspaceKernel ρ (fixedSpace ρ P) L) : False := by
  let A := (((pResidual 2 H).map H.subtype).subgroupOf X).map q
  have hr : 2 ≤ primeRank 3 A := by
    rw [ResidualCentralizerRank.primeRank_map_of_twoGroup_kernel (by decide) q
      (by rw [hker]; exact pCore_isPGroup),
      primeRank_equiv 3 (subgroupOfEquivOfLe hKX)]
    exact K_threeRank_ge_two d hpair
  apply naturalDual_not_le_fixedCentralizer s hn hL hnat P A hr
  rw [← hcentralizer]
  exact map_mono (fun _ hx => ⟨hKX hx, d.residual_centralizes hx⟩)

/-- The same exclusion on the actual moved plane module. The action law
uses the original quotient map and ambient conjugation; the only geometric
input is the Sylow-fixed centralizer alignment. It does not require the
Sylow-fixed space itself to lie in ZS, which may have a fixed attachment. -/
theorem false_of_naturalDual_on_U
    (d : PlaneUniquenessPreceding hsource H ZS)
    (hKX : (pResidual 2 H).map H.subtype ≤ X)
    (hpair : Nonempty ((KS H T ZS ⧸ pCore 2 (KS H T ZS)) ≃*
      (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3))))
    [IsElementaryAbelian 2 (U X ZS)]
    (σ : Representation (ZMod 2) (X ⧸ pCore 2 X) (Additive (U X ZS)))
    (hσ : ∀ (x : X) (u : Additive (U X ZS)),
      ((σ (QuotientGroup.mk' (pCore 2 X) x) u).toMul : G) =
        (x : G) * (u.toMul : G) * (x : G)⁻¹)
    (hn : n = 4 ∨ n = 5) (hnat : IsNaturalPlusDual σ n)
    (P : Sylow 2 (X ⧸ pCore 2 X))
    (hfixed : M1 X ZS ≤ centralizer
      {g : G | ∃ u : Additive (U X ZS), u ∈ fixedSpace σ P ∧ (u.toMul : G) = g}) :
    False := by
  let q := QuotientGroup.mk' (pCore 2 X)
  let A := (((pResidual 2 H).map H.subtype).subgroupOf X).map q
  have hr : 2 ≤ primeRank 3 A := by
    have hqker : q.ker = pCore 2 X := by
      dsimp [q]
      exact QuotientGroup.ker_mk' _
    rw [ResidualCentralizerRank.primeRank_map_of_twoGroup_kernel (by decide) q
      (by rw [hqker]; exact pCore_isPGroup),
      primeRank_equiv 3 (subgroupOfEquivOfLe hKX)]
    exact K_threeRank_ge_two d hpair
  have hA : A ≤ subspaceKernel σ (fixedSpace σ P) ⊤ := by
    rintro a ⟨x,hx,rfl⟩
    refine ⟨mem_top _,?_⟩
    intro u hu
    apply Additive.toMul.injective
    apply Subtype.ext
    change ((σ (q x) u).toMul : G) = (u.toMul : G)
    rw [hσ]
    have hcomm := hfixed ⟨hKX hx, d.residual_centralizes hx⟩ _ ⟨u,hu,rfl⟩
    have hcomm' : (u.toMul : G) * (x : G) = (x : G) * (u.toMul : G) := by
      simpa only [Subgroup.coe_subtype] using hcomm
    calc
      (x : G) * (u.toMul : G) * (x : G)⁻¹ =
          (u.toMul : G) * (x : G) * (x : G)⁻¹ := by rw [hcomm']
      _ = (u.toMul : G) := by simp
  have hb := (primeRank_mono 3 hA).trans
    (naturalDual_fixedCentralizer_threeRank hn hnat P)
  omega

end CFSG.Quasithin.Chapter15.Section02.TerminalLinear
