module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.CentralHall.Nonlinear.Modules.SeedAnalysis.NaturalCentralizer
public import CFSG.KnownSimple.PrimeToFifteen

/-!
# The remaining odd-degree natural centralizer branch

The quotient-action kernel inherits the full known-simple K-group hypothesis.
The component extraction from D.3.9 makes that kernel nonsolvable. Its order
is prime to three, so the full catalogue forces an actual factor five. When
the SL₂ field degree is even, five also divides the original component order;
the source orbit-index restriction then excludes this kernel altogether.

The final theorem retains the actual starred actor and the ordinary component
it moves in the kernel. Its field degree is odd and this component has order
divisible by five and prime to three. Separation and exclusion of this last
nonsolvable component branch remain with qt-d-10-nona5-central-hall-orders;
neither SeedAnalysisAt nor the unconditional Hall theorem is asserted.
Source: Aschbacher--Smith D.3.9(2), D.3.21(3) and10.1.3,
printed pp.200--201,205--206 and742.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.Chapter10.CentralHall.Nonlinear.Modules
open Chapter3.Section02 Representation.BinaryOffender
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
local instance : IsElementaryAbelian 2 (⁅D.fullModule,L⁆ : Subgroup G) :=
  source_original_full_moved_elementary D

private theorem five_dvd_card_sl2_of_even (n : ℕ) (hn : 0 < n) (heven : Even n) :
    5 ∣ Nat.card SL(2,GaloisField 2 n) := by
  rw [Atlas.card_sl_two, GaloisField.card 2 n (by omega)]
  apply dvd_mul_of_dvd_right
  obtain ⟨k,rfl⟩ := heven
  have hpow : (2 ^ (k + k)) ^ 2 = 16 ^ k := by
    rw [←pow_mul, show (k + k) * 2 = 4 * k by omega, pow_mul]
    rfl
  rw [hpow]
  exact dvd_trans (by decide : 5 ∣ 16 - 1)
    (by simpa using Nat.sub_dvd_pow_sub_pow 16 1 k)

local instance (n : ℕ) : Algebra (ZMod 2) (GaloisField 2 n) := ZMod.algebra _ 2

/-- An even-degree natural constituent is impossible in the separated original
Hall context, including actors nonfaithful on the component quotient. -/
theorem no_even_natural_constituent
    {H : Subgroup G} {B : Subgroup H} (c : Context D H B)
    {t : G} (ht : t ∈ (T : Subgroup G)) (htn : t ∉ normalizer (L : Set G))
    (hsep : D.seed ≤ centralizer (L.map (MulAut.conj t).toMonoidHom : Set G) ∨
      D.seed ≤ centralizer (L : Set G))
    (n : ℕ) (hn : 1 < n) (heven : Even n)
    (e : (L ⧸ pCore 2 L) ≃* SL(2,GaloisField 2 n))
    (I : Subrepresentation ((movedStabilizerAction D).comp (movedStabilizerComponent D).subtype))
    (hI : I.toRepresentation.IsIrreducible)
    (E : (Fin 2 → GaloisField 2 n) ≃ₗ[ZMod 2] I.toSubmodule)
    (hE : ∀ (l : movedStabilizerComponent D) v,
      E (naturalComponent e ⟨l.val.val,l.property⟩ v) = I.toRepresentation l (E v)) : False := by
  let α := movedNaturalImageQuotientAction D e I E hE
  have h3 : Nat.Coprime 3 (Nat.card α.ker) := by
    apply naturalImageQuotientAction_ker_card_coprime D c ht htn hsep e I E hE 3 (by decide)
    rw [Nat.card_congr e.toEquiv]
    exact Theory.SpecificGroups.three_dvd_card_sl_two _
  have h5 : Nat.Coprime 5 (Nat.card α.ker) := by
    let : Fact (Nat.Prime 5) := ⟨by decide⟩
    apply naturalImageQuotientAction_ker_card_coprime D c ht htn hsep e I E hE 5 (by decide)
    rw [Nat.card_congr e.toEquiv]
    exact five_dvd_card_sl2_of_even n (by omega) heven
  exact naturalImageQuotientAction_kernel_not_solvable D c ht htn hsep n hn e I hI E hE
    (KnownSimple.isSolvable_of_coprime_three_five _
      ((movedStabilizerImage_isKGroup D).subgroup α.ker) h3 h5)

/-- The outstanding natural branch has odd field degree and a genuine
five-divisible component orbit moved by the same starred actor in its kernel. -/
theorem source_natural_starred_actor_five_component
    {H : Subgroup G} {B : Subgroup H} (c : Context D H B)
    {t : G} (ht : t ∈ (T : Subgroup G)) (htn : t ∉ normalizer (L : Set G))
    (hsep : D.seed ≤ centralizer (L.map (MulAut.conj t).toMonoidHom : Set G) ∨
      D.seed ≤ centralizer (L : Set G))
    (n : ℕ) (hn : 1 < n)
    (e : (L ⧸ pCore 2 L) ≃* SL(2,GaloisField 2 n))
    (I : Subrepresentation ((movedStabilizerAction D).comp (movedStabilizerComponent D).subtype))
    (hI : I.toRepresentation.IsIrreducible)
    (E : (Fin 2 → GaloisField 2 n) ≃ₗ[ZMod 2] I.toSubmodule)
    (hE : ∀ (l : movedStabilizerComponent D) v,
      E (naturalComponent e ⟨l.val.val,l.property⟩ v) = I.toRepresentation l (E v)) :
    Odd n ∧ ∃ A : Subgroup (actionImage (movedStabilizerAction D)),
      A ∈ ChapterD.QhatStar (imageRepresentation (movedStabilizerAction D)) ∧
      1 < rank A ∧ ∃ J : Subgroup (actionImage (movedStabilizerAction D)),
        IsComponent _ J ∧ J ≤ (movedNaturalImageQuotientAction D e I E hE).ker ∧
        Nat.Coprime 3 (Nat.card J) ∧ 5 ∣ Nat.card J ∧
        ⁅componentOrbit J A,A ⊓ (movedNaturalImageQuotientAction D e I E hE).ker⁆ =
          componentOrbit J A ∧ componentOrbit J A ≠ ⊥ := by
  have ho : Odd n := Nat.not_even_iff_odd.mp (fun he =>
    no_even_natural_constituent D c ht htn hsep n hn he e I hI E hE)
  obtain ⟨A,hA,hr,J,hJ,hJK,hm,hJn⟩ :=
    source_natural_starred_actor_component D c ht htn hsep n hn e I hI E hE
  have h3 : Nat.Coprime 3 (Nat.card J) := by
    apply (naturalImageQuotientAction_ker_card_coprime D c ht htn hsep e I E hE
      3 (by decide) ?_).of_dvd_right (card_dvd_of_le hJK)
    rw [Nat.card_congr e.toEquiv]
    exact Theory.SpecificGroups.three_dvd_card_sl_two _
  have h5 : 5 ∣ Nat.card J := by
    by_contra hd
    have hc := Nat.prime_five.coprime_iff_not_dvd.mpr hd
    exact hJ.isCComponent.not_isSolvable (KnownSimple.isSolvable_of_coprime_three_five _
      ((movedStabilizerImage_isKGroup D).subgroup J) h3 hc)
  exact ⟨ho,A,hA,hr,J,hJ,hJK,h3,h5,hm,hJn⟩

end CFSG.Quasithin.Chapter10.CentralHall.Nonlinear.Modules
