module
public import CFSG.Quasithin.ChapterA.Section04.Intersection
public import Theory.GroupTheory.PResidual.NormalizerImage
public import CFSG.Quasithin.Chapter15.Section04.Centralizer.Defs

/-!
# The literal iterated cores in 15.4.3

Both iterated cores are inverse images in M/O₂(M), embedded back in G.
The solvable case identifies the Fitting preimage with the generalized
Fitting preimage used in A.4.4. Containment in the iterated p-core gives
containment of the two-cores by disjointness of odd and two-group images;
it does not imply normality of the original subgroup.

Source: Aschbacher–Smith, combined manuscript, printed p.1157,
15.4.3(2) and the subsequent application of A.4.4.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section04.MaximalPrimeSource
variable {G : Type*} [Group G]

@[expose] def twoPrimePreimage (p : ℕ) (M : Subgroup G) : Subgroup G :=
  ((pCore p (M ⧸ pCore 2 M)).comap (QuotientGroup.mk' (pCore 2 M))).map M.subtype

@[expose] def twoFittingPreimage (M : Subgroup G) : Subgroup G :=
  ((fittingSubgroup (M ⧸ pCore 2 M)).comap (QuotientGroup.mk' (pCore 2 M))).map M.subtype

@[expose] def quotientImage (M A : Subgroup G) : Subgroup (M ⧸ pCore 2 M) :=
  (A.subgroupOf M).map (QuotientGroup.mk' (pCore 2 M))

private theorem generalizedFitting_eq_fitting_of_solvable
    (A : Type*) [Group A] [Group.IsSolvable A] :
    generalizedFitting A = fittingSubgroup A := by
  have hl : componentLayer A = ⊥ := by
    apply le_bot_iff.mp
    apply sSup_le
    rintro K ⟨_, hK⟩
    let : IsQuasisimple K := hK
    by_contra hn
    have hne : K ≠ ⊥ := fun he => hn he.le
    let : Nontrivial K := (Subgroup.nontrivial_iff_ne_bot K).mpr hne
    exact Group.IsPerfect.not_isSolvable K inferInstance
  simp only [generalizedFitting, hl, sup_bot_eq]

theorem twoFittingPreimage_eq_generalized (M : Subgroup G) (hs : Group.IsSolvable M) :
    twoFittingPreimage M = ChapterA.Section04.twoGeneralizedFittingPreimage M := by
  let : Group.IsSolvable M := hs
  simp only [twoFittingPreimage, ChapterA.Section04.twoGeneralizedFittingPreimage,
    generalizedFitting_eq_fitting_of_solvable]

theorem quotientImage_twoPrimePreimage (p : ℕ) (M : Subgroup G) :
    quotientImage M (twoPrimePreimage p M) = pCore p (M ⧸ pCore 2 M) := by
  unfold quotientImage twoPrimePreimage
  rw [subgroupOf, comap_map_eq_self_of_injective M.subtype_injective]
  exact map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _) _

theorem quotientImage_twoFittingPreimage (M : Subgroup G) :
    quotientImage M (twoFittingPreimage M) = fittingSubgroup (M ⧸ pCore 2 M) := by
  unfold quotientImage twoFittingPreimage
  rw [subgroupOf, comap_map_eq_self_of_injective M.subtype_injective]
  exact map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _) _

theorem le_twoPrimePreimage_iff (p : ℕ) {M X : Subgroup G} (hXM : X ≤ M) :
    X ≤ twoPrimePreimage p M ↔ quotientImage M X ≤ pCore p (M ⧸ pCore 2 M) := by
  rw [quotientImage, map_le_iff_le_comap]
  constructor
  · intro h
    exact (comap_mono h).trans_eq (comap_map_eq_self_of_injective M.subtype_injective _)
  · intro h
    have hh := map_mono (f := M.subtype) h
    rwa [map_subgroupOf_eq_of_le hXM] at hh

theorem twoCore_le_twoPrimePreimage (p : ℕ) (M : Subgroup G) :
    M.pCoreIn 2 ≤ twoPrimePreimage p M := by
  apply map_mono
  intro x hx
  change QuotientGroup.mk' (pCore 2 M) x ∈ pCore p (M ⧸ pCore 2 M)
  have he : QuotientGroup.mk' (pCore 2 M) x = 1 := (QuotientGroup.eq_one_iff x).mpr hx
  rw [he]
  exact one_mem _

theorem twoPrimePreimage_le_twoFittingPreimage [Finite G] (p : ℕ) [Fact p.Prime] (M : Subgroup G) :
    twoPrimePreimage p M ≤ twoFittingPreimage M :=
  map_mono (comap_mono (pCore_le_fitting _ p))

theorem twoCore_le_of_le_twoPrimePreimage [Finite G] {p : ℕ} [Fact p.Prime] (hp : Odd p)
    {M X : Subgroup G} (hX : X ≤ twoPrimePreimage p M) : X.pCoreIn 2 ≤ M.pCoreIn 2 := by
  have hXM : X ≤ M := hX.trans (map_subtype_le _)
  have hQX : X.pCoreIn 2 ≤ M := (pCoreIn_le 2 X).trans hXM
  let q := QuotientGroup.mk' (pCore 2 M)
  have hle : quotientImage M (X.pCoreIn 2) ≤ pCore p (M ⧸ pCore 2 M) :=
    (map_mono (comap_mono (pCoreIn_le 2 X))).trans ((le_twoPrimePreimage_iff p hXM).mp hX)
  have htwo : IsPGroup 2 (quotientImage M (X.pCoreIn 2)) :=
    ((isPGroup_pCoreIn 2 X).comap_subtype).map q
  have hdis := IsPGroup.disjoint_of_coprime htwo (pCore_isPGroup (p := p) (G := M ⧸ pCore 2 M))
    hp.coprime_two_left
  have hz : quotientImage M (X.pCoreIn 2) = ⊥ := bot_unique
    ((le_inf le_rfl hle).trans hdis.le_bot)
  have hk : (X.pCoreIn 2).subgroupOf M ≤ pCore 2 M := by
    simpa only [quotientImage, Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] using hz
  have hh := map_mono (f := M.subtype) hk
  rwa [map_subgroupOf_eq_of_le hQX] at hh
end CFSG.Quasithin.Chapter15.Section04.MaximalPrimeSource
