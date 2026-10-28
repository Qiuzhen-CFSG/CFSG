module

public import CFSG.Quasithin.Chapter15.Section02.SourceChosenGeometry.Residuals.EqualityRow.NonlinearGeometry
public import CFSG.Quasithin.Chapter15.Section02.SourceChosenGeometry.Residuals.EscapingReductions
public import CFSG.Quasithin.Chapter15.Section02.SourcePlaneUniqueness.CharacteristicTwo.ComponentModels.Catalogue.G2
public import CFSG.Quasithin.Chapter15.Section02.SourcePlaneUniqueness.CharacteristicTwo.ComponentModels.Catalogue.Symplectic

/-!
# Original nonbinary G₂ and symplectic component contradictions

For each literal normalized component, the source star marking identifies
its entire quotient by the two-core.  The original solvable H meets that
component in a subgroup containing a full Sylow two-subgroup.  The native
Sylow-normalizer calculation places its image in the marked M intersection,
then the two-kernel lifts that placement.  The actual rank-two residual
forces a cubic in this intersection, contradicting K ∩ M = O₂(K).

Both original component models are excluded directly from `ResidualInput`;
no partner-residual identity or `PlaneUniquenessPreceding` is assumed.
Source: Aschbacher--Smith C.2.7 and proof of 15.2.23, printed pp.145--147
and 1116--1117, refs/quasithin.pdf.
-/

public section
open Subgroup Theory.GroupTheory PerfectCentralCovering
open scoped MatrixGroups Pointwise
namespace CFSG.Quasithin.Chapter15.Section02.ChosenGeometry
open ComponentCatalogue PlaneUniquenessPreceding ChapterC.C27Source
open Chapter1.RadicalExclusions.ModelReduction FullSieve FullSieve.SourceInterface
open Theory.SpecificGroups.SymplecticFour
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc V H B I X : Subgroup G}
variable {hsource : ChosenSmallSource T M Mc V}
variable {F : Type*} [Field F] [Finite F] [CharP F 2]

/-- The actual nonbinary G₂ component cannot occur on the original plane. -/
theorem ResidualInput.normalized_component_g2_false
    (r : ResidualInput hsource H B)
    (hI : PlaneEscapes Mc ⁅V,B⁆ I)
    (hcore : (M ⊓ I).pCoreIn 2 = M.pCoreIn 2)
    (selection : Normalized H M I X)
    {n : ℕ} (hn : 1 < n) (hF : Nat.card F = 2 ^ n)
    (e : starImage X ((M ⊓ I).pCoreIn 2) X ≃* Atlas.G2.Model F) : False := by
  let h := normalized_component_input (hsource := hsource) hI hcore selection
  have hlarge : 3 < Nat.card F := by
    have hpow := Nat.pow_le_pow_right (by decide : 0 < 2) (show 2 ≤ n by omega)
    omega
  let a := g2CoreEquiv h hn hF e
  let f := a.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 X))
  have hf : Function.Surjective f := a.surjective.comp (QuotientGroup.mk'_surjective _)
  have hker : f.ker = pCore 2 X := by
    ext x
    change a (QuotientGroup.mk' (pCore 2 X) x) = 1 ↔ _
    rw [a.map_eq_one_iff]
    exact QuotientGroup.eq_one_iff x
  obtain ⟨P,hP⟩ := r.component_sylow_in_plane hI selection.component
  let Q := P.mapSurjective hf
  let J := H.subgroupOf X
  let N := (M ⊓ I).subgroupOf X
  have hPN : (P : Subgroup X) ≤ N := by
    intro x hx
    exact ⟨hsource.maximal.1.2 ((hP hx).1),selection.component.1 x.property⟩
  have hPJ : (P : Subgroup X) ≤ J := by
    intro x hx
    exact r.outside.1.1.2 (hP hx).1
  let : Group.IsSolvable H := r.local_solvable
  let j : J →* H := {
    toFun := fun x => ⟨x.val.val,x.property⟩
    map_one' := rfl
    map_mul' := fun _ _ => rfl }
  have hj : Function.Injective j := by
    intro x y hh
    exact Subtype.ext (Subtype.ext (congrArg (fun z : H => (z : G)) hh))
  let : Group.IsSolvable J := Group.isSolvable_of_isSolvable_injective hj
  have hs : Group.IsSolvable (J.map f) :=
    Group.isSolvable_of_surjective (f.subgroupMap_surjective J)
  have hJN : J.map f ≤ N.map f :=
    (Atlas.G2.solvable_sylow_overgroup_normalizes (by omega) Q (J.map f)
      (map_mono hPJ) hs).trans
      (g2_star_sylow_normalizer_le h hn hF e Q (map_mono hPN))
  have hkerN : f.ker ≤ N := by
    rw [hker]
    exact ((pCore_isPGroup (p := 2) (G := X)).le_sylow_of_normal P).trans hPN
  have hJN' : J ≤ N := by
    have hh := map_le_iff_le_comap.mp hJN
    rwa [comap_map_eq_self hkerN] at hh
  let K := residual H
  have hKM : K ⊓ X ≤ K ⊓ M := by
    intro x hx
    have hxH : x ∈ H := (map_subtype_le (pResidual 2 H)) hx.1
    exact ⟨hx.1,(hJN' (show (⟨x,hx.2⟩ : X) ∈ J from hxH)).1⟩
  have ht : IsPGroup 2 (K ⊓ X : Subgroup G) := by
    apply (isPGroup_pCoreIn 2 K).to_le
    rwa [←r.residual_intersection_eq_core]
  have hr : 2 ≤ primeRank 3 (Atlas.G2.Model F) :=
    Theory.SpecificGroups.Classical.BinaryDerivedCubicRank.g2.trans
      (Theory.GroupTheory.primeRank_le_of_injective 3 (commutator (Atlas.G2.Model F)).subtype
        (commutator (Atlas.G2.Model F)).subtype_injective)
  have hthree : 3 ∣ Nat.card X := by
    have hd : 3 ∣ Nat.card (Atlas.G2.Model F) := by
      by_contra hh
      have hz := PrimeRank.eq_zero_iff_not_dvd_card.mpr hh
      omega
    exact hd.trans (card_dvd_of_surjective f hf)
  have hd := r.residual_intersection_three_dvd hI selection.component.1
    selection.residual_normalizes hthree
  obtain ⟨k,hk⟩ := ht.exists_card_eq
  rw [hk] at hd
  exact (by norm_num : ¬ (3 : ℕ) ∣ 2) (Nat.prime_three.dvd_of_dvd_pow hd)

/-- The actual nonbinary symplectic component cannot occur on the original plane. -/
theorem ResidualInput.normalized_component_symplectic_false
    (r : ResidualInput hsource H B)
    (hI : PlaneEscapes Mc ⁅V,B⁆ I)
    (hcore : (M ⊓ I).pCoreIn 2 = M.pCoreIn 2)
    (selection : Normalized H M I X)
    {n : ℕ} (hn : 1 < n) (hF : Nat.card F = 2 ^ n)
    (e : starImage X ((M ⊓ I).pCoreIn 2) X ≃* Sp F) : False := by
  let h := normalized_component_input (hsource := hsource) hI hcore selection
  have hlarge : 3 < Nat.card F := by
    have hpow := Nat.pow_le_pow_right (by decide : 0 < 2) (show 2 ≤ n by omega)
    omega
  let a := symplecticCoreEquiv h hlarge e
  let f := a.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 X))
  have hf : Function.Surjective f := a.surjective.comp (QuotientGroup.mk'_surjective _)
  have hker : f.ker = pCore 2 X := by
    rw [MonoidHom.ker_comp_of_injective _ _ a.injective,QuotientGroup.ker_mk']
  obtain ⟨P,hP⟩ := r.component_sylow_in_plane hI selection.component
  let Q := P.mapSurjective hf
  let J := H.subgroupOf X
  let N := (M ⊓ I).subgroupOf X
  have hPN : (P : Subgroup X) ≤ N := by
    intro x hx
    exact ⟨hsource.maximal.1.2 ((hP hx).1),selection.component.1 x.property⟩
  have hPJ : (P : Subgroup X) ≤ J := by
    intro x hx
    exact r.outside.1.1.2 (hP hx).1
  let : Group.IsSolvable H := r.local_solvable
  let j : J →* H := {
    toFun := fun x => ⟨x.val.val,x.property⟩
    map_one' := rfl
    map_mul' := fun _ _ => rfl }
  have hj : Function.Injective j := by
    intro x y hh
    exact Subtype.ext (Subtype.ext (congrArg (fun z : H => (z : G)) hh))
  let : Group.IsSolvable J := Group.isSolvable_of_isSolvable_injective hj
  have hs : Group.IsSolvable (J.map f) :=
    Group.isSolvable_of_surjective (f.subgroupMap_surjective J)
  have hJN : J.map f ≤ N.map f :=
    (solvable_sylow_overgroup_normalizes (by omega) Q (J.map f) hs (map_mono hPJ)).trans
      (normalizer_le_marked_parabolic hF hn.le Q (N.map f) (map_mono hPN)
        (symplectic_core_parabolic h hlarge e))
  have hkerN : f.ker ≤ N := by
    rw [hker]
    exact ((pCore_isPGroup (p := 2) (G := X)).le_sylow_of_normal P).trans hPN
  have hJN' : J ≤ N := by
    have hh := map_le_iff_le_comap.mp hJN
    rwa [comap_map_eq_self hkerN] at hh
  let K := residual H
  have hKM : K ⊓ X ≤ K ⊓ M := by
    intro x hx
    have hxH : x ∈ H := (map_subtype_le (pResidual 2 H)) hx.1
    exact ⟨hx.1,(hJN' (show (⟨x,hx.2⟩ : X) ∈ J from hxH)).1⟩
  have ht : IsPGroup 2 (K ⊓ X : Subgroup G) := by
    apply (isPGroup_pCoreIn 2 K).to_le
    rwa [←r.residual_intersection_eq_core]
  have hr : 2 ≤ primeRank 3 (Sp F) :=
    Theory.SpecificGroups.Classical.BinaryDerivedCubicRank.symplectic.trans
      (Theory.GroupTheory.primeRank_le_of_injective 3 (commutator (Sp F)).subtype
        (commutator (Sp F)).subtype_injective)
  have hthree : 3 ∣ Nat.card X := by
    have hd : 3 ∣ Nat.card (Sp F) := by
      by_contra hh
      have hz := PrimeRank.eq_zero_iff_not_dvd_card.mpr hh
      omega
    exact hd.trans (card_dvd_of_surjective f hf)
  have hd := r.residual_intersection_three_dvd hI selection.component.1
    selection.residual_normalizes hthree
  obtain ⟨k,hk⟩ := ht.exists_card_eq
  rw [hk] at hd
  exact (by norm_num : ¬ (3 : ℕ) ∣ 2) (Nat.prime_three.dvd_of_dvd_pow hd)

end CFSG.Quasithin.Chapter15.Section02.ChosenGeometry
