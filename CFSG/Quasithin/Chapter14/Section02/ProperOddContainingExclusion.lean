module
public import CFSG.Quasithin.Chapter14.Section02.ProperQuasisimpleSource
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.PrimePSL2
public import Theory.SpecificGroups.PSL3Three.ProperSubgroups
public import Theory.AtlasPort.ExceptionalIsomorphisms.Support
public import Theory.GroupTheory.SolvableSylowOvergroups

/-!
# Early exclusion of the odd containing models

In the original proper completion, the local C-component K is proper in
its containing C-component L. For odd prime PSL₂, A.3.12 forces the prime
to be 3 or 5 modulo 8 with square 1 modulo 5. A Fermat or Mersenne prime
with the first property is 3 or 5, and neither has the second property.
For PSL₃(3), every proper subgroup is solvable, forcing K = L instead.

The theorem applies these two obstructions to the actual original full
Sylow subgroup and canonical residual. It rules out the complete model
disjunction in the odd constructor of 1.1.5 without any later rank input.
Source: Aschbacher--Smith 14.2.15, pp.985--986; A.3.12(8), pp.47--48;
1.1.5(3); GLS III, Theorem 6.5.3 for the PSL₃(3) proper subgroups.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter14.Section02
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]

private theorem fermatMersenne_odd {p : ℕ} (hp : IsFermatOrMersennePrime p) : Odd p := by
  apply hp.1.odd_of_ne_two
  rintro rfl
  rcases hp.2 with ⟨a, ha⟩ | ⟨a, ha⟩
  · have hlow : 2 ≤ 2 ^ (2 ^ a) := Nat.le_pow (by norm_num)
    omega
  · have hd : 2 ∣ 2 ^ a := dvd_pow_self _ (by rintro rfl; norm_num at ha)
    omega

private theorem not_exceptional_fermatMersenne {p : ℕ}
    (hp : IsFermatOrMersennePrime p) : ¬ Chapter1.Section02.A312ExceptionalPrime p := by
  rintro ⟨_,_,h5,h8⟩
  rcases hp.2 with ⟨k,rfl⟩ | ⟨k,hk⟩
  · by_cases hk : k < 2
    · interval_cases k <;> norm_num at h5
    · have hl : 3 ≤ 2 ^ k := by
        have h := Nat.pow_le_pow_right (by decide : 1 ≤ 2) (show 2 ≤ k by omega)
        norm_num at h
        omega
      have hd : 8 ∣ 2 ^ (2 ^ k) := Nat.pow_dvd_pow 2 hl
      have hm := Nat.mod_eq_zero_of_dvd hd
      omega
  · by_cases hk3 : k < 3
    · interval_cases k
      · norm_num at hk
        have := hp.1.two_le
        omega
      · norm_num at hk
        have := hp.1.two_le
        omega
      · have hp3 : p = 3 := by norm_num at hk; omega
        norm_num [hp3] at h5
    · have hd : 8 ∣ 2 ^ k := Nat.pow_dvd_pow 2 (show 3 ≤ k by omega)
      have hm := Nat.mod_eq_zero_of_dvd hd
      omega

private theorem psl3_three_solvable_sylow_overgroups
    {A : Type*} [Group A] [Finite A] (h : ClassicalGroup.IsPSL A 3 3) :
    SolvableSylowOvergroups A := by
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := h
  let := Fintype.ofFinite F
  let f : F ≃+* ZMod 3 := (ZMod.ringEquivOfPrime F Nat.prime_three
    (by simpa only [Nat.card_eq_fintype_card] using hF)).symm
  apply SolvableSylowOvergroups.of_equiv (e.trans (Atlas.fieldEquivPSL 3 f))
  intro _ D _ hD
  exact Matrix.PSL3Three.isSolvable_of_ne_top D hD

/-- Original 14.2.15 excludes the complete odd-model disjunction of
1.1.5(3), without a paired-residual or later maximal-local premise. -/
theorem source_proper_completion_odd_model_exclusion
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (H : Subgroup G) (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (K S : Subgroup G) (hST : S ≤ (T : Subgroup G))
    (hi : S.relIndex (T : Subgroup G) = 2)
    (hN : normalizer (omegaOneCenterAmbient S : Set G) ≤ Mc)
    (hplacement : ∀ P : Sylow 2 Mc, S ≤ (P : Subgroup Mc).map Mc.subtype →
      maximalTwoLocalOvergroups (K ⊔ (P : Subgroup Mc).map Mc.subtype) = {Mc})
    (hgen : K ⊔ (T : Subgroup G) = H)
    (hK : K ∈ Chapter1.L G S) (hSN : S ≤ normalizer (K : Set G))
    (hcore : pCore 2 (K ⊔ sourceResidual M Mc ⊔ S : Subgroup G) ≠ ⊥) :
    let X := K ⊔ sourceResidual M Mc ⊔ S
    let L := (solvableResidual X).map X.subtype
    ¬ (ClassicalGroup.IsPSL L 3 3 ∨
      ∃ p, IsFermatOrMersennePrime p ∧ ClassicalGroup.IsPSL L 2 p) := by
  let X := K ⊔ sourceResidual M Mc ⊔ S
  let L := (solvableResidual X).map X.subtype
  change ¬ (ClassicalGroup.IsPSL L 3 3 ∨
      ∃ p, IsFermatOrMersennePrime p ∧ ClassicalGroup.IsPSL L 2 p)
  intro hmodel
  have hcorea : X.pCoreIn 2 ≠ ⊥ := fun hh =>
    hcore (((pCore 2 X).map_eq_bot_iff_of_injective X.subtype_injective).mp hh)
  have hs := source_proper_completion_sylow hG T hempty hM hu hmany hcard e H hH
    K S hST hi hN hplacement hcore
  obtain ⟨hL,hKL,_⟩ := source_proper_completion_component hG T hempty hM hu hmany
    hcard e K S hST hK hSN hcorea hs
  have hKC : K ≤ centralizer (centralInvolutions T : Set G) :=
    (le_sup_left.trans_eq hgen).trans
      (source_lemma_14_2_3 hG T hempty hM hu hmany hcard e H hH.1.1 hH.1.2).2
  have hne : K ≠ L := fun he =>
    source_proper_completion_component_noncentral hG T hempty hM hu hmany hcard e
      H hH K S hST hgen hK hSN hcorea hs (he.ge.trans hKC)
  have hKX : K ≤ X := le_sup_left.trans le_sup_left
  have hSX : S ≤ X := le_sup_right
  obtain ⟨P,hP⟩ := hs
  have hPS : (P : Subgroup X) = S.subgroupOf X := by
    apply map_injective X.subtype_injective
    rw [hP,map_subgroupOf_eq_of_le hSX]
  have hKP : K.subgroupOf X ∈ Chapter1.L X P := by
    rw [hPS]
    exact (Chapter1.mem_LIn_iff_subgroupOf hSX hKX).mp ⟨hKX,hK⟩
  have hneX : K.subgroupOf X ≠ L.subgroupOf X := by
    intro he
    apply hne
    have hm := congrArg (Subgroup.map X.subtype) he
    rwa [map_subgroupOf_eq_of_le hKX,map_subgroupOf_eq_of_le hL.1] at hm
  rcases hmodel with hm | ⟨p,hp,hm⟩
  · apply hneX
    exact ChapterA.Section03.SourceEmbeddings.eq_of_solvable_sylow_overgroups
      P hKP.1 hL.2 (comap_mono hKL)
      (psl3_three_solvable_sylow_overgroups (hm.of_mulEquiv (subgroupOfEquivOfLe hL.1)))
  · have he := ChapterA.Section03.SourceEmbeddings.proper_primePSL2_models
      P hKP.1 hL.2 (comap_mono hKL) hneX hp.1 (fermatMersenne_odd hp)
      (hm.of_mulEquiv (subgroupOfEquivOfLe hL.1))
    exact not_exceptional_fermatMersenne hp he.1

end CFSG.Quasithin.Chapter14.Section02
