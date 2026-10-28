module
public import CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.Centralizers.Pure.Sylows.Four.Swapped.Positive
public import Theory.SpecificGroups.PSL2.CubicNormalizerCongruence

/-!
# Cubic normalizers in the remaining original swapped quotient

When O₂(X) lies in O₂(K₀), the image of the original X in K₀/O₂(K₀)
is exactly its cubic complement image. A nontrivial coordinate projection
is cyclic of order three and normalized by the full Klein-four Sylow.
The intrinsic torus-normalizer calculation forces p = 11 or 13 modulo 24.
The same original complement satisfies [O₂(K₀),A] = O₂(X).

These results use the actual swapped input, component orbit and quotient
maps. Their pure-point application is in `CoreAction`, with the original
MS fixed-subgroup premise retained for `qt-rank-two-ms93` and final owner
`qt-d-double-natural-centralizers`. Exclusion of the remaining noncentral
case and the Sylow/fusion/closure assembly remain with this task.
The coordinate argument adapts BinaryThreeAction/OddSmallCongruence.
Source: Aschbacher--Smith 12.1.4, printed pp.790--791; compare the intrinsic
rank-one normalizer calculation in 10.2.5, printed p.748.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.PureFourXi
open Chapter1 Chapter1.XiEmbedding InvariantThree
private theorem small_pair_cubic_congruence
    {Q B : Type*} [Group Q] [Finite Q] [Group B] [Finite B]
    {p : ℕ} (hp : p.Prime) (ho : Odd p)
    (hm : ClassicalGroup.IsPSL Q 2 p) (hmod : p % 8 = 3 ∨ p % 8 = 5)
    (e : B ≃* Q × Q) (S : Sylow 2 B) (A : Subgroup B)
    [IsElementaryAbelian 3 A] (hA : A ≠ ⊥)
    (hr : primeRank 3 (Q × Q) ≤ 2)
    (hn : (S : Subgroup B) ≤ normalizer (A : Set B)) :
    p % 24 = 11 ∨ p % 24 = 13 := by
  let : Fact p.Prime := ⟨hp⟩
  let A' := A.map e.toMonoidHom
  let S' := S.mapSurjective (f := e.toMonoidHom) e.surjective
  have hA' : A' ≠ ⊥ := by
    intro hh
    exact hA ((map_eq_bot_iff_of_injective A e.injective).mp hh)
  obtain ⟨f,hf,hfA⟩ : ∃ f : (Q × Q) →* Q, Function.Surjective f ∧ A'.map f ≠ ⊥ := by
    by_cases hfst : A'.map (MonoidHom.fst Q Q) = ⊥
    · refine ⟨MonoidHom.snd Q Q,fun x => ⟨(1,x),rfl⟩,?_⟩
      intro hsnd
      apply hA'
      apply bot_unique
      intro x hx
      exact Prod.ext (mem_bot.mp (hfst ▸ mem_map_of_mem (MonoidHom.fst Q Q) hx))
        (mem_bot.mp (hsnd ▸ mem_map_of_mem (MonoidHom.snd Q Q) hx))
    · exact ⟨MonoidHom.fst Q Q,fun x => ⟨(x,1),rfl⟩,hfst⟩
  let C := A'.map f
  let V := S'.mapSurjective hf
  let : IsElementaryAbelian 3 A' := IsElementaryAbelian.map e.toMonoidHom
  let : IsElementaryAbelian 3 C := IsElementaryAbelian.map f
  let : IsCyclic C := SwappedFactorsProof.cyclic_pSubgroup_of_product_rank
    (by decide : Odd 3) hr C (IsElementaryAbelian.isPGroup 3 C)
  let : Nontrivial C := (nontrivial_iff_ne_bot C).mpr hfA
  have hC : Nat.card C = 3 := by
    rw [← IsCyclic.exponent_eq_card,IsElementaryAbelian.exponent_eq_prime (p := 3)]
  have hVC : (V : Subgroup Q) ≤ normalizer (C : Set Q) :=
    (map_mono ((map_mono hn).trans (le_normalizer_map e.toMonoidHom))).trans
      (le_normalizer_map f)
  obtain ⟨F,_,_,hF,⟨eF⟩⟩ := hm
  let : Fintype F := Fintype.ofFinite F
  let c : F ≃+* ZMod p := FiniteField.ringEquivOfCardEq (by
    simpa only [← Nat.card_eq_fintype_card,Nat.card_zmod] using hF)
  let j := eF.trans (Atlas.fieldEquivPSL 2 c)
  let W := V.mapSurjective (f := j.toMonoidHom) j.surjective
  let C' := C.map j.toMonoidHom
  have hodd : GorensteinWalter.IsOddPrimePower (Nat.card (ZMod p)) :=
    ⟨p,1,hp,ho,by decide,by simp⟩
  have h8 : ¬ 8 ∣ Nat.card (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (ZMod p)) :=
    Theory.PSL2.not_eight_dvd_card_of_small_mod_eight (by simpa using ho) (by simpa using hmod)
  let : IsKleinFour W := Theory.PSL2.small_sylow_kleinFour hodd h8 W
  apply Theory.PSL2.prime_mod24_of_four_normalizes_cubic ho hmod
    (W : Subgroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (ZMod p))) C'
  · rw [card_map_of_injective j.injective]
    exact hC
  · exact (map_mono hVC).trans (le_normalizer_map j.toMonoidHom)

variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
/-- Radical containment identifies the residual image with the same cubic complement. -/
theorem collapsed_quotient_residual_eq_complement (T : Sylow 2 G) {X A H I : Subgroup G}
    (hs : SwappedSylowInput KnownSimple.IsKnownSimple 3 (T : Subgroup G) X A H I)
    (hc : X.pCoreIn 2 ≤ (componentOrbit I (T : Subgroup G)).pCoreIn 2) :
    quotientImage (componentOrbit I (T : Subgroup G)) X =
      quotientImage (componentOrbit I (T : Subgroup G)) A := by
  let K := componentOrbit I (T : Subgroup G)
  have hKH : K ≤ H := SwappedSylow.orbit_le_overgroup hs.toSwappedInput
  have hHK : H ≤ normalizer (K : Set G) :=
    (normal_subgroupOf_iff_le_normalizer hKH).mp hs.orbit_normal
  have hXK := hs.toLocalInput.le_of_complement_le hs.complement_le_orbit hHK
  have hCK : X.pCoreIn 2 ≤ K := (pCoreIn_le 2 X).trans hXK
  have hz : quotientImage K (X.pCoreIn 2) = ⊥ := by
    apply (Subgroup.map_eq_bot_iff _).mpr
    rw [QuotientGroup.ker_mk']
    intro x hx
    obtain ⟨y,hy,he⟩ := hc hx
    exact (Subtype.ext he : y=x) ▸ hy
  have he := congrArg (fun B : Subgroup G => B.subgroupOf K) hs.complement
  rw [subgroupOf_sup hCK hs.complement_le_orbit] at he
  have he' := congrArg (Subgroup.map (QuotientGroup.mk' (pCore 2 K))) he
  rw [Subgroup.map_sup] at he'
  change quotientImage K (X.pCoreIn 2) ⊔ quotientImage K A = quotientImage K X at he'
  rw [hz,bot_sup_eq] at he'
  exact he'.symm

/-- The full quotient Sylow normalizes the cubic image only in these two residues. -/
theorem collapsed_small_prime_mod24 (T : Sylow 2 G) {X A H I : Subgroup G}
    (hs : SwappedSylowInput KnownSimple.IsKnownSimple 3 (T : Subgroup G) X A H I)
    {p : ℕ} (hp : p.Prime) (ho : Odd p)
    (hm : ClassicalGroup.IsPSL (XiQuotient I) 2 p)
    (hmod : p % 8 = 3 ∨ p % 8 = 5)
    (hc : X.pCoreIn 2 ≤ (componentOrbit I (T : Subgroup G)).pCoreIn 2) :
    p % 24 = 11 ∨ p % 24 = 13 := by
  let K := componentOrbit I (T : Subgroup G)
  have hKH : K ≤ H := SwappedSylow.orbit_le_overgroup hs.toSwappedInput
  have hHK : H ≤ normalizer (K : Set G) :=
    (normal_subgroupOf_iff_le_normalizer hKH).mp hs.orbit_normal
  have hXK := hs.toLocalInput.le_of_complement_le hs.complement_le_orbit hHK
  obtain ⟨e,_,_,_⟩ := swapped_quotient_subgroup T hs X hs.invariant
  have hpc := hs.toLocalInput.complement_elementary_of_commutative
    (SwappedFactorsProof.complement_commutative hs.toSwappedInput e)
  let : IsElementaryAbelian 3 A := hpc.1
  let ep := complementEquiv hs.toLocalInput hs.complement_le_orbit
  let : IsElementaryAbelian 3 (quotientImage K A) :=
    IsElementaryAbelian.of_surjective ep.toMonoidHom ep.surjective
  have hA : quotientImage K A ≠ ⊥ := by
    intro he
    have hh := Nat.card_congr ep.toEquiv
    rw [hpc.2,he,card_bot] at hh
    norm_num at hh
  have hr : primeRank 3 (XiQuotient I × XiQuotient I) ≤ 2 := by
    rw [← primeRank_congr 3 e]
    exact (SwappedSylow.orbit_quotient_sqtk hs.toSwappedInput).stronglyQuasithin 3 (by decide) (by decide)
  obtain ⟨S,hS⟩ := component_quotient_sylow hs.sylow_two hKH hs.orbit_normal
  apply small_pair_cubic_congruence hp ho hm hmod e S (quotientImage K A) hA hr
  rw [hS,←collapsed_quotient_residual_eq_complement T hs hc]
  have hnorm : (T : Subgroup G).subgroupOf K ≤ normalizer (X.subgroupOf K : Set K) := by
    rw [←subgroupOf_normalizer_eq hXK]
    exact subgroupOf_mono K hs.invariant
  exact (map_mono hnorm).trans (le_normalizer_map (QuotientGroup.mk' (pCore 2 K)))

/-- The original complement recovers O₂(X) by its action on the containing radical. -/
theorem collapsed_core_commutator (T : Sylow 2 G) {X A H I : Subgroup G}
    (hs : SwappedSylowInput KnownSimple.IsKnownSimple 3 (T : Subgroup G) X A H I)
    (hc : X.pCoreIn 2 ≤ (componentOrbit I (T : Subgroup G)).pCoreIn 2) :
    ⁅(componentOrbit I (T : Subgroup G)).pCoreIn 2,A⁆ = X.pCoreIn 2 := by
  let K := componentOrbit I (T : Subgroup G)
  have hKH : K ≤ H := SwappedSylow.orbit_le_overgroup hs.toSwappedInput
  have hHK : H ≤ normalizer (K : Set G) :=
    (normal_subgroupOf_iff_le_normalizer hKH).mp hs.orbit_normal
  have hXK := hs.toLocalInput.le_of_complement_le hs.complement_le_orbit hHK
  have hcT : K.pCoreIn 2 ≤ (T : Subgroup G) :=
    (SwappedSylow.orbit_core_le_two hs).trans inf_le_left
  have hnorm : H ≤ normalizer (K.pCoreIn 2 : Set G) :=
    hHK.trans (normalizer_le_normalizer_characteristic_image K (pCore 2 K))
  apply le_antisymm
  · have hle : ⁅K.pCoreIn 2,A⁆ ≤ X ⊓ K.pCoreIn 2 :=
      le_inf ((commutator_mono le_rfl hs.toLocalInput.complement_le).trans
        (le_normalizer_iff_commutator_le_right.mp (hcT.trans hs.invariant)))
        (le_normalizer_iff_commutator_le_left.mp
          (hs.complement_le_orbit.trans (hKH.trans hnorm)))
    exact hle.trans (inf_pCoreIn_le_of_le 2 hXK)
  · rw [hs.core_commutator]
    exact commutator_mono hc le_rfl
end CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.PureFourXi

