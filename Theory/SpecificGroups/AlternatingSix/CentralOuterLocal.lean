module
public import Theory.SpecificGroups.AlternatingSix.ShadowLocal.SylowGeometry
public import Theory.SpecificGroups.AlternatingSix.ShadowLocal.InvolutionGeometry
public import Theory.GroupTheory.SymmetricFourModelCoreData
public import Theory.GroupTheory.SylowKernelCore
public import Theory.SpecificGroups.AlternatingSix.ProperSylowOvergroups
/-! The two four-group normalizers in a marked Aut(A6) Sylow.
An outer transposition centralizing the inner Sylow lies outside the center
of the full Sylow. Its centralizer is the natural S6 intersection, which
normalizes both inner four-groups. Their S4 normalizers are distinct because
each has its four-group as two-core. At least one therefore escapes the
transposition's fixed S4. This S4 is maximal in A6 by the checked proper
Sylow-overgroup theorem. Source: Aschbacher--Smith 2.5.2, printed p.551,
using the actual holomorph calculations on pp.568--570. -/
public section
open Subgroup
namespace AlternatingSix.ShadowLocal.CentralOuterLocal
open SylowGeometry

private theorem normalizer_core (F : Subgroup A6) [IsKleinFour F] :
    (normalizer (F : Set A6)).pCoreIn 2 = F := by
  have hf : F ≤ (normalizer (F : Set A6)).pCoreIn 2 :=
    le_pCoreIn_of_normalizes (IsPGroup.of_card (show Nat.card F = 2^2 from IsKleinFour.card_four))
      F.le_normalizer le_rfl
  obtain ⟨_, hc⟩ := symmetric_four_model_twoCore_data (.inl (four_normalizer_equiv_symmetric F))
  have hcard : Nat.card (pCore 2 (normalizer (F : Set A6))) = 4 := by
    have hn := four_normalizer_card F
    rcases hc with hc | hc
    · exact hc.1
    · omega
  apply (eq_of_le_of_card_ge hf ?_).symm
  rw [pCoreIn,card_map_of_injective (normalizer (F : Set A6)).subtype_injective,hcard]
  exact IsKleinFour.card_four.ge

private theorem normalizer_injective (F E : Subgroup A6) [IsKleinFour F] [IsKleinFour E]
    (h : normalizer (F : Set A6) = normalizer (E : Set A6)) : F = E := by
  rw [← normalizer_core F,← normalizer_core E,h]

private theorem center_le_inner (P : Sylow 2 AutA6) : center P ≤ sylowInner P := by
  rw [center_eq]
  apply zpowers_le.mpr
  rw [← Identification.sylowEquiv_innerD P]
  apply mem_map_of_mem
  have hh := (Holomorph.innerD).pow_mem
    (show Holomorph.rotation ^ 2 ∈ Holomorph.innerD from subset_closure (by simp)) 2
  simpa only [← pow_mul] using hh

private def fromInner (P : Sylow 2 AutA6) (F : Subgroup P) : Subgroup A6 :=
  (F.map (P : Subgroup AutA6).subtype).comap (MulAut.conj : A6 →* AutA6)

private theorem fromInner_map (P : Sylow 2 AutA6) (F : Subgroup P)
    (hF : F ≤ sylowInner P) :
    (fromInner P F).map (MulAut.conj : A6 →* AutA6) = F.map (P : Subgroup AutA6).subtype := by
  have hle : F.map (P : Subgroup AutA6).subtype ≤ (MulAut.conj : A6 →* AutA6).range := by
    rintro _ ⟨a,ha,rfl⟩
    exact hF ha
  rw [fromInner,map_comap_eq,inf_eq_right.mpr hle]

private theorem fromInner_klein (P : Sylow 2 AutA6) (F : Subgroup P)
    [IsKleinFour F] (hF : F ≤ sylowInner P) : IsKleinFour (fromInner P F) := by
  let e := ((fromInner P F).equivMapOfInjective (MulAut.conj : A6 →* AutA6) inner_injective).trans
    ((MulEquiv.subgroupCongr (fromInner_map P F hF)).trans
      (F.equivMapOfInjective (P : Subgroup AutA6).subtype (P : Subgroup AutA6).subtype_injective).symm)
  exact { card_four := (Nat.card_congr e.toEquiv).trans IsKleinFour.card_four
          exponent_two := (Monoid.exponent_eq_of_mulEquiv e).trans IsKleinFour.exponent_two }

private theorem fromInner_invariant (P : Sylow 2 AutA6) (F : Subgroup P)
    (b : P) (hb : b ∈ normalizer (F : Set P)) :
    (fromInner P F).map b.val.toMonoidHom = fromInner P F := by
  apply eq_of_le_of_card_ge ?_ (card_map_of_injective b.val.injective).ge
  rintro _ ⟨x,hx,rfl⟩
  obtain ⟨a,ha,he⟩ := hx
  refine ⟨b*a*b⁻¹,(mem_normalizer_iff.mp hb a).mp ha,?_⟩
  change b.val * a.val * b.val⁻¹ = MulAut.conj (b.val x)
  change (a : AutA6) = MulAut.conj x at he
  rw [he]
  ext y
  simp

/-- A Sylow centralizer of an outer marked involution preserves an S4
which is not pointwise fixed by that involution. -/
theorem exists_invariant_local (P : Sylow 2 AutA6)
    (σ : Equiv.Perm (Fin 6)) (hσ : σ.IsSwap)
    (huP : permutationAction σ ∈ (P : Subgroup AutA6))
    (hfix : ∀ a ∈ sylowInner P, permutationAction σ * a.val = a.val * permutationAction σ) :
    ∃ K : Subgroup A6, Nonempty (K ≃* Equiv.Perm (Fin 4)) ∧
      (∀ b : P, b.val * permutationAction σ = permutationAction σ * b.val →
        K.map b.val.toMonoidHom = K) ∧
      ¬ ∀ x ∈ K, permutationAction σ x = x := by
  let u : P := ⟨permutationAction σ,huP⟩
  have hun : u ∉ sylowInner P := by
    rintro ⟨a,ha⟩
    have he : (a : Equiv.Perm (Fin 6)) = σ :=
      permutationAction_injective ((permutationAction_coe a).trans ha)
    have hs := a.property
    rw [Equiv.Perm.mem_alternatingGroup,he,hσ.sign_eq] at hs
    norm_num at hs
  have huc : u ∈ centralizer (sylowInner P : Set P) := by
    intro a ha
    exact Subtype.ext (hfix a ha).symm
  have hu2 : u^2=1 := Subtype.ext (by
    change permutationAction σ ^2=1
    obtain ⟨a,b,hab,rfl⟩ := hσ
    rw [pow_two,← map_mul]
    simp)
  have hcent := centralizer_innerCentralizer_involution P u huc
    (fun h => hun (center_le_inner P h)) hu2
  rw [centralizer_transposition] at hcent
  let F := fromInner P (kleinZero P)
  let E := fromInner P (kleinOne P)
  let : IsKleinFour F := fromInner_klein P _ (kleinZero_le_inner P)
  let : IsKleinFour E := fromInner_klein P _ (kleinOne_le_inner P)
  have hFE : F ≠ E := by
    intro he
    have hh := congrArg (map (MulAut.conj : A6 →* AutA6)) he
    rw [fromInner_map P _ (kleinZero_le_inner P),fromInner_map P _ (kleinOne_le_inner P)] at hh
    exact kleinZero_ne_kleinOne P (map_injective (P : Subgroup AutA6).subtype_injective hh)
  have invariant (W : Subgroup P)
      (hn : normalizer (W : Set P) = sylowNatural P) (b : P)
      (hb : b.val * permutationAction σ = permutationAction σ * b.val) :
      (normalizer (fromInner P W : Set A6)).map b.val.toMonoidHom =
        normalizer (fromInner P W : Set A6) := by
    rw [map_equiv_normalizer_eq,fromInner_invariant]
    rw [hn,← hcent]
    exact mem_centralizer_singleton_iff.mpr (Subtype.ext hb)
  have escape : ¬ ((∀ x ∈ normalizer (F : Set A6), permutationAction σ x=x) ∧
      ∀ x ∈ normalizer (E : Set A6), permutationAction σ x=x) := by
    rintro ⟨hF,hE⟩
    obtain ⟨e⟩ := swap_fixed_equiv_symmetricFour σ hσ
    have hc : Nat.card (GLS3.Chapter5.automorphismFixedSubgroup (permutationAction σ)) = 24 := by
      rw [Nat.card_congr e.toEquiv,Nat.card_eq_fintype_card,Fintype.card_perm]
      decide
    have hNF : normalizer (F : Set A6) = GLS3.Chapter5.automorphismFixedSubgroup (permutationAction σ) :=
      eq_of_le_of_card_ge hF (by rw [hc,four_normalizer_card])
    have hNE : normalizer (E : Set A6) = GLS3.Chapter5.automorphismFixedSubgroup (permutationAction σ) :=
      eq_of_le_of_card_ge hE (by rw [hc,four_normalizer_card])
    exact hFE (normalizer_injective F E (hNF.trans hNE.symm))
  by_cases hF : ∀ x ∈ normalizer (F : Set A6), permutationAction σ x=x
  · exact ⟨normalizer (E : Set A6),four_normalizer_equiv_symmetric E,
      invariant _ (normalizer_kleinOne P),fun hE => escape ⟨hF,hE⟩⟩
  · exact ⟨normalizer (F : Set A6),four_normalizer_equiv_symmetric F,
      invariant _ (normalizer_kleinZero P),hF⟩

theorem symmetric_four_isCoatom (K : Subgroup A6) (e : K ≃* Equiv.Perm (Fin 4)) :
    IsCoatom K := by
  classical
  have hc : Nat.card K = 24 := by
    rw [Nat.card_congr e.toEquiv,Nat.card_eq_fintype_card,Fintype.card_perm]
    decide
  let P : Sylow 2 K := Classical.choice inferInstance
  have hp : Nat.card P = 8 := by
    rw [P.card_eq_multiplicity,hc,show (24 : ℕ) = 2^3*3 by decide,
      Nat.factorization_mul (by decide) (by decide),Finsupp.add_apply,
      Nat.prime_two.factorization_pow,Finsupp.single_eq_same]
    norm_num [Nat.prime_three.factorization]
  let D := (P : Subgroup K).map K.subtype
  obtain ⟨Q,hDQ⟩ := (P.isPGroup'.map K.subtype).exists_le_sylow
  have hDeq : D = (Q : Subgroup A6) := eq_of_le_of_card_ge hDQ (by
    rw [alternatingSylow_card]
    change 8 ≤ Nat.card ((P : Subgroup K).map K.subtype)
    rw [card_map_of_injective K.subtype_injective,hp])
  have hQK : (Q : Subgroup A6) ≤ K := hDeq ▸ map_subtype_le _
  refine ⟨?_,?_⟩
  · intro he
    have hh := congrArg (fun J : Subgroup A6 => Nat.card J) he
    rw [hc,card_top,card_A6] at hh
    omega
  · intro U hKU
    by_contra hU
    rcases ProperSylowOvergroups.card_eight_or_twentyFour Q U (hQK.trans hKU.le) hU with h8 | h24
    · have hh := card_le_of_le hKU.le
      rw [hc,h8] at hh
      omega
    · exact hKU.ne (eq_of_le_of_card_ge hKU.le (by rw [hc,h24]))


theorem exists_invariant_local_of_action {A : Type*} [Group A] [Finite A]
    (ρ : A →* AutA6) (hA : IsPGroup 2 A) (R : Sylow 2 A6)
    (hR : (R : Subgroup A6).map (MulAut.conj : A6 →* AutA6) ≤ ρ.range)
    (σ : Equiv.Perm (Fin 6)) (hσ : σ.IsSwap)
    (hu : permutationAction σ ∈ ρ.range)
    (hcentral : ∀ a, ρ a * permutationAction σ = permutationAction σ * ρ a) :
    ∃ K : Subgroup A6, Nonempty (K ≃* Equiv.Perm (Fin 4)) ∧
      (∀ a, K.map (ρ a).toMonoidHom = K) ∧
      ¬ ∀ x ∈ K, permutationAction σ x=x := by
  obtain ⟨P,hAP⟩ := (hA.of_surjective ρ.rangeRestrict ρ.rangeRestrict_surjective).exists_le_sylow
  let D := (R : Subgroup A6).map (MulAut.conj : A6 →* AutA6)
  have hDP : D ≤ (P : Subgroup AutA6) := hR.trans hAP
  have hDcard : Nat.card (D.subgroupOf P) = 8 := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hDP).toEquiv,
      card_map_of_injective inner_injective,alternatingSylow_card]
  have he : D.subgroupOf P = sylowInner P :=
    eq_of_le_of_card_ge (fun a ha => map_le_range _ _ ha)
      (by rw [sylowInner_card,hDcard])
  obtain ⟨K,hK,hinv,hesc⟩ := exists_invariant_local P σ hσ (hAP hu) (by
    intro a ha
    have haD : a.val ∈ D := by rwa [← he] at ha
    obtain ⟨b,hb⟩ := hR haD
    rw [← hb]
    exact (hcentral b).symm)
  exact ⟨K,hK,fun a => hinv ⟨ρ a,hAP ⟨a,rfl⟩⟩ (hcentral a),hesc⟩

end AlternatingSix.ShadowLocal.CentralOuterLocal
