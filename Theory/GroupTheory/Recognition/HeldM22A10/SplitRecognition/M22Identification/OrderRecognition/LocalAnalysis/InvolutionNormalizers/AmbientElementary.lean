module

public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.M22Identification.OrderRecognition.LocalAnalysis.InvolutionNormalizers.ElementarySixteen
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.M22Identification.OrderRecognition.LocalAnalysis.InvolutionNormalizers.SylowTransport
/-!
# Ambient forms of Janko's first local lemma

Pulling an elementary subgroup back along the faithful coordinate map gives
exactly E or F in the coordinate Sylow group. Sylow conjugacy then shows
that every elementary subgroup of order sixteen is normal in every ambient
Sylow two-subgroup containing it. No compatibility between the arbitrary
coordinate map and the originally chosen Sylow subgroup is assumed.

We also transport the local normalizer calculation, obtaining the exact
intersection of N_G(F) with the distinguished involution centralizer.

Source: Z. Janko, *A characterization of the Mathieu simple groups, I*,
J. Algebra 9 (1968), Section 2, p.4 and Lemma 1.
-/

open Subgroup
open scoped Pointwise
namespace Theory.GroupTheory.HeldM22A10.M22Identification.CaseII
open LocalModelDichotomy
universe u
variable {G : Type u} [Group G] [Finite G] (D : LocalData G)
  (k : TwistedModel ≃* D.centralizer)

/-- The coordinate image contains exactly E and F as elementary sixteens. -/
public theorem elementary_sixteen_in_caseIISylow (A : Subgroup G)
    (hAT : A ≤ caseIISylow D k) (hA : IsElementaryAbelian 2 A)
    (hcard : Nat.card A = 16) : A = E D k ∨ A = F D k := by
  let f := into D k
  let B := A.comap f
  have hf : Function.Injective f := into_injective D k
  have hArange : A ≤ f.range := hAT.trans (map_le_range _ _)
  have hmap : B.map f = A := map_comap_eq_self hArange
  have hBT : B ≤ modelT := by
    have h := comap_mono (f := f) hAT
    change B ≤ (modelT.map f).comap f at h
    rwa [comap_map_eq_self_of_injective hf] at h
  have hBc : Nat.card B = 16 := by
    rw [Nat.card_congr (B.equivMapOfInjective f hf).toEquiv, hmap, hcard]
  have hBe : IsElementaryAbelian 2 B := by
    have hs (x : B) : x ^ 2 = 1 := by
      apply Subtype.ext
      apply hf
      let := hA
      simpa only [Subgroup.coe_pow, Subgroup.coe_one, map_pow, map_one] using
        elemPow_eq_one_of_isElementaryAbelian (p := 2) (f x) x.property
    refine
      { is_comm := ?_
        exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr hs }
    exact ⟨fun x y => (Commute.of_orderOf_dvd_two
      (fun x => orderOf_dvd_of_pow_eq_one (hs x)) x y).eq⟩
  rcases model_elementary_sixteen B hBT hBe hBc with h | h
  · exact Or.inl (hmap.symm.trans ((congrArg (Subgroup.map f) h).trans (modelE_map D k)))
  · exact Or.inr (hmap.symm.trans ((congrArg (Subgroup.map f) h).trans (modelF_map D k)))

include D k in
/-- Every elementary sixteen is normal in any ambient Sylow two-group containing it. -/
public theorem elementary_sixteen_normal_in_sylow (P : Sylow 2 G) (A : Subgroup G)
    (hAP : A ≤ P) (hA : IsElementaryAbelian 2 A) (hcard : Nat.card A = 16) :
    (A.subgroupOf P).Normal := by
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G P (caseIISylow D k)
  let f := (MulAut.conj g).toMonoidHom
  have hPmap : (P : Subgroup G).map f = caseIISylow D k :=
    congrArg Sylow.toSubgroup hg
  have hAmap : A.map f ≤ caseIISylow D k := (map_mono hAP).trans_eq hPmap
  have hAmape : IsElementaryAbelian 2 (A.map f) := by
    let := hA
    exact IsElementaryAbelian.map f
  have hAmapc : Nat.card (A.map f) = 16 := by
    rw [← Nat.card_congr (A.equivMapOfInjective f (MulAut.conj g).injective).toEquiv, hcard]
  have hN : (caseIISylow D k : Subgroup G) ≤ normalizer (A.map f : Set G) := by
    rcases elementary_sixteen_in_caseIISylow D k (A.map f) hAmap hAmape hAmapc with h | h
    · rw [h]; exact caseIISylow_le_normalizer_E D k
    · rw [h]; exact caseIISylow_le_normalizer_F D k
  rw [← hPmap, map_le_iff_le_comap,
    comap_normalizer_eq_of_le_range (map_le_range _ _),
    comap_map_eq_self_of_injective (MulAut.conj g).injective] at hN
  exact (normal_subgroupOf_iff_le_normalizer hAP).mpr hN

/-- Inside the distinguished centralizer, the normalizer of F is precisely the coordinate Sylow. -/
public theorem normalizer_F_inf_centralizer :
    normalizer (F D k : Set G) ⊓ D.centralizer = caseIISylow D k := by
  have hf : Function.Injective (into D k) := into_injective D k
  have hrange : (into D k).range = D.centralizer := by
    rw [into, MonoidHom.range_comp, MonoidHom.range_eq_top.mpr k.surjective, ← MonoidHom.range_eq_map, D.centralizer.range_subtype]
  have h := comap_normalizer_eq_of_le_range (show F D k ≤ (into D k).range by
    rw [← modelF_map D k]; exact map_le_range _ _)
  rw [← modelF_map D k, comap_map_eq_self_of_injective hf, modelF_normalizer] at h
  have hm := congrArg (Subgroup.map (into D k)) h
  rw [map_comap_eq, hrange, modelF_map D k] at hm
  change normalizer (F D k : Set G) ⊓ D.centralizer = modelT.map (into D k)
  simpa only [inf_comm] using hm
end Theory.GroupTheory.HeldM22A10.M22Identification.CaseII
