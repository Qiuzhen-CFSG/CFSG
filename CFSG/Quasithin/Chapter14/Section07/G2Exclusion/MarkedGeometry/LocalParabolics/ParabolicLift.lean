module

public import CFSG.Quasithin.Chapter14.Section07.G2Exclusion.MarkedGeometry.LocalParabolics.ConjugateCoverage
public import Theory.GroupTheory.PCoreImage
public import CFSG.Quasithin.ChapterB.Section06To07.Elementary

/-!
# Marked line-parabolic lifts and their two-cores

The normalizer of the literal lift of Ṽ is the preimage of its stabilizer
under the actual starred quotient action. The marked B.4.6 line parabolic
has Borel index three. Since L₁ has image outside that Borel, L₁T maps
onto the parabolic; containing the kernel then identifies its whole
preimage with N_H(V). Minimality and distinction from the marked point
parabolic transport along these literal maps.

Finally the earlier identity QQ_H=R₁=O₂(L₁T) and the two-group quotient
kernel give Q*=R₁*=O₂(M₁*). The model facts and earlier local identities
are explicit inputs; no source equality of normalizers is assumed.
The three-offender orbit from B.4.6(13) is a separate remaining branch.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), 14.7.57,
printed pp.1066–1067, using 14.7.4(4) and B.4.6(3),(4),(13).
-/

@[expose] public noncomputable section
namespace CFSG.Quasithin.Chapter14.Section07.G2Exclusion.MarkedGeometry.LocalParabolics
open Subgroup
open scoped Pointwise
variable {H K : Type*} [Group H] [Group K]

/-- The marked quotient line has exactly the relative normalizer of its
literal preimage. This is the source identification N_H(V)*=N_{H*}(Ṽ). -/
theorem relative_line_normalizer
    {G : Type*} [Group G] (H U Z V : Subgroup G) [(Z.subgroupOf U).Normal]
    (hHU : H ≤ normalizer U) (hVU : V ≤ U) (hZV : Z ≤ V)
    (π : H →* K) (τ : K →* MulAut (U ⧸ Z.subgroupOf U))
    (hact : ∀ h : H, ∀ u : U,
      τ (π h) (QuotientGroup.mk' (Z.subgroupOf U) u) =
        QuotientGroup.mk' (Z.subgroupOf U)
          ⟨(h : G) * (u : G) * (h : G)⁻¹,
            (mem_normalizer_iff.mp (hHU h.property) u).mp u.property⟩) :
    (normalizer V).subgroupOf H =
      ((MulAction.stabilizer (MulAut (U ⧸ Z.subgroupOf U))
        ((V.subgroupOf U).map (QuotientGroup.mk' (Z.subgroupOf U)))).comap τ).comap π := by
  let B := (V.subgroupOf U).map (QuotientGroup.mk' (Z.subgroupOf U))
  have hb : linePreimage U Z B = V := linePreimage_image U Z V hVU hZV
  have hinj : Function.Injective (linePreimage U Z) := by
    intro A B h
    exact comap_injective (QuotientGroup.mk'_surjective _)
      (map_injective U.subtype_injective h)
  ext h
  change (h : G) ∈ normalizer V ↔ τ (π h) ∈ MulAction.stabilizer _ B
  rw [mem_normalizer_iff_map_conj_eq, MulAction.mem_stabilizer_iff]
  change conjugate V h = V ↔ B.map (τ (π h)).toMonoidHom = B
  have hc := lift_support_conjugate H U Z hHU (τ.comp π) hact B h
  change conjugate (linePreimage U Z B) h =
    linePreimage U Z (B.map (τ (π h)).toMonoidHom) at hc
  rw [hb] at hc
  rw [hc, ← hb]
  exact hinj.eq_iff

/-- An index-three parabolic has no proper intermediate subgroup over its
Borel. The source L₁ contributes an element outside that Borel. -/
theorem eq_parabolic_of_index_three (B J P : Subgroup K)
    (hBJ : B ≤ J) (hJP : J ≤ P) (hindex : B.relIndex P = 3) (hne : ¬ J ≤ B) :
    J = P := by
  have hm := relIndex_mul_relIndex B J P hBJ hJP
  rw [hindex] at hm
  have hd : B.relIndex J ∣ 3 := ⟨J.relIndex P, hm.symm⟩
  rcases (Nat.dvd_prime Nat.prime_three).mp hd with h1 | h3
  · exact (hne (relIndex_eq_one.mp h1)).elim
  · rw [h3] at hm
    have hJP1 : J.relIndex P = 1 := by omega
    exact le_antisymm hJP (relIndex_eq_one.mp hJP1)

/-- Recover N_H(V)=L₁T by lifting its marked quotient parabolic. The input
index three and the strict Borel enlargement are the earlier model/local
facts, not an assumed equality of the two source normalizers. -/
theorem parabolic_preimage_eq_join (π : H →* K) (L₁ T : Subgroup H)
    (P : Subgroup K) (hker : π.ker ≤ T)
    (hLP : L₁.map π ≤ P) (hTP : T.map π ≤ P)
    (hindex : (T.map π).relIndex P = 3)
    (hne : ¬ L₁.map π ≤ T.map π) :
    P.comap π = L₁ ⊔ T := by
  have he : (L₁ ⊔ T).map π = P := by
    apply eq_parabolic_of_index_three (T.map π) _ P
    · exact map_mono le_sup_right
    · rw [Subgroup.map_sup]
      exact sup_le hLP hTP
    · exact hindex
    · intro hj
      exact hne ((map_mono le_sup_left).trans hj)
  rw [← he, comap_map_eq_self (hker.trans le_sup_right)]

/-- After identifying the marked preimage, the actual image is the specified
minimal parabolic and remains distinct from the point parabolic. -/
theorem marked_parabolic_image (π : H →* K) (hsurj : Function.Surjective π)
    (L₁ T : Subgroup H) (P Ppoint : Subgroup K) (hker : π.ker ≤ T)
    (hLP : L₁.map π ≤ P) (hTP : T.map π ≤ P)
    (hindex : (T.map π).relIndex P = 3) (hne : ¬ L₁.map π ≤ T.map π)
    (hminimal : P ∈ nonNormalUniqueMaximalOvergroups (T.map π)) (hdistinct : P ≠ Ppoint) :
    (L₁ ⊔ T).map π ∈ nonNormalUniqueMaximalOvergroups (T.map π) ∧
      (L₁ ⊔ T).map π ≠ Ppoint := by
  have he := congrArg (fun S : Subgroup H => S.map π)
    (parabolic_preimage_eq_join π L₁ T P hker hLP hTP hindex hne)
  rw [map_comap_eq_self_of_surjective hsurj] at he
  rw [← he]
  exact ⟨hminimal,hdistinct⟩

/-- Conditional 14.7.57(1), with the line parabolic and distinct point
parabolic identified through the actual starred action. The index-three,
minimality, and distinctness inputs are the marked B.4.6 model facts. -/
theorem source_marked_normalizer
    {G : Type*} [Group G] (H U Z V : Subgroup G) [(Z.subgroupOf U).Normal]
    (hHU : H ≤ normalizer U) (hVU : V ≤ U) (hZV : Z ≤ V)
    (π : H →* K) (hsurj : Function.Surjective π)
    (τ : K →* MulAut (U ⧸ Z.subgroupOf U))
    (hact : ∀ h : H, ∀ u : U,
      τ (π h) (QuotientGroup.mk' (Z.subgroupOf U) u) =
        QuotientGroup.mk' (Z.subgroupOf U)
          ⟨(h : G) * (u : G) * (h : G)⁻¹,
            (mem_normalizer_iff.mp (hHU h.property) u).mp u.property⟩)
    (L₁ T Y : Subgroup H) (P Ppoint : Subgroup K)
    (hP : P = (MulAction.stabilizer (MulAut (U ⧸ Z.subgroupOf U))
      ((V.subgroupOf U).map (QuotientGroup.mk' (Z.subgroupOf U)))).comap τ)
    (hpoint : (Y ⊔ T).map π = Ppoint)
    (hker : π.ker ≤ T) (hLP : L₁.map π ≤ P) (hTP : T.map π ≤ P)
    (hindex : (T.map π).relIndex P = 3) (hne : ¬ L₁.map π ≤ T.map π)
    (hminimal : P ∈ nonNormalUniqueMaximalOvergroups (T.map π)) (hdistinct : P ≠ Ppoint) :
    (normalizer V).subgroupOf H = L₁ ⊔ T ∧
      (L₁ ⊔ T).map π ∈ nonNormalUniqueMaximalOvergroups (T.map π) ∧
      (L₁ ⊔ T).map π ≠ (Y ⊔ T).map π := by
  have hnormal := relative_line_normalizer H U Z V hHU hVU hZV π τ hact
  rw [← hP, parabolic_preimage_eq_join π L₁ T P hker hLP hTP hindex hne] at hnormal
  have himage := marked_parabolic_image π hsurj L₁ T P Ppoint hker hLP hTP
    hindex hne hminimal hdistinct
  exact ⟨hnormal,himage.1,hpoint ▸ himage.2⟩

variable [Finite H] [Finite K]

/-- The image of QQ_H=R₁=O₂(L₁T) is the two-core of the actual parabolic
image. This uses a two-group kernel and preserves the literal starred map. -/
theorem source_radical_image (π : H →* K) (hker : IsPGroup 2 π.ker)
    (Q QH L₁ T : Subgroup H) (hQH : QH ≤ π.ker)
    (hproduct : Q ⊔ QH = (L₁ ⊔ T).pCoreIn 2) :
    Q.map π = ((L₁ ⊔ T).pCoreIn 2).map π ∧
      Q.map π = ((L₁ ⊔ T).map π).pCoreIn 2 := by
  have hzero : QH.map π = ⊥ := (QH.map_eq_bot_iff).mpr hQH
  have he := congrArg (fun S : Subgroup H => S.map π) hproduct
  rw [Subgroup.map_sup, hzero, sup_bot_eq] at he
  exact ⟨he,he.trans (map_pCoreIn_of_ker_isPGroup π hker (L₁ ⊔ T))⟩

/-- Actual 14.7.57(2) application to H*=H/O₂(H), with Q_H=O₂(H).
The product identity is the explicit earlier 14.7.4(4) input. -/
theorem source_starred_radical (Q L₁ T : Subgroup H)
    (hproduct : Q ⊔ pCore 2 H = (L₁ ⊔ T).pCoreIn 2) :
    let π := QuotientGroup.mk' (pCore 2 H)
    Q.map π = ((L₁ ⊔ T).pCoreIn 2).map π ∧
      Q.map π = ((L₁ ⊔ T).map π).pCoreIn 2 := by
  dsimp only
  apply source_radical_image (QuotientGroup.mk' (pCore 2 H)) _ Q (pCore 2 H) L₁ T _ hproduct
  · rw [QuotientGroup.ker_mk']
    exact pCore_isPGroup
  · rw [QuotientGroup.ker_mk']

end CFSG.Quasithin.Chapter14.Section07.G2Exclusion.MarkedGeometry.LocalParabolics
