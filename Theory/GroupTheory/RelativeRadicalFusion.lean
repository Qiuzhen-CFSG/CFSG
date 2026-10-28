module

public import Theory.GroupTheory.ConjugationFamily
public import Theory.GroupTheory.NormalizerFusionExtension
public import Theory.PGroupCore
/-!
# Fusion through centric subgroups radical in their ambient automizer

The automizer here is the actual image of the normalizer on the subgroup,
not the full abstract automorphism group. Pull back its p-core and intersect
with the Sylow normalizer. If this image exceeds the inner automorphisms,
Frattini correction extends every local action to a strictly larger subgroup.
Descending induction applied to the centric Huppert decomposition removes
these steps and proves the relation form of element fusion.

This refines `CentricRadicalCharacterFusion` at the relative automizer needed
for Alperin–Goldschmidt fusion. The comparison with the odd-core formulation
is a separate structural result; it is not part of the radical predicate.
Source: Huppert X.4.8 and X.4.12, as used in Aschbacher–Smith, combined
1 March 2004 manuscript, Definition 2.2.1 and Proposition 2.2.2, pp. 518–519.
-/

noncomputable section
open BenderSuzuki.External
public theorem Sylow.exists_strict_normalizer_extension_of_not_relative_radical
    {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (S : Sylow p G) (U : Subgroup G) (hU : HuppertExtremal S U)
    (hrad : ¬ (pCore p U.normalizerMonoidHom.range) ≤
        (U.subgroupOf (Subgroup.normalizer (U : Set G))).map U.normalizerMonoidHom.rangeRestrict) :
    ∃ V : Subgroup G, U < V ∧ V ≤ (S : Subgroup G) ∧
      ∀ g ∈ Subgroup.normalizer (U : Set G),
        ∃ n ∈ Subgroup.normalizer (V : Set G),
          ∀ x ∈ U, g⁻¹ * x * g = n⁻¹ * x * n := by
  classical
  let N := Subgroup.normalizer (U : Set G)
  let f := U.normalizerMonoidHom.rangeRestrict
  obtain ⟨P, hP⟩ := hU.exists_sylow_normalizer
  let D := (P : Subgroup N) ⊓ (pCore p U.normalizerMonoidHom.range).comap f
  let B := D.map N.subtype
  let V := U ⊔ B
  have hBS : B ≤ (S : Subgroup G) := by
    have h := Subgroup.map_mono (f := N.subtype)
      (show D ≤ (P : Subgroup N) from inf_le_left)
    rw [hP] at h
    exact h.trans inf_le_left
  have hUV : U < V := by
    refine lt_of_le_of_ne le_sup_left ?_
    intro heq
    apply hrad
    intro a hcore
    have ha : a ∈ (P : Subgroup N).map f :=
      pCore_isPGroup.le_sylow_of_normal
        (P.mapSurjective U.normalizerMonoidHom.rangeRestrict_surjective) hcore
    obtain ⟨x, hxP, rfl⟩ := ha
    have hxB : (x : G) ∈ B := Subgroup.mem_map.mpr ⟨x, ⟨hxP, hcore⟩, rfl⟩
    have hxU : (x : G) ∈ U := heq.ge (Subgroup.mem_sup_right hxB)
    exact ⟨x, hxU, rfl⟩
  refine ⟨V, hUV, sup_le hU.1 hBS, ?_⟩
  intro g hg
  obtain ⟨n, hn, hfn⟩ := P.exists_normalizer_preimage_correction f
    (pCore p U.normalizerMonoidHom.range) pCore_isPGroup ⟨g, hg⟩
  have hnB : (n : G) ∈ Subgroup.normalizer (B : Set G) :=
    Subgroup.le_normalizer_map N.subtype (Subgroup.mem_map.mpr ⟨n, hn, rfl⟩)
  have hnV : (n : G) ∈ Subgroup.normalizer (V : Set G) :=
    Subgroup.normalizer_inf_normalizer_le_normalizer_sup U B ⟨n.property, hnB⟩
  refine ⟨n, hnV, ?_⟩
  intro x hx
  have h := congrArg (fun a : U.normalizerMonoidHom.range => (((a : MulAut U)⁻¹) ⟨x, hx⟩ : G)) hfn
  change (n : G)⁻¹ * x * ((n : G)⁻¹)⁻¹ = g⁻¹ * x * (g⁻¹)⁻¹ at h
  simpa only [inv_inv] using h.symm

open BenderSuzuki.PFchapter1section1

/-- A reflexive transitive relation on a Sylow subgroup is preserved by ambient
conjugacy if it is preserved by the normalizers of the centric extremal
subgroups satisfying the relative radical condition. -/
public theorem Sylow.relative_radical_fusion_relation
    {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (S : Sylow p G) (R : S → S → Prop)
    (hrefl : ∀ x, R x x)
    (htrans : ∀ {x y z}, R x y → R y z → R x z)
    (hlocal : ∀ (U : Subgroup G), U ≤ (S : Subgroup G) →
      (Nat.card ↥((S : Subgroup G) ⊓ Subgroup.normalizer (U : Set G))).factorization p =
        (Nat.card (Subgroup.normalizer (U : Set G))).factorization p →
      ((S : Subgroup G) ⊓ Subgroup.centralizer (U : Set G)) ≤ U →
      (pCore p U.normalizerMonoidHom.range) ≤
        (U.subgroupOf (Subgroup.normalizer (U : Set G))).map U.normalizerMonoidHom.rangeRestrict →
      ∀ g : G, g ∈ Subgroup.normalizer (U : Set G) →
      ∀ x y : S, (x : G) ∈ U → g⁻¹ * (x : G) * g = (y : G) → R x y)
    {x y : S} (hxy : IsConj (x : G) (y : G)) : R x y := by
  classical
  have hsub : ∀ (A : Subgroup G), A ≤ (S : Subgroup G) →
      ∀ g : G, rightConjugate A g ≤ (S : Subgroup G) →
        ∀ x y : S, (x : G) ∈ A → g⁻¹ * (x : G) * g = (y : G) → R x y := by
    let motive : ℕ → Prop := fun n ↦
      ∀ A : Subgroup G, A ≤ (S : Subgroup G) →
      Nat.card (S : Subgroup G) - Nat.card A = n →
      ∀ g : G, rightConjugate A g ≤ (S : Subgroup G) →
        ∀ x y : S, (x : G) ∈ A → g⁻¹ * (x : G) * g = (y : G) → R x y
    intro A hAS
    suffices motive (Nat.card (S : Subgroup G) - Nat.card A) from this A hAS rfl
    apply Nat.strong_induction_on
    intro k ih A hAS hk g hg x y hx hxy
    have hlarger : ∀ B : Subgroup G, Nat.card A < Nat.card B →
        B ≤ (S : Subgroup G) → ∀ n : G,
        rightConjugate B n ≤ (S : Subgroup G) →
        ∀ w z : S, (w : G) ∈ B → n⁻¹ * (w : G) * n = (z : G) → R w z := by
      intro B hAB hBS
      have hcard := Subgroup.card_le_of_le hBS
      exact ih (Nat.card (S : Subgroup G) - Nat.card B) (by omega) B hBS rfl
    have hd := HuppertExtremal.centric_conjugation_decomposition S hAS hg
    have hstep : ∀ {g : G},
        HuppertCentricConjugationDecomposition (S : Subgroup G)
          (HuppertExtremal S) A g →
        ∀ z : S, g⁻¹ * (x : G) * g = (z : G) → R x z := by
      intro g hd
      induction hd with
      | one =>
        intro z hz
        have hxz : x = z := Subtype.ext (by simpa using hz)
        rw [hxz]
        exact hrefl z
      | @tail g h U hd hU hUS hAU hh hcent ihstep =>
        intro z hz
        have hcurrent : g⁻¹ * (x : G) * g ∈ U := by
          apply hAU
          exact Subgroup.mem_map.mpr ⟨(x : G), hx, by simp⟩
        let w : S := ⟨g⁻¹ * (x : G) * g, hUS hcurrent⟩
        have hxw : R x w := ihstep w rfl
        have hwz : h⁻¹ * (w : G) * h = (z : G) := by
          simpa [w, mul_inv_rev, mul_assoc] using hz
        apply htrans hxw
        rcases hcent with hcent | hcent
        · by_cases hrad : (pCore p U.normalizerMonoidHom.range) ≤
              (U.subgroupOf (Subgroup.normalizer (U : Set G))).map U.normalizerMonoidHom.rangeRestrict
          · exact hlocal U hU.1 hU.2 hcent hrad h hh w z hcurrent hwz
          · obtain ⟨V, hUV, hVS, hext⟩ :=
              S.exists_strict_normalizer_extension_of_not_relative_radical U hU hrad
            obtain ⟨n, hn, hnact⟩ := hext h hh
            have hcard : Nat.card A < Nat.card V := by
              have heq : Nat.card A = Nat.card (rightConjugate A g) := by
                exact (Subgroup.card_map_of_injective (K := A)
                  (f := (MulAut.conj g⁻¹).toMonoidHom) (MulAut.conj g⁻¹).injective).symm
              have hle := Subgroup.card_le_of_le hAU
              have hlt : Nat.card U < Nat.card V := by
                refine lt_of_le_of_ne (Subgroup.card_le_of_le hUV.le) ?_
                intro heq
                exact hUV.ne (Subgroup.eq_of_le_of_card_ge hUV.le heq.ge)
              omega
            have hnV : rightConjugate V n ≤ (S : Subgroup G) := by
              change V.map (MulAut.conj n⁻¹) ≤ (S : Subgroup G)
              rw [Subgroup.mem_normalizer_iff_map_conj_eq.mp
                ((Subgroup.normalizer (V : Set G)).inv_mem hn)]
              exact hVS
            exact hlarger V hcard hVS n hnV w z (hUV.le hcurrent)
              ((hnact (w : G) hcurrent).symm.trans hwz)
        · have hcomm := Subgroup.mem_centralizer_iff.mp hcent (w : G) hcurrent
          have heq : w = z := by
            apply Subtype.ext
            calc
              (w : G) = h⁻¹ * (w : G) * h := by
                rw [mul_assoc, hcomm]
                simp
              _ = (z : G) := hwz
          rw [heq]
          exact hrefl z
    exact hstep hd y hxy
  obtain ⟨c, hc⟩ := isConj_iff.mp hxy
  have hAS : Subgroup.zpowers (x : G) ≤ (S : Subgroup G) :=
    Subgroup.zpowers_le.mpr x.property
  have hcA : rightConjugate (Subgroup.zpowers (x : G)) c⁻¹ ≤ (S : Subgroup G) := by
    simp only [rightConjugate, inv_inv, Subgroup.conjBy]
    rw [Subgroup.map_le_iff_le_comap]
    apply Subgroup.zpowers_le.mpr
    change c * (x : G) * c⁻¹ ∈ (S : Subgroup G)
    rw [hc]
    exact y.property
  exact hsub _ hAS c⁻¹ hcA x y (Subgroup.mem_zpowers _) (by simpa using hc)
