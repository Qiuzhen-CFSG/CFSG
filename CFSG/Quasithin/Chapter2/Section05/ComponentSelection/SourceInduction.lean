module
public import CFSG.Quasithin.Chapter2.Section05.ComponentSelection.SymplecticFamily
public import CFSG.Quasithin.Chapter2.Section05.ComponentSelection.LinearEvenFamily
public import CFSG.Quasithin.Chapter2.Section05.ComponentSelection.LinearPrimeFamily
public import CFSG.Quasithin.Chapter2.Section05.ComponentSelection.SmallContainedSource
public import CFSG.Quasithin.Chapter2.Section05.ComponentSelection.SmallSource
public import CFSG.Quasithin.Chapter2.Section05.ComponentSelection.BenderAlignedSource
public import CFSG.Quasithin.Chapter2.Section05.ComponentSelection.NoComponents

/-!
# Selecting the original component by finite source descent

The actual local model calculations either produce the required component
join or remove an entire model family in a proper source subgroup. Finite
subgroup descent retains the prescribed Sylow, the literal family of
normalizers, and both starred conditions. Components are transported back
along their actual ambient inclusions. The initial Bender-family removal
and the component-free contradiction are already proved.

The only classification input here is the model-valued part of earlier
2.5.2. Its surviving-model producer is separate; no selection, radical,
normality or replacement certificate is assumed.

Source: Aschbacher--Smith, Lemma 2.5.3(4), printed pp.552--553.
-/

public section
namespace CFSG.Quasithin.Chapter2.Section05.ComponentSelection
open Subgroup Theory.GroupTheory
variable {G : Type*} [Group G] [Finite G] {M H A : Subgroup G}

private def Selected (M H A : Subgroup G) : Prop :=
  ∃ D : Subgroup H, IsComponent H D ∧ ¬ ClassificationModels.IsBenderModel D ∧
    let X := D.map H.subtype ⊔ A
    X ∈ gammaZero (Chapter1.He G) M ∧
      (H ∈ gammaStar (Chapter1.He G) M → X ∈ gammaStar (Chapter1.He G) M) ∧
      (H ∈ gammaMax (Chapter1.He G) M → X ∈ gammaMax (Chapter1.He G) M)

private def Replacement (M H A : Subgroup G) : Prop :=
  ∃ (X : Subgroup G) (n : ℕ) (B : Fin n → Subgroup G),
    X < H ∧ X ∈ gammaZero (Chapter1.He G) M ∧
      (H ∈ gammaStar (Chapter1.He G) M → X ∈ gammaStar (Chapter1.He G) M) ∧
      (H ∈ gammaMax (Chapter1.He G) M → X ∈ gammaMax (Chapter1.He G) M) ∧
      A ≤ X ∧ (∀ i, IsPGroup 2 (B i)) ∧ (∀ i, B i ≤ X) ∧
      X = ⨅ i, normalizer (B i : Set G) ∧
      ∀ K : Subgroup X, IsComponent X K → IsComponentIn (K.map X.subtype) H

omit [Finite G] in
private theorem bender_free_of_descent {X : Subgroup G}
    (hno : ∀ D : Subgroup H, IsComponent H D → ¬ ClassificationModels.IsBenderModel D)
    (hdesc : ∀ K : Subgroup X, IsComponent X K → IsComponentIn (K.map X.subtype) H) :
    ∀ K : Subgroup X, IsComponent X K → ¬ ClassificationModels.IsBenderModel K := by
  intro K hK hm
  have hd := hdesc K hK
  let D := (K.map X.subtype).subgroupOf H
  let e : K ≃* D := (K.equivMapOfInjective X.subtype X.subtype_injective).trans
    (subgroupOfEquivOfLe hd.1).symm
  exact hno D hd.2 (hm.of_mulEquiv e.symm)

omit [Finite G] in
private theorem selected_of_descent {X : Subgroup G}
    (hstar : H ∈ gammaStar (Chapter1.He G) M → X ∈ gammaStar (Chapter1.He G) M)
    (hmax : H ∈ gammaMax (Chapter1.He G) M → X ∈ gammaMax (Chapter1.He G) M)
    (hdesc : ∀ K : Subgroup X, IsComponent X K → IsComponentIn (K.map X.subtype) H)
    (hsel : Selected M X A) : Selected M H A := by
  obtain ⟨K, hK, hn, hj, hs, hm⟩ := hsel
  have hd := hdesc K hK
  let D := (K.map X.subtype).subgroupOf H
  let e : K ≃* D := (K.equivMapOfInjective X.subtype X.subtype_injective).trans
    (subgroupOfEquivOfLe hd.1).symm
  have he : D.map H.subtype = K.map X.subtype := map_subgroupOf_eq_of_le hd.1
  refine ⟨D, hd.2, fun hb => hn (hb.of_mulEquiv e), ?_⟩
  dsimp only
  rw [he]
  exact ⟨hj, hs ∘ hstar, hm ∘ hmax⟩

private theorem select_or_replace
    {C : GroupClass} (hG : IsSimpleQTKE C G)
    (T₀ : Sylow 2 G) (hM : IsMaximalTwoLocal M) (hT₀M : (T₀ : Subgroup G) ≤ M)
    (hunique : ∀ N : Subgroup G, IsMaximalTwoLocal N → (T₀ : Subgroup G) ≤ N → N = M)
    (hH : H ∈ gammaZero (Chapter1.He G) M)
    (hempty : gammaEvenZero (Chapter1.He G) M = ∅)
    {n : ℕ} (B : Fin n → Subgroup G)
    (hp : ∀ i, IsPGroup 2 (B i)) (hBH : ∀ i, B i ≤ H)
    (hHnorm : H = ⨅ i, normalizer (B i : Set G))
    (S : Sylow 2 H) (hSM : (S : Subgroup H).map H.subtype ≤ M)
    (hno : ∀ D : Subgroup H, IsComponent H D → ¬ ClassificationModels.IsBenderModel D)
    (hmodels : ∀ D : Subgroup H, IsComponent H D → ¬ ClassificationModels.IsBenderModel D →
      IsDerivedSymplecticFour D ∨ IsEvenLinearThreeCover D ∨
      (Nonempty (D ≃* Matrix.PSL3Three.PSL) ∨ Nonempty (D ≃* Sporadic.Mathieu.M11)) ∨
      IsLargePrimeLinear D) :
    Selected M H ((S : Subgroup H).map H.subtype) ∨
      Replacement M H ((S : Subgroup H).map H.subtype) := by
  classical
  obtain ⟨U, HU, hpair, hUS, hQS, hbig, hsat⟩ := exists_saturated_pair_aligned hH S hSM
  have hQSi : (twoCore HU).subgroupOf H ≤ (S : Subgroup H) := by
    intro x hx
    obtain ⟨s, hs, he⟩ := hQS hx
    exact (Subtype.ext he : s = x) ▸ hs
  obtain ⟨D, hD⟩ := exists_component_of_normalizer_intersection hG T₀ hM hT₀M
    hunique hH hempty B hp hBH hHnorm
  rcases hmodels D hD (hno D hD) with hm | hm | hm | hm
  · rcases derived_symplectic_source_alternative hG T₀ hM hT₀M hunique hH hempty
      B hp hBH hHnorm hpair hbig hsat S hUS hQSi with hs | hr
    · obtain ⟨K,hK,_,hj⟩ := hs
      exact .inl ⟨K,hK,hno K hK,hj⟩
    · obtain ⟨X,B',hXH,hX,hs,hmax,_,hSX,hp',hBX,hn,hc⟩ := hr
      have hlt : X < H := lt_of_le_of_ne hXH (by
        intro he; cases he; exact (hc D hD).2 hm)
      exact .inr ⟨X,n+1,B',hlt,hX,hs,hmax,hSX,hp',hBX,hn,fun K hK => (hc K hK).1⟩
  · rcases linear_even_source_alternative hG T₀ hM hT₀M hunique hH hempty
      B hp hBH hHnorm hpair hbig hsat S hUS hQSi with hs | hr
    · obtain ⟨K,hK,_,hj⟩ := hs
      exact .inl ⟨K,hK,hno K hK,hj⟩
    · obtain ⟨X,B',hXH,hX,hs,hmax,_,hSX,hp',hBX,hn,hc⟩ := hr
      have hlt : X < H := lt_of_le_of_ne hXH (by
        intro he; cases he; exact (hc D hD).2 hm)
      exact .inr ⟨X,n+1,B',hlt,hX,hs,hmax,hSX,hp',hBX,hn,fun K hK => (hc K hK).1⟩
  · by_cases hi : (D ⊓ normalizer ((D ⊓ (twoCore HU).subgroupOf H : Subgroup H) : Set H)).map
        H.subtype ≤ M
    · obtain ⟨B',hlt,hX,hs,hmax,_,hSX,hp',hBX,hn,hc⟩ :=
        small_component_contained_source hG T₀ hM hT₀M hunique hH B hp hBH hHnorm
          hpair hbig hsat D hD hm hi S hUS hSM hQSi
      exact .inr ⟨_,n+1,B',hlt,hX,hs,hmax,hSX,hp',hBX,hn,fun K hK => (hc K hK).1⟩
    · exact .inl ⟨D,hD,hno D hD,small_component_escaping_source hG T₀ hM hT₀M hunique
        hH B hp hBH hHnorm hpair hbig hsat S hUS D hD hm hi⟩
  · rcases linear_prime_source_alternative hG T₀ hM hT₀M hunique hH
      B hp hBH hHnorm hpair hbig hsat S hUS hQSi with hs | hr
    · obtain ⟨K,hK,_,hj⟩ := hs
      exact .inl ⟨K,hK,hno K hK,hj⟩
    · obtain ⟨X,B',hXH,hX,hs,hmax,_,hSX,hp',hBX,hn,hc⟩ := hr
      have hlt : X < H := lt_of_le_of_ne hXH (by
        intro he; cases he; exact (hc D hD).2 hm)
      exact .inr ⟨X,n+1,B',hlt,hX,hs,hmax,hSX,hp',hBX,hn,fun K hK => (hc K hK).1⟩

/-- The model-valued part of original 2.5.2, restricted to non-Bender
components. This is an earlier classification input, not the selected-component
conclusion of 2.5.3. -/
@[expose] def NonBenderSourceModels (M : Subgroup G) : Prop :=
  ∀ H : Subgroup G, H ∈ gammaZero (Chapter1.He G) M →
    ∀ D : Subgroup H, IsComponent H D → ¬ ClassificationModels.IsBenderModel D →
      IsDerivedSymplecticFour D ∨ IsEvenLinearThreeCover D ∨
      (Nonempty (D ≃* Matrix.PSL3Three.PSL) ∨ Nonempty (D ≃* Sporadic.Mathieu.M11)) ∨
      IsLargePrimeLinear D

private theorem select_bender_free
    {C : GroupClass} (hG : IsSimpleQTKE C G)
    (T₀ : Sylow 2 G) (hM : IsMaximalTwoLocal M) (hT₀M : (T₀ : Subgroup G) ≤ M)
    (hunique : ∀ N : Subgroup G, IsMaximalTwoLocal N → (T₀ : Subgroup G) ≤ N → N = M)
    (hempty : gammaEvenZero (Chapter1.He G) M = ∅)
    (hmodels : NonBenderSourceModels M) :
    ∀ H : Subgroup G, H ∈ gammaZero (Chapter1.He G) M →
    ∀ (n : ℕ) (B : Fin n → Subgroup G),
    (∀ i, IsPGroup 2 (B i)) → (∀ i, B i ≤ H) →
    H = ⨅ i, normalizer (B i : Set G) →
    ∀ S : Sylow 2 H, (S : Subgroup H).map H.subtype ≤ M →
    (∀ D : Subgroup H, IsComponent H D → ¬ ClassificationModels.IsBenderModel D) →
    Selected M H ((S : Subgroup H).map H.subtype) := by
  classical
  let : Finite (Subgroup G) := Finite.of_injective (fun H : Subgroup G => (H : Set G)) SetLike.coe_injective
  intro H
  induction H using (wellFounded_lt (α := Subgroup G)).induction with
  | h H ih =>
    intro hH n B hp hBH hnorm S hSM hno
    rcases select_or_replace hG T₀ hM hT₀M hunique hH hempty B hp hBH hnorm
      S hSM hno (hmodels H hH) with hs | hr
    · exact hs
    · obtain ⟨X,n',B',hlt,hX,hstar,hmax,hSX,hp',hBX,hnorm',hdesc⟩ := hr
      obtain ⟨R,hR⟩ := (show Chapter1.IsSylowIn 2 ((S : Subgroup H).map H.subtype) H
        from ⟨S,rfl⟩).restrict hSX hlt.le
      have hRM : (R : Subgroup X).map X.subtype ≤ M := hR.symm ▸ hSM
      have hsel := ih X hlt hX n' B' hp' hBX hnorm' R hRM
        (bender_free_of_descent hno hdesc)
      rw [hR] at hsel
      exact selected_of_descent hstar hmax hdesc hsel

/-- Original 2.5.3(4) from the genuine earlier 2.5.2 model classification.
All Bender removal, local radical analysis and finite descent are proved;
the selected component belongs to the original H, and its join uses the
prescribed original Sylow. Both starred conditions are retained separately. -/
theorem lemma_2_5_3_four_of_source_models
    {C : GroupClass} (hG : IsSimpleQTKE C G)
    (T₀ : Sylow 2 G) (hM : IsMaximalTwoLocal M) (hT₀M : (T₀ : Subgroup G) ≤ M)
    (hunique : ∀ N : Subgroup G, IsMaximalTwoLocal N → (T₀ : Subgroup G) ≤ N → N = M)
    (hH : H ∈ gammaZero (Chapter1.He G) M)
    (hempty : gammaEvenZero (Chapter1.He G) M = ∅)
    (hmodels : NonBenderSourceModels M)
    {n : ℕ} (B : Fin n → Subgroup G)
    (hp : ∀ i, IsPGroup 2 (B i)) (hBH : ∀ i, B i ≤ H)
    (hHnorm : H = ⨅ i, normalizer (B i : Set G))
    (S : Sylow 2 H) (hSM : (S : Subgroup H).map H.subtype ≤ M) :
    ∃ D : Subgroup H, IsComponent H D ∧ ¬ ClassificationModels.IsBenderModel D ∧
      let X := D.map H.subtype ⊔ (S : Subgroup H).map H.subtype
      X ∈ gammaZero (Chapter1.He G) M ∧
        (H ∈ gammaStar (Chapter1.He G) M → X ∈ gammaStar (Chapter1.He G) M) ∧
        (H ∈ gammaMax (Chapter1.He G) M → X ∈ gammaMax (Chapter1.He G) M) := by
  obtain ⟨X,B',hXH,hX,hstar,hmax,hSX,hp',hBX,hnorm,hc⟩ :=
    exists_bender_free_source_replacement_prescribed_sylow hG T₀ hM hT₀M hunique
      hH B hp hBH hHnorm S hSM
  obtain ⟨R,hR⟩ := (show Chapter1.IsSylowIn 2 ((S : Subgroup H).map H.subtype) H
    from ⟨S,rfl⟩).restrict hSX hXH
  have hRM : (R : Subgroup X).map X.subtype ≤ M := hR.symm ▸ hSM
  have hsel := select_bender_free hG T₀ hM hT₀M hunique hempty hmodels X hX
    (n+1) B' hp' hBX hnorm R hRM (fun K hK => (hc K hK).2)
  rw [hR] at hsel
  exact selected_of_descent hstar hmax (fun K hK => (hc K hK).1) hsel

/-- The literal source tuple form of 2.5.3(4), using its ambient subgroup S. -/
theorem SourceTuple.component_selection_of_source_models
    {C : GroupClass} (hG : IsSimpleQTKE C G)
    (T₀ : Sylow 2 G) (hM : IsMaximalTwoLocal M) (hT₀M : (T₀ : Subgroup G) ≤ M)
    (hunique : ∀ N : Subgroup G, IsMaximalTwoLocal N → (T₀ : Subgroup G) ≤ N → N = M)
    (hempty : gammaEvenZero (Chapter1.He G) M = ∅)
    (hmodels : NonBenderSourceModels M)
    {S T : Subgroup G} {z : G} (d : SourceTuple M H S T z)
    {n : ℕ} (B : Fin n → Subgroup G)
    (hp : ∀ i, IsPGroup 2 (B i)) (hBH : ∀ i, B i ≤ H)
    (hHnorm : H = ⨅ i, normalizer (B i : Set G)) :
    ∃ D : Subgroup H, IsComponent H D ∧ ¬ ClassificationModels.IsBenderModel D ∧
      let X := D.map H.subtype ⊔ S
      X ∈ gammaZero (Chapter1.He G) M ∧
        (H ∈ gammaStar (Chapter1.He G) M → X ∈ gammaStar (Chapter1.He G) M) ∧
        (H ∈ gammaMax (Chapter1.He G) M → X ∈ gammaMax (Chapter1.He G) M) := by
  have hMe : M ∈ Chapter1.He G :=
    Chapter1.mem_He_iff.mpr (hG.evenCharacteristic T₀ M hM hT₀M)
  obtain ⟨_,_,R,hR⟩ := lemma_2_5_1 hMe hempty d
  have hSM : S ≤ M := by
    obtain ⟨P,hP⟩ := d.sylow_intersection
    exact hP ▸ (map_subtype_le (P : Subgroup ↥(H ⊓ M))).trans inf_le_right
  simpa only [hR] using lemma_2_5_3_four_of_source_models hG T₀ hM hT₀M hunique
    d.gamma_zero hempty hmodels B hp hBH hHnorm R (hR.symm ▸ hSM)

end CFSG.Quasithin.Chapter2.Section05.ComponentSelection
