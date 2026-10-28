module

public import CFSG.Quasithin.Chapter1.Section03.Embeddings.Swapped.Factors
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.Swapped.BenderNormalizers
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.Swapped.JankoLocal
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.Swapped.OuterAction
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.Swapped.OuterParameters

/-!
# The sufficient Sylow variant of the swapped-component embedding

For the intrinsic local input with T Sylow two in H, a noninvariant component
L gives P = (P ∩ L) × (P ∩ L)^t ≅ E_(p²), with the specified moving element
in N_T(P). Its quotient is either PSL₂(2ⁿ), where n is even and 2ⁿ ≡ 1 mod p,
or PSL₂(q) for an odd prime q.

The two-component quotient product and complement factors come from the
proved A.3.7/A.3.8 reductions. Transporting the solvable local product into
the two model factors supplies Borel normalization; the binary Cartan order
supplies the congruence. Restricting the actual automizer to H preserves its
Frattini subgroup. Sylow restriction to the relatively normal orbit, followed
by the two-core quotient, then justifies the outer-action obstruction. Even
single-factor outer order excludes Suzuki and J₁ and forces even binary degree.

Only the exact universal earlier A.3.7/A.3.8 implications remain parameters,
as in Section 1.2. No additional model-local or action hypothesis is assumed.
The unbundled wrapper explicitly adds the Sylow hypothesis to the unchanged
`SwappedInput`; the false unrestricted intrinsic assertion is not made.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, combined
1 March 2004 manuscript, Proposition 1.3.4(1), printed pp.509–510 (PDF pp.526–527).
-/

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter1.XiEmbedding.SwappedSylow
universe u
variable {G : Type u} [Group G] {T P H : Subgroup G}

private def restrictActor (hTH : T ≤ H) (hPH : P ≤ H) :
    (T ⊓ normalizer P : Subgroup G) →*
      (T.subgroupOf H ⊓ normalizer (P.subgroupOf H : Set H) : Subgroup H) where
  toFun s := ⟨⟨s, hTH s.property.1⟩, s.property.1, by
    rw [← subgroupOf_normalizer_eq hPH]
    exact s.property.2⟩
  map_one' := rfl
  map_mul' _ _ := rfl

private theorem automizer_restriction (hTH : T ≤ H) (hPH : P ≤ H) :
    Nonempty (automizer T P ≃* automizer (T.subgroupOf H) (P.subgroupOf H)) := by
  let e := MulAut.congr (subgroupOfEquivOfLe hPH).symm
  have hm : (automizer T P).map e.toMonoidHom =
      automizer (T.subgroupOf H) (P.subgroupOf H) := by
    apply le_antisymm
    · rintro _ ⟨a, ⟨s, rfl⟩, rfl⟩
      refine ⟨restrictActor hTH hPH s, ?_⟩
      ext x
      rfl
    · rintro a ⟨s, rfl⟩
      have hs : (s : H).val ∈ normalizer P := by
        have hh := s.property.2
        simp only [← subgroupOf_normalizer_eq hPH] at hh
        exact hh
      let t : (T ⊓ normalizer P : Subgroup G) := ⟨(s : H).val, s.property.1, hs⟩
      refine ⟨P.normalizerMonoidHom (inclusion inf_le_right t), ⟨t, rfl⟩, ?_⟩
      ext x
      rfl
  exact ⟨((automizer T P).equivMapOfInjective e.toMonoidHom e.injective).trans
    (MulEquiv.subgroupCongr hm)⟩

private theorem frattini_restriction
    (hTH : T ≤ H) (hPH : P ≤ H) (hPhi : frattini (automizer T P) ≠ ⊥) :
    frattini (automizer (T.subgroupOf H) (P.subgroupOf H)) ≠ ⊥ := by
  obtain ⟨e⟩ := automizer_restriction hTH hPH
  intro hb
  apply hPhi
  apply bot_unique
  intro a ha
  have he := frattini_le_comap_frattini_of_surjective (φ := e.toMonoidHom) e.surjective ha
  have hz : e a = 1 := by
    change e a ∈ frattini _ at he
    simpa only [hb, mem_bot] using he
  exact e.injective (hz.trans e.map_one.symm)

variable [Finite G] {𝒦 : GroupClass.{u}} {p : ℕ} {X L : Subgroup G}

private theorem outer_even_of_quotient_normalizes
    (h : SwappedSylowInput 𝒦 p T X P H L)
    (hsimple : IsSimpleGroup (XiQuotient L))
    (e : XiQuotient (componentOrbit L T) ≃* XiQuotient L × XiQuotient L)
    (hn : imageInOrbit L T P ≤ normalizer (imageInOrbit L T T)) :
    Even (Nat.card (MulAut.Outer (XiQuotient L))) := by
  let _ : Fact p.Prime := ⟨h.prime⟩
  let _ := hsimple
  let _ := h.quasisimple
  let K := componentOrbit L T
  let N := K.subgroupOf H
  let R := P.subgroupOf H
  let _ : N.Normal := h.orbit_normal
  have hTH : T ≤ H := le_sup_right.trans h.overgroup
  have hPH : P ≤ H := h.complement_le.trans (le_sup_left.trans h.overgroup)
  obtain ⟨S, hS⟩ := h.sylow_two
  have hS' : (S : Subgroup H) = T.subgroupOf H := by
    apply map_injective H.subtype_injective
    rw [map_subgroupOf_eq_of_le hTH]
    exact hS
  let eK : N ≃* K := subgroupOfEquivOfLe (orbit_le_overgroup h.toSwappedInput)
  let eQ : (N ⧸ pCore 2 N) ≃* XiQuotient K :=
    QuotientGroup.congr _ _ eK (pCore_map_iso 2 eK)
  have hnorm := normalizes_two_of_quotient h hn
  have hnN : R.subgroupOf N ≤ normalizer ((S : Subgroup H).subgroupOf N) := by
    rw [hS']
    apply le_normalizer_iff.mpr
    intro a ha s hs
    have hna : (a : H).val ∈ normalizer ((T ⊓ K : Subgroup G) : Set G) := hnorm ha
    have hss : (s : H).val ∈ T ⊓ K := ⟨hs, s.property⟩
    exact ((mem_normalizer_iff.mp hna (s : H).val).mp hss).1
  have hnq : SwappedOuter.Image N R ≤ normalizer (SwappedOuter.Image N S) :=
    (Subgroup.map_mono hnN).trans (Subgroup.le_normalizer_map _)
  have hPhi : frattini (automizer S R) ≠ ⊥ := by
    rw [hS']
    exact frattini_restriction hTH hPH h.toLocalInput.frattini_automizer_ne_bot
  exact SwappedOuter.even_outer_order_of_frattini_automizer N S R h.odd
    h.odd_complement.isPGroup.comap_subtype (fun x hx => h.complement_le_orbit hx)
    (eQ.trans e) hnq hPhi

public theorem model_of_product
    (h : SwappedSylowInput 𝒦 p T X P H L)
    (hsimple : IsSimpleGroup (XiQuotient L))
    (e : XiQuotient (componentOrbit L T) ≃* XiQuotient L × XiQuotient L)
    (hm : Section02.NonnormalCComponentModel (XiQuotient L)) :
    SwappedModel p (XiQuotient L) := by
  let _ : Fact p.Prime := ⟨h.prime⟩
  let R := imageInOrbit L T P
  obtain ⟨S, hS⟩ := orbit_quotient_sylow h
  let U := S.mapSurjective (f := e.toMonoidHom) e.surjective
  let A := R.map e.toMonoidHom
  have hU : (U : Subgroup _) = (imageInOrbit L T T).map e.toMonoidHom := by
    change (S : Subgroup _).map e.toMonoidHom = _
    rw [hS]
  have hsol : Group.IsSolvable (A ⊔ (U : Subgroup _) : Subgroup _) := by
    have he : A ⊔ (U : Subgroup _) =
        (imageInOrbit L T P ⊔ imageInOrbit L T T).map e.toMonoidHom := by
      rw [Subgroup.map_sup, hU]
    rw [he]
    let _ := quotient_solvable h.toSwappedInput
    exact Group.isSolvable_of_surjective (e.toMonoidHom.subgroupMap_surjective _)
  let _ := hsol
  have hA : IsPGroup p A := (quotient_complement_odd h.toSwappedInput).isPGroup.map _
  have hne : A ≠ ⊥ := by
    intro hb
    have hz : imageInOrbit L T P = ⊥ :=
      Subgroup.map_injective e.injective (hb.trans (Subgroup.map_bot _).symm)
    apply quotient_complement_not_cyclic h.toSwappedInput
    rw [hz]
    infer_instance
  have heven (hn : A ≤ normalizer (U : Set _)) :
      Even (Nat.card (MulAut.Outer (XiQuotient L))) := by
    apply outer_even_of_quotient_normalizes h hsimple e
    apply (Subgroup.map_le_map_iff_of_injective (f := e.toMonoidHom) e.injective).mp
    rw [Subgroup.map_normalizer_eq_of_bijective _ e.bijective]
    change A ≤ normalizer ((U : Subgroup (XiQuotient L × XiQuotient L)) :
      Set (XiQuotient L × XiQuotient L)) at hn
    rw [hU] at hn
    exact hn
  cases hm with
  | linear_even n hn iso =>
    obtain ⟨hN, hmod⟩ := binary_model_prod_restrictions hn iso h.odd U A hA hne
    exact Or.inl ⟨n, binary_degree_even_of_outer_even iso (heven hN), hmod, iso⟩
  | linear_prime q hq ho iso => exact Or.inr ⟨q, hq, ho, iso⟩
  | suzuki m hm iso =>
    obtain ⟨eqv⟩ := iso
    exact ((Nat.not_even_iff_odd.mpr (suzuki_model_outer_odd hm eqv))
      (heven (suzuki_model_prod_le_normalizer hm eqv U A))).elim
  | janko iso =>
    obtain ⟨eqv⟩ := iso
    exact ((Nat.not_even_iff_odd.mpr (janko_one_outer_odd eqv))
      (heven (janko_one_model_prod_le_normalizer eqv U A))).elim

/-- The sufficient Sylow variant of the swapped-component alternative.
The exact universal A.3.7 and A.3.8 inputs remain for the Chapter 1 owner;
all conjugate-product, Borel, Cartan and outer-action premises are discharged. -/
public theorem embedding_of_A_3_7_A_3_8
    (hA37 : ∀ (D : Type u) [Group D] [Finite D],
      IsSQTK 𝒦 D → pCore 2 D = ⊥ →
      ∀ B C : Subgroup D, B.IsCComponent → C.IsCComponent → B ≠ C → ⁅B, C⁆ = ⊥)
    (hA38 : ∀ (D : Type u) [Group D] [Finite D],
      IsSQTK 𝒦 D → pCore 2 D = ⊥ → ∀ B : Subgroup D, B.IsCComponent →
      B.Normal ∨ (normalizer (B : Set D)).index = 2 ∧ Section02.NonnormalCComponentModel B)
    (h : SwappedSylowInput 𝒦 p T X P H L) :
    Nonempty (P ≃* Plane p) ∧ SwappedFactors T P L ∧ SwappedModel p (XiQuotient L) := by
  obtain ⟨hp, hf, hs, ⟨e⟩⟩ := factors_of_A_3_7_A_3_8 hA37 hA38 h
  exact ⟨hp, hf, model_of_product h hs e (nonnormal_model_of_A_3_8 hA38 h.toSwappedInput).2⟩

end CFSG.Quasithin.Chapter1.XiEmbedding.SwappedSylow

namespace CFSG.Quasithin.Chapter1.XiEmbedding.SwappedInput
universe u
variable {G : Type u} [Group G] [Finite G]
variable {𝒦 : GroupClass.{u}} {p : ℕ} {T X P H L : Subgroup G}

/-- The original intrinsic record yields the complete swapped alternative
when the genuine Sylow hypothesis is supplied separately. -/
public theorem embedding_of_sylow_of_A_3_7_A_3_8
    (hA37 : ∀ (D : Type u) [Group D] [Finite D],
      IsSQTK 𝒦 D → pCore 2 D = ⊥ →
      ∀ B C : Subgroup D, B.IsCComponent → C.IsCComponent → B ≠ C → ⁅B, C⁆ = ⊥)
    (hA38 : ∀ (D : Type u) [Group D] [Finite D],
      IsSQTK 𝒦 D → pCore 2 D = ⊥ → ∀ B : Subgroup D, B.IsCComponent →
      B.Normal ∨ (normalizer (B : Set D)).index = 2 ∧ Section02.NonnormalCComponentModel B)
    (h : SwappedInput 𝒦 p T X P H L) (hSylow : IsSylowIn 2 T H) :
    Nonempty (P ≃* Plane p) ∧ SwappedFactors T P L ∧ SwappedModel p (XiQuotient L) :=
  SwappedSylow.embedding_of_A_3_7_A_3_8 hA37 hA38
    { toSwappedInput := h, sylow_two := hSylow }

end CFSG.Quasithin.Chapter1.XiEmbedding.SwappedInput
