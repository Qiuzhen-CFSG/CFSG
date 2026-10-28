module

public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.DiagonalOuter.FieldModels
public import Theory.GroupTheory.PResidual.PerfectCover
public import Theory.Quasithin.EvenCharacteristic

/-!
# The order-nine joint centralizer in the diagonal-outer branch

The final paragraph of Aschbacher--Smith 15.3.38 (combined manuscript of
1 March 2004, printed p.1137) claims an extraspecial group of order 27
as the two-residual of C_G(⟨U₁,f⟩). `SourceObstruction` proves that this
cannot be combined with the earlier central-cover description.

Here the earlier data instead produce E₉, with an actual isomorphism.
If L has index two in C_G(V₁), then C_L(w) has two-power index in
C_G(V₁) ∩ C_G(w). A finite normal subgroup with p-group quotient has
the same embedded p-residual, which proves equality of these two-residuals.
The known E₉ model for O²(C_L(w)) therefore transports along the actual
fusion w ~ f to O²(C_G(⟨V₁ᵍ,f⟩)).

This repairs the construction of the joint residual only. The reduction
must still supply the index-two inclusion and the graph-field centralizer
model. The field-component analysis must still prove the containment
contradicting `order_nine_not_le_component_centralizer`.
-/

public section

open Subgroup

private theorem residual_eq_of_normal_quotient
    {G : Type*} [Group G] [Finite G] (p : ℕ) (N : Subgroup G) [N.Normal]
    (hQ : IsPGroup p (G ⧸ N)) :
    pResidual p G = (pResidual p N).map N.subtype := by
  let R := (pResidual p N).map N.subtype
  have hRQ : IsPGroup p (G ⧸ R) := by
    intro x
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective R x
    obtain ⟨n, hn⟩ := hQ (QuotientGroup.mk' N g)
    have hgn : g ^ p ^ n ∈ N := by
      apply (QuotientGroup.eq_one_iff _).mp
      change QuotientGroup.mk' N (g ^ p ^ n) = 1
      rw [map_pow]
      exact hn
    obtain ⟨m, hm⟩ := isPGroup_quotient_pResidual (G := N) p
      (QuotientGroup.mk' (pResidual p N) ⟨g ^ p ^ n, hgn⟩)
    have hgm : (⟨g ^ p ^ n, hgn⟩ : N) ^ p ^ m ∈ pResidual p N := by
      apply (QuotientGroup.eq_one_iff _).mp
      change QuotientGroup.mk' (pResidual p N) ((⟨g ^ p ^ n, hgn⟩ : N) ^ p ^ m) = 1
      rw [map_pow]
      exact hm
    refine ⟨n + m, ?_⟩
    rw [← map_pow]
    apply (QuotientGroup.eq_one_iff _).mpr
    exact mem_map.mpr ⟨_, hgm, by simp only [coe_pow, subtype_apply, pow_add, pow_mul]⟩
  exact le_antisymm (sInf_le ⟨inferInstance, hRQ⟩) (map_pResidual_le p N.subtype)


private theorem residual_intersection_of_index_two
    {G : Type*} [Group G] [Finite G] (L C A : Subgroup G)
    (hLC : L ≤ C) (hindex : L.relIndex C = 2) :
    (pResidual 2 (C ⊓ A : Subgroup G)).map (C ⊓ A).subtype =
      (pResidual 2 (L ⊓ A : Subgroup G)).map (L ⊓ A).subtype := by
  let H := C ⊓ A
  let N := L.subgroupOf C
  let K := (L ⊓ A).subgroupOf H
  have hLH : L ⊓ A ≤ H := inf_le_inf hLC le_rfl
  let : N.Normal := normal_of_index_eq_two hindex
  let q : H →* C ⧸ N := (QuotientGroup.mk' N).comp (inclusion inf_le_left)
  have hker : q.ker = K := by
    ext x
    change QuotientGroup.mk' N (inclusion inf_le_left x) = 1 ↔ x ∈ K
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    change (x : G) ∈ L ↔ (x : G) ∈ L ⊓ A
    exact ⟨fun hx => ⟨hx, x.property.2⟩, fun hx => hx.1⟩
  let : K.Normal := hker ▸ q.normal_ker
  have hQ : IsPGroup 2 (C ⧸ N) := IsPGroup.of_card (n := 1) (by
    rw [pow_one, ← index_eq_card]
    exact hindex)
  have hK : IsPGroup 2 (H ⧸ K) := by
    exact ((hQ.to_subgroup q.range).of_equiv (QuotientGroup.quotientKerEquivRange q).symm).of_equiv
      (QuotientGroup.quotientMulEquivOfEq hker)
  have he := congrArg (fun J : Subgroup H => J.map H.subtype)
    (residual_eq_of_normal_quotient 2 K hK)
  have hKm : K.map H.subtype = L ⊓ A := map_subgroupOf_eq_of_le hLH
  have ht := map_embedded_pResidual 2 K H.subtype
  rw [hKm] at ht
  exact he.trans ht


namespace CFSG.Quasithin.Chapter15.Section03.DiagonalOuter
variable {G : Type*} [Group G]

/-- C_G(⟨V,w⟩), expressed as an intersection of pointwise centralizers. -/
@[expose] def jointCentralizer (V : Subgroup G) (w : G) : Subgroup G :=
  centralizer (V : Set G) ⊓ centralizer ({w} : Set G)

/-- The two-residual, computed inside the joint centralizer and embedded in G. -/
@[expose] def jointResidual (V : Subgroup G) (w : G) : Subgroup G :=
  (pResidual 2 (jointCentralizer V w)).map (jointCentralizer V w).subtype

/-- Adjoining the outer involution does not change the joint two-residual. -/
theorem jointResidual_eq [Finite G] (V L : Subgroup G) (w : G)
    (hLC : L ≤ centralizer (V : Set G))
    (hindex : L.relIndex (centralizer (V : Set G)) = 2) :
    jointResidual V w = (pResidual 2 (L ⊓ centralizer ({w} : Set G) : Subgroup G)).map
      (L ⊓ centralizer ({w} : Set G)).subtype :=
  residual_intersection_of_index_two L _ _ hLC hindex

/-- Actual automorphisms transport the joint centralizer. -/
theorem map_jointCentralizer (V : Subgroup G) (w : G) (e : G ≃* G) :
    (jointCentralizer V w).map e.toMonoidHom =
      jointCentralizer (V.map e.toMonoidHom) (e w) := by
  have he : (centralizer ({w} : Set G)).map e.toMonoidHom =
      centralizer ({e w} : Set G) := by
    have h := Theory.Quasithin.map_centralizer e (zpowers w)
    rw [MonoidHom.map_zpowers] at h
    simpa only [zpowers_eq_closure, centralizer_closure, MulEquiv.coe_toMonoidHom] using h
  unfold jointCentralizer
  rw [map_inf _ _ _ e.injective, Theory.Quasithin.map_centralizer, he]

/-- Actual automorphisms transport its embedded two-residual. -/
theorem map_jointResidual [Finite G] (V : Subgroup G) (w : G) (e : G ≃* G) :
    (jointResidual V w).map e.toMonoidHom =
      jointResidual (V.map e.toMonoidHom) (e w) := by
  unfold jointResidual
  rw [map_embedded_pResidual, map_jointCentralizer]

/-- The concrete elementary abelian group of order nine. -/
abbrev ElementaryNine := Multiplicative (Fin 2 → ZMod 3)

/-- Fusion supplies a conjugate plane with joint two-residual E₉. -/
theorem jointResidual_model_of_fusion [Finite G] (V L : Subgroup G)
    (hLC : L ≤ centralizer (V : Set G))
    (hindex : L.relIndex (centralizer (V : Set G)) = 2)
    {w f : G} (hfusion : IsConj w f)
    (eF : pResidual 2 (L ⊓ centralizer ({w} : Set G) : Subgroup G) ≃* ElementaryNine) :
    ∃ g : G, (MulAut.conj g) w = f ∧
      Nonempty (jointResidual (V.map (MulAut.conj g).toMonoidHom) f ≃* ElementaryNine) := by
  obtain ⟨g, hg⟩ := isConj_iff.mp hfusion
  refine ⟨g, hg, ?_⟩
  let e := MulAut.conj g
  let A := L ⊓ centralizer ({w} : Set G)
  let e₀ : jointResidual V w ≃* ElementaryNine :=
    (MulEquiv.subgroupCongr (jointResidual_eq V L w hLC hindex)).trans
      (((pResidual 2 A).equivMapOfInjective A.subtype A.subtype_injective).symm.trans eF)
  have he : (jointResidual V w).map e.toMonoidHom =
      jointResidual (V.map e.toMonoidHom) f := by
    rw [map_jointResidual, show e w = f from hg]
  exact ⟨(MulEquiv.subgroupCongr he.symm).trans
    (((jointResidual V w).equivMapOfInjective e.toMonoidHom e.injective).symm.trans e₀)⟩

/-- Once the joint two-residual is E₉, it is also the joint odd core. -/
theorem jointResidual_eq_oddCore_of_model [Finite G] (V : Subgroup G) (w : G)
    (e : jointResidual V w ≃* ElementaryNine) :
    jointResidual V w = (pPrimeCore 2 (jointCentralizer V w)).map
      (jointCentralizer V w).subtype := by
  let H := jointCentralizer V w
  have hcard : Nat.card (pResidual 2 H) = 9 := by
    calc
      _ = Nat.card (jointResidual V w) := Nat.card_congr
        ((pResidual 2 H).equivMapOfInjective H.subtype H.subtype_injective).toEquiv
      _ = Nat.card ElementaryNine := Nat.card_congr e.toEquiv
      _ = 9 := by simp [ElementaryNine, Nat.card_eq_fintype_card]
  have he : pResidual 2 H = pPrimeCore 2 H := by
    apply le_antisymm
    · exact le_sSup ⟨inferInstance, by norm_num [hcard]⟩
    · intro x hx
      exact mem_pResidual_of_orderOf_coprime
        (pPrimeCore_coprime_card.of_dvd_right ((pPrimeCore 2 H).orderOf_dvd_natCard hx))
  exact congrArg (fun K : Subgroup H => K.map H.subtype) he

/-- The corrected joint residual contradicts either centralizer alternative
as soon as the field-component argument proves it centralizes the component. -/
theorem jointResidual_not_le_component_centralizer [Finite G]
    (V K : Subgroup G) (f : G) (e : jointResidual V f ≃* ElementaryNine)
    (hC : FieldComponentCentralizerAlternative (centralizer ({f} : Set G)) K) :
    ¬ jointResidual V f ≤ centralizer (K : Set G) := by
  have hcard : Nat.card (jointResidual V f) = 9 := by
    rw [Nat.card_congr e.toEquiv]
    simp [ElementaryNine, Nat.card_eq_fintype_card]
  have hexp : ∀ b : jointResidual V f, b ^ 3 = 1 := by
    intro b
    apply e.injective
    rw [map_pow, map_one]
    change (3 : ℕ) • Multiplicative.toAdd (e b) = 0
    ext i
    change (3 : ℕ) • (Multiplicative.toAdd (e b) i : ZMod 3) = 0
    exact ZModModule.char_nsmul_eq_zero 3 _
  exact order_nine_not_le_component_centralizer _ K _ hcard hexp
    ((map_subtype_le _).trans inf_le_right) hC
end CFSG.Quasithin.Chapter15.Section03.DiagonalOuter
