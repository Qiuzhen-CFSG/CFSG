module

public import CFSG.Quasithin.Chapter2.Section04.DoubleA3
public import Theory.SpecificGroups.AlternatingSix.ShadowLocal.Identification
public import Theory.GroupTheory.MarkedInternalProduct
public import Theory.SpecificGroups.AlternatingSix.ShadowLocal.SymmetricRestriction

/-!
# Constructing the terminal quotient coordinates

The original normal A₆ acts faithfully modulo its centralizer. When R is
D₈ × D₈ and that centralizer is C₄, the actual image of R has order 16.
Inside a Sylow subgroup of Aut(A₆), its natural placement therefore makes
it exactly the natural Sylow intersection. The existing marked holomorph
model supplies C₂ × D₈ coordinates in which membership in Inn(A₆) is
precisely triviality of the first coordinate.

This discharges the coordinate and marking hypotheses of the literal
centralizer consumer, using the actual conjugation and quotient maps.
Source: Aschbacher–Smith, §2.4, printed pp.549–550.
-/

@[expose] public section
namespace CFSG.Quasithin.Chapter2.DoubleA3
open Subgroup
open AlternatingSix.ShadowLocal
open AlternatingSix.ShadowLocal.Identification

private theorem model_natural_mark (a : Holomorph.natural) :
    (a : Holomorph.Model) ∈ Holomorph.innerD ↔ (Holomorph.naturalEquiv a).1 = 1 := by
  obtain ⟨v, rfl⟩ := Holomorph.naturalEquiv.symm.surjective a
  rw [MulEquiv.apply_symm_apply]
  change Holomorph.naturalEmbedding v ∈ Holomorph.innerD ↔ v.1 = 1
  have hc : ∀ v : Holomorph.C2 × DihedralGroup 4,
      (∃ d : DihedralGroup 4, Holomorph.innerEmbedding d = Holomorph.naturalEmbedding v) ↔
        v.1 = 1 := by decide +kernel
  rw [Holomorph.mem_innerD]
  exact hc v

private noncomputable def naturalSylowModelEquiv (P : Sylow 2 AutA6) :
    sylowNatural P ≃* Holomorph.natural where
  toFun a := ⟨(sylowEquiv P).symm a.1, by
    have ha : a.1 ∈ Holomorph.natural.map (sylowEquiv P).toMonoidHom := by
      rw [sylowEquiv_natural]
      exact a.2
    simpa only [mem_map_equiv] using ha⟩
  invFun a := ⟨sylowEquiv P a.1, by
    rw [← sylowEquiv_natural]
    exact mem_map_of_mem (sylowEquiv P).toMonoidHom a.2⟩
  left_inv a := Subtype.ext ((sylowEquiv P).apply_symm_apply a.1)
  right_inv a := Subtype.ext ((sylowEquiv P).symm_apply_apply a.1)
  map_mul' a b := Subtype.ext ((sylowEquiv P).symm.map_mul a.1 b.1)

private noncomputable def naturalSylowCoordinates (P : Sylow 2 AutA6) :
    sylowNatural P ≃* (Multiplicative (ZMod 2) × DihedralGroup 4) :=
  (naturalSylowModelEquiv P).trans Holomorph.naturalEquiv

private theorem naturalSylowCoordinates_mark (P : Sylow 2 AutA6)
    (a : sylowNatural P) :
    ((a : P) : AutA6) ∈ AlternatingSix.ShadowLocal.inner ↔
      (naturalSylowCoordinates P a).1 = 1 := by
  rw [show (naturalSylowCoordinates P a).1 =
      (Holomorph.naturalEquiv (naturalSylowModelEquiv P a)).1 from rfl,
    ← model_natural_mark]
  change a.1 ∈ sylowInner P ↔ (sylowEquiv P).symm a.1 ∈ Holomorph.innerD
  rw [← sylowEquiv_innerD, mem_map_equiv]

private def naturalIntersectionEquiv (P : Sylow 2 AutA6) :
    ((P : Subgroup AutA6) ⊓ natural : Subgroup AutA6) ≃* sylowNatural P where
  toFun a := ⟨⟨a.1, a.2.1⟩, a.2.2⟩
  invFun a := ⟨a.1.1, a.1.2, a.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

/-- An order-16 subgroup in the natural part of a Sylow Aut(A₆) has
marked C₂ × D₈ coordinates. The inner subgroup is the second factor. -/
theorem exists_natural_image_coordinates (P : Sylow 2 AutA6)
    (N : Subgroup AutA6) (hNP : N ≤ (P : Subgroup AutA6))
    (hNnatural : N ≤ natural) (hNcard : Nat.card N = 16) :
    ∃ e : N ≃* (Multiplicative (ZMod 2) × DihedralGroup 4),
      ∀ a : N, (a : AutA6) ∈ AlternatingSix.ShadowLocal.inner ↔ (e a).1 = 1 := by
  have hN : N = (P : Subgroup AutA6) ⊓ natural := by
    apply Subgroup.eq_of_le_of_card_ge (le_inf hNP hNnatural)
    rw [hNcard, Nat.card_congr (naturalIntersectionEquiv P).toEquiv, sylowNatural_card]
  let e₀ := (MulEquiv.subgroupCongr hN).trans (naturalIntersectionEquiv P)
  refine ⟨e₀.trans (naturalSylowCoordinates P), ?_⟩
  intro a
  exact naturalSylowCoordinates_mark P (e₀ a)

/-- The literal quotient image acquires the required coordinates from
R ≅ D₈ × D₈, B ≅ C₄, and its natural placement. Its order 16 and its
inner-subgroup marking are consequences, not extra assumptions. -/
theorem exists_centralizer_quotient_coordinates {H : Type*} [Group H] [Finite H]
    (K : Subgroup H) [K.Normal] (eK : K ≃* A6)
    (R : Subgroup H) (S : Sylow 2 H) (hRS : R ≤ (S : Subgroup H))
    (hBR : centralizer (K : Set H) ≤ R)
    (eB : centralizer (K : Set H) ≃* Multiplicative (ZMod 4))
    (eR : R ≃* (DihedralGroup 4 × DihedralGroup 4))
    (hsurj : Function.Surjective (conjugationAction K eK))
    (hnatural : R.map (conjugationAction K eK) ≤ natural) :
    ∃ e : R.map (QuotientGroup.mk' (centralizer (K : Set H))) ≃*
        (Multiplicative (ZMod 2) × DihedralGroup 4),
      ∀ q : R.map (QuotientGroup.mk' (centralizer (K : Set H))),
        (q : H ⧸ centralizer (K : Set H)) ∈
          K.map (QuotientGroup.mk' (centralizer (K : Set H))) ↔ (e q).1 = 1 := by
  let B := centralizer (K : Set H)
  let action := conjugationAction K eK
  let N := R.map action
  let f : R →* AutA6 := action.comp R.subtype
  have hker : f.ker = B.subgroupOf R := by
    change (action.ker).comap R.subtype = B.subgroupOf R
    rw [conjugationAction_ker]
    rfl
  have hrange : f.range = N := MonoidHom.range_comp _ _ |>.trans (by rw [R.range_subtype])
  have hRcard : Nat.card R = 64 := by
    rw [Nat.card_congr eR.toEquiv, Nat.card_prod, DihedralGroup.nat_card]
  have hBcard : Nat.card B = 4 := by
    rw [Nat.card_congr eB.toEquiv, Nat.card_eq_fintype_card]
    rfl
  have hkerCard : Nat.card f.ker = 4 := by
    rw [hker, Nat.card_congr (subgroupOfEquivOfLe hBR).toEquiv, hBcard]
  have hNcard : Nat.card N = 16 := by
    have hc := f.ker.card_mul_index
    rw [index_ker, hrange, hRcard, hkerCard] at hc
    omega
  let P := S.mapSurjective hsurj
  have hNP : N ≤ (P : Subgroup AutA6) := map_mono hRS
  obtain ⟨eN, hNmark⟩ := exists_natural_image_coordinates P N hNP hnatural hNcard
  let eQ := conjugationQuotientEquiv K eK hsurj
  let π := QuotientGroup.mk' B
  have hcomp : eQ.toMonoidHom.comp π = action := rfl
  have hmap : (R.map π).map eQ.toMonoidHom = N := by rw [map_map, hcomp]
  let e₀ := (eQ.subgroupMap (R.map π)).trans (MulEquiv.subgroupCongr hmap)
  have hinner : (K.map π).map eQ.toMonoidHom = AlternatingSix.ShadowLocal.inner := by
    rw [map_map, hcomp, conjugationAction_map_inner]
  refine ⟨e₀.trans eN, ?_⟩
  intro q
  have hi : (q : H ⧸ B) ∈ K.map π ↔ eQ q ∈ AlternatingSix.ShadowLocal.inner := by
    rw [← hinner, mem_map_equiv, MulEquiv.symm_apply_apply]
  exact hi.trans (hNmark (e₀ q))

/-- The actual Sylow of a marked A₆ has dihedral-eight coordinates. -/
theorem exists_component_sylow_coordinates {H : Type*} [Group H] [Finite H]
    (K : Subgroup H) (eK : K ≃* A6) (P : Sylow 2 K) :
    Nonempty (((P : Subgroup K).map K.subtype) ≃* DihedralGroup 4) := by
  let P₀ : Sylow 2 A6 := (P.mapSurjective (f := eK.toMonoidHom) eK.surjective)
  obtain ⟨e₀⟩ := alternatingSylow_dihedral P₀
  let ep : P ≃* P₀ := eK.subgroupMap (P : Subgroup K)
  exact ⟨((P : Subgroup K).equivMapOfInjective K.subtype K.subtype_injective).symm.trans
    (ep.trans e₀)⟩

/-- Right conjugation carries the original dihedral Sylow coordinates
onto the other factor using the supplied equality of ambient subgroup maps. -/
theorem exists_right_conjugate_factor_coordinates {G : Type*} [Group G]
    (H : Subgroup G) (D E : Subgroup H) (s : G)
    (hE : E.map H.subtype = (D.map H.subtype).map (MulAut.conj s⁻¹).toMonoidHom)
    (eD : D ≃* DihedralGroup 4) : Nonempty (E ≃* DihedralGroup 4) := by
  let e₀ := (E.equivMapOfInjective H.subtype H.subtype_injective).trans
    (MulEquiv.subgroupCongr hE)
  let e₁ := ((MulAut.conj s⁻¹).subgroupMap (D.map H.subtype)).symm
  let e₂ := (D.equivMapOfInjective H.subtype H.subtype_injective).symm
  exact ⟨e₀.trans (e₁.trans (e₂.trans eD))⟩

/-- The original two-factor product yields its D₈ × D₈ model from an
actual Sylow of K, rather than taking both model markings as assumptions. -/
theorem exists_pair_coordinates {G : Type*} [Group G] [Finite G]
    (H : Subgroup G) (K R E : Subgroup H) (eK : K ≃* A6)
    (P : Sylow 2 K) (hP : (P : Subgroup K).map K.subtype = R ⊓ K)
    (s : G)
    (hE : E.map H.subtype = ((R ⊓ K).map H.subtype).map (MulAut.conj s⁻¹).toMonoidHom)
    (hgen : (R ⊓ K) ⊔ E = R) (hd : Disjoint (R ⊓ K) E)
    (hc : (R ⊓ K) ≤ centralizer (E : Set H)) :
    Nonempty (E ≃* DihedralGroup 4) ∧
      Nonempty (R ≃* (DihedralGroup 4 × DihedralGroup 4)) := by
  obtain ⟨eP⟩ := exists_component_sylow_coordinates K eK P
  let eD : (R ⊓ K : Subgroup H) ≃* DihedralGroup 4 :=
    (MulEquiv.subgroupCongr hP.symm).trans eP
  obtain ⟨eE⟩ := exists_right_conjugate_factor_coordinates H (R ⊓ K) E s hE eD
  obtain ⟨eR, _, _⟩ := Theory.GroupTheory.exists_marked_internalProductEquiv
    R (R ⊓ K) E hgen hd hc
  exact ⟨⟨eE⟩, ⟨eR.trans (eD.prodCongr eE)⟩⟩

/-- A source transposition and a source nonsymmetric automorphism generate
all automorphisms together with the already present inner action. This
discharges quotient surjectivity from the two clauses of 2.4.35. -/
theorem conjugation_surjective_of_source_outer_actions {H : Type*} [Group H]
    (K : Subgroup H) [K.Normal] (eK : K ≃* A6)
    (u x : H) (σ : Equiv.Perm (Fin 6)) (hσ : σ.IsSwap)
    (hu : conjugationAction K eK u = permutationAction σ)
    (hx : conjugationAction K eK x ∉ natural) :
    Function.Surjective (conjugationAction K eK) := by
  let f := conjugationAction K eK
  have hi : AlternatingSix.ShadowLocal.inner ≤ f.range := by
    rw [← conjugationAction_map_inner K eK]
    exact map_le_range _ _
  have hσmem : permutationAction σ ∈ f.range := ⟨u, hu⟩
  have hnatural : natural ≤ f.range := by
    rintro _ ⟨τ, rfl⟩
    change permutationAction τ ∈ f.range
    by_cases ht : τ ∈ alternatingGroup (Fin 6)
    · exact hi ⟨⟨τ, ht⟩, (permutationAction_coe ⟨τ, ht⟩).symm⟩
    · have hsign : Equiv.Perm.sign τ = -1 := by
        rcases Int.units_eq_one_or (Equiv.Perm.sign τ) with h | h
        · exact (ht (Equiv.Perm.mem_alternatingGroup.mpr h)).elim
        · exact h
      have hτσ : τ * σ⁻¹ ∈ alternatingGroup (Fin 6) := by
        rw [Equiv.Perm.mem_alternatingGroup, map_mul, map_inv, hsign, hσ.sign_eq]
        decide
      have he : permutationAction (τ * σ⁻¹) ∈ f.range :=
        hi ⟨⟨τ * σ⁻¹, hτσ⟩, (permutationAction_coe ⟨τ * σ⁻¹, hτσ⟩).symm⟩
      simpa only [← map_mul, inv_mul_cancel_right] using f.range.mul_mem he hσmem
  apply MonoidHom.range_eq_top.mp
  apply eq_top_of_natural_lt
  apply lt_of_le_of_ne hnatural
  intro h
  exact hx (h ▸ (show f x ∈ f.range from ⟨x, rfl⟩))

/-- Source consumer with the D₈-factor and quotient-coordinate hypotheses
removed. The original Sylow, right conjugate factor and direct-product
relations construct all the markings required by the terminal proof. -/
theorem false_of_source_pair_geometry {G : Type*} [Group G] [Finite G]
    (z : G) (hz : z ^ 2 = 1) (hz1 : z ≠ 1)
    (K : Subgroup (involutionCentralizer z)) [K.Normal] (eK : K ≃* A6)
    (R E : Subgroup (involutionCentralizer z))
    (S : Sylow 2 (involutionCentralizer z)) (hRS : R ≤ (S : Subgroup (involutionCentralizer z)))
    (hBR : centralizer (K : Set (involutionCentralizer z)) ≤ R)
    (eB : centralizer (K : Set (involutionCentralizer z)) ≃* Multiplicative (ZMod 4))
    (u x : involutionCentralizer z) (σ : Equiv.Perm (Fin 6)) (hσ : σ.IsSwap)
    (hu : conjugationAction K eK u = permutationAction σ)
    (hx : conjugationAction K eK x ∉ natural)
    (hnatural : R.map (conjugationAction K eK) ≤ natural)
    (P : Sylow 2 K) (hP : (P : Subgroup K).map K.subtype = R ⊓ K)
    (s : G)
    (hE : E.map (involutionCentralizer z).subtype =
      ((R ⊓ K).map (involutionCentralizer z).subtype).map (MulAut.conj s⁻¹).toMonoidHom)
    (hgen : (R ⊓ K) ⊔ E = R) (hd : Disjoint (R ⊓ K) E)
    (hc : (R ⊓ K) ≤ centralizer (E : Set (involutionCentralizer z)))
    (z₁ : involutionCentralizer z) (hz₁ : z₁ ∈ R ⊓ K)
    (hs : s⁻¹ * (z₁ : G) * s = z)
    (hpure : ∀ a : involutionCentralizer z, IsConj z (a : G) → a ∈ R → a ∈ K ∨ a ∈ E) :
    False := by
  let H := involutionCentralizer z
  have hsurj := conjugation_surjective_of_source_outer_actions K eK u x σ hσ hu hx
  obtain ⟨⟨eE⟩, ⟨eR⟩⟩ := exists_pair_coordinates H K R E eK P hP s hE hgen hd hc
  obtain ⟨eQ, hmark⟩ := exists_centralizer_quotient_coordinates K eK R S hRS hBR
    eB eR hsurj hnatural
  have hER : E ≤ R := hgen ▸ (show E ≤ (R ⊓ K) ⊔ E from le_sup_right)
  have hEK : Disjoint E K := by
    apply disjoint_def.mpr
    intro a haE haK
    exact disjoint_def.mp hd ⟨hER haE, haK⟩ haE
  have hEconj : E.map H.subtype ≤ rightConjugateComponent H K s := by
    rw [hE]
    exact map_mono (map_mono inf_le_right)
  have hzconj : z ∈ rightConjugateComponent H K s := by
    change z ∈ (K.map H.subtype).map (MulAut.conj s⁻¹).toMonoidHom
    refine ⟨(z₁ : G), mem_map_of_mem H.subtype hz₁.2, ?_⟩
    simpa only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv] using hs
  exact false_of_centralizer_geometry z hz hz1 K eK R E hBR hER hEK
    eB eE hsurj hnatural eQ hmark hpure s hEconj hzconj

end CFSG.Quasithin.Chapter2.DoubleA3
