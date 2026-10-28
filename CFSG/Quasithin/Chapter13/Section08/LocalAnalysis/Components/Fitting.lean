module

public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.Components.Basic
public import Theory.GroupTheory.Fitting.PrimeComplementCentralizer
public import Theory.GroupTheory.PResidual.PerfectCover
public import Theory.GroupTheory.PResidual.NormalSubgroup
public import Theory.GroupTheory.PPerfectHom
public import Theory.GroupTheory.PGroup.NormalDirectPowerSection
public import Mathlib.GroupTheory.SpecificGroups.Cyclic
/-!
# The local Fitting calculation and component orbit in §13.8

Write H* = H/O₂(H). The subgroup `twoFitting H` is the actual inverse
image of F(H*), and `twoFittingResidual H` is its two-residual embedded in G.
Since O₂(H*) = 1, F(H*) has odd order and the image of that residual is
exactly F(H*). The three alternatives of 13.8.14, together with the marked
order-three quotients from the earlier setup, therefore make F(H*) trivial
or of order three. Its automorphism group is then a two-group, so O²(H*)
centralizes it. Conversely the center of the characteristic residual is a
normal abelian subgroup. This proves F(H*) = Z(O²(H*)), with the center
mapped into H*. Perfectness of a C-component then gives the separate
Fitting-centralizer bound; the existing criterion gives quasisimplicity.

For the orbit calculation, 1.2.1(3) says that a relative C-component is
normal or has normalizer of index two. A two-perfect subgroup lies in that
normalizer. T-invariance of L₁ extends this normalization to ⟨K^T⟩, which
identifies the generated overgroup with the literal set product ⟨K^T⟩L₁T.
The final theorem uses the actual parabolic N_{LT}(V₁) and its two-residual.

The conditional inputs are explicit: 13.8.14 (supplied by 13.8.12(2) and
13.8.13), the marked quotient orders in the 13.2.1 setup, T-invariance of
the source flag, and the orbit-length clause of 1.2.1(3). The triple-cover
alternative uses the actual central quotient of L/O₂(L), identified with
A₆, and its center of order three; it is not a group-family label. The
section owner must supply these earlier inputs in the standing counterexample.
This module does not assemble 13.8.15–17.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, combined
manuscript of 1 March 2004, printed pp.951–952 (PDF pp.968–969), with
Notation 13.2.1 on p.877 and Proposition 1.2.1(3) on p.504.
-/

@[expose] public section

open Subgroup Theory.GroupTheory
open scoped Pointwise
namespace CFSG.Quasithin.Chapter13.Section08.Components.Fitting
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
private theorem residual_eq_top_of_coprime (p : ℕ) (hc : Nat.Coprime p (Nat.card G)) :
    pResidual p G = ⊤ := by
  apply top_unique
  intro x _
  exact mem_pResidual_of_orderOf_coprime (hc.of_dvd_right (orderOf_dvd_natCard x))

private theorem fitting_residual_eq_top (hcore : pCore 2 G = ⊥) :
    pResidual 2 (fittingSubgroup G) = ⊤ := by
  apply residual_eq_top_of_coprime
  exact (pPrimeCore_coprime_card (p := 2) (G := G)).of_dvd_right
    (card_dvd_of_le (fitting_le_pPrimeCore_of_pCore_eq_bot 2 hcore))

/-- The literal preimage O₂,F(H). -/
def twoFitting (H : Subgroup G) : Subgroup H :=
  (fittingSubgroup (Source.Hstar H)).comap (QuotientGroup.mk' (pCore 2 H))

/-- The residual inside H. -/
def twoFittingResidualIn (H : Subgroup G) : Subgroup H :=
  (pResidual 2 (twoFitting H)).map (twoFitting H).subtype

/-- The source's X, in the ambient group. -/
def twoFittingResidual (H : Subgroup G) : Subgroup G :=
  (twoFittingResidualIn H).map H.subtype

instance twoFitting_normal (H : Subgroup G) : (twoFitting H).Normal :=
  inferInstanceAs (((fittingSubgroup (Source.Hstar H)).comap _).Normal)
instance twoFittingResidualIn_normal (H : Subgroup G) : (twoFittingResidualIn H).Normal :=
  inferInstanceAs (((pResidual 2 (twoFitting H)).map (twoFitting H).subtype).Normal)

omit [Finite G] in
theorem twoFittingResidual_le (H : Subgroup G) : twoFittingResidual H ≤ H :=
  map_subtype_le _

omit [Finite G] in
theorem twoFittingResidual_subgroupOf (H : Subgroup G) :
    (twoFittingResidual H).subgroupOf H = twoFittingResidualIn H :=
  comap_map_eq_self_of_injective H.subtype_injective _

omit [Finite G] in
theorem twoFittingResidual_normal (H : Subgroup G) :
    ((twoFittingResidual H).subgroupOf H).Normal := by
  rw [twoFittingResidual_subgroupOf]
  infer_instance

/-- The residual of the Fitting preimage maps onto F(H*) because F(H*) has odd order. -/
theorem twoFittingResidual_star (H : Subgroup G) :
    Source.starImage H (twoFittingResidual H) = fittingSubgroup (Source.Hstar H) := by
  unfold Source.starImage
  rw [twoFittingResidual_subgroupOf, twoFittingResidualIn, map_embedded_pResidual]
  have hf : (twoFitting H).map (QuotientGroup.mk' (pCore 2 H)) =
      fittingSubgroup (Source.Hstar H) :=
    map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _) _
  rw [hf, fitting_residual_eq_top (pCore_quotient_pCore_eq_bot 2),
    ← MonoidHom.range_eq_map, range_subtype]

/-- The intrinsic two-core quotient of a relatively subnormal subgroup is
its literal image in H*, using the existing subnormal core-intersection theorem. -/
noncomputable def subnormalStarEquiv (H X : Subgroup G) (hXH : X ≤ H)
    (hX : (X.subgroupOf H).IsSubnormal) :
    (X ⧸ pCore 2 X) ≃* Source.starImage H X := by
  let B := X.subgroupOf H
  let e : X ≃* B := (subgroupOfEquivOfLe hXH).symm
  exact (QuotientGroup.congr _ _ e (pCore_map_iso 2 e)).trans
    (hX.quotientCoreImageEquiv 2)

/-- The equivalence sends each representative through the actual H → H* map. -/
theorem subnormalStarEquiv_mk (H X : Subgroup G) (hXH : X ≤ H)
    (hX : (X.subgroupOf H).IsSubnormal) (x : X) :
    (subnormalStarEquiv H X hXH hX (QuotientGroup.mk' (pCore 2 X) x) : Source.Hstar H) =
      QuotientGroup.mk' (pCore 2 H) ⟨x, hXH x.property⟩ := by
  rfl

private theorem residual_centralizes_normal_three (N : Subgroup G) [N.Normal]
    (hn : Nat.card N = 3) : pResidual 2 G ≤ centralizer (N : Set G) := by
  let : IsCyclic N := isCyclic_of_prime_card hn
  have ha : IsPGroup 2 (MulAut N) := by
    apply IsPGroup.of_card (n := 1)
    rw [IsCyclic.card_mulAut, hn, Nat.totient_prime Nat.prime_three]
    norm_num
  let f : G →* MulAut N := MulAut.conjNormal
  have he := (isPPerfect_pResidual (G := G) 2).hom_eq_one_of_isPGroup ha
    (f.comp (pResidual 2 G).subtype)
  intro x hx y hy
  have hh := congrArg (fun a : pResidual 2 G →* MulAut N => a ⟨x, hx⟩ ⟨y, hy⟩) he
  have hh' : x * y * x⁻¹ = y := congrArg Subtype.val hh
  exact (mul_inv_eq_iff_eq_mul.mp hh').symm

private theorem fitting_le_center_residual_of_card (hcore : pCore 2 G = ⊥)
    (hcard : fittingSubgroup G = ⊥ ∨ Nat.card (fittingSubgroup G) = 3) :
    fittingSubgroup G ≤ (center (pResidual 2 G)).map (pResidual 2 G).subtype := by
  rcases hcard with h | h
  · rw [h]; exact bot_le
  have hc := residual_centralizes_normal_three (fittingSubgroup G) h
  have hle : fittingSubgroup G ≤ pResidual 2 G := by
    have hm := map_pResidual_le 2 (fittingSubgroup G).subtype
    rwa [fitting_residual_eq_top hcore, ← MonoidHom.range_eq_map, range_subtype] at hm
  intro x hx
  refine mem_map.mpr ⟨⟨x, hle hx⟩, ?_, rfl⟩
  apply mem_center_iff.mpr
  intro y
  apply Subtype.ext
  exact ((hc y.property) x hx).symm

omit [Finite G] in
private theorem center_residual_le_fitting :
    (center (pResidual 2 G)).map (pResidual 2 G).subtype ≤ fittingSubgroup G := by
  apply le_sSup
  refine ⟨inferInstance, ?_⟩
  let : CommGroup (center (pResidual 2 G)) :=
    { (inferInstance : Group (center (pResidual 2 G))) with
      mul_comm := fun a b => Subtype.ext ((mem_center_iff.mp a.property b).symm) }
  exact Group.nilpotent_of_surjective
    ((pResidual 2 G).subtype.subgroupMap (center (pResidual 2 G)))
    ((pResidual 2 G).subtype.subgroupMap_surjective _)

private theorem fitting_eq_center_residual_of_card (hcore : pCore 2 G = ⊥)
    (hcard : fittingSubgroup G = ⊥ ∨ Nat.card (fittingSubgroup G) = 3) :
    fittingSubgroup G = (center (pResidual 2 G)).map (pResidual 2 G).subtype :=
  le_antisymm (fitting_le_center_residual_of_card hcore hcard) center_residual_le_fitting

/-- Intrinsic description of the genuine perfect central triple cover of A₆.
The quotient is by the actual center of the given group. -/
def IsTripleCoverSix (A : Type*) [Group A] : Prop :=
  Group.IsPerfect A ∧ Nat.card (center A) = 3 ∧
    Nonempty ((A ⧸ center A) ≃* alternatingGroup (Fin 6))

/-- The three alternatives of 13.8.14, retaining both actual quotient models. -/
def ResidualAlternatives (H L L₁ Lplus : Subgroup G) : Prop :=
  twoFittingResidual H = ⊥ ∨
    (Nonempty ((L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6)) ∧
      twoFittingResidual H = L₁) ∨
    (IsTripleCoverSix (L ⧸ pCore 2 L) ∧ twoFittingResidual H = Lplus)

/-- Transport all three source alternatives along the literal quotient map. -/
theorem fitting_star_alternatives (H L L₁ Lplus : Subgroup G)
    (halt : ResidualAlternatives H L L₁ Lplus) :
    fittingSubgroup (Source.Hstar H) = ⊥ ∨
      (Nonempty ((L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6)) ∧
        fittingSubgroup (Source.Hstar H) = Source.starImage H L₁) ∨
      (IsTripleCoverSix (L ⧸ pCore 2 L) ∧
        fittingSubgroup (Source.Hstar H) = Source.starImage H Lplus) := by
  rw [← twoFittingResidual_star H]
  rcases halt with h | ⟨hm, h⟩ | ⟨hm, h⟩
  · left
    simp [h, Source.starImage]
  · exact Or.inr (Or.inl ⟨hm, congrArg (Source.starImage H) h⟩)
  · exact Or.inr (Or.inr ⟨hm, congrArg (Source.starImage H) h⟩)

/-- The marked order-three quotients in Notation 13.2.1 turn 13.8.14
into a precise calculation of the Fitting subgroup's order. -/
theorem fitting_star_trivial_or_card_three (H L L₁ Lplus : Subgroup G)
    (halt : ResidualAlternatives H L L₁ Lplus)
    (ha6 : Nonempty ((L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6)) →
      Nat.card (L₁ ⧸ pCore 2 L₁) = 3)
    (hcover : IsTripleCoverSix (L ⧸ pCore 2 L) →
      Nat.card (Lplus ⧸ pCore 2 Lplus) = 3) :
    fittingSubgroup (Source.Hstar H) = ⊥ ∨ Nat.card (fittingSubgroup (Source.Hstar H)) = 3 := by
  have key (X : Subgroup G) (he : twoFittingResidual H = X)
      (hc : Nat.card (X ⧸ pCore 2 X) = 3) :
      Nat.card (fittingSubgroup (Source.Hstar H)) = 3 := by
    have hXH : X ≤ H := he ▸ twoFittingResidual_le H
    have hn : (X.subgroupOf H).Normal := he ▸ twoFittingResidual_normal H
    rw [← twoFittingResidual_star H, he]
    exact (Nat.card_congr (subnormalStarEquiv H X hXH hn.isSubnormal).symm.toEquiv).trans hc
  rcases halt with h | ⟨hm, h⟩ | ⟨hm, h⟩
  · left
    rw [← twoFittingResidual_star H, h]
    simp [Source.starImage]
  · exact Or.inr (key L₁ h (ha6 hm))
  · exact Or.inr (key Lplus h (hcover hm))

/-- The local Fitting equality preceding 13.8.15. Inputs are precisely
13.8.14 and the two marked quotient orders from the earlier local setup. -/
theorem fitting_star_eq_center_twoResidual (H L L₁ Lplus : Subgroup G)
    (halt : ResidualAlternatives H L L₁ Lplus)
    (ha6 : Nonempty ((L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6)) →
      Nat.card (L₁ ⧸ pCore 2 L₁) = 3)
    (hcover : IsTripleCoverSix (L ⧸ pCore 2 L) →
      Nat.card (Lplus ⧸ pCore 2 Lplus) = 3) :
    fittingSubgroup (Source.Hstar H) =
      (center (pResidual 2 (Source.Hstar H))).map (pResidual 2 (Source.Hstar H)).subtype :=
  fitting_eq_center_residual_of_card (pCore_quotient_pCore_eq_bot 2)
    (fitting_star_trivial_or_card_three H L L₁ Lplus halt ha6 hcover)

private theorem perfect_twoPerfect {A : Type*} [Group A] [Finite A]
    [Group.IsPerfect A] : IsPPerfect 2 A := by
  intro N hn hp
  let := hn
  have hs : Subsingleton (A ⧸ N) := by
    by_contra! h
    exact Group.IsPerfect.not_isNilpotent (A ⧸ N) hp.isNilpotent
  apply eq_top_iff.mpr
  intro x _
  exact (QuotientGroup.eq_one_iff x).mp (Subsingleton.elim _ _)

/-- Every relative C-component is centralized by the Fitting subgroup of H*.
Neither quasisimplicity nor this centralizer bound is an input. -/
theorem fitting_star_le_component_centralizer (H L L₁ Lplus K : Subgroup G)
    (halt : ResidualAlternatives H L L₁ Lplus)
    (ha6 : Nonempty ((L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6)) →
      Nat.card (L₁ ⧸ pCore 2 L₁) = 3)
    (hcover : IsTripleCoverSix (L ⧸ pCore 2 L) →
      Nat.card (Lplus ⧸ pCore 2 Lplus) = 3)
    (hK : (K.subgroupOf H).IsCComponent) :
    fittingSubgroup (Source.Hstar H) ≤ centralizer (Source.starImage H K : Set (Source.Hstar H)) := by
  rw [fitting_star_eq_center_twoResidual H L L₁ Lplus halt ha6 hcover]
  have hk := starImage_isCComponent H K hK
  let := hk.perfect
  have hle : Source.starImage H K ≤ pResidual 2 (Source.Hstar H) :=
    le_pResidual_of_isPPerfect _ perfect_twoPerfect
  rintro x ⟨z, hz, rfl⟩ y hy
  exact congrArg Subtype.val (mem_center_iff.mp hz ⟨y, hle hy⟩)

/-- Apply the existing C-component criterion only after deriving its premise. -/
theorem component_star_quasisimple (H L L₁ Lplus K : Subgroup G)
    (halt : ResidualAlternatives H L L₁ Lplus)
    (ha6 : Nonempty ((L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6)) →
      Nat.card (L₁ ⧸ pCore 2 L₁) = 3)
    (hcover : IsTripleCoverSix (L ⧸ pCore 2 L) →
      Nat.card (Lplus ⧸ pCore 2 Lplus) = 3)
    (hK : (K.subgroupOf H).IsCComponent) :
    IsQuasisimple (Source.starImage H K) :=
  star_quasisimple_of_fitting_centralizes H K hK
    (fitting_star_le_component_centralizer H L L₁ Lplus K halt ha6 hcover hK)

omit [Finite G] in
private theorem twoPerfect_normalizes_of_small_orbit (A K : Subgroup G)
    (hA : IsPPerfect 2 A) (horbit : K.Normal ∨ (normalizer (K : Set G)).index = 2) :
    A ≤ normalizer (K : Set G) := by
  rcases horbit with hn | hi
  · let := hn
    exact le_normalizer_of_normal
  · let N := normalizer (K : Set G)
    let : N.Normal := normal_of_index_eq_two hi
    have hp : IsPGroup 2 (G ⧸ N) := by
      apply IsPGroup.of_card (n := 1)
      exact hi
    exact (le_pResidual_of_isPPerfect A hA).trans (sInf_le ⟨inferInstance, hp⟩)

omit [Finite G] in
/-- The orbit-length conclusion of 1.2.1(3) forces the two-perfect L₁
to normalize K. Normality and the index are both taken inside H. -/
theorem marked_normalizes_component (H K L₁ : Subgroup G)
    (hKH : K ≤ H) (hLH : L₁ ≤ H) (hL : IsPPerfect 2 L₁)
    (horbit : (K.subgroupOf H).Normal ∨
      (normalizer (K.subgroupOf H : Set H)).index = 2) :
    L₁ ≤ normalizer (K : Set G) := by
  have hL' : IsPPerfect 2 (L₁.subgroupOf H) :=
    hL.of_surjective (subgroupOfEquivOfLe hLH).symm.toMonoidHom
      (subgroupOfEquivOfLe hLH).symm.surjective
  have hn := twoPerfect_normalizes_of_small_orbit (L₁.subgroupOf H) (K.subgroupOf H) hL' horbit
  apply le_normalizer_iff.mpr
  intro a ha k hk
  exact le_normalizer_iff.mp hn ⟨a, hLH ha⟩ ha ⟨k, hKH hk⟩ hk

omit [Finite G] in
private theorem normalizes_span (A K T : Subgroup G)
    (hAK : A ≤ normalizer (K : Set G)) (hTA : T ≤ normalizer (A : Set G)) :
    A ≤ normalizer (conjugateSpanBy K T : Set G) := by
  apply le_normalizer_closure_iff.mpr
  rintro a ha x ⟨t, ht, k, hk, rfl⟩
  have hb : t⁻¹ * a * t ∈ A := by
    simpa only [inv_inv] using le_normalizer_iff.mp hTA t⁻¹ (T.inv_mem ht) a ha
  have hc := le_normalizer_iff.mp hAK _ hb k hk
  apply Subgroup.subset_closure
  refine ⟨t, ht, (t⁻¹ * a * t) * k * (t⁻¹ * a * t)⁻¹, hc, ?_⟩
  group

omit [Finite G] in
/-- L₁ normalizes the T-component orbit. The inputs are its definition as
a two-residual (13.2.1), T-invariance, and the orbit bound of 1.2.1(3). -/
theorem marked_normalizes_component_orbit (H K L₁ T : Subgroup G)
    (hKH : K ≤ H) (hLH : L₁ ≤ H) (hL : IsPPerfect 2 L₁)
    (hT : T ≤ normalizer (L₁ : Set G))
    (horbit : (K.subgroupOf H).Normal ∨
      (normalizer (K.subgroupOf H : Set H)).index = 2) :
    L₁ ≤ normalizer (conjugateSpanBy K T : Set G) :=
  normalizes_span L₁ K T (marked_normalizes_component H K L₁ hKH hLH hL horbit) hT

omit [Finite G] in
/-- The generated overgroup is exactly the source's setwise product. No
closure or normalization of that product is assumed. -/
theorem component_orbit_product (H K L₁ T : Subgroup G)
    (hKH : K ≤ H) (hLH : L₁ ≤ H) (hL : IsPPerfect 2 L₁)
    (hT : T ≤ normalizer (L₁ : Set G))
    (horbit : (K.subgroupOf H).Normal ∨
      (normalizer (K.subgroupOf H : Set H)).index = 2) :
    ((conjugateSpanBy K T ⊔ (L₁ ⊔ T) : Subgroup G) : Set G) =
      (conjugateSpanBy K T : Set G) * (L₁ : Set G) * (T : Set G) :=
  generated_overgroup_product K L₁ T
    (marked_normalizes_component_orbit H K L₁ T hKH hLH hL hT horbit) hT

/-- Conditional local assembly preceding 13.8.15. The section owner supplies:
* 13.8.14, with the genuine 13.2.1 marked quotient orders;
* the 13.2.1 two-residual and T-invariance of L₁;
* the relative component-orbit bound from 1.2.1(3).
All centralization, quasisimplicity and setwise-product conclusions are derived. -/
theorem local_fitting_and_orbit (H L L₁ Lplus K T : Subgroup G)
    (hKH : K ≤ H) (hLH : L₁ ≤ H) (hK : (K.subgroupOf H).IsCComponent)
    (halt : ResidualAlternatives H L L₁ Lplus)
    (ha6 : Nonempty ((L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6)) →
      Nat.card (L₁ ⧸ pCore 2 L₁) = 3)
    (hcover : IsTripleCoverSix (L ⧸ pCore 2 L) →
      Nat.card (Lplus ⧸ pCore 2 Lplus) = 3)
    (hL : IsPPerfect 2 L₁) (hT : T ≤ normalizer (L₁ : Set G))
    (horbit : (K.subgroupOf H).Normal ∨
      (normalizer (K.subgroupOf H : Set H)).index = 2) :
    fittingSubgroup (Source.Hstar H) =
        (center (pResidual 2 (Source.Hstar H))).map (pResidual 2 (Source.Hstar H)).subtype ∧
      fittingSubgroup (Source.Hstar H) ≤ centralizer (Source.starImage H K : Set (Source.Hstar H)) ∧
      IsQuasisimple (Source.starImage H K) ∧
      L₁ ≤ normalizer (conjugateSpanBy K T : Set G) ∧
      ((conjugateSpanBy K T ⊔ (L₁ ⊔ T) : Subgroup G) : Set G) =
        (conjugateSpanBy K T : Set G) * (L₁ : Set G) * (T : Set G) :=
  ⟨fitting_star_eq_center_twoResidual H L L₁ Lplus halt ha6 hcover,
    fitting_star_le_component_centralizer H L L₁ Lplus K halt ha6 hcover hK,
    component_star_quasisimple H L L₁ Lplus K halt ha6 hcover hK,
    marked_normalizes_component_orbit H K L₁ T hKH hLH hL hT horbit,
    component_orbit_product H K L₁ T hKH hLH hL hT horbit⟩

/-- The actual parabolic M₁ = N_{LT}(V₁) of Notation 13.2.1. -/
def markedParabolic (L T V₁ : Subgroup G) : Subgroup G :=
  (L ⊔ T) ⊓ normalizer (V₁ : Set G)

/-- The actual marked subgroup L₁,+ = O²([L₁,T ∩ L]) of Notation 13.2.1. -/
def markedPlus (L L₁ T : Subgroup G) : Subgroup G :=
  (pResidual 2 (⁅L₁, T ⊓ L⁆ : Subgroup G)).map (⁅L₁, T ⊓ L⁆ : Subgroup G).subtype

/-- Derive the two-perfect and normalization inputs from the literal definition
`L₁ = O²(M₁)` in 13.2.1, where T lies in the marked parabolic M₁. -/
theorem marked_residual_inputs (M₁ L₁ T : Subgroup G)
    (hdef : L₁ = (pResidual 2 M₁).map M₁.subtype) (hTM : T ≤ M₁) :
    IsPPerfect 2 L₁ ∧ T ≤ normalizer (L₁ : Set G) := by
  subst L₁
  refine ⟨isPPerfect_embedded_pResidual 2 M₁, hTM.trans ?_⟩
  have hn := (pResidual 2 M₁).le_normalizer_map M₁.subtype
  simpa only [normalizer_eq_top, ← MonoidHom.range_eq_map, range_subtype] using hn

/-- Source-facing version of the local calculation. Both marked subgroups
retain their definitions from 13.2.1. Besides subgroup containment and the
relative C-component hypothesis, the earlier inputs are the three alternatives
of 13.8.14, the two marked quotient orders, T-invariance of V₁, and the
normal-or-two-conjugates clause of 1.2.1(3). -/
theorem local_fitting_and_orbit_of_source_parabolic (H L L₁ K T V₁ : Subgroup G)
    (hKH : K ≤ H) (hLH : L₁ ≤ H) (hK : (K.subgroupOf H).IsCComponent)
    (halt : ResidualAlternatives H L L₁ (markedPlus L L₁ T))
    (ha6 : Nonempty ((L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6)) →
      Nat.card (L₁ ⧸ pCore 2 L₁) = 3)
    (hcover : IsTripleCoverSix (L ⧸ pCore 2 L) →
      Nat.card (markedPlus L L₁ T ⧸ pCore 2 (markedPlus L L₁ T)) = 3)
    (hdef : L₁ = (pResidual 2 (markedParabolic L T V₁)).map (markedParabolic L T V₁).subtype)
    (hTV : T ≤ normalizer (V₁ : Set G))
    (horbit : (K.subgroupOf H).Normal ∨
      (normalizer (K.subgroupOf H : Set H)).index = 2) :
    fittingSubgroup (Source.Hstar H) =
        (center (pResidual 2 (Source.Hstar H))).map (pResidual 2 (Source.Hstar H)).subtype ∧
      fittingSubgroup (Source.Hstar H) ≤ centralizer (Source.starImage H K : Set (Source.Hstar H)) ∧
      IsQuasisimple (Source.starImage H K) ∧
      L₁ ≤ normalizer (conjugateSpanBy K T : Set G) ∧
      ((conjugateSpanBy K T ⊔ (L₁ ⊔ T) : Subgroup G) : Set G) =
        (conjugateSpanBy K T : Set G) * (L₁ : Set G) * (T : Set G) := by
  obtain ⟨hp, hn⟩ := marked_residual_inputs (markedParabolic L T V₁) L₁ T hdef
    (le_inf le_sup_right hTV)
  exact local_fitting_and_orbit H L L₁ (markedPlus L L₁ T) K T
    hKH hLH hK halt ha6 hcover hp hn horbit

end CFSG.Quasithin.Chapter13.Section08.Components.Fitting

end
