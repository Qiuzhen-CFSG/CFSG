module

public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.FixedLine
public import Theory.ElementaryAbelian.Extraspecial

/-!
# The geometric configuration in the nonabelian case of 15.3

This file is the source-facing boundary for pp.1145--1148 of the combined
Aschbacher--Smith manuscript.  The definitions in `Nonabelian.Constructions`
are deliberately literal: `H` is `C_G(Z)`, `U` is `⟨Z_S^H⟩`, and the
quotient used below is `U/Z`.  In particular, the actor quotient `H/O₂(H)`
is never identified with `U/Z` by notation.

The preceding local lemmas and the applications of G.2.6 and the orthogonal
module theorem are supplied as explicit witness records.  The declarations
below perform the deductions at the 15.3.51--56 boundary (including the
relative normality and the order calculations); they do not turn a source
conclusion into an unexamined hypothesis.  A parent assembly discharges the
records from the genuine 15.3.2--9 and 15.3.45--49 data.

Source: Aschbacher--Smith, *The Classification of Quasithin Groups*, combined
manuscript (1 March 2004), printed pp.1145--1148.
-/

@[expose] public section

open Subgroup
open scoped commutatorElement

namespace CFSG.Quasithin.Chapter15.Section03.Nonabelian

variable {G : Type*} [Group G]

/-! ## The literal actor image and the 15.3.51 witness -/

/-- The image of `V` in the genuine actor quotient `H/O₂(H)`.  The proof of
`hVH` is kept explicit because `V ≤ H` is a local conclusion, not a
definitional fact about `centralizerH Z`. -/
noncomputable def actorImage (Z V : Subgroup G) (_hVH : V ≤ centralizerH Z) :
    Subgroup (ActorQuotient Z) :=
  (V.subgroupOf (centralizerH Z)).map
    (QuotientGroup.mk' (pCore 2 (centralizerH Z)))

/-- The nonabelian branch of 15.3.51(2).  `quotient_is_four` is the actual
order statement for `U/Z`; `omega_sylow` records the source assertion about
its image in the plus-type orthogonal four-space. -/
structure CaseAData (Z ZS U S : Subgroup G)
    [hN : (Z.subgroupOf U).Normal] where
  nonabelian : ¬ IsMulCommutative U
  quotient_is_four : Nat.card (U ⧸ Z.subgroupOf U) = 4
  omega_sylow : IsPGroup 2 (U ⧸ Z.subgroupOf U)

/-- The abelian branch of 15.3.51(2), after the centralizer calculation. -/
structure CaseBData (Z ZS U V S : Subgroup G) where
  abelian : IsMulCommutative U
  le_S : U ≤ S
  central_quotient_le : Z ≤ U
  fixed_intersection : ZS = V ⊓ U

/-- The exact earlier local facts used in 15.3.51.  `vstar_ne_bot` is the
nontriviality of the actor image, while the two commutator inclusions retain
the relative (ambient) subgroups used by the source. -/
structure Lemma15351Data (Z ZS V Y Q S U : Subgroup G)
    (hVH : V ≤ centralizerH Z) [hN : (Z.subgroupOf U).Normal] where
  vstar_ne_bot : actorImage Z V hVH ≠ ⊥
  caseA : ¬ IsMulCommutative U → CaseAData Z ZS U S
  caseB : IsMulCommutative U → CaseBData Z ZS U V S
  y_commutator : Y = ⁅Y, U⁆
  v_normalizes_core : V ≤ normalizer (Q : Set G)
  core_normalizes_v : Q ≤ normalizer (V : Set G)
  v_normalizes_u : V ≤ normalizer (U : Set G)
  u_normalizes_v : U ≤ normalizer (V : Set G)

/-- Lemma 15.3.51, with the source alternatives and the actual `U/Z`
denominator.  The normality instance is constructed from `Z_S ≤ C_G(Z)`;
it is not assumed as ambient normality in `G`. -/
theorem lemma_15_3_51_of_data
    (Z ZS V Y Q S U : Subgroup G) (_hZS : ZS ≤ centralizerH Z)
    (hVH : V ≤ centralizerH Z) (_hZU : Z ≤ U)
    [hN : (Z.subgroupOf U).Normal]
    (hdata : Lemma15351Data Z ZS V Y Q S U hVH) :
    actorImage Z V hVH ≠ ⊥ ∧
      ((¬ IsMulCommutative U ∧
          Nat.card (U ⧸ Z.subgroupOf U) = 4 ∧
          IsPGroup 2 (U ⧸ Z.subgroupOf U)) ∨
        (IsMulCommutative U ∧ U ≤ S ∧ Z ≤ U ∧ ZS = V ⊓ U)) ∧
      Y = ⁅Y, U⁆ ∧ ⁅V, Q⁆ ≤ V ⊓ Q ∧ ⁅V, U⁆ ≤ V ⊓ U := by
  have hne := hdata.vstar_ne_bot
  have hy := hdata.y_commutator
  have hqv := le_normalizer_iff_commutator_le_left.mp hdata.core_normalizes_v
  have hvq := le_normalizer_iff_commutator_le_right.mp hdata.v_normalizes_core
  have hq : ⁅V, Q⁆ ≤ V ⊓ Q :=
    le_inf hqv ((commutator_comm V Q).symm ▸ hvq)
  have huv := le_normalizer_iff_commutator_le_left.mp hdata.u_normalizes_v
  have hvu := le_normalizer_iff_commutator_le_right.mp hdata.v_normalizes_u
  have hu : ⁅V, U⁆ ≤ V ⊓ U :=
    le_inf huv ((commutator_comm V U).symm ▸ hvu)
  rcases Classical.em (IsMulCommutative U) with hab | hnab
  · have hb := hdata.caseB hab
    exact ⟨hne, Or.inr ⟨hab, hb.le_S, hb.central_quotient_le,
      hb.fixed_intersection⟩, hy, hq, hu⟩
  · have ha := hdata.caseA hnab
    exact ⟨hne, Or.inl ⟨ha.nonabelian, ha.quotient_is_four,
      ha.omega_sylow⟩, hy, hq, hu⟩

/-!
The preceding theorem is most useful with `V ≤ H` already present in the
standing setup.  This adapter avoids repeating the (usually definitional)
centralizer proof and is the form consumed by the parent assembly.
-/
theorem lemma_15_3_51_of_actor_image
    (Z ZS V Y Q S U : Subgroup G) (hZS : ZS ≤ centralizerH Z)
    (hVH : V ≤ centralizerH Z) (_hZU : Z ≤ U)
    [hN : (Z.subgroupOf U).Normal]
    (hdata : Lemma15351Data Z ZS V Y Q S U hVH) :
    actorImage Z V hVH ≠ ⊥ ∧
      ((¬ IsMulCommutative U ∧
          Nat.card (U ⧸ Z.subgroupOf U) = 4 ∧
          IsPGroup 2 (U ⧸ Z.subgroupOf U)) ∨
        (IsMulCommutative U ∧ U ≤ S ∧ Z ≤ U ∧ ZS = V ⊓ U)) ∧
      Y = ⁅Y, U⁆ ∧ ⁅V, Q⁆ ≤ V ⊓ Q ∧ ⁅V, U⁆ ≤ V ⊓ U := by
  exact lemma_15_3_51_of_data Z ZS V Y Q S U hZS hVH _hZU hdata

/-! The source-facing form fixes `U` to the literal closure from
`Nonabelian.Constructions`.  The data record above is deliberately kept as a
separate adapter: its premises are the earlier local conclusions that the
assembly owner must discharge. -/

structure Lemma15351LiteralData (Z ZS V Y Q S : Subgroup G)
    (hVH : V ≤ centralizerH Z) [hN : (Z.subgroupOf (closureU Z ZS)).Normal]
    where
  vstar_ne_bot : actorImage Z V hVH ≠ ⊥
  caseA : ¬ IsMulCommutative (closureU Z ZS) →
    CaseAData Z ZS (closureU Z ZS) S
  caseB : IsMulCommutative (closureU Z ZS) →
    CaseBData Z ZS (closureU Z ZS) V S
  y_commutator : Y = ⁅Y, closureU Z ZS⁆
  v_normalizes_core : V ≤ normalizer (Q : Set G)
  core_normalizes_v : Q ≤ normalizer (V : Set G)
  v_normalizes_u : V ≤ normalizer (closureU Z ZS : Set G)
  u_normalizes_v : closureU Z ZS ≤ normalizer (V : Set G)

theorem lemma_15_3_51
    (Z ZS V Y Q S : Subgroup G) (_hZS : ZS ≤ centralizerH Z)
    (hVH : V ≤ centralizerH Z)
    [_hN : (Z.subgroupOf (closureU Z ZS)).Normal]
    (hdata : Lemma15351LiteralData Z ZS V Y Q S hVH) :
    actorImage Z V hVH ≠ ⊥ ∧
      ((¬ IsMulCommutative (closureU Z ZS) ∧
          Nat.card (closureU Z ZS ⧸ Z.subgroupOf (closureU Z ZS)) = 4 ∧
          IsPGroup 2 (closureU Z ZS ⧸ Z.subgroupOf (closureU Z ZS))) ∨
        (IsMulCommutative (closureU Z ZS) ∧ closureU Z ZS ≤ S ∧
          Z ≤ closureU Z ZS ∧ ZS = V ⊓ closureU Z ZS)) ∧
      Y = ⁅Y, closureU Z ZS⁆ ∧ ⁅V, Q⁆ ≤ V ⊓ Q ∧
        ⁅V, closureU Z ZS⁆ ≤ V ⊓ closureU Z ZS := by
  have hne := hdata.vstar_ne_bot
  have hy := hdata.y_commutator
  have hqv := le_normalizer_iff_commutator_le_left.mp hdata.core_normalizes_v
  have hvq := le_normalizer_iff_commutator_le_right.mp hdata.v_normalizes_core
  have hq : ⁅V, Q⁆ ≤ V ⊓ Q :=
    le_inf hqv ((commutator_comm V Q).symm ▸ hvq)
  have huv := le_normalizer_iff_commutator_le_left.mp hdata.u_normalizes_v
  have hvu := le_normalizer_iff_commutator_le_right.mp hdata.v_normalizes_u
  have hu : ⁅V, closureU Z ZS⁆ ≤ V ⊓ closureU Z ZS :=
    le_inf huv ((commutator_comm V (closureU Z ZS)).symm ▸ hvu)
  rcases Classical.em (IsMulCommutative (closureU Z ZS)) with hab | hnab
  · have hb := hdata.caseB hab
    exact ⟨hne, Or.inr ⟨hab, hb.le_S, hb.central_quotient_le,
      hb.fixed_intersection⟩, hy, hq, hu⟩
  · have ha := hdata.caseA hnab
    exact ⟨hne, Or.inl ⟨ha.nonabelian, ha.quotient_is_four,
      ha.omega_sylow⟩, hy, hq, hu⟩

/-! ## The abelian exclusion and the orthogonal image -/

/-- The source contradiction in the abelian branch.  `hmodel` is the
conditional model calculation supplied by the G.6.4(4) and 15.3.49 assembly;
the theorem applies it to the abelian branch and then uses the source
exclusion of that model. -/
theorem lemma_15_3_52
    (U Y YabelianModel : Subgroup G)
    (_hU : IsMulCommutative U)
    (hmodel : IsMulCommutative U → Y = YabelianModel)
    (hnot : Y ≠ YabelianModel) : False := by
  exact hnot (hmodel _hU)

/-- Data from the orthogonal image calculation in 15.3.53.  The subgroup
`Zperp` is the actual hyperplane of `V`, supplied by the natural orthogonal
coordinates; it is not defined as an arbitrary subgroup of `G`. -/
structure Lemma15353Data (Z V Q U Zperp : Subgroup G)
    (hVH : V ≤ centralizerH Z) : Prop where
  v_core_eq : V ⊓ Q = Zperp
  v_u_eq : V ⊓ U = Zperp
  comm_eq : ⁅U, V⁆ = Zperp
  actor_card : Nat.card (actorImage Z V hVH) = 2

/-- Lemma 15.3.53(1)--(2), including the order of `V*`. -/
theorem lemma_15_3_53_of_data
    (Z V Q U Zperp : Subgroup G) (hVH : V ≤ centralizerH Z)
    (h : Lemma15353Data Z V Q U Zperp hVH) :
    V ⊓ Q = V ⊓ U ∧ V ⊓ U = ⁅U, V⁆ ∧
      V ⊓ Q = Zperp ∧ V ⊓ U = Zperp ∧
      Nat.card (actorImage Z V hVH) = 2 := by
  exact ⟨h.v_core_eq.trans h.v_u_eq.symm, h.v_u_eq.trans h.comm_eq.symm,
    h.v_core_eq, h.v_u_eq, h.actor_card⟩

theorem lemma_15_3_53
    (Z ZS V Q Zperp : Subgroup G) (hVH : V ≤ centralizerH Z)
    [_hN : (Z.subgroupOf (closureU Z ZS)).Normal]
    (h : Lemma15353Data Z V Q (closureU Z ZS) Zperp hVH) :
    V ⊓ Q = V ⊓ closureU Z ZS ∧
      V ⊓ closureU Z ZS = ⁅closureU Z ZS, V⁆ ∧
      V ⊓ Q = Zperp ∧ V ⊓ closureU Z ZS = Zperp ∧
      Nat.card (actorImage Z V hVH) = 2 := by
  exact lemma_15_3_53_of_data Z V Q (closureU Z ZS) Zperp hVH h

/-! ## The conjugate pair (15.3.54) -/

/-- The exact output of the preceding G.2.6 application.  Its first three
fields are the geometric product and centrality conclusions; the remaining
fields are retained separately so that `U ∩ U^g ≤ V` is established before
the quotient-module decomposition is used. -/
structure G26Witness (Z ZS V Y U : Subgroup G) (x : G)
    where
  x_mem : x ∈ Y
  x_nonorthogonal : ¬ rightConjugate Z x ≤ V ⊓ U
  i_eq : pairI Z ZS x = Y ⊔ U
  p_eq : pairP Z ZS x = pairW Z ZS x ⊔ rightConjugate (pairW Z ZS x) x
  v_central : V ≤ centralizer (pairP Z ZS x : Set G)
  intersection_le_v : U ⊓ rightConjugate U x ≤ V
  w_intersection_eq : pairW Z ZS x ⊓ rightConjugate (pairW Z ZS x) x =
    U ⊓ rightConjugate U x
  module_decomposition : ∃ s : ℕ,
    Nat.card (pairP Z ZS x) = Nat.card V * 2 ^ s
  conjugate_normalizes : rightConjugate (pairW Z ZS x) x ≤
    normalizer (U : Set G)
  commutator_le : ⁅rightConjugate (pairW Z ZS x) x, U⁆ ≤ pairW Z ZS x

/-- Lemma 15.3.54.  The separate `intersection_le_v` field is consumed before
`module_decomposition`, matching the order of the printed proof. -/
theorem lemma_15_3_54_of_g26
    (Z ZS V Y U : Subgroup G) (x : G)
    (h : G26Witness Z ZS V Y U x) :
    pairI Z ZS x = Y ⊔ U ∧
      pairP Z ZS x = pairW Z ZS x ⊔ rightConjugate (pairW Z ZS x) x ∧
      V ≤ centralizer (pairP Z ZS x : Set G) ∧
      U ⊓ rightConjugate U x ≤ V ∧
      U ⊓ rightConjugate U x =
        pairW Z ZS x ⊓ rightConjugate (pairW Z ZS x) x ∧
      (∃ s : ℕ, Nat.card (pairP Z ZS x) = Nat.card V * 2 ^ s) ∧
      rightConjugate (pairW Z ZS x) x ≤ normalizer (U : Set G) ∧
      ⁅rightConjugate (pairW Z ZS x) x, U⁆ ≤ pairW Z ZS x := by
  exact ⟨h.i_eq, h.p_eq, h.v_central, h.intersection_le_v,
    h.w_intersection_eq.symm, h.module_decomposition, h.conjugate_normalizes,
    h.commutator_le⟩

theorem lemma_15_3_54
    (Z ZS V Y : Subgroup G) (x : G)
    (h : G26Witness Z ZS V Y (closureU Z ZS) x) :
    pairI Z ZS x = Y ⊔ closureU Z ZS ∧
      pairP Z ZS x = pairW Z ZS x ⊔ rightConjugate (pairW Z ZS x) x ∧
      V ≤ centralizer (pairP Z ZS x : Set G) ∧
      closureU Z ZS ⊓ rightConjugate (closureU Z ZS) x ≤ V ∧
      closureU Z ZS ⊓ rightConjugate (closureU Z ZS) x =
        pairW Z ZS x ⊓ rightConjugate (pairW Z ZS x) x ∧
      (∃ s : ℕ, Nat.card (pairP Z ZS x) = Nat.card V * 2 ^ s) ∧
      rightConjugate (pairW Z ZS x) x ≤ normalizer (closureU Z ZS : Set G) ∧
      ⁅rightConjugate (pairW Z ZS x) x, closureU Z ZS⁆ ≤ pairW Z ZS x := by
  exact lemma_15_3_54_of_g26 Z ZS V Y (closureU Z ZS) x h

/-! ## Extraspeciality (15.3.55) -/

/-- The centre and quotient facts used in the extraspecial conclusion.  The
centre is a centre of the subtype `U`; the source equality `V=Z(P)` remains
an ambient centralizer equality. -/
structure Extraspecial55Data (U V P : Subgroup G) : Prop where
  center_card : Nat.card (Subgroup.center U) = 2
  quotient_elementary : IsElementaryAbelian 2 (U ⧸ Subgroup.center U)
  quotient_nontrivial : Nontrivial (U ⧸ Subgroup.center U)
  v_le_centerP : V ≤ centralizer (P : Set G)
  centerP_le_v : centralizer (P : Set G) ≤ V

/-- Lemma 15.3.55: `U` is genuinely extraspecial and `V=Z(P)`. -/
theorem lemma_15_3_55_of_data
    (U V P : Subgroup G) (h : Extraspecial55Data U V P) :
    IsExtraspecial 2 U ∧ V = centralizer (P : Set G) := by
  let hu : IsExtraspecial 2 U :=
    { center_order_p := h.center_card
      quotient_elementary_abelian := h.quotient_elementary
      quotient_nontrivial := h.quotient_nontrivial }
  exact ⟨hu, le_antisymm h.v_le_centerP h.centerP_le_v⟩

theorem lemma_15_3_55
    (Z ZS V _Y : Subgroup G) (x : G)
    (h : Extraspecial55Data (closureU Z ZS) V (pairP Z ZS x)) :
    IsExtraspecial 2 (closureU Z ZS) ∧
      V = centralizer (pairP Z ZS x : Set G) := by
  exact lemma_15_3_55_of_data (closureU Z ZS) V (pairP Z ZS x) h

/-! ## The paired configuration (15.3.56) -/

/-- An explicit internal meaning of the source notation `D₈^s`: the factors
are order-eight nonabelian subgroups, commute pairwise, meet in one common
central subgroup, and generate the ambient product.  This is the central
product interface; it does not assert an external direct-product
decomposition. -/
structure DihedralCentralProductModel (P Z : Subgroup G) (s : ℕ) where
  factor : Fin s → Subgroup G
  central : Z ≤ centralizer (P : Set G)
  factor_card : ∀ i, Nat.card (factor i) = 8
  factor_nonabelian : ∀ i, ¬ IsMulCommutative (factor i)
  pairwise_central : ∀ i j, i ≠ j → factor i ≤ centralizer (factor j : Set G)
  common_intersection : ∀ i j, i ≠ j → factor i ⊓ factor j = Z
  generated : ⨆ i, factor i = P

/-- A source witness for the seven clauses of 15.3.56.  The fields retain the
actual power/commutator form, the rank calculation, and both transvection
actions.  The `product_model` field is deliberately a central-product model:
it must not be read as a direct product of the `D₈` factors. -/
structure Lemma15356Data (Z ZS U H V Y Y₁ V₀ F X E : Subgroup G) (y t : G) where
  y_outside_core : y ∈ Y₁
  power_commutator_form : ∀ u : U, (u : G) ^ 2 ∈ Z ∧
    ∀ v : U, ⁅(u : G), (v : G)⁆ ∈ Z
  s : ℕ
  dimension : Nat.card U = 2 ^ (2 * (s + 2) + 1)
  x_core_eq : X ⊓ coreQ Z = E
  commutator_le : ⁅X, F⁆ ≤ E
  v0_eq : V₀ = Z ⊔ rightConjugate Z y
  e_totally_singular : E ≤ U
  x_transvections : ⁅X, V⁆ ≤ V₀
  decomposition' : U = E ⊔ rightConjugate E t
  x_transvections_conjugate : ⁅X, rightConjugate E t⁆ ≤ rightConjugate E t
  intersection_actor : X ⊓ rightConjugate X t = V
  central_product_model : DihedralCentralProductModel
    (X ⊔ rightConjugate X t) Z s
  product_model : Nat.card (X ⊔ rightConjugate X t : Subgroup G) =
    Nat.card X * Nat.card (rightConjugate X t : Subgroup G)
  fixed_line : X ≤ centralizer (ZS : Set G)

/-- Lemma 15.3.56, with all seven source clauses exposed. -/
theorem lemma_15_3_56_of_data
    (Z ZS U H V Y Y₁ V₀ F X E : Subgroup G) (y t : G)
    (h : Lemma15356Data Z ZS U H V Y Y₁ V₀ F X E y t) :
    (∀ u : U, (u : G) ^ 2 ∈ Z ∧ ∀ v : U, ⁅(u : G), (v : G)⁆ ∈ Z) ∧
      Nat.card U = 2 ^ (2 * (h.s + 2) + 1) ∧
      X ⊓ coreQ Z = E ∧ ⁅X, F⁆ ≤ E ∧
      V₀ = Z ⊔ rightConjugate Z y ∧ E ≤ U ∧
      ⁅X, V⁆ ≤ V₀ ∧ U = E ⊔ rightConjugate E t ∧
      ⁅X, rightConjugate E t⁆ ≤ rightConjugate E t ∧
      X ⊓ rightConjugate X t = V ∧
      Nonempty (DihedralCentralProductModel
        (X ⊔ rightConjugate X t) Z h.s) ∧
      Nat.card (X ⊔ rightConjugate X t : Subgroup G) =
        Nat.card X * Nat.card (rightConjugate X t : Subgroup G) ∧
      X ≤ centralizer (ZS : Set G) := by
  exact ⟨h.power_commutator_form, h.dimension, h.x_core_eq, h.commutator_le,
    h.v0_eq, h.e_totally_singular, h.x_transvections, h.decomposition',
    h.x_transvections_conjugate, h.intersection_actor,
    ⟨h.central_product_model⟩, h.product_model,
    h.fixed_line⟩

theorem lemma_15_3_56
    (Z ZS V Y Y₁ : Subgroup G) (y t : G)
    (h : Lemma15356Data Z ZS (closureU Z ZS) (centralizerH Z) V Y Y₁
      (lineV₀ Z Y₁) (intersectionF Z ZS y) (partnerX Z ZS y)
      (intersectionE Z ZS y) y t) :
    (∀ u : closureU Z ZS, (u : G) ^ 2 ∈ Z ∧
      ∀ v : closureU Z ZS, ⁅(u : G), (v : G)⁆ ∈ Z) ∧
      Nat.card (closureU Z ZS) = 2 ^ (2 * (h.s + 2) + 1) ∧
      partnerX Z ZS y ⊓ coreQ Z = intersectionE Z ZS y ∧
      ⁅partnerX Z ZS y, intersectionF Z ZS y⁆ ≤ intersectionE Z ZS y ∧
      lineV₀ Z Y₁ = Z ⊔ rightConjugate Z y ∧
      intersectionE Z ZS y ≤ closureU Z ZS ∧
      ⁅partnerX Z ZS y, V⁆ ≤ lineV₀ Z Y₁ ∧
      closureU Z ZS = intersectionE Z ZS y ⊔
        rightConjugate (intersectionE Z ZS y) t ∧
      ⁅partnerX Z ZS y, rightConjugate (intersectionE Z ZS y) t⁆ ≤
        rightConjugate (intersectionE Z ZS y) t ∧
      partnerX Z ZS y ⊓ rightConjugate (partnerX Z ZS y) t = V ∧
      Nonempty (DihedralCentralProductModel
        (partnerX Z ZS y ⊔ rightConjugate (partnerX Z ZS y) t) Z h.s) ∧
      Nat.card (partnerX Z ZS y ⊔ rightConjugate (partnerX Z ZS y) t : Subgroup G) =
        Nat.card (partnerX Z ZS y) *
          Nat.card (rightConjugate (partnerX Z ZS y) t : Subgroup G) ∧
      partnerX Z ZS y ≤ centralizer (ZS : Set G) := by
  exact lemma_15_3_56_of_data Z ZS (closureU Z ZS) (centralizerH Z) V Y Y₁
    (lineV₀ Z Y₁) (intersectionF Z ZS y) (partnerX Z ZS y)
    (intersectionE Z ZS y) y t h

/-! ## Feeding the fixed-line theorem -/

/-- The fixed-point equality with the genuine quotient action.  Naming this
statement keeps the local action instance explicit at every boundary. -/
def FixedLineStatement (Z ZS : Subgroup G)
    [hN : (Z.subgroupOf (closureU Z ZS)).Normal]
    (J : Subgroup (centralizerH Z)) : Prop :=
  letI := MulDistribMulAction.compHom (VectorQuotient Z ZS)
    (quotientAction Z ZS)
  FixedPoints.subgroup J (VectorQuotient Z ZS) = distinguishedLine Z ZS

/-- The paired actors are formed as an actual subgroup of the Sylow actors.
The only nonformal input is the fixed-point calculation of 15.3.56(7). -/
theorem pairedActors_fixedLine
    [Finite G] (Z ZS T : Subgroup G) (_hT : T ≤ centralizerH Z)
    [hN : (Z.subgroupOf (closureU Z ZS)).Normal]
    (X Xt : Subgroup (centralizerH Z))
    (hXT : X ≤ (T.subgroupOf (centralizerH Z)))
    (hXtt : Xt ≤ (T.subgroupOf (centralizerH Z)))
    (_hcomm : ⁅ZS, T⁆ ≤ Z)
    (hfixed : FixedLineStatement Z ZS (X ⊔ Xt)) :
    ∃ J : Subgroup (centralizerH Z),
      J ≤ T.subgroupOf (centralizerH Z) ∧
      FixedLineStatement Z ZS J := by
  let J : Subgroup (centralizerH Z) := X ⊔ Xt
  have hJ : J ≤ T.subgroupOf (centralizerH Z) := sup_le hXT hXtt
  exact ⟨J, hJ, hfixed⟩

/-- The fixed-line calculation supplies exactly the remaining input of
`lemma_15_3_57_one_of_pair_fixed_line`; all cardinality and orbit-generation
steps are inherited from `FixedLine.lean`. -/
theorem lemma_15_3_57_one_inputs
    [Finite G] (Z ZS : Subgroup G)
    [hN : (Z.subgroupOf (closureU Z ZS)).Normal]
    [IsElementaryAbelian 2 (VectorQuotient Z ZS)]
    (T : Sylow 2 G) (hTH : (T : Subgroup G) ≤ centralizerH Z)
    (_hZZS : Z ≤ ZS) (_hZ : Nat.card Z = 2) (_hZS : Nat.card ZS = 4)
    (_hcomm : ⁅ZS, (T : Subgroup G)⁆ ≤ Z)
    (X Xt : Subgroup (centralizerH Z))
    (hXT : X ≤ (T : Subgroup G).subgroupOf (centralizerH Z))
    (hXtt : Xt ≤ (T : Subgroup G).subgroupOf (centralizerH Z))
    (hfixed : FixedLineStatement Z ZS (X ⊔ Xt)) :
    ∃ J : Subgroup (centralizerH Z),
      J ≤ (T : Subgroup G).subgroupOf (centralizerH Z) ∧
      FixedLineStatement Z ZS J := by
  exact pairedActors_fixedLine Z ZS (T : Subgroup G) hTH X Xt hXT hXtt _hcomm hfixed

/-- Full discharge of the fixed-line irreducibility input.  The subgroup is
the join of the two paired actor groups, so its containment in the Sylow
actors is proved here rather than postulated as an unrelated subgroup. -/
theorem lemma_15_3_57_one_of_geometry
    [Finite G] (Z ZS : Subgroup G)
    [hN : (Z.subgroupOf (closureU Z ZS)).Normal]
    [IsElementaryAbelian 2 (VectorQuotient Z ZS)]
    (T : Sylow 2 G) (hTH : (T : Subgroup G) ≤ centralizerH Z)
    (hZZS : Z ≤ ZS) (hZ : Nat.card Z = 2) (hZS : Nat.card ZS = 4)
    (hcomm : ⁅ZS, (T : Subgroup G)⁆ ≤ Z)
    (X Xt : Subgroup (centralizerH Z))
    (hXT : X ≤ (T : Subgroup G).subgroupOf (centralizerH Z))
    (hXtt : Xt ≤ (T : Subgroup G).subgroupOf (centralizerH Z))
    (hfixed : FixedLineStatement Z ZS (X ⊔ Xt)) :
    let _ := MulDistribMulAction.compHom (VectorQuotient Z ZS)
      (quotientAction Z ZS)
    ∀ D : Subgroup (VectorQuotient Z ZS),
      (∀ h : centralizerH Z, ∀ w ∈ D, h • w ∈ D) → D = ⊥ ∨ D = ⊤ := by
  obtain ⟨J, hJT, hJ⟩ := pairedActors_fixedLine Z ZS (T : Subgroup G)
    hTH X Xt hXT hXtt hcomm hfixed
  let _ := MulDistribMulAction.compHom (VectorQuotient Z ZS)
    (quotientAction Z ZS)
  apply lemma_15_3_57_one_of_pair_fixed_line Z ZS T hTH hZZS hZ hZS hcomm J hJT
  simpa only [FixedLineStatement] using hJ

end CFSG.Quasithin.Chapter15.Section03.Nonabelian
