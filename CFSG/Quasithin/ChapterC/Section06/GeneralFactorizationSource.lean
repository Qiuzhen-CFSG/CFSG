module

public import CFSG.Quasithin.ChapterC.Section06.GeneralFactorization
public import CFSG.Quasithin.ChapterC.Section06.GeneralLocal

/-!
# Applying the C.6.3 factorization to the actual source cores

The source subgroups are `U = [O₂(L), L]`, `Q = O₂(LR)` and
`D = C_R(L)`. Their containment, normalization and two-group properties
are derived from C.6.2 and the local core calculation. C.6.3(1) supplies
an escaping conjugate, and the elementary quotient in C.6.3(3)(b)
supplies its exact index. Applying the factorization and Frattini
arguments gives every structural conclusion of C.6.3(3)(i)--(iii).
Only the final assertion about maximal elementary abelian subgroups
requires the separate offender argument.

Source: Aschbacher--Smith, *The Classification of Quasithin Groups*,
combined manuscript (1 March 2004), C.6.2--C.6.3, printed pp. 166--167.
-/

open Subgroup Stellmacher
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterC
variable {G : Type*} [Group G]

/-- The commutator defining the source subgroup `U` lies in `L`. -/
public theorem c6_3_residual_core_le (L : Subgroup G) :
    ⁅(pCore 2 L).map L.subtype, L⁆ ≤ L :=
  le_normalizer_iff_commutator_le_right.mp ((map_subtype_le _).trans L.le_normalizer)

/-- Restricting the two-core of `LR` to `R` gives a normal subgroup. -/
public theorem c6_3_two_core_normal (L R : Subgroup G) :
    (((pCore 2 (↥(L ⊔ R))).map (L ⊔ R).subtype).subgroupOf R).Normal := by
  apply normal_subgroupOf_of_le_normalizer
  have hh := (pCore 2 (↥(L ⊔ R))).le_normalizer_map (L ⊔ R).subtype
  have h : L ⊔ R ≤ normalizer
      ((pCore 2 (↥(L ⊔ R))).map (L ⊔ R).subtype : Set G) := by
    simpa only [normalizer_eq_top, ← MonoidHom.range_eq_map, range_subtype] using hh
  exact le_sup_right.trans h

/-- The actual C.6.2 core supplies an escaping pair with the structural
conclusions of C.6.3(3)(iii). The quotient and its rank are exactly the hypothesis C.6.3(3)(b). -/
public theorem c6_3_source_structural_factorization
    (L R T Λ : Subgroup G) [Finite L] [Finite R] [Finite T] [Finite Λ]
    [IsElementaryAbelian 2 (⁅(pCore 2 L).map L.subtype, L⁆ : Subgroup G)]
    (hres : twoResidualAmbient L = L)
    (hU : ⁅(pCore 2 L).map L.subtype, L⁆ ≠ ⊥)
    (hQR : (pCore 2 (↥(L ⊔ R))).map (L ⊔ R).subtype ≤ R)
    (hRT : R ≤ T) (hTR : (R.subgroupOf T).Normal)
    (hTtwo : IsPGroup 2 T)
    (hTΛ : T ≤ normalizer (Λ : Set G))
    (hTL : T ≤ normalizer (L : Set G))
    (hno : ∀ W : Subgroup G, W ≠ ⊥ → W ≤ R →
      (W.subgroupOf (L ⊔ T)).Normal →
      ¬ Λ ⊓ normalizer (R : Set G) ≤ Λ ⊓ normalizer (W : Set G))
    (hi : (T ⊓ Λ).relIndex (Λ ⊓ normalizer (R : Set G)) = 2) :
    let U := ⁅(pCore 2 L).map L.subtype, L⁆
    let Q := (pCore 2 (↥(L ⊔ R))).map (L ⊔ R).subtype
    let D := R ⊓ centralizer (L : Set G)
    let S := L ⊔ R
    let : Finite U := Finite.of_injective (inclusion (c6_3_residual_core_le L))
      (inclusion_injective (c6_3_residual_core_le L))
    letI := c6_3_centralizer_normal L R (hRT.trans hTL)
    let f := QuotientGroup.mk' (D.subgroupOf S)
    letI := c6_3_two_core_normal L R
    Q = R ⊓ centralizer (U : Set G) →
    IsElementaryAbelian 2 (R ⧸ Q.subgroupOf R) →
    Group.rank (R ⧸ Q.subgroupOf R) = centralizerRankMinimum R U →
    frattini ((Q.subgroupOf S).map f) = ⊥ →
    ∃ x ∈ (Λ ⊓ normalizer (R : Set G)) ⊔ T,
      ¬ U.map (MulAut.conj x⁻¹ : G →* G) ≤ Q ∧
      R = U.map (MulAut.conj x⁻¹ : G →* G) ⊔ Q ∧
      Q = U ⊔ (Q ⊓ centralizer (U.map (MulAut.conj x⁻¹ : G →* G) : Set G)) ∧
      R = (U ⊔ U.map (MulAut.conj x⁻¹ : G →* G)) ⊔
        (R ⊓ centralizer ((U ⊔ U.map (MulAut.conj x⁻¹ : G →* G) : Subgroup G) : Set G)) ∧
      (((Q.subgroupOf S).map f ⊓ centralizer ((R.subgroupOf S).map f : Set _)
        ≤ (U.subgroupOf S).map f) → (U.subgroupOf S).map f = (Q.subgroupOf S).map f) ∧
      D ⊓ D.map (MulAut.conj x⁻¹ : G →* G) = ⊥ ∧
      frattini D = ⊥ ∧ IsElementaryAbelian 2 Q ∧
      R = Q ⊔ Q.map (MulAut.conj x⁻¹ : G →* G) := by
  intro U Q D S instU f hQ hRQ hrank hPhi
  let : (Q.subgroupOf R).Normal := c6_3_two_core_normal L R
  let : IsElementaryAbelian 2 (R ⧸ Q.subgroupOf R) := hRQ
  let : Finite U := Finite.of_injective (inclusion (c6_3_residual_core_le L))
    (inclusion_injective (c6_3_residual_core_le L))
  have hRL : R ≤ normalizer (L : Set G) := hRT.trans hTL
  have hTR' : T ≤ normalizer (R : Set G) :=
    (normal_subgroupOf_iff_le_normalizer hRT).mp hTR
  have hMU : L ≤ normalizer ((pCore 2 L).map L.subtype : Set G) := by
    have hh := (pCore 2 L).le_normalizer_map L.subtype
    simpa only [normalizer_eq_top, ← MonoidHom.range_eq_map, range_subtype] using hh
  have hUR : U ≤ R :=
    (le_normalizer_iff_commutator_le_left.mp hMU).trans
      ((c6_3_commutator_core_bound_local hRL hres).2.trans hQR)
  have hindex : Q.relIndex R = 2 ^ centralizerRankMinimum R U :=
    (c6_3_order_of_elementary_quotient R Q).trans (congrArg (2 ^ ·) hrank)
  obtain ⟨x, hx, hescape⟩ :=
    c6_3_exists_escaping_conjugate_local L R T Λ hRL hres hQR hU hRT hTR hno
  have hRU : R ≤ normalizer (U : Set G) := by
    intro r hr
    apply mem_normalizer_iff_map_conj_eq.mpr
    change (⁅(pCore 2 L).map L.subtype, L⁆).map (MulAut.conj r : G →* G) = _
    have hLM : r ∈ normalizer ((pCore 2 L).map L.subtype : Set G) := by
      have hn : normalizer (L : Set G) ≤
          normalizer ((pCore 2 L).map L.subtype : Set G) := by
        apply le_normalizer_iff.mpr
        intro g hg y hy
        obtain ⟨c, hc, rfl⟩ := hy
        let e := L.normalizerMonoidHom ⟨g, hg⟩
        exact ⟨e c, characteristic_iff_le_comap.mp inferInstance e hc, rfl⟩
      exact hn (hRL hr)
    rw [map_commutator, mem_normalizer_iff_map_conj_eq.mp hLM,
      mem_normalizer_iff_map_conj_eq.mp (hRL hr)]
  have hxR : x ∈ normalizer (R : Set G) := (sup_le inf_le_right hTR') hx
  have hfac := c6_3_factorization R U Q hUR hRU hQ x hxR hescape hindex
  let : (D.subgroupOf S).Normal := c6_3_centralizer_normal L R hRL
  have hquot := c6_3_quotient_factorization L R U Q hUR hRU hQ
    ((pCore_isPGroup (p := 2) (G := S)).map S.subtype) x hxR hescape hindex hPhi
  exact ⟨x, hx, hescape, hfac.1, hfac.2.2.1, hfac.2.2.2, hquot,
    c6_3_structure_of_residual_core L R T Λ U Q rfl hUR hRT hTtwo hTR'
      hTΛ hTL hQ hno hi x hx hescape hindex hPhi⟩

end CFSG.Quasithin.ChapterC
