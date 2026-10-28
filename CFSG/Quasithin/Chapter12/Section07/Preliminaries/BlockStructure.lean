module

public import CFSG.Quasithin.Chapter12.Section02.SourceHypotheses
public import CFSG.Quasithin.ChapterA.Section03.OddPrime.SourceModels
public import CFSG.Quasithin.ChapterC.Section01.BlockCohomology
public import CFSG.Quasithin.ChapterI.Section01.AlternatingCohomology
public import Theory.GroupTheory.DisjointCommutingProduct

/-!
# 12.7: characteristic generation and the Â₆ block calculation

This file records the two structural interfaces used by the 12.7 assembly.
The first is the literal order-three subgroup `theta`, including its ambient
transport and characteristicity.  The second is the C.1.13(b) calculation for
an exceptional Â₆ block.  The rank estimate is obtained from the actual block
cohomology theorem; the vanishing input is the checked I.1.6(9) theorem for a
faithful irreducible six-dimensional action.  The remaining source inputs are
left explicit so that the 12.7 assembly discharges them with the hypotheses
of 12.2.8 and 3.2.11.

Source: Aschbacher--Smith, combined manuscript, printed pp.798 and 839--840
(PDF pp.815 and 856--857), together with C.1.13(b), 3.2.11 and I.1.6(9).
-/

public section
noncomputable section

open Subgroup Theory.GroupTheory
open CFSG.Quasithin
open CFSG.Quasithin.ChapterA.Section03.OddPrime.SourceModels
open CFSG.Quasithin.ChapterC
open Representation Representation.OneCohomology
open scoped IsMulCommutative

namespace CFSG.Quasithin.Chapter12.Section07.Preliminaries.BlockStructure

universe u v

variable {G : Type u} [Group G]

/-- The ambient copy of the order-three subgroup of an actual subgroup. -/
def thetaAmbient (M : Subgroup G) : Subgroup G :=
  (theta M).map M.subtype

/-- The literal local centralizer `C_L(t)` used for the residual `L_t`. -/
def localCentralizer (L : Subgroup G) (t : G) : Subgroup G :=
  L ⊓ centralizer ({t} : Set G)

/-- The actual second factor `C_T(L)` in the Â₆ block product. -/
def blockCentralizer (L T : Subgroup G) : Subgroup G :=
  T ⊓ centralizer (L : Set G)

/-- The order-three subgroup is characteristic, by its literal generating set. -/
theorem theta_characteristic (M : Subgroup G) : (theta M).Characteristic := by
  apply Subgroup.characteristic_iff_map_le.mpr
  intro e
  rw [theta, MonoidHom.map_closure]
  apply (closure_le _).2
  rintro _ ⟨x, hx, rfl⟩
  apply Subgroup.subset_closure
  change orderOf (e x) = 3
  exact (e.orderOf_eq x).trans hx

theorem thetaAmbient_le (M : Subgroup G) : thetaAmbient M ≤ M := by
  intro x hx
  rcases hx with ⟨y, hy, rfl⟩
  exact y.property

/-- Transport an intrinsic 12.2.8 generation identity back to the ambient group. -/
theorem thetaAmbient_eq_of_subgroupOf_eq {L M : Subgroup G}
    (hLM : L ≤ M) (hgen : L.subgroupOf M = theta M) :
    L = thetaAmbient M := by
  calc
    L = (L.subgroupOf M).map M.subtype :=
      (map_subgroupOf_eq_of_le hLM).symm
    _ = (theta M).map M.subtype := congrArg (Subgroup.map M.subtype) hgen
    _ = thetaAmbient M := rfl

theorem theta_subgroupOf_characteristic {L M : Subgroup G}
    (hgen : L.subgroupOf M = theta M) :
    (L.subgroupOf M).Characteristic := by
  rw [hgen]
  exact theta_characteristic M

/-- 12.7.2(6), using the A.3.17 order-three definition of `theta`.

`h1228` is the exact generation branch supplied by the earlier 12.2.8
alternative.  No ambient conclusion is hidden in this theorem: the displayed
ambient equality is proved by transporting the intrinsic equality through the
actual subtype map, and `M` is definitionally the normalizer of `L`. -/
theorem source_1272_6 {L M : Subgroup G}
    (hblock : IsExceptionalAhat6Block L)
    (hM : M = Subgroup.normalizer (L : Set G))
    (h1228 : L.subgroupOf M = theta M) :
    L = thetaAmbient M ∧ (theta M).Characteristic ∧
      (L.subgroupOf M).Characteristic ∧ IsExceptionalAhat6Block L := by
  have hLM : L ≤ M := by
    rw [hM]
    exact Subgroup.le_normalizer
  refine ⟨thetaAmbient_eq_of_subgroupOf_eq hLM h1228, theta_characteristic M, ?_, hblock⟩
  exact theta_subgroupOf_characteristic h1228

/-- The pointwise content of 12.7.4(3), with `L_t` retained as an ambient
subgroup and `M_t` retained as its actual local overgroup. -/
theorem source_1274_3 {L V Lt Mt : Subgroup G} {t : G}
    (htV : t ∈ V) (hcomm : V = ⁅V, Lt⁆) (hVLt : ⁅V, Lt⁆ ≤ Lt)
    (hLMt : Lt ≤ Mt) (h1228 : Lt.subgroupOf Mt = theta Mt)
    (hres : Lt = (pResidual 2 (localCentralizer L t)).map
      (localCentralizer L t).subtype) :
    t ∈ V ∧ V = ⁅V, Lt⁆ ∧ ⁅V, Lt⁆ ≤ Lt ∧
      Lt = thetaAmbient Mt ∧ (Lt.subgroupOf Mt).Characteristic ∧
      Lt = (pResidual 2 (localCentralizer L t)).map
        (localCentralizer L t).subtype := by
  refine ⟨htV, hcomm, hVLt, thetaAmbient_eq_of_subgroupOf_eq hLMt h1228, ?_, hres⟩
  exact theta_subgroupOf_characteristic h1228

/-- The C.1.13(b) estimate and I.1.6(9) vanishing force the quotient by the
two displayed factors to be trivial.  This is stated in the intrinsic group
`Q`, which is the form in which the block theorem is applied. -/
theorem block_factors_eq_top_of_C113
    {L Q W P : Type*} [Group L] [Finite L] [Group Q] [Finite Q] [Group P]
    (U D : Subgroup Q) [(U ⊔ D).Normal]
    [IsElementaryAbelian 2 (Q ⧸ (U ⊔ D))]
    [AddCommGroup W] [Module (ZMod 2) W]
    [FiniteDimensional (ZMod 2) W]
    (ρ : Representation (ZMod 2) (L ⧸ pCore 2 L) W)
    (V : Subrepresentation ρ) (htrivial : HasTrivialQuotient V)
    (hperfect : IsPPerfect 2 (L ⧸ pCore 2 L)) (hP : IsPGroup 2 P)
    (displacement : fixed ρ → (L ⧸ pCore 2 L) →* P)
    (hdisplacement : Function.Injective displacement)
    (e : Additive (Q ⧸ (U ⊔ D)) ≃ₗ[ZMod 2] (W ⧸ V.toSubmodule))
    (hH1 : Module.finrank (ZMod 2) (H1 V.toRepresentation) = 0) :
    U ⊔ D = ⊤ := by
  have hbound := CFSG.Quasithin.ChapterC.block_quotient_rank_le_H1_of_twoPerfect_detection U D ρ V
    htrivial hperfect hP displacement hdisplacement e
  have hzero : Module.finrank (ZMod 2) (Additive (Q ⧸ (U ⊔ D))) = 0 := by
    omega
  have hsubadd : Subsingleton (Additive (Q ⧸ (U ⊔ D))) :=
    Module.finrank_zero_iff.mp hzero
  have hsub : Subsingleton (Q ⧸ (U ⊔ D)) := by
    constructor
    intro a b
    apply Additive.toMul.injective
    exact @Subsingleton.elim (Additive (Q ⧸ (U ⊔ D))) hsubadd
      (Additive.ofMul a) (Additive.ofMul b)
  exact QuotientGroup.subsingleton_iff.mp hsub

/-- The ambient form of the preceding quotient calculation. -/
theorem ambient_factors_eq_of_intrinsic
    {Q V C : Subgroup G} (hVQ : V ≤ Q) (hCQ : C ≤ Q)
    (hprod : V.subgroupOf Q ⊔ C.subgroupOf Q = ⊤) :
    Q = V ⊔ C := by
  have hm := congrArg (Subgroup.map Q.subtype) hprod
  have hm' : V ⊔ C = Q := by
    simpa only [Subgroup.map_sup, map_subgroupOf_eq_of_le hVQ,
      map_subgroupOf_eq_of_le hCQ, ← MonoidHom.range_eq_map,
      range_subtype] using hm
  exact hm'.symm

/-- The actual Â₆ first-cohomology input used by 12.7.6. -/
theorem alternatingSix_H1_zero
    {K W : Type*} [Group K] [Finite K] [IsQuasisimple K]
    [AddCommGroup W] [Module (ZMod 2) W]
    [FiniteDimensional (ZMod 2) W]
    (eK : K ⧸ Subgroup.center K ≃* alternatingGroup (Fin 6))
    (hcenter : Nat.card (Subgroup.center K) = 3)
    (ρ : Representation (ZMod 2) K W) [IsIrreducible ρ]
    (hfaithful : Function.Injective ρ)
    (hdim : Module.finrank (ZMod 2) W = 6) :
    Module.finrank (ZMod 2) (H1 ρ) = 0 :=
  CFSG.Quasithin.ChapterI.alternatingSixTripleCover_firstCohomology_eq_zero_of_centralQuotient
    eK hcenter ρ hfaithful hdim

/-- 12.7.6(1): the block factors commute and have trivial intersection, so the
actual 2-core is their internal product.  The first hypothesis is the output of
`block_factors_eq_top_of_C113`, hence this theorem does not assume the product
conclusion in place of C.1.13(b). -/
theorem source_1276_1 {L T V : Subgroup G}
    (hVQ : V ≤ (L ⊔ T).pCoreIn 2)
    (hCQ : blockCentralizer L T ≤ (L ⊔ T).pCoreIn 2)
    (hprod : V.subgroupOf ((L ⊔ T).pCoreIn 2) ⊔
      (blockCentralizer L T).subgroupOf ((L ⊔ T).pCoreIn 2) = ⊤)
    (hcomm : V ≤ centralizer ((blockCentralizer L T : Set G)))
    (hdisj : V ⊓ blockCentralizer L T = ⊥) :
    (L ⊔ T).pCoreIn 2 = V ⊔ blockCentralizer L T ∧
      ⁅V, blockCentralizer L T⁆ = ⊥ ∧
      V ⊓ blockCentralizer L T = ⊥ ∧
      ∃ e : V × blockCentralizer L T ≃*
          ↥(V ⊔ blockCentralizer L T),
        ∀ v c, (e (v, c) : G) = (v : G) * (c : G) := by
  let Q := (L ⊔ T).pCoreIn 2
  let C := blockCentralizer L T
  have hQ : Q = V ⊔ C := ambient_factors_eq_of_intrinsic hVQ hCQ hprod
  have hcomm' : ⁅V, C⁆ = ⊥ := commutator_eq_bot_iff_le_centralizer.mpr hcomm
  have hd : Disjoint V C := disjoint_iff_inf_le.mpr (by rw [hdisj])
  obtain ⟨e, he⟩ := exists_mulEquiv_prod_sup_of_disjoint_of_commuting V C hd hcomm
  exact ⟨hQ, hcomm', hdisj, e, he⟩

/-- 12.7.6(2), with the exact implication supplied by 3.2.11.  Once
`C_T(L)=1`, the first clause gives `O₂(LT)=V`; 3.2.11 then gives all four
ambient conclusions, including the distinction between `M` and `N_G(V)`. -/
theorem source_1276_2 {L M T V : Subgroup G}
    (hQ : (L ⊔ T).pCoreIn 2 = V ⊔ blockCentralizer L T)
    (hCT : blockCentralizer L T = ⊥)
    (h3211 : (L ⊔ T).pCoreIn 2 = V →
      L.pCoreIn 2 = V ∧ M.pCoreIn 2 = V ∧
        centralizer (V : Set G) = V ∧ M = L ⊔ T) :
    L.pCoreIn 2 = V ∧ M.pCoreIn 2 = V ∧
      centralizer (V : Set G) = V ∧ M = L ⊔ T := by
  have hQV : (L ⊔ T).pCoreIn 2 = V := by
    simpa [hCT] using hQ
  exact h3211 hQV

end CFSG.Quasithin.Chapter12.Section07.Preliminaries.BlockStructure

