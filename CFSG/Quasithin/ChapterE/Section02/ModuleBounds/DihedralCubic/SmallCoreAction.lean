module
public import CFSG.Quasithin.ChapterE.Section02.ModuleBounds.DihedralCubic.SmallCore
public import CFSG.Quasithin.ChapterE.Section02.ModuleBounds.DihedralCubic.SmallShape
public import CFSG.Quasithin.ChapterE.Section02.ModuleBounds.DihedralCubic.SmallAutomizerAction
public import Theory.GroupTheory.QuaternionCentralProductTransport
public import CFSG.Quasithin.ChapterE.Section02.ModuleBounds.DihedralCubic
public import Theory.GroupTheory.PCoreLocalSetup

/-!
# The marked quaternion core in the original chosen-module action

The small-automizer theorem is applied through the original quotient U/C_U(V)
and the literal inclusion of the source pair I. Both quaternion factors are
transported into the actual ambient O₂(I). The product U=O₂(I)C_U(V) and the
centralizer identity are unconditional under the marked pair inputs; the
commutator bound additionally records exactly the ambient normalization that
must be supplied by the E.2.17 extension step.

The chosen V is arbitrary, so this applies to V(M) in 15.1.4(1–5) and to
the moved four-space in case (6), without identifying those two subgroups.

Source: Aschbacher–Smith, E.2.17 and its application in 15.1.11,
printed pp.229 and 1085. The original minimal-parabolic witness and the
global normal-closure identification remain with source assembly.
-/

@[expose] public section
open Subgroup Representation.BinaryOffender
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.ChapterE.DihedralCubic
open TwoConjugate
variable {G D : Type*} [Group G] [Finite G] [Group D] [Finite D]
variable {I U V : Subgroup G} {S : Sylow 2 I} {N : Subgroup I} {g : I}

/-- The chosen source V gives embedded quaternion factors in the literal O₂(I),
its centralizer and product decomposition, and the commutator bound once the
remaining ambient normalization premise is supplied. -/
theorem ambient_small_quaternion_core [IsElementaryAbelian 2 V]
    (hVI : V ≤ I) (hn : U ≤ normalizer (V : Set G))
    (h : Hypotheses S (V.subgroupOf I) N g)
    (hSU : (S : Subgroup I).map I.subtype ≤ U)
    (hproper : V.subgroupOf I ≠ ⊤)
    (hfit : Theory.GroupTheory.generalizedFitting I = pCore 2 I)
    (hcard : Nat.card ((V.subgroupOf I).map (QuotientGroup.mk' (J N))) = 2)
    (hV : Nat.card V = 16)
    (q : U →* D) (hq : Function.Surjective q)
    (hk : q.ker = (centralizer (V : Set G)).subgroupOf U)
    (hD : Nat.card D ≤ 4)
    (hratio : 1 < cubicRatio (representation U V hn q hq hk)) :
    Nonempty (QuaternionCentralProductData (I.pCoreIn 2)) ∧
      U = I.pCoreIn 2 ⊔ (U ⊓ centralizer (V : Set G)) ∧
      I.pCoreIn 2 ⊓ centralizer (V : Set G) = I.pCoreIn 2 ⊓ V ∧
      (U ≤ normalizer (I.pCoreIn 2 : Set G) →
        ⁅U ⊓ centralizer (V : Set G), I.pCoreIn 2⁆ ≤ I.pCoreIn 2 ⊓ V) := by
  let e := subgroupOfEquivOfLe hVI
  let ρ := representation U V hn q hq hk
  let f := actorMap h hSU q
  have hρ := representation_injective U V hn q hq hk
  have ha (a : A (V.subgroupOf I) N g) (v : V.subgroupOf I) :
      (e.symm (ρ (f a) (Additive.ofMul (e v))).toMul : I) =
        (a : I) * v * (a : I)⁻¹ := by
    apply Subtype.ext
    change ((ρ (q (actorIn h hSU a)) (Additive.ofMul (e v))).toMul : G) =
      ((a : I) : G) * ((v : I) : G) * ((a : I) : G)⁻¹
    rw [representation_apply]
    rfl
  have hVi : Nat.card (V.subgroupOf I) = 16 := (Nat.card_congr e.toEquiv).trans hV
  obtain ⟨_, _, ⟨d⟩⟩ := h.small_automizer_quaternion_core
    hproper hfit hcard hVi e ρ hρ f ha hD hratio
  have hP : P (V.subgroupOf I) N g = pCore 2 I := (h.odd_dihedral hcard).1
  let eP : P (V.subgroupOf I) N g ≃* I.pCoreIn 2 :=
    (MulEquiv.subgroupCongr hP).trans
      ((pCore 2 I).equivMapOfInjective I.subtype I.subtype_injective)
  have hc := ambient_small_automizer hVI hn h hSU hproper hfit hcard hV q hq hk hD hratio
  refine ⟨⟨d.map eP⟩, hc.2.2.2.2, hc.2.2.2.1, ?_⟩
  intro hPN
  have hPU : I.pCoreIn 2 ≤ U := (pCoreIn_le_sylow I S).trans hSU
  rw [← hc.2.2.2.1]
  apply le_inf
  · exact le_normalizer_iff_commutator_le_right.mp (inf_le_left.trans hPN)
  · apply commutator_le.mpr
    intro r hr p hp
    let rU : U := ⟨r, hr.1⟩
    let pU : U := ⟨p, hPU hp⟩
    have hrK : rU ∈ q.ker := hk.symm ▸ hr.2
    have hcomm : ⁅rU, pU⁆ ∈ q.ker := by
      change q ⁅rU, pU⁆ = 1
      rw [map_commutatorElement, show q rU = 1 from hrK, commutatorElement_one_left]
    rw [hk] at hcomm
    exact hcomm

/-- The pair from the original chosen-module action has the actual order-six
quotient by its two-core, completing the local shape used in E.2.17. -/
theorem ambient_small_dihedral_quotient [IsElementaryAbelian 2 V]
    (hVI : V ≤ I) (hn : U ≤ normalizer (V : Set G))
    (h : Hypotheses S (V.subgroupOf I) N g)
    (hSU : (S : Subgroup I).map I.subtype ≤ U)
    (hproper : V.subgroupOf I ≠ ⊤)
    (hfit : Theory.GroupTheory.generalizedFitting I = pCore 2 I)
    (hcard : Nat.card ((V.subgroupOf I).map (QuotientGroup.mk' (J N))) = 2)
    (hV : Nat.card V = 16)
    (q : U →* D) (hq : Function.Surjective q)
    (hk : q.ker = (centralizer (V : Set G)).subgroupOf U)
    (hD : Nat.card D ≤ 4)
    (hratio : 1 < cubicRatio (representation U V hn q hq hk)) :
    Nonempty ((I ⧸ pCore 2 I) ≃* DihedralGroup 3) := by
  let e := subgroupOfEquivOfLe hVI
  let ρ := representation U V hn q hq hk
  let f := actorMap h hSU q
  have hρ := representation_injective U V hn q hq hk
  have ha (a : A (V.subgroupOf I) N g) (v : V.subgroupOf I) :
      (e.symm (ρ (f a) (Additive.ofMul (e v))).toMul : I) =
        (a : I) * v * (a : I)⁻¹ := by
    apply Subtype.ext
    change ((ρ (q (actorIn h hSU a)) (Additive.ofMul (e v))).toMul : G) =
      ((a : I) : G) * ((v : I) : G) * ((a : I) : G)⁻¹
    rw [representation_apply]
    rfl
  have hVi : Nat.card (V.subgroupOf I) = 16 := (Nat.card_congr e.toEquiv).trans hV
  obtain ⟨_, _, ⟨d⟩⟩ := h.small_automizer_quaternion_core
    hproper hfit hcard hVi e ρ hρ f ha hD hratio
  let := h.core_geometry.1
  obtain ⟨eQ⟩ := h.quotient_three_of_quaternion_core hproper hfit hcard d
  have hP : P (V.subgroupOf I) N g = pCore 2 I := (h.odd_dihedral hcard).1
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hP.symm).trans eQ⟩

end CFSG.Quasithin.ChapterE.DihedralCubic
