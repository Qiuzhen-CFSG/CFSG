module

public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.WeakClosureBounds.ModuleBound.QuotientAction
public import Theory.GroupTheory.GeneralizedFitting.Defs
public import Theory.GroupTheory.PResidual.Defs

/-!
# Source hypotheses used to apply F.9 in Section 15.3

`SourceF91` spells out all of F.9.1, with Y, Z_S and Z in the roles of
L, V_+ and V_1. The ambient group is finite and T is Sylow. The residual
L_1 is O^2(C_Y(Z)); R_2 means a normal elementary abelian subgroup with
O_2 of its centralizer quotient trivial. Every normality and normal core
is taken inside the stated local group. Irreducibility of Z_S/Z is
expressed by the absence of intermediate invariant subgroups. The included
containment V <= T is the usual consequence of V in R_2(YT) and is already
available in Section 15.3. These are hypotheses, not assertions of F.9.1.

`SourceF98` retains both alternatives of (g). We prove (f) from 15.3.62(2)
using the nontrivial subgroup Z of V intersect V^g, and (g)(ii) by restricting
15.3.47 from C_G(Z_S) to C_H(Z_S). The notation [V,x] means [V,<x>].

`F9163Input` is an explicit earlier-theorem implication: under F.9.8 it
supplies B <= O_2((YT) intersect H) whose image in H/O_2(H) belongs to
Q(H*,U_H/Z). We spell out Q using Definition D.2.1: nontrivial elementary
abelian image, quadratic action, and fixed codimension at most twice its
rank. The representation is the literal quotient action. This input does
not assume the global ratio bound. The F.9 assembly owners must supply
this implication; Section09 currently exports only F.9.7.

`Earlier48Input` retains the side condition of 15.3.48 in the two cases of
15.3.7: either O_2(Y)=C_Y(V), or C_Y(V)<=H. It requests exactly 15.3.48(1)
and (3). The equality supplied by 15.3.49(3) discharges this side condition
in the application; no case-(2) containment is silently assumed.

Sources: Aschbacher--Smith, combined manuscript (1 March 2004), F.9.1,
F.9.8 and F.9.16(3), printed pp.317--324; Definition D.2.1, pp.177--178;
15.3.47--49, pp.1141--1142; and the application on p.1151.
-/

@[expose] public section
open Subgroup
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.ModuleBound
variable {G : Type*} [Group G]

/-- The source L₁=O²(C_Y(Z)), embedded from its own ambient group. -/
noncomputable def residualCentralizer (Y Z : Subgroup G) : Subgroup G :=
  (pResidual 2 (Y ⊓ centralizer (Z : Set G) : Subgroup G)).map
    (Y ⊓ centralizer (Z : Set G)).subtype

/-- Every clause of F.9.1, specialized to the Section 15.3 names. The field
`v_reduced` is B.2.11, and `a_kernel` is a normal core inside H. -/
structure SourceF91 [Finite G] (T : Sylow 2 G) (Y V ZS Z H : Subgroup G)
    [IsElementaryAbelian 2 V] : Prop where
  residual : pResidual 2 Y = ⊤
  normalizes_Y : (T : Subgroup G) ≤ normalizer (Y : Set G)
  characteristic_Y : Theory.GroupTheory.generalizedFitting Y = pCore 2 Y
  v_le_sylow : V ≤ (T : Subgroup G)
  v_reduced : ∃ hN : (V.subgroupOf (Y ⊔ (T : Subgroup G))).Normal,
    letI := hN
    pCore 2 ((Y ⊔ (T : Subgroup G) : Subgroup G) ⧸
      centralizer (V.subgroupOf (Y ⊔ (T : Subgroup G)) :
        Set (Y ⊔ (T : Subgroup G) : Subgroup G))) = ⊥
  sylow_centralizer : (T : Subgroup G) ⊓ centralizer (V : Set G) =
    (Y ⊔ (T : Subgroup G)).pCoreIn 2
  z_card : Nat.card Z = 2
  normalizes_Z : (T : Subgroup G) ≤ normalizer (Z : Set G)
  z_lt : Z < ZS
  zs_le : ZS ≤ V
  a_centralizes : H ≤ centralizer (Z : Set G)
  a_contains : residualCentralizer Y Z ⊔ (T : Subgroup G) ≤ H
  a_characteristic : Theory.GroupTheory.generalizedFitting H = pCore 2 H
  a_kernel :
    letI : (Z.subgroupOf H).Normal :=
      normal_subgroupOf_of_le_normalizer
        (a_centralizes.trans (centralizer_le_normalizer (Z : Set G)))
    (centralizerModulo (⊤ : Subgroup H) (ZS.subgroupOf H) (Z.subgroupOf H)).normalCore ≤
      pCore 2 H
  b_normalizes : residualCentralizer Y Z ⊔ (T : Subgroup G) ≤ normalizer (ZS : Set G)
  b_irreducible : ∀ W : Subgroup G, Z ≤ W → W ≤ ZS →
    residualCentralizer Y Z ⊔ (T : Subgroup G) ≤ normalizer (W : Set G) → W = Z ∨ W = ZS
  c_normalizer : H ⊓ normalizer (ZS : Set G) ≤ H ⊓ normalizer (V : Set G)
  d_core : pCore 2 ((Y ⊔ (T : Subgroup G)) ⊔ H : Subgroup G) = ⊥
  e_commutators : ∀ g ∈ H,
    ⁅V, V.map (MulAut.conj g).toMonoidHom⁆ ≤ V ⊓ V.map (MulAut.conj g).toMonoidHom →
    ⁅ZS, V.map (MulAut.conj g).toMonoidHom⁆ ≤ Z →
    ⁅ZS.map (MulAut.conj g).toMonoidHom, V⁆ ≤ Z →
    ⁅ZS, V.map (MulAut.conj g).toMonoidHom⁆ = ⊥ ∧
      ⁅ZS.map (MulAut.conj g).toMonoidHom, V⁆ = ⊥

/-- The actual containment Vᴳ ∩ N_G([V,x]) ⊆ C_G(V), with conjugate
subgroups interpreted as subgroups of the ambient group. -/
def NormalizingConjugatesCentralize (V : Subgroup G) (x : G) : Prop :=
  ∀ g : G, V.map (MulAut.conj g).toMonoidHom ≤
    normalizer ((⁅V, zpowers x⁆ : Subgroup G) : Set G) →
    V.map (MulAut.conj g).toMonoidHom ≤ centralizer (V : Set G)

/-- F.9.8 extends F.9.1 by exactly (f) and the two alternatives of (g). -/
structure SourceF98 [Finite G] (T : Sylow 2 G) (Y V ZS Z H : Subgroup G)
    [IsElementaryAbelian 2 V] : Prop extends SourceF91 T Y V ZS Z H where
  f : ∀ g : G, Z ≤ V.map (MulAut.conj g).toMonoidHom →
    ⁅V, V.map (MulAut.conj g).toMonoidHom⁆ = ⊥
  g : ⁅V, H ⊓ centralizer (ZS : Set G)⁆ ≤ Z ∨
    ∀ x ∈ H ⊓ centralizer (ZS : Set G), ⁅V, zpowers x⁆ ≠ ⊥ →
      NormalizingConjugatesCentralize V x

/-- Verify (f) using nontrivial Z in the intersection and (g)(ii) by
restricting the ambient centralizer conclusion of 15.3.47. -/
theorem sourceF98_of_intersection_and_47 [Finite G]
    {T : Sylow 2 G} {Y V ZS Z H : Subgroup G} [IsElementaryAbelian 2 V]
    (h91 : SourceF91 T Y V ZS Z H)
    (h62 : ∀ g : G, V ⊓ V.map (MulAut.conj g).toMonoidHom ≠ ⊥ →
      ⁅V, V.map (MulAut.conj g).toMonoidHom⁆ = ⊥)
    (h47 : ∀ x ∈ centralizer (ZS : Set G),
      ⁅V, zpowers x⁆ = ⊥ ∨ NormalizingConjugatesCentralize V x) :
    SourceF98 T Y V ZS Z H := by
  refine ⟨h91, ?_, Or.inr ?_⟩
  · intro g hg
    apply h62
    intro hzero
    have hz : Z = ⊥ := le_bot_iff.mp
      ((le_inf (h91.z_lt.le.trans h91.zs_le) hg).trans_eq hzero)
    have hcard := h91.z_card
    rw [hz] at hcard
    simp at hcard
  · intro x hx hnonzero
    exact (h47 x hx.2).resolve_left hnonzero

open Representation.BinaryOffender

/-- The exact offender-existence output of F.9.16(3), as an earlier-theorem
implication. It applies to every action with the specified conjugation formula.
Its source proof remains the responsibility of the F.9 assembly owners. -/
def F9163Input [Finite G] (T : Sylow 2 G) (Y V ZS Z H : Subgroup G)
    [IsElementaryAbelian 2 V] : Prop :=
  ∀ hU : IsElementaryAbelian 2 (conjugateSpanBy ZS H),
    letI := hU
    SourceF98 T Y V ZS Z H →
      ∀ a : LocalQuotientAction H (conjugateSpanBy ZS H) Z,
        ∃ B : Subgroup H,
          B ≤ (((Y ⊔ (T : Subgroup G)) ⊓ H).pCoreIn 2).subgroupOf H ∧
          IsElementaryTwo (B.map (QuotientGroup.mk' (pCore 2 H))) ∧
          IsQuadratic a.representation (B.map (QuotientGroup.mk' (pCore 2 H))) ∧
          fixedCodim a.representation (B.map (QuotientGroup.mk' (pCore 2 H))) ≤
            2 * rank (B.map (QuotientGroup.mk' (pCore 2 H)))

/-- The consumed conclusions 15.3.48(1) and (3), including the literal
centralizer equality in H/Z. The other parts of 15.3.48 are not needed here. -/
structure Earlier48Conclusions [Finite G] (T : Sylow 2 G) (Y V ZS Z H : Subgroup G)
    [IsElementaryAbelian 2 V] : Prop extends SourceF91 T Y V ZS Z H where
  centralizer_kernel :
    letI : (Z.subgroupOf H).Normal :=
      normal_subgroupOf_of_le_normalizer
        (a_centralizes.trans (centralizer_le_normalizer (Z : Set G)))
    centralizerModulo (⊤ : Subgroup H) ((conjugateSpanBy ZS H).subgroupOf H)
      (Z.subgroupOf H) = pCore 2 H

/-- 15.3.48 under the earlier dichotomy 15.3.7. Case (1) permits every H;
case (2) still requires C_Y(V)≤H. -/
def Earlier48Input [Finite G] (T : Sylow 2 G) (Y V ZS Z H : Subgroup G)
    [IsElementaryAbelian 2 V] : Prop :=
  (Y.pCoreIn 2 = Y ⊓ centralizer (V : Set G) ∨ Y ⊓ centralizer (V : Set G) ≤ H) →
    Earlier48Conclusions T Y V ZS Z H


end CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.ModuleBound
