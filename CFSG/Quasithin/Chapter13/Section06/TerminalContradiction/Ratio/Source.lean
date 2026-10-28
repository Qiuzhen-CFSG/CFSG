module

public import CFSG.Quasithin.Chapter13.Section06.TerminalContradiction.Ratio.QuotientAction
public import Theory.GroupTheory.GeneralizedFitting.Defs
public import Theory.GroupTheory.PResidual.Defs
public import Theory.GroupTheory.SolvableResidual

/-!
# The source F.9 hypotheses and earlier implications for the terminal A₅ case

This records every clause of F.9.1 and F.9.8 on the literal subgroups and
quotients. In particular L₁ is O²(C_L(V₁)), R₂ is the reduced normal
binary module condition, and the kernel in (a) is a normal core inside H.
The additional V ≤ T is the usual consequence of V ∈ R₂(LT).

The earlier theorem implications below are explicit inputs, not proofs of
13.5.7, F.9.2(3), or F.9.16(3). Their assembly owners are qt-13-05,
qt-f09-foundations, and qt-f09-geometry. The terminal consumer verifies their
local applicability and constructs the faithful action before using them.
These definitions follow the generic F.9 contracts already used in the
Chapter 15 ModuleBound/Source development, without importing that assembly.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), F.9.1,
F.9.8 and F.9.16(3), printed pp.317–324, and 13.5.7 / 13.6, pp.917,935.
-/

@[expose] public section
open Subgroup
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter13.Section06.TerminalContradiction.Ratio
open Section08
variable {G : Type*} [Group G]

/-- The source L₁=O²(C_L(V₁)), embedded from its own ambient group. -/
noncomputable def residualCentralizer (L V₁ : Subgroup G) : Subgroup G :=
  (pResidual 2 (L ⊓ centralizer (V₁ : Set G) : Subgroup G)).map
    (L ⊓ centralizer (V₁ : Set G)).subtype

/-- Every clause of F.9.1, with the Section 13.6 names. The field
`v_reduced` is B.2.11, and `a_kernel` is a normal core inside H. -/
structure SourceF91 [Finite G] (T : Sylow 2 G) (L V V₃ V₁ H : Subgroup G)
    [IsElementaryAbelian 2 V] : Prop where
  residual : pResidual 2 L = ⊤
  normalizes_L : (T : Subgroup G) ≤ normalizer (L : Set G)
  characteristic_L : Theory.GroupTheory.generalizedFitting L = pCore 2 L
  v_le_sylow : V ≤ (T : Subgroup G)
  v_reduced : ∃ hN : (V.subgroupOf (L ⊔ (T : Subgroup G))).Normal,
    letI := hN
    pCore 2 ((L ⊔ (T : Subgroup G) : Subgroup G) ⧸
      centralizer (V.subgroupOf (L ⊔ (T : Subgroup G)) :
        Set (L ⊔ (T : Subgroup G) : Subgroup G))) = ⊥
  sylow_centralizer : (T : Subgroup G) ⊓ centralizer (V : Set G) =
    (L ⊔ (T : Subgroup G)).pCoreIn 2
  z_card : Nat.card V₁ = 2
  normalizes_V₁ : (T : Subgroup G) ≤ normalizer (V₁ : Set G)
  z_lt : V₁ < V₃
  v₃_le : V₃ ≤ V
  a_centralizes : H ≤ centralizer (V₁ : Set G)
  a_contains : residualCentralizer L V₁ ⊔ (T : Subgroup G) ≤ H
  a_characteristic : Theory.GroupTheory.generalizedFitting H = pCore 2 H
  a_kernel :
    letI : (V₁.subgroupOf H).Normal :=
      normal_subgroupOf_of_le_normalizer
        (a_centralizes.trans (centralizer_le_normalizer (V₁ : Set G)))
    (centralizerModulo (⊤ : Subgroup H) (V₃.subgroupOf H) (V₁.subgroupOf H)).normalCore ≤
      pCore 2 H
  b_normalizes : residualCentralizer L V₁ ⊔ (T : Subgroup G) ≤ normalizer (V₃ : Set G)
  b_irreducible : ∀ W : Subgroup G, V₁ ≤ W → W ≤ V₃ →
    residualCentralizer L V₁ ⊔ (T : Subgroup G) ≤ normalizer (W : Set G) → W = V₁ ∨ W = V₃
  c_normalizer : H ⊓ normalizer (V₃ : Set G) ≤ H ⊓ normalizer (V : Set G)
  d_core : pCore 2 ((L ⊔ (T : Subgroup G)) ⊔ H : Subgroup G) = ⊥
  e_commutators : ∀ g ∈ H,
    ⁅V, V.map (MulAut.conj g).toMonoidHom⁆ ≤ V ⊓ V.map (MulAut.conj g).toMonoidHom →
    ⁅V₃, V.map (MulAut.conj g).toMonoidHom⁆ ≤ V₁ →
    ⁅V₃.map (MulAut.conj g).toMonoidHom, V⁆ ≤ V₁ →
    ⁅V₃, V.map (MulAut.conj g).toMonoidHom⁆ = ⊥ ∧
      ⁅V₃.map (MulAut.conj g).toMonoidHom, V⁆ = ⊥

namespace SourceF91
variable [Finite G] {T : Sylow 2 G} {L V V₃ V₁ H : Subgroup G}
  [IsElementaryAbelian 2 V] (h : SourceF91 T L V V₃ V₁ H)

include h in
/-- The Sylow subgroup in the edge contains V, hence the seed V₃ lies in H. -/
theorem seed_le : V₃ ≤ H :=
  h.v₃_le.trans (h.v_le_sylow.trans (le_sup_right.trans h.a_contains))

include h in
/-- The source central line is actually contained in U_H. -/
theorem line_le_UH : V₁ ≤ Source.UH H V₃ :=
  h.z_lt.le.trans (le_conjugateSpanBy V₃ H)

include h in
/-- The whole conjugate span is contained in its local overgroup. -/
theorem UH_le : Source.UH H V₃ ≤ H := Ratio.UH_le h.seed_le

omit [Finite G] in
/-- U_H is normal in H, not asserted normal in the ambient simple group. -/
theorem UH_normal : ((Source.UH H V₃).subgroupOf H).Normal :=
  normal_subgroupOf_of_le_normalizer (le_normalizer_conjugateSpanBy V₃ H)

include h in
/-- The central line is normal in H. -/
theorem line_normal : (V₁.subgroupOf H).Normal :=
  normal_subgroupOf_of_le_normalizer
    (h.a_centralizes.trans (centralizer_le_normalizer (V₁ : Set G)))

include h in
/-- The same line is normal in the actual numerator U_H. -/
theorem line_normal_UH : (V₁.subgroupOf (Source.UH H V₃)).Normal :=
  normal_subgroupOf_of_le_normalizer
    (h.UH_le.trans (h.a_centralizes.trans (centralizer_le_normalizer (V₁ : Set G))))

end SourceF91

/-- The terminal paragraph resets K to the solvable residual H^∞. -/
def terminalResidual (H : Subgroup G) : Subgroup G :=
  (solvableResidual H).map H.subtype

/-- Restriction to H recovers the intrinsic solvable residual. -/
theorem terminalResidual_subgroupOf (H : Subgroup G) :
    (terminalResidual H).subgroupOf H = solvableResidual H := by
  ext h
  constructor
  · rintro ⟨k, hk, he⟩
    exact (Subtype.ext he : k = h) ▸ hk
  · intro hh
    exact mem_map_of_mem H.subtype hh

/-- Its star image is the solvable residual of the literal star quotient. -/
theorem terminalResidual_star [Finite G] (H : Subgroup G) :
    Source.starImage H (terminalResidual H) = solvableResidual (Source.Hstar H) := by
  rw [Source.starImage, terminalResidual_subgroupOf]
  exact map_solvableResidual_eq _ (QuotientGroup.mk'_surjective _)

/-- The actual containment Vᴳ ∩ N_G([V,x]) ⊆ C_G(V), with conjugate
subgroups interpreted as subgroups of the ambient group. -/
def NormalizingConjugatesCentralize (V : Subgroup G) (x : G) : Prop :=
  ∀ g : G, V.map (MulAut.conj g).toMonoidHom ≤
    normalizer ((⁅V, zpowers x⁆ : Subgroup G) : Set G) →
    V.map (MulAut.conj g).toMonoidHom ≤ centralizer (V : Set G)

/-- F.9.8 extends F.9.1 by exactly (f) and the two alternatives of (g). -/
structure SourceF98 [Finite G] (T : Sylow 2 G) (L V V₃ V₁ H : Subgroup G)
    [IsElementaryAbelian 2 V] : Prop extends SourceF91 T L V V₃ V₁ H where
  f : ∀ g : G, V₁ ≤ V.map (MulAut.conj g).toMonoidHom →
    ⁅V, V.map (MulAut.conj g).toMonoidHom⁆ = ⊥
  g : ⁅V, H ⊓ centralizer (V₃ : Set G)⁆ ≤ V₁ ∨
    ∀ x ∈ H ⊓ centralizer (V₃ : Set G), ⁅V, zpowers x⁆ ≠ ⊥ →
      NormalizingConjugatesCentralize V x

/-- The genuine universal 13.5.7 implication, with V₃ as V₊. The Chapter 13
assembly supplies its standing hypotheses when discharging this input. -/
def Earlier1357 [Finite G] (T : Sylow 2 G) (L V V₃ V₁ G₁ M : Subgroup G)
    [IsElementaryAbelian 2 V] : Prop :=
  ∀ H ∈ Source.Hz (residualCentralizer L V₁) (T : Subgroup G) G₁ M,
    SourceF91 T L V V₃ V₁ H

/-- The universal centralizer identity F.9.2(3), in the ambient convention
proved equal to the literal quotient-action kernel in `map_ker`. -/
def EarlierF923 [Finite G] (T : Sylow 2 G) (L V V₃ V₁ : Subgroup G)
    [IsElementaryAbelian 2 V] : Prop :=
  ∀ H, SourceF91 T L V V₃ V₁ H →
    commutatorPreimage H (Source.UH H V₃) V₁ = Source.QH H

open Representation.BinaryOffender

/-- The universal offender-existence assertion in F.9.16(3). It retains
B ≤ O₂((LT) ∩ H), its actual star image, quadraticity and the rank bound.
It does not assume a specialized terminal strict-ratio conclusion. -/
def EarlierF9163 [Finite G] (T : Sylow 2 G) (L V V₃ V₁ : Subgroup G)
    [IsElementaryAbelian 2 V] : Prop :=
  ∀ H, ∀ hU : IsElementaryAbelian 2 (Source.UH H V₃),
    letI := hU
    SourceF98 T L V V₃ V₁ H →
    ∀ (hn : H ≤ normalizer (V₁ : Set G))
      (hk : commutatorPreimage H (Source.UH H V₃) V₁ = Source.QH H),
      ∃ B : Subgroup H,
        B ≤ (((L ⊔ (T : Subgroup G)) ⊓ H).pCoreIn 2).subgroupOf H ∧
        IsElementaryTwo (B.map (QuotientGroup.mk' (pCore 2 H))) ∧
        IsQuadratic (starRepresentation H V₃ V₁ hn hk)
          (B.map (QuotientGroup.mk' (pCore 2 H))) ∧
        fixedCodim (starRepresentation H V₃ V₁ hn hk)
          (B.map (QuotientGroup.mk' (pCore 2 H))) ≤
          2 * rank (B.map (QuotientGroup.mk' (pCore 2 H)))

/-- The numerical part of F.9.16(3) follows from its actual offender witness. -/
theorem bound_of_F9163 [Finite G] {T : Sylow 2 G} {L V V₃ V₁ H : Subgroup G}
    [IsElementaryAbelian 2 V] [hU : IsElementaryAbelian 2 (Source.UH H V₃)]
    (h98 : SourceF98 T L V V₃ V₁ H) (hF : EarlierF9163 T L V V₃ V₁)
    (hn : H ≤ normalizer (V₁ : Set G))
    (hk : commutatorPreimage H (Source.UH H V₃) V₁ = Source.QH H) :
    quadraticRatio (starRepresentation H V₃ V₁ hn hk) ≤ 2 := by
  obtain ⟨B, _, hB, hq, hr⟩ := hF H hU h98 hn hk
  apply (quadraticRatio_le_iff _ (by simp)).mpr
  refine ⟨_, hB, hq, ?_⟩
  rw [actionRatio, ENNReal.div_le_iff (by exact_mod_cast (ne_of_gt hB.rank_pos)) (by simp)]
  exact_mod_cast hr

end CFSG.Quasithin.Chapter13.Section06.TerminalContradiction.Ratio
end
