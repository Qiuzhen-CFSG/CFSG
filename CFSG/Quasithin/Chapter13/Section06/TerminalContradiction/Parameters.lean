module

public import CFSG.Quasithin.Chapter13.Section06.TerminalContradiction.Coordinates
public import CFSG.Quasithin.ChapterE.Section03.Offenders.Basic
public import CFSG.Quasithin.ChapterE.Section03.Offenders.Transport
public import CFSG.Quasithin.ChapterE.Section03.Parameters.Global
public import CFSG.Quasithin.ChapterE.Section03.Parameters.Module
public import CFSG.Quasithin.Chapter3.Defs
public import CFSG.Quasithin.Chapter1.Defs
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents
public import CFSG.Quasithin.Chapter13.Section08.SourceDefs
public import Theory.GroupTheory.PResidual.Defs

/-!
# The parameter part of the terminal A₅ argument

This file is the interface between the genuine 13.3/13.6 local setup and the
two terminal lemmas on printed p.934.  The fields of `SourceParameters` and
`SourceTerminal` are earlier source implications (the weak-closure generators,
the E.3.35 implication, and 13.3.8(2)); none of them is one of the four
conclusions of 13.6.25 or either conclusion of 13.6.26.

The small module lemma below is deliberately separated from the source
interface.  Its input is the actual faithful automizer representation and the
five-point coordinates.  The only finite calculation needed by the assembly is
that two distinct involution lines have different fixed spaces.  Thus the
calculation is transported to the automizer rather than being encoded as a
fixed-space-family exclusion.

Source: Aschbacher--Smith, combined manuscript (1 March 2004),
13.6.24--26, printed pp.934--935, with E.3.8--9 and E.3.35.
-/

@[expose] public section

namespace CFSG.Quasithin.Chapter13.Section06.TerminalContradiction

open Subgroup
open Representation.BinaryOffender
open scoped Pointwise IsMulCommutative

namespace ModuleGeometry

variable {G : Type*} [Group G] {V : Subgroup G} [IsElementaryAbelian 2 V]

/-! The coordinate calculation used for `a(\bar M_V,V)=1`. -/

/--
The finite five-point calculation, after transport through the actual
coordinates.  `line_index_one` records the elementary rank-two fact needed to
apply the definition of `fixedSpaceFamily`; it is a property of the concrete
five-point model, not a fixed-space-family conclusion.
-/
structure FiveModuleGeometry (V : Subgroup G)
    [IsElementaryAbelian 2 V] where
  actor : _root_.CFSG.Quasithin.ChapterE.Automizer V →* Equiv.Perm (Fin 5)
  actor_injective : Function.Injective actor
  fixed_space_distinct :
    ∀ {a b : _root_.CFSG.Quasithin.ChapterE.Automizer V},
      a ≠ 1 → b ≠ 1 → a ≠ b →
      fixedSpace (_root_.CFSG.Quasithin.ChapterE.automizerRepresentation V)
        (Subgroup.zpowers a) ≠
      fixedSpace (_root_.CFSG.Quasithin.ChapterE.automizerRepresentation V)
        (Subgroup.zpowers b)
  line_index_one :
    ∀ {A : Subgroup (_root_.CFSG.Quasithin.ChapterE.Automizer V)},
      A ∈ _root_.CFSG.Quasithin.ChapterE.fixedSpaceFamily
        (_root_.CFSG.Quasithin.ChapterE.automizerRepresentation V) 2 →
      ∃ a b : _root_.CFSG.Quasithin.ChapterE.Automizer V,
        a ∈ A ∧ b ∈ A ∧ a ≠ 1 ∧ b ≠ 1 ∧ a ≠ b ∧
          Nat.log 2 ((Subgroup.zpowers a).relIndex A) = 1 ∧
          Nat.log 2 ((Subgroup.zpowers b).relIndex A) = 1

theorem moduleA_eq_one_of_five_geometry
    [Finite (_root_.CFSG.Quasithin.ChapterE.Automizer V)]
    (_hρ : Function.Injective
      (_root_.CFSG.Quasithin.ChapterE.automizerRepresentation V))
    (heven : Even (Nat.card (_root_.CFSG.Quasithin.ChapterE.Automizer V)))
    (d : FiveModuleGeometry V) :
    _root_.CFSG.Quasithin.ChapterE.localA V = 1 := by
  let ρ := _root_.CFSG.Quasithin.ChapterE.automizerRepresentation V
  have hnon : (_root_.CFSG.Quasithin.ChapterE.fixedSpaceFamily ρ 1).Nonempty :=
    _root_.CFSG.Quasithin.ChapterE.fixedSpaceFamily_one_nonempty_of_even ρ heven
  have htwo : _root_.CFSG.Quasithin.ChapterE.fixedSpaceFamily ρ 2 = ∅ := by
    ext A
    constructor
    · intro hA
      obtain ⟨a, b, haA, hbA, ha1, hb1, hab, hia, hib⟩ := d.line_index_one hA
      have hfa := hA.2.2 (Subgroup.zpowers a) (Subgroup.zpowers_le.mpr haA)
        (by simp [hia])
      have hfb := hA.2.2 (Subgroup.zpowers b) (Subgroup.zpowers_le.mpr hbA)
        (by simp [hib])
      exact d.fixed_space_distinct ha1 hb1 hab (hfa.symm.trans hfb)
    · intro hA
      exact hA.elim
  have hle : _root_.CFSG.Quasithin.ChapterE.moduleA ρ ≤ 1 := by
    apply iSup_le
    intro k
    apply iSup_le
    rintro ⟨A, hA⟩
    by_cases hk0 : k = 0
    · simp [hk0]
    by_cases hk1 : k = 1
    · simp [hk1]
    have hk2 : 2 ≤ k := by omega
    have hA2 : A ∈ _root_.CFSG.Quasithin.ChapterE.fixedSpaceFamily ρ 2 :=
      _root_.CFSG.Quasithin.ChapterE.fixedSpaceFamily_mono ρ (by decide) hk2 hA
    exact (htwo ▸ hA2).elim
  have hge : (1 : ℕ∞) ≤ _root_.CFSG.Quasithin.ChapterE.moduleA ρ := by
    obtain ⟨A, hA⟩ := hnon
    exact _root_.CFSG.Quasithin.ChapterE.le_moduleA_of_mem ρ hA
  exact le_antisymm hle hge

end ModuleGeometry

namespace Source

variable {G : Type*} [Group G] [Finite G]

/--
The exact prior local facts used in 13.6.25.  The first two fields are the
source's generator calculation for `W_i(T,V)`; `r_lower` and `r_witness` are
the two inequalities in the definition of `r(G,V)`; and `e335` is the earlier
E.3.35 implication with its actual hypotheses still explicit.
-/
structure SourceParameters where
  V : Subgroup G
  T : Subgroup G
  M : Subgroup G
  LT : Subgroup G
  hV : V ≤ T
  hTnormalizes : T ≤ normalizer (V : Set G)
  hcentral : T ⊓ centralizer (V : Set G) = pCoreIn 2 LT
  generator_central :
    ∀ {i : ℕ}, i = 0 ∨ i = 1 →
      ∀ {A : Subgroup G},
        A ∈ _root_.CFSG.Quasithin.ChapterE.conjugateCorankFamily V i → A ≤ T →
        A ≤ centralizer (V : Set G)
  hLT : LT ≤ normalizer (T : Set G)
  r_lower :
    ∀ {A : Subgroup G}, A ≤ V →
      (_root_.CFSG.Quasithin.ChapterE.subgroupCorank V A : ℕ∞) < 3 →
        centralizer (A : Set G) ≤ normalizer (V : Set G)
  r_witness :
    ∃ A : Subgroup G, A ≤ V ∧
      ¬ centralizer (A : Set G) ≤ normalizer (V : Set G) ∧
      (_root_.CFSG.Quasithin.ChapterE.subgroupCorank V A : ℕ∞) = 3
  e335 :
    1 < _root_.CFSG.Quasithin.ChapterE.globalR V →
      1 < _root_.CFSG.Quasithin.ChapterE.globalW V T →
      (∀ H : Subgroup G, H ∈ Chapter3.HStar T M →
        1 < _root_.CFSG.Quasithin.ChapterE.generationParameter H) ∧
      (∀ H : Subgroup G, H ∈ Chapter1.HOver G (T : Set G) →
        Group.IsSolvable H → H ≤ M)

end Source

namespace Source
namespace SourceParameters

variable {G : Type*} [Group G] [Finite G]

theorem weakClosure_le_core (s : Source.SourceParameters (G := G))
    {i : ℕ} (hi : i = 0 ∨ i = 1) :
    _root_.CFSG.Quasithin.ChapterE.indexedWeakClosure s.V s.T i ≤ pCoreIn 2 s.LT := by
  rw [← s.hcentral]
  apply le_inf
  · exact _root_.CFSG.Quasithin.ChapterE.indexedWeakClosure_le s.V s.T i
  · rw [_root_.CFSG.Quasithin.ChapterE.weakClosure_eq_sSup_gamma]
    apply sSup_le
    intro A hA
    exact s.generator_central hi hA.1 hA.2

theorem weakClosure_normalIn_LT (s : Source.SourceParameters (G := G))
    {i : ℕ} (hi : i = 0 ∨ i = 1) :
    Chapter3.NormalIn
      (_root_.CFSG.Quasithin.ChapterE.indexedWeakClosure s.V s.T i) s.LT := by
  refine ⟨(s.weakClosure_le_core hi).trans (pCoreIn_le 2 s.LT), ?_⟩
  intro g hg n hn
  exact (Subgroup.mem_normalizer_iff.mp
    (s.hLT.trans (_root_.CFSG.Quasithin.ChapterE.normalizer_le_weakClosure_normalizer
      s.V s.T i) hg) n).mp hn

theorem globalR_eq_three (s : Source.SourceParameters (G := G)) :
    _root_.CFSG.Quasithin.ChapterE.globalR s.V = 3 := by
  apply le_antisymm
  · obtain ⟨A, hAV, hnot, hthree⟩ := s.r_witness
    have hle := _root_.CFSG.Quasithin.ChapterE.globalR_le_corank hAV hnot
    rw [hthree] at hle
    exact hle
  · apply le_iInf
    intro A
    apply le_iInf
    intro hA
    apply le_of_not_gt
    intro hlt
    exact hA.2 (s.r_lower hA.1 hlt)

theorem globalW_ge_two (s : Source.SourceParameters (G := G)) :
    (2 : ℕ∞) ≤ _root_.CFSG.Quasithin.ChapterE.globalW s.V s.T := by
  apply le_iInf
  intro j
  apply le_iInf
  intro hj
  have hj' : 2 ≤ j := by
    by_contra h
    have hcases : j = 0 ∨ j = 1 := by omega
    rcases hcases with rfl | rfl
    · exact hj ((s.weakClosure_le_core (by left; rfl)).trans
        (by rw [s.hcentral]))
    · exact hj ((s.weakClosure_le_core (by right; rfl)).trans
        (by rw [s.hcentral]))
  exact_mod_cast hj'

theorem parameters_13_6_25 (s : Source.SourceParameters (G := G)) :
    (_root_.CFSG.Quasithin.ChapterE.globalR s.V = 3) ∧
    (1 < _root_.CFSG.Quasithin.ChapterE.globalW s.V s.T) ∧
    (∀ H : Subgroup G, H ∈ Chapter3.HStar s.T s.M →
      1 < _root_.CFSG.Quasithin.ChapterE.generationParameter H) ∧
    (∀ H : Subgroup G, H ∈ Chapter1.HOver G (s.T : Set G) →
      Group.IsSolvable H → H ≤ s.M) ∧
    (∀ {i : ℕ}, i = 0 ∨ i = 1 →
      _root_.CFSG.Quasithin.ChapterE.indexedWeakClosure s.V s.T i ≤ pCoreIn 2 s.LT ∧
      Chapter3.NormalIn
        (_root_.CFSG.Quasithin.ChapterE.indexedWeakClosure s.V s.T i) s.LT) := by
  have hR : _root_.CFSG.Quasithin.ChapterE.globalR s.V = 3 := s.globalR_eq_three
  have hW : 1 < _root_.CFSG.Quasithin.ChapterE.globalW s.V s.T :=
    lt_of_lt_of_le (by norm_num) s.globalW_ge_two
  obtain ⟨hn, hs⟩ := s.e335 (by rw [hR]; norm_num) hW
  refine ⟨hR, hW, hn, hs, ?_⟩
  intro i hi
  exact ⟨s.weakClosure_le_core hi, s.weakClosure_normalIn_LT hi⟩

end SourceParameters
end Source

namespace TerminalSource

variable {G : Type*} [Group G] [Finite G]

/-- The literal two-prime core `O_{2,p}(H)=O₂(H)O_p(H)`, viewed in the
ambient group.  The residual below is the ambient image of the intrinsic
`p`-residual, so its kernel and carrier conventions are explicit. -/
noncomputable def O2p (H : Subgroup G) (p : ℕ) : Subgroup G :=
  pCoreIn 2 H ⊔ pCoreIn p H

noncomputable def O2pResidual (H : Subgroup G) (p : ℕ) : Subgroup G :=
  (pResidual p (O2p H p)).map (O2p H p).subtype

/-- Exact prior-source consequences used in 13.6.26.  `o2p_mem_H` is the
source's solvable-member clause (the subgroup is the relevant member of
`H(T)`); `component_1338` and `residual_1338` are the two applications of
13.3.8(2).  The final equality is the standard residual convention for
`O_{2,p}` and is kept explicit so quotient/residual choices cannot be hidden.
-/
structure SourceTerminal where
  L1 : Subgroup G
  T : Subgroup G
  G1 : Subgroup G
  M : Subgroup G
  Hmem : ∀ H : Subgroup G,
      H ∈ _root_.CFSG.Quasithin.Chapter13.Section08.Source.Hz L1 T G1 M →
      H ∈ Chapter1.H G
  solvable_member_in_M :
    ∀ {X : Subgroup G}, X ∈ Chapter1.HOver G (T : Set G) →
      Group.IsSolvable X → X ≤ M
  o2p_mem_H :
    ∀ {H : Subgroup G} {p : ℕ},
      H ∈ _root_.CFSG.Quasithin.Chapter13.Section08.Source.Hz L1 T G1 M → 3 < p →
      Group.IsSolvable (O2pResidual H p) ∧
      O2pResidual H p ∈ Chapter1.HOver G (T : Set G)
  component_1338 :
    ∀ {H K : Subgroup G},
      H ∈ _root_.CFSG.Quasithin.Chapter13.Section08.Source.Hz L1 T G1 M →
      K.IsCComponent → K ≤ M → False
  residual_1338 :
    ∀ {H X : Subgroup G} {p : ℕ},
      H ∈ _root_.CFSG.Quasithin.Chapter13.Section08.Source.Hz L1 T G1 M → 3 < p →
      X = O2pResidual H p → X ≤ M → X = ⊥
  residual_eq_core :
    ∀ {H : Subgroup G} {p : ℕ},
      3 < p → O2pResidual H p = ⊥ → O2p H p =
        _root_.CFSG.Quasithin.Chapter13.Section08.Source.QH H

variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
theorem no_C_component_in_M (s : TerminalSource.SourceTerminal (G := G))
    {H : Subgroup G} (hH : H ∈
      _root_.CFSG.Quasithin.Chapter13.Section08.Source.Hz s.L1 s.T s.G1 s.M)
    {K : Subgroup G} (hK : K.IsCComponent) (hKM : K ≤ s.M) : False :=
  s.component_1338 hH hK hKM

omit [Finite G] in
theorem o2p_eq_QH (s : TerminalSource.SourceTerminal (G := G))
    {H : Subgroup G} (hH : H ∈
      _root_.CFSG.Quasithin.Chapter13.Section08.Source.Hz s.L1 s.T s.G1 s.M)
    {p : ℕ} (hp : 3 < p) : O2p H p =
      _root_.CFSG.Quasithin.Chapter13.Section08.Source.QH H := by
  obtain ⟨hsol, hHT⟩ := s.o2p_mem_H hH hp
  have hM := s.solvable_member_in_M hHT hsol
  have hzero := s.residual_1338 hH hp rfl hM
  exact s.residual_eq_core hp hzero

end TerminalSource

end CFSG.Quasithin.Chapter13.Section06.TerminalContradiction
