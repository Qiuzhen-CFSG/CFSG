module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceOrthogonal.Selection.ParabolicConstruction
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceOrthogonal.Selection.IntrinsicModels

/-!
# Source rank-four selection and ambient residual identification

Apply the geometric construction to every member of the literal Y_z family.
The inner-action branch yields a moving local SL₃(2) replacement and is
excluded by 13.6.22. The surviving action has an outside actor, so its
normalized minimal parabolic is the middle node of SL₄(2).

The containing component D from genuine 1.2.4 also belongs to Y_z. Applying
the same selection to D and using the proved A.3.6 catalogue comparison
constructs both intrinsic two-core markings. Their comparison gives K = D.
The centerless A.3.18 argument then gives prime-to-three index and the
literal equality K = O^{3′}(Gᵥ). Finally faithfulness and the binary
automorphism theorem identify an actual Tᵥ⁺ actor with inverse transpose
times an inner automorphism.

The final theorem discharges the intermediate rank-four premise of
`exists_containing_models_and_residual_of_a36`. Its explicit assumptions
are earlier source conclusions: the local SQTK/Sylow setup, the star and
W_K two-reduced actions, the central Fitting equality after 13.6.13,
13.6.14, 13.6.16(3), 13.6.20, 13.6.22 and the reduced model list. Universal
A.3.6, A.3.8 and A.3.12 remain explicit under the parent source contract.
Their discharge belongs to the earlier-source owners and component
elimination; the orthogonal-module and final Thompson argument belong to
the parent SourceOrthogonal task. No assertion of 13.6.23 is assumed here.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
13.6.23, printed p.933/PDF p.950, with the minimal-parabolic argument on p.932.
-/

public section
open Subgroup
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceOrthogonal.Selection
open ComponentSelection BinaryLinear.InvariantNodeActions BinaryLinear.OuterCyclic
universe u
variable {G : Type u} [Group G] [Finite G]

/-- Conjugation by the literal plus actor on its normal K⁺, transported
through the selected rank-four model. -/
noncomputable def plusComponentAction
    (K L T : Subgroup G) (z v : G)
    (hL : Tv T v ≤ normalizer (Lv L v : Set G))
    (hz : Tv T v ≤ centralizer ({z} : Set G))
    (hLK : Lv L v ≤ K) (hKn : Tv T v ≤ normalizer (K : Set G))
    (e : plusImage K L T z v hL hz K ≃* SL(4, ZMod 2)) :
    Gplus K L T z v hL hz →* MulAut (LinearGroup 4) := by
  let := plusComponent_normal K L T z v hL hz hLK hKn
  exact componentAction (plusImage K L T z v hL hz K) (e.trans (slEquivLinear 4))

omit [Finite G] in
/-- The selected action is conjugation on the same marked component. -/
theorem plusComponentAction_eq
    (K L T : Subgroup G) (z v : G)
    (hL : Tv T v ≤ normalizer (Lv L v : Set G))
    (hz : Tv T v ≤ centralizer ({z} : Set G))
    (hLK : Lv L v ≤ K) (hKn : Tv T v ≤ normalizer (K : Set G))
    (e : plusImage K L T z v hL hz K ≃* SL(4, ZMod 2)) :
    letI := plusComponent_normal K L T z v hL hz hLK hKn
    plusComponentAction K L T z v hL hz hLK hKn e =
      componentAction (plusImage K L T z v hL hz K) (e.trans (slEquivLinear 4)) := by rfl

/-- All three source conclusions of 13.6.23 under the genuine earlier-source
contract, together with the intrinsic marking, faithful action and relative
component/index assertions needed by the orthogonal endgame. The witness for
the nontrivial diagram action is conjugation by an actual element of Tᵥ⁺. -/
theorem source_rankFour_selection {𝒦 : GroupClass.{u}}
    (hA312 : ∀ (X : Type u) [Group X] [Finite X],
      IsSQTK 𝒦 X → pCore 2 X = ⊥ → ∀ (T : Sylow 2 X) (B : Subgroup X),
      B ∈ ChapterA.Section03.localCComponents T →
      ∃! D : Subgroup X, D.IsCComponent ∧ B ≤ D)
    (hA38 : ∀ (X : Type u) [Group X] [Finite X],
      IsSQTK 𝒦 X → pCore 2 X = ⊥ → ∀ D : Subgroup X, D.IsCComponent →
      D.Normal ∨ (normalizer (D : Set X)).index = 2 ∧
        Chapter1.Section02.NonnormalCComponentModel D)
    (hA36 : ∀ (X : Type u) [Group X] [Finite X],
      IsSQTK 𝒦 X → pCore 2 X = ⊥ → ∀ B : Subgroup X,
      B.IsCComponent → Chapter1.Section02.A36Conclusion B)
    (K L T : Subgroup G) (z v : G)
    (hlocal : IsSQTK 𝒦 (Gv v)) (hcore : Gv v ∈ Chapter1.H G)
    (hSyl : Chapter1.IsSylowIn 2 (Tv T v) (Gv v))
    (hL : Tv T v ≤ normalizer (Lv L v : Set G))
    (hz : Tv T v ≤ centralizer ({z} : Set G))
    (hcubic : Nat.card (Lv L v ⧸ pCore 2 (Lv L v)) = 3)
    (hmove : ¬ Lv L v ≤ centralizer ({z} : Set G))
    (hstarCore : pCore 2 (Gstar z v) = ⊥)
    (hfit : fittingSubgroup (JGstar z v) = center (JGstar z v))
    (hR : ∀ B ∈ Yz L T z v, pCore 2 (Gplus B L T z v hL hz) = ⊥)
    (h14 : ∀ B ∈ Yz L T z v, Tv T v ≤ normalizer (B : Set G))
    (h16 : ∀ B ∈ Chapter1.LIn (Gv v) (Tv T v),
      Tv T v ≤ normalizer (B : Set G) → ¬ B ≤ centralizer ({z} : Set G) →
      ⁅B, Stellmacher.elementaryAbelianMaxJ (Tv T v)⁆ = B)
    (hcontain : ∀ B ∈ Yz L T z v, Lv L v ≤ B)
    (hsmall : ∀ B ∈ Yz L T z v,
      ¬ Nonempty (plusImage B L T z v hL hz B ≃* SL(3, ZMod 2)))
    (hmodels : ∀ B ∈ Yz L T z v,
      Nonempty (plusImage B L T z v hL hz B ≃* SL(4, ZMod 2)) ∨
      Nonempty (plusImage B L T z v hL hz B ≃* SL(5, ZMod 2)))
    (hK : K ∈ Yz L T z v) :
    ∃ (e : plusImage K L T z v hL hz K ≃* SL(4, ZMod 2)) (b : Basis 3)
      (eK : K ⧸ pCore 2 K ≃* SL(4, ZMod 2)),
      K = (primeToResidual 3 (Gv v)).map (Gv v).subtype ∧
      K ∈ Chapter1.cComponentsIn (Gv v) ∧
      Gv v ≤ normalizer (K : Set G) ∧
      Nat.Coprime 3 (K.subgroupOf (Gv v)).index ∧
      (centralizer (WK K L T z v : Set G)).subgroupOf K = pCore 2 K ∧
      (∀ k : K, eK (QuotientGroup.mk' _ k) =
        e (intrinsicToPlus K L T z v hK.1.1 hL hz k)) ∧
      centralizer (plusImage K L T z v hL hz K : Set (Gplus K L T z v hL hz)) = ⊥ ∧
      (¬ plusImage K L T z v hL hz (Tv T v) ≤ plusImage K L T z v hL hz K) ∧
      ((plusImage K L T z v hL hz (sourceParabolic K L T v)).subgroupOf
        (plusImage K L T z v hL hz K)).map
        (e.trans (slEquivLinear 4)).toMonoidHom = minimalParabolic b (1 : Fin 3) ∧
      ∃ s ∈ plusImage K L T z v hL hz (Tv T v),
        plusComponentAction K L T z v hL hz (hcontain K hK) (h14 K hK) e s ∉
          MulAut.innerSubgroup (LinearGroup 4) ∧
        ∃ g : LinearGroup 4,
          plusComponentAction K L T z v hL hz (hcontain K hK) (h14 K hK) e s =
            graphLinear 4 * MulAut.conj g := by
  have hselect (B : Subgroup G) (hB : B ∈ Yz L T z v) :=
    ParabolicConstruction.exists_rankFour_sourceParabolic B L T z v hL hz hB
      (hcontain B hB) (h14 B hB) hcubic hmove h16 hR hsmall (hmodels B hB)
  have hfour : ∀ B ∈ Yz L T z v,
      Nonempty (plusImage B L T z v hL hz B ≃* SL(4, ZMod 2)) := by
    intro B hB
    obtain ⟨e, _, _⟩ := hselect B hB
    exact ⟨e⟩
  obtain ⟨e, b, hout, hP⟩ := hselect K hK
  obtain ⟨D, hD, _, _, hDn, _, _, hKD, hres⟩ :=
    exists_containing_models_and_residual_of_a36 hA312 hA38 hA36 K L T z v
      hlocal hcore hSyl hL hz hK (h14 K hK) (hcontain K hK) hmove h16
      hstarCore hfit hR hfour
  have hKC : K ∈ Chapter1.cComponentsIn (Gv v) := hKD.symm ▸ hD
  have hKn : Gv v ≤ normalizer (K : Set G) := hKD.symm ▸ hDn
  obtain ⟨eK, heK⟩ := exists_intrinsic_four_marking_of_a36 hA36
    K L T z v hlocal hL hz hK (hR K hK) e
  have hi := relative_component_index_coprime K T v hK.1 hKC.2 hKn eK
    (hlocal.stronglyQuasithin 3 (by decide) (by decide))
  have hfaith := plusComponent_centralizer_eq_bot K L T z v hL hz
    (hcontain K hK) (h14 K hK) (Chapter1.isSylowIn_iff.mp hSyl).1
    (hR K hK) (by decide : 0 < 4) e
  refine ⟨e, b, eK, hres, hKC, hKn, hi,
    intrinsic_action_kernel_eq_twoCore_of_a36 hA36 K L T z v hlocal hL hz hK
      (hR K hK) e, heK, hfaith, hout, hP, ?_⟩
  obtain ⟨s, hs, hsK⟩ : ∃ s, s ∈ plusImage K L T z v hL hz (Tv T v) ∧
      s ∉ plusImage K L T z v hL hz K := by
    by_contra h
    apply hout
    intro s hs
    by_contra hsK
    exact h ⟨s, hs, hsK⟩
  let := plusComponent_normal K L T z v hL hz (hcontain K hK) (h14 K hK)
  let a := plusComponentAction K L T z v hL hz (hcontain K hK) (h14 K hK) e s
  have ha : a ∉ MulAut.innerSubgroup (LinearGroup 4) := by
    intro hinner
    exact hsK ((componentAction_mem_inner (plusImage K L T z v hL hz K)
      (e.trans (slEquivLinear 4)) hfaith s).mp hinner)
  refine ⟨s, hs, ha, ?_⟩
  obtain ⟨g, hg | hg⟩ := inner_graph (Or.inl rfl) a
  · exact (ha (hg.symm ▸ ⟨g, rfl⟩)).elim
  · exact ⟨g, hg⟩

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceOrthogonal.Selection
