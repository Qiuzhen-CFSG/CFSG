module

public import CFSG.Quasithin.ChapterE.Section06.FrobeniusReduction.LocalFactors.ExceptionalCore
public import CFSG.Quasithin.ChapterE.Section06.CentralizerStructure.Blocks.Setup
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents

/-!
# Constructing the enlarged local C-component in E.6.25

The unique-containment clause of 1.2.4 and residual-normalization consequence
of 1.2.1(3) are explicit earlier-source inputs. The proof derives the local
family membership and both Sylow conditions, constructs the actual containing
C-component of C_G(V₂), and places the normally generated X-lift inside it.
Its fixed subgroup is exactly V₂ and has corank three. Since the original
component fixes U of corank two, the containment is proper.

The component-versus-block model sieve and its E.6.8 rank contradiction
remain separate mathematical obligations. None is encoded in these inputs.
Source: Aschbacher–Smith, E.6.25, printed p.256 (PDF p.267); 1.2.1(3) and
1.2.4, printed pp.504–505.
-/

@[expose] public section

open Subgroup
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterE.Section06.FrobeniusReduction.LocalFactors
universe u
variable {G : Type u} [Group G] [Finite G]
variable {K : GroupClass.{u}} {T : Sylow 2 G} {M V U W X L : Subgroup G}

/-- The unique-containment clause of source 1.2.4, kept as an earlier-source premise. -/
def EarlierLocalContainment (K : GroupClass.{u}) : Prop :=
  ∀ (J : Type u) [Group J] [Finite J], IsSQTK K J →
    ∀ (S : Sylow 2 J) (B : Subgroup J), B ∈ Chapter1.L J S →
      ∃! C : Subgroup J, C.IsCComponent ∧ B ≤ C

/-- The residual-normalization consequence of source 1.2.1(3).
The residual is computed inside the specified finite SQTK group. -/
def EarlierResidualNormalization (K : GroupClass.{u}) : Prop :=
  ∀ (J : Type u) [Group J] [Finite J], IsSQTK K J →
    ∀ C : Subgroup J, C.IsCComponent → pResidual 2 J ≤ normalizer (C : Set J)

/-- Construct a containing C-component of C_G(W) from an actual component of
C_G(U). Both Sylow memberships and the nontrivial two-core are derived. -/
theorem exists_containing_cComponent (h : HypothesisE61 K T M V)
    (earlier : EarlierLocalContainment K)
    (hU : U ∈ obstructionFamily M V) (hW : W ∈ obstructionFamily M V)
    (hWU : W ≤ U) (hL : L ∈ Chapter1.cComponentsIn (centralizer (U : Set G))) :
    ∃! L₂ : Subgroup G, L₂ ∈ Chapter1.cComponentsIn (centralizer (W : Set G)) ∧
      L ≤ L₂ := by
  let _ := h.elementary
  let H := centralizer (U : Set G)
  let H₂ := centralizer (W : Set G)
  let Q := sylowCentralizer (T : Subgroup G) V
  have hUH : U ≤ H := hU.1.trans (V.le_centralizer.trans (Subgroup.centralizer_le hU.1))
  have hH : H ∈ Chapter1.H G := by
    have hcore : U ≤ H.pCoreIn 2 := le_pCoreIn_of_normalizes
      ((IsElementaryAbelian.isPGroup 2 V).to_le hU.1) hUH (centralizer_le_normalizer _)
    exact fun he => hU.2.1 (le_bot_iff.mp (he ▸ hcore))
  have hQ : Chapter1.IsSylowIn 2 Q H := h.sylow_obstruction hU
  have hlocal : L ∈ Chapter1.L G Q := Chapter1.mem_L_of_cComponent hH hQ hL.1 hL.2
  have hLH₂ : L ≤ H₂ := hL.1.trans (Subgroup.centralizer_le hWU)
  obtain ⟨S, hS⟩ := h.sylow_obstruction hW
  change (S : Subgroup H₂).map H₂.subtype = Q at hS
  have hQH₂ : Q ≤ H₂ := hS ▸ map_subtype_le (S : Subgroup H₂)
  have hloc₂ := (Chapter1.mem_LIn_iff_subgroupOf hQH₂ hLH₂).mp ⟨hLH₂, hlocal⟩
  have hQS : Q.subgroupOf H₂ = (S : Subgroup H₂) := by
    rw [← hS]
    exact comap_map_eq_self_of_injective H₂.subtype_injective _
  rw [hQS] at hloc₂
  exact (Chapter1.existsUnique_cComponentsIn_iff hLH₂).mp
    (earlier H₂ (h.obstructionCentralizer_sqtk hW) S _ hloc₂)

omit [Finite G] in
/-- A two-perfect subgroup of H lies in the two-residual computed inside H. -/
private theorem twoPerfect_le_residual {R H : Subgroup G}
    (hRH : R ≤ H) (hR : IsPPerfect 2 R) :
    R ≤ (pResidual 2 H).map H.subtype := by
  intro x hx
  have hxR : (⟨x, hx⟩ : R) ∈ pResidual 2 R := by
    rw [(pResidual_eq_top_iff 2 R).mpr hR]
    trivial
  refine ⟨inclusion hRH ⟨x, hx⟩, ?_, rfl⟩
  exact map_pResidual_le 2 (inclusion hRH) (mem_map_of_mem _ hxR)

/-- A genuine residual lift inside a local centralizer normalizes each of its
C-components by 1.2.1(3), without an odd-order assertion about any preimage. -/
theorem residualLift_normalizes_cComponent (h : HypothesisE61 K T M V)
    (earlier : EarlierResidualNormalization K)
    (hW : W ∈ obstructionFamily M V) (B : Subgroup (Automizer V))
    (hR : residualLift V B ≤ centralizer (W : Set G))
    (hL : L ∈ Chapter1.cComponentsIn (centralizer (W : Set G))) :
    residualLift V B ≤ normalizer (L : Set G) := by
  let H := centralizer (W : Set G)
  have hn := earlier H (h.obstructionCentralizer_sqtk hW) (L.subgroupOf H) hL.2
  have hn' : (pResidual 2 H).map H.subtype ≤ normalizer (L : Set G) := by
    have hb := (map_mono (f := H.subtype) hn).trans (le_normalizer_map H.subtype)
    rwa [map_subgroupOf_eq_of_le hL.1] at hb
  exact (twoPerfect_le_residual hR (residualLift_twoPerfect V B)).trans hn'
/-- Construction of the actual enlarged component and its corank-three fixed
space in the exceptional two-factor case. Model identification is separate. -/
theorem exceptional_enlargement [IsElementaryAbelian 2 V]
    (h : HypothesisE61 K T M V)
    (containment : EarlierLocalContainment K)
    (normalization : EarlierResidualNormalization K)
    (hU : U ∈ obstructionFamily M V) (hX : RegularCyclicSection M V U X)
    (D : Representation.RegularCyclicNormalClosure.Decomposition
      (automizerRepresentation V) (inducedAutomizer V X))
    (j : Fin D.size) (hij : D.distinguished ≠ j)
    (htwo : ∀ k, k = D.distinguished ∨ k = j)
    (hC : Nat.card (inducedAutomizer V X) = 3)
    (hmodel : Nonempty (D.factor D.distinguished ≃* Frobenius21.Model))
    (hgen : normalClosure ((inducedAutomizer V X).subgroupOf
      (D.factor D.distinguished) : Set (D.factor D.distinguished)) = ⊤)
    (hdim : ∀ i, Module.finrank (ZMod 2) (D.summand i) = 3)
    (hact : ∀ a ∈ inducedAutomizer V
        (M ⊓ centralizer (subspaceGroup (D.summand j) : Set G)),
      ∃ b ∈ D.factor D.distinguished, ∀ v ∈ D.summand D.distinguished,
        automizerRepresentation V a v = automizerRepresentation V b v)
    (hL : L ∈ Chapter1.cComponentsIn (centralizer (U : Set G)))
    (hXL : X ≤ L) (hfixed : V ⊓ centralizer (L : Set G) = U) :
    let W := subspaceGroup (D.summand j)
    W ≤ U ∧ W.relIndex U = 2 ∧ W ∈ obstructionFamily M V ∧
      ∃ L₂ : Subgroup G,
        L₂ ∈ Chapter1.cComponentsIn (centralizer (W : Set G)) ∧
        L < L₂ ∧ generatedFactorLift V X (D.factor D.distinguished) ≤ L₂ ∧
        V ⊓ centralizer (L₂ : Set G) = W ∧
        subgroupCorank V (V ⊓ centralizer (L₂ : Set G)) = 3 := by
  dsimp only
  obtain ⟨hWU, hWcor, hW, _⟩ :=
    exceptional_summand_obstruction h hU hX D j hij htwo hdim hmodel hact
  have hr := exceptional_corank_eq_two hX hC
  obtain ⟨L₂, ⟨hL₂, hLL₂⟩, _⟩ :=
    exists_containing_cComponent h containment hU hW hWU hL
  have ho : Odd (Nat.card (D.factor D.distinguished)) := by
    obtain ⟨e⟩ := hmodel
    rw [Nat.card_congr e.toEquiv, Frobenius21.card_model]
    decide
  have hf := residualLift_fixed_other h hU hX D j hij htwo ho
  have hRH : residualLift V (D.factor D.distinguished) ≤
      centralizer (subspaceGroup (D.summand j) : Set G) := by
    apply le_centralizer_iff.mpr
    rw [← hf]
    exact inf_le_right
  have hn := residualLift_normalizes_cComponent h normalization hW _ hRH hL₂
  obtain ⟨hYL₂, heq, hcor⟩ := containing_fixedSpace_eq_other h hU hX D j hij htwo
    hC hmodel hgen (hdim D.distinguished) L₂ (hXL.trans hLL₂) hL₂.1 hn
  have hne : L ≠ L₂ := by
    intro he
    rw [← he, hfixed, hr] at hcor
    contradiction
  exact ⟨hWU, relativeIndex_eq_two_of_coranks hWU hU.1 hWcor hr, hW,
    L₂, hL₂, lt_of_le_of_ne hLL₂ hne, hYL₂, heq, hcor⟩
end CFSG.Quasithin.ChapterE.Section06.FrobeniusReduction.LocalFactors
