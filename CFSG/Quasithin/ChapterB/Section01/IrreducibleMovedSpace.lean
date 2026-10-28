module

public import Theory.Representation.BinaryOffender.IrreducibleMovedGeneration
public import CFSG.Quasithin.ChapterB.Section01.Restriction

/-!
# B.7.2(1): faithful moved-space reduction

For a moved member I of Irr⁺(X,V), the normalizer action transports
irreducibility to Iᵃ. Their sum W is nonzero and equals both [W,X] and
[[I,a],X]. Since A fixes [I,a] and normalizes X, W is A-invariant, and
moving I guarantees [W,A] ≠ 0.

We then use the actual action image of the stabilizer of W. The representation
`subspaceImageRepresentation ρ W` is faithful; its subgroups
`restrictedSubgroup ρ W A` and `restrictedSubgroup ρ W X` inherit the best
offender, nontriviality, residual, commutator, and central-chief-factor
hypotheses. The chosen image of a satisfies the original quadratic identity.
The restricted member is literally `I.comap W.subtype`, and it and its distinct
image under a span W. The inclusion of W and the surjections from the acting
subgroups are exposed by the imported transport API.

This completes the reduction portion of B.7.2(1). The stabilizer and regular
orbit contradiction belong to the source theorem's assembly owner.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*,
1 March 2004 manuscript, B.7.2(1), printed p. 119 (PDF p. 130).
-/

public section

namespace CFSG.Quasithin.ChapterB
open Representation.BinaryOffender
variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V)

/-- The moved pair and its diagonal generate the same nonzero invariant space. -/
theorem movedSpace_geometry {X A : Subgroup G} (hXA : ⁅X, A⁆ = X)
    {a : G} (ha : a ∈ A)
    (hq : ∀ b ∈ A, ∀ v, ρ b (ρ a v - v) = ρ a v - v)
    {I : Submodule (ZMod 2) V} (hI : IsIrrPlus ρ X I) (hne : I ≠ I.map (ρ a)) :
    let W := I ⊔ I.map (ρ a)
    IsIrrPlus ρ X (I.map (ρ a)) ∧ W ≠ ⊥ ∧
      subspaceCommutator ρ W X = W ∧
      subspaceCommutator ρ (diagonalSubspace ρ I a) X = W ∧
      A ≤ subspaceStabilizer ρ W ∧ subspaceCommutator ρ W A ≠ ⊥ := by
  have hAN : A ≤ Subgroup.normalizer X :=
    Subgroup.le_normalizer_iff_commutator_le_left.mpr hXA.le
  have hIa := hI.map_normalizer ρ (hAN ha)
  have hgen := hI.diagonal_generation ρ hIa hne ha hXA hq
  refine ⟨hIa, ?_, hI.sup_commutator ρ hIa, hgen,
    diagonal_generation_invariant ρ hXA hq hgen, ?_⟩
  · intro he
    exact hI.ne_bot ρ (le_bot_iff.mp (he ▸ (le_sup_left : I ≤ I ⊔ I.map (ρ a))))
  · intro h
    exact movedSpace_not_fixed ρ ha hne ((subspaceCommutator_eq_bot_iff ρ _ A).mp h)

variable [Finite G] [FiniteDimensional (ZMod 2) V]

/-- All source hypotheses descend to the faithful action on the moved space.
The witness `aw` is the image of `a`, as certified by its action under the
inclusion of W. The two actual restricted Irr⁺ subspaces are distinct and span
the whole new module, so the reduced contradiction can be applied here. -/
theorem movedSpace_action_data
    (hfaithful : Function.Injective ρ) {X A : Subgroup G}
    (hA : IsBestOffender ρ A) (_hXne : X ≠ ⊥) (hres : pResidual 2 X = ⊤)
    (hXA : ⁅X, A⁆ = X) (hchief : Subgroup.HasCentralPChiefFactors 2 X)
    {a : G} (ha : a ∈ A)
    (hq : ∀ b ∈ A, ∀ v, ρ b (ρ a v - v) = ρ a v - v)
    {I : Submodule (ZMod 2) V} (hI : IsIrrPlus ρ X I)
    (hne : I ≠ I.map (ρ a)) :
    let W := I ⊔ I.map (ρ a)
    let ρw := subspaceImageRepresentation ρ W
    let Aw := restrictedSubgroup ρ W A
    let Xw := restrictedSubgroup ρ W X
    let Iw := I.comap W.subtype
    Function.Injective ρw ∧ IsBestOffender ρw Aw ∧ Xw ≠ ⊥ ∧
      pResidual 2 Xw = ⊤ ∧ ⁅Xw, Aw⁆ = Xw ∧ Subgroup.HasCentralPChiefFactors 2 Xw ∧
      subspaceCommutator ρw ⊤ Xw = ⊤ ∧ IsIrrPlus ρw Xw Iw ∧
      Iw.map W.subtype = I ∧
      ∃ aw : subspaceActionImage ρ W, aw ∈ Aw ∧
        (∀ w : W, (ρw aw w : V) = ρ a w) ∧
        (∀ b ∈ Aw, ∀ v : W, ρw b (ρw aw v - v) = ρw aw v - v) ∧
        Iw ≠ Iw.map (ρw aw) ∧ Iw ⊔ Iw.map (ρw aw) = ⊤ := by
  obtain ⟨hIa, _, hfull, _, hWA, hmove⟩ := movedSpace_geometry ρ hXA ha hq hI hne
  let W := I ⊔ I.map (ρ a)
  have hWX : X ≤ subspaceStabilizer ρ W := subspaceStabilizer_sup ρ hI.choose hIa.choose
  have hbest := source_lemma_B_7_1_1 ρ W hfaithful hA
    (fun b hb w hw => (hWA hb w).2 hw) hmove
  have hXne : restrictedSubgroup ρ W X ≠ ⊥ := by
    apply restrictedSubgroup_ne_bot ρ W hWX
    intro hfix
    exact hI.not_le_fixedSpace ρ (le_sup_left.trans hfix)
  refine ⟨subspaceImageRepresentation_injective ρ W, hbest, hXne,
    restricted_pResidual_eq_top ρ W X hWX hres,
    restrictedSubgroup_commutator ρ W hWX hWA hXA,
    restricted_centralChiefFactors ρ W X hWX hchief,
    restricted_commutator_eq_top ρ W X hWX hfull,
    hI.restricted ρ hWX le_sup_left, ?_, ?_⟩
  · rw [Submodule.map_comap_subtype, inf_eq_right.mpr (le_sup_left : I ≤ W)]
  · refine ⟨subspaceActionHom ρ W ⟨a, hWA ha⟩, ⟨⟨a, hWA ha⟩, ha, rfl⟩,
      fun _ => rfl, restricted_quadratic ρ W hWA ha hq, ?_⟩
    exact restricted_pair ρ W (hWA ha) le_sup_left hne rfl
end CFSG.Quasithin.ChapterB
