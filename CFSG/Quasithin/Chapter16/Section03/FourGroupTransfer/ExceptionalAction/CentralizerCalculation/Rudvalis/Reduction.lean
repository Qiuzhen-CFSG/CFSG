module

public import CFSG.Quasithin.Chapter16.Section03.FourGroupTransfer.ExceptionalAction.CentralizerCalculation.Quotient
public import CFSG.Quasithin.Chapter16.Section03.FourGroupTransfer.ExceptionalAction.CentralizerCalculation.Transport
public import BenderSuzuki.External.Huppert.XI.theorem_3_6
public import Theory.GroupTheory.AutomorphismTowerSimple

/-!
# Reducing the Rudvalis pair fixer to an intrinsic element centralizer

Let P be the image of the actual embedded L under I → I/O₂(I) ≃ Ru.
The supplied L ≃ Sz(8), together with the checked simplicity of Sz(8),
makes L centerless. The central kernel of the cover therefore intersects L
trivially, so the projection identifies L with P. Simplicity and perfectness
of Ru are inherited from the given component I and quotient equivalence.

If every automorphism of Ru is inner, conjugation identifies C_Ru(P) with
the full pointwise fixer of P. The faithful order-four action on I and the
injective descent of automorphisms give |C_Ru(P)| ≥ 4. An intrinsic upper
bound and square calculation then descend back to the original pair fixer.

`ElementCentralizerBound` records the remaining intrinsic calculation. It
uses the actual subgroup P and an actual Sz(8) equivalence. It is not a
consequence here of the abstract E₄ × Sz(8) involution-centralizer shape.
The conditional assembly below does not establish the Rudvalis row until
both the innerness and element-centralizer inputs have been proved.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
16.1.2, 16.1.5(11), 16.1.7(3i), and 16.3.5, printed pp.1170–1173
and 1178–1179. GLS3 Table 5.3r, p.279, additionally describes the
(E₄ × Sz(8)).3 normalizer with its coupled action, relevant to the
outstanding element-centralizer calculation.
-/

public section

namespace CFSG.Quasithin.Chapter16.FourGroupTransfer.ExceptionalAction.CentralizerCalculation.RudvalisPair
open Subgroup Theory.GroupTheory PerfectCentralCovering ClassificationModels

/-- The actual degree-4060 Rudvalis permutation carrier. -/
abbrev Model := _root_.Rudvalis.Model
/-- The Suzuki matrix carrier with field order eight. -/
noncomputable abbrev SzEight := BenderSuzuki.MatrixGroups.SuzukiMatrixGroup 1

/-- The precise intrinsic obligation still to be discharged. The lower bound
comes from the faithful actor in the application, and is not an assumption
about the abstract isomorphism type of the full automorphism fixer. -/
@[expose] def ElementCentralizerBound : Prop :=
  ∀ P : Subgroup Model, Nonempty (P ≃* SzEight) →
    4 ≤ Nat.card (centralizer (P : Set Model)) →
    Nat.card (centralizer (P : Set Model)) ≤ 4 ∧
      ∀ x : centralizer (P : Set Model), x ^ 2 = 1

private theorem center_eq_bot_of_simple_perfect {A : Type*} [Group A]
    [IsSimpleGroup A] [Group.IsPerfect A] : center A = ⊥ := by
  rcases (inferInstance : (center A).Normal).eq_bot_or_eq_top with h | h
  · exact h
  · exact (Group.IsPerfect.not_isMulCommutative A (center_eq_top_iff.mp h)).elim

variable {G : Type*} [Group G] [Finite G] {𝒦 : GroupClass}
variable {E L I : Subgroup G} {t i : G}

/-- The image of the actual smaller subgroup under the specified quotient cover. -/
@[expose] noncomputable def projectedSubgroup (h : PairContext E L I t i)
    (hG : Hypothesis1611 𝒦 G) (e : (I ⧸ pCore 2 I) ≃* Model) : Subgroup Model :=
  (L.subgroupOf I).map (h.coreCover hG e).toMonoidHom

/-- Quasisimplicity of I supplies simplicity of the specified quotient model. -/
theorem model_isSimple (h : PairContext E L I t i)
    (hG : Hypothesis1611 𝒦 G) (e : (I ⧸ pCore 2 I) ≃* Model) : IsSimpleGroup Model := by
  let := h.component.quasisimple
  let := IsQuasisimple.simple (G := I)
  let q := (QuotientGroup.quotientMulEquivOfEq
    (hG.evenType.component_center_eq_twoCore h.setup.involution_i h.component)).trans e
  exact q.symm.isSimpleGroup

/-- Perfectness is transported from the component, without model certification. -/
theorem model_isPerfect (h : PairContext E L I t i)
    (hG : Hypothesis1611 𝒦 G) (e : (I ⧸ pCore 2 I) ≃* Model) : Group.IsPerfect Model := by
  let f := h.coreCover hG e
  let := f.isPerfect
  exact Group.IsPerfect.ofSurjective f.surjective

/-- The quotient projection is injective on the actual L ≃ Sz(8): a central
kernel restricts to the trivial center of this simple perfect subgroup. -/
noncomputable def projectedEquiv (h : PairContext E L I t i)
    (hG : Hypothesis1611 𝒦 G) (e : (I ⧸ pCore 2 I) ≃* Model)
    (eL : L ≃* SzEight) : L ≃* projectedSubgroup h hG e := by
  let := (BenderSuzuki.External.huppert_blackburn_XI_3_6 1 (by decide)).1
  let := eL.isSimpleGroup
  let := h.setup.component.quasisimple
  have hZ : center L = ⊥ := center_eq_bot_of_simple_perfect
  let f := h.coreCover hG e
  let j : L →* I := inclusion h.proper.le
  have hfi : Function.Injective (f.toMonoidHom.comp j) := by
    apply (MonoidHom.ker_eq_bot_iff _).mp
    apply le_bot_iff.mp
    intro x hx
    have hzI : j x ∈ center I := f.ker_le_center hx
    have hzL : x ∈ center L := by
      rw [mem_center_iff]
      intro y
      apply Subtype.ext
      exact congrArg (fun z : I => (z : G)) (mem_center_iff.mp hzI (j y))
    simpa only [hZ] using hzL
  let fP := f.toMonoidHom.subgroupMap (L.subgroupOf I)
  have hfP : Function.Injective fP := by
    intro x y hxy
    have heq : (⟨x, x.property⟩ : L) = ⟨y, y.property⟩ :=
      hfi (congrArg Subtype.val hxy)
    exact Subtype.ext (Subtype.ext (congrArg (fun z : L => (z : G)) heq))
  exact (subgroupOfEquivOfLe h.proper.le).symm.trans
    (MulEquiv.ofBijective fP ⟨hfP, f.toMonoidHom.subgroupMap_surjective _⟩)

/-- The equivalence with the projected subgroup is the original quotient map,
restricted to the actual smaller subgroup. -/
theorem projectedEquiv_apply (h : PairContext E L I t i)
    (hG : Hypothesis1611 𝒦 G) (e : (I ⧸ pCore 2 I) ≃* Model)
    (eL : L ≃* SzEight) (x : L) :
    ((projectedEquiv h hG e eL x : projectedSubgroup h hG e) : Model) =
      e (QuotientGroup.mk' (pCore 2 I) ⟨x, h.proper.le x.property⟩) := by
  unfold projectedEquiv
  rfl

private noncomputable def elementCentralizerEquivFixer
    (hc : center Model = ⊥)
    (hi : Function.Surjective (MulAut.conj : Model →* MulAut Model))
    (P : Subgroup Model) :
    centralizer (P : Set Model) ≃* fixingSubgroup (MulAut Model) (P : Set Model) := by
  let f : centralizer (P : Set Model) →*
      fixingSubgroup (MulAut Model) (P : Set Model) :=
    ((MulAut.conj : Model →* MulAut Model).comp (centralizer (P : Set Model)).subtype).codRestrict
      _ (fun x => by
        rw [mem_fixingSubgroup_iff]
        intro p hp
        change (x : Model) * p * (x : Model)⁻¹ = p
        rw [← mem_centralizer_iff.mp x.property p hp, mul_inv_cancel_right])
  refine MulEquiv.ofBijective f ⟨?_, ?_⟩
  · intro x y hxy
    apply Subtype.ext
    exact MulAut.conj_injective_of_center_eq_bot hc (congrArg Subtype.val hxy)
  · intro a
    obtain ⟨x, hx⟩ := hi a
    have hxC : x ∈ centralizer (P : Set Model) := by
      rw [mem_centralizer_iff]
      intro p hp
      have he : (a : MulAut Model) p = p := a.property ⟨p, hp⟩
      change (a : MulAut Model) p = p at he
      rw [← hx] at he
      exact (mul_inv_eq_iff_eq_mul.mp he).symm
    exact ⟨⟨x, hxC⟩, Subtype.ext hx⟩

/-- Conditional assembly of the Ru–Sz(8) bound. Both model inputs may use
simplicity and perfectness inherited from the actual component and quotient.
Neither missing input is asserted by this theorem. -/
theorem rudvalisBound_of_inner_of_elementCentralizers
    (h : PairContext E L I t i) (hG : Hypothesis1611 𝒦 G)
    (hi : ∀ (_ : IsSimpleGroup Model) (_ : Group.IsPerfect Model),
      Function.Surjective (MulAut.conj : Model →* MulAut Model))
    (hb : ∀ (_ : IsSimpleGroup Model) (_ : Group.IsPerfect Model),
      ElementCentralizerBound) : RudvalisBound L I := by
  change Nonempty ((I ⧸ pCore 2 I) ≃* Model) → Nonempty (L ≃* SzEight) → FourBound L I
  rintro ⟨e⟩ ⟨eL⟩
  let hs := model_isSimple h hG e
  let hp := model_isPerfect h hG e
  let := hs
  let := hp
  let : Finite Model := Finite.of_surjective (h.coreCover hG e).toMonoidHom
    (h.coreCover hG e).surjective
  let f := h.coreCover hG e
  let P := projectedSubgroup h hG e
  let c := elementCentralizerEquivFixer center_eq_bot_of_simple_perfect (hi hs hp) P
  have hP : Nonempty (P ≃* SzEight) := ⟨(projectedEquiv h hG e eL).symm.trans eL⟩
  have hl : 4 ≤ Nat.card (centralizer (P : Set Model)) := by
    rw [Nat.card_congr c.toEquiv]
    calc
      4 = Nat.card E := h.card.symm
      _ ≤ Nat.card (pairFixer L I) :=
        card_le_pairFixer h.normalizes h.centralizes h.faithful
      _ ≤ Nat.card (fixingSubgroup (MulAut Model) (P : Set Model)) :=
        Nat.le_of_dvd Nat.card_pos (f.card_fixing_dvd (h.coreCover_kernel hG e) _)
  obtain ⟨hcard, hsq⟩ := hb hs hp P hP hl
  apply fourBound_of_cover f (h.coreCover_kernel hG e)
  · exact (Nat.card_congr c.toEquiv).symm.trans_le hcard
  · intro a
    obtain ⟨x, rfl⟩ := c.surjective a
    change c x ^ 2 = 1
    exact (map_pow c x 2).symm.trans ((congrArg c (hsq x)).trans (map_one c))

end CFSG.Quasithin.Chapter16.FourGroupTransfer.ExceptionalAction.CentralizerCalculation.RudvalisPair
