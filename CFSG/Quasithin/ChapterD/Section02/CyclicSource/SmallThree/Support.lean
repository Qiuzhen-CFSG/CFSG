module
public import CFSG.Quasithin.ChapterD.Section02.CyclicSource.SmallThree.Factors
public import CFSG.Quasithin.ChapterD.Section02.CyclicSource.Preparation
public import CFSG.Quasithin.ChapterD.Section02.CyclicSource.Separation
public import CFSG.Quasithin.ChapterD.Section02.SmallSupportPermutation.NormalizedFactors
public import CFSG.Quasithin.ChapterD.Section02.CyclicSource.SmallThree.FixedComplementSource

/-!
# Full canonical support in the small-three source branch

Involutions centralizing the canonical cubic subgroup fix each of its
irreducible binary planes. The fixed-complement theorem handles all other
small-support involutions using the original Fitting-moved hypothesis.
The starred actors therefore fix one side of the invariant coprime splitting.
Ratio indecomposability and the absence of global fixed vectors force the
nonzero canonical support to be all of V.

This proves the full-support step of Aschbacher–Smith D.2.25, printed p.190,
from the original source hypotheses and the actual order-three witness.
-/

@[expose] public section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
namespace CFSG.Quasithin.ChapterD.CyclicSource
variable {G V : Type*} [Group G] [Finite G]
  [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V)

/-- The positive class in D.2.25 fixes every canonical support plane. -/
theorem canonical_support_fixed_of_centralizes (t : G) (ht : t ^ 2 = 1) :
    let := BinaryGroupAction.action ρ
    t ∈ centralizer (smallSupportGroup G (Multiplicative V) 1 : Set G) →
    subspaceCommutator ρ ⊤ (smallSupportGroup G (Multiplicative V) 1) ≤
      fixedSpace ρ (zpowers t) := by
  let := BinaryGroupAction.action ρ
  let := BinaryGroupAction.elementary (V := V)
  let : Finite V := Module.finite_of_finite (ZMod 2)
  dsimp only
  intro hc
  rw [smallSupportGroup_eq_iSup,BinaryGroupAction.moved_iSup]
  apply iSup_le
  intro X v hv
  apply (mem_fixedSpace_zpowers_iff ρ t v).mpr
  have hx (x : G) (hx : x ∈ X.val) : Commute t x :=
    (hc x (le_sSup X.property hx)).symm
  have hh := smallSupportFactor_support_fixed_of_centralizes
    (G := G) (V := Multiplicative V) (Or.inl rfl) X.property t ht hx
  have hm : Multiplicative.ofAdd v ∈ commutatorAction X.val (Multiplicative V) := by
    rw [BinaryGroupAction.commutator_eq]
    exact hv
  exact congrArg Multiplicative.toAdd (hh _ hm)

/-- D.2.25's two classes of starred actors force the canonical support to be all
of V. The noncentral class uses the separately constructed residual cubic. -/
theorem canonical_moved_of_fixed_complement (h : Hypotheses ρ)
    (hq : cubicRatio ρ = 2)
    (hne : let := BinaryGroupAction.action ρ
      (smallSupportFactors G (Multiplicative V) 1).Nonempty)
    (hfix : let := BinaryGroupAction.action ρ
      ∀ t ∈ smallSupportInvolutions ρ,
        t ∉ centralizer (smallSupportGroup G (Multiplicative V) 1 : Set G) →
        fixedSpace ρ (smallSupportGroup G (Multiplicative V) 1) ≤ fixedSpace ρ (zpowers t)) :
    let := BinaryGroupAction.action ρ
    subspaceCommutator ρ ⊤ (smallSupportGroup G (Multiplicative V) 1) = ⊤ := by
  let := BinaryGroupAction.action ρ
  let Y := smallSupportGroup G (Multiplicative V) 1
  let W := subspaceCommutator ρ ⊤ Y
  let C := fixedSpace ρ Y
  have hodd : Odd (Nat.card Y) := by
    obtain ⟨n,hn⟩ := (pCore_isPGroup (p := 3) (G := G)).to_le
      (canonical_le_threeCore ρ) |>.exists_card_eq
    exact hn ▸ (by decide : Odd 3).pow
  have hsplit : IsCompl W C :=
    (ElementaryCore.SupportExclusion.moved_split ρ Y hodd).symm
  have hW : ∀ g w, w ∈ W → ρ g w ∈ W := by
    intro g w hw
    exact (subspaceCommutator_invariant_normalizer ρ (X := Y) (A := ⊤)
      (D := ⊤) (le_subspaceStabilizer ρ ⊤ (by intros; trivial)) le_normalizer_of_normal
        (mem_top g) w).2 hw
  have hC : ∀ g w, w ∈ C → ρ g w ∈ C :=
    fun g w hw => (normalFixed ρ Y).apply_mem_toSubmodule g hw
  have hWne : W ≠ ⊥ := by
    obtain ⟨X,hX⟩ := hne
    have hx := (show X ∈ {X : Subgroup G | X ≤ pCore 3 G ∧ Nat.card X = 3 ∧
        Module.finrank (ZMod 2) (subspaceCommutator ρ ⊤ X) = 2} from
      (x1_eq_canonical ρ).symm ▸ hX).2.2
    have hle : subspaceCommutator ρ ⊤ X ≤ W := by
      apply Submodule.span_mono
      rintro v ⟨x,hx,v,hv,rfl⟩
      exact ⟨x,le_sSup hX hx,v,hv,rfl⟩
    intro he
    have hz := le_bot_iff.mp (hle.trans_eq he)
    rw [hz,finrank_bot] at hx
    omega
  apply (support_eq_top_of_starred_dichotomy ρ h.generated h.indecomposable
    h.fixedSpace_eq_bot W C hsplit hW hC hWne ?_).1
  intro A hA
  obtain ⟨t,ht,he⟩ := starred_generator ρ hA (h.rank_one A hA)
  have hs : t ∈ smallSupportInvolutions ρ := by
    refine ⟨ht,?_⟩
    have hh := starred_codimension ρ hA (h.rank_one A hA)
    rw [hq] at hh
    have hh' : fixedCodim ρ A ≤ 2 := by exact_mod_cast hh.le
    rw [← he] at hh'
    change Module.finrank (ZMod 2) (ρ t - LinearMap.id).range ≤ 2
    simpa only [fixedCodim_zpowers_eq_displacement_rank] using hh'
  rw [← he]
  by_cases hc : t ∈ centralizer (Y : Set G)
  · exact Or.inl (canonical_support_fixed_of_centralizes ρ t
      (by simpa only [ht] using pow_orderOf_eq_one t) hc)
  · exact Or.inr (hfix t hs hc)
/-- The original D.2.25 full-support conclusion, with the residual-cubic and
indecomposable-separation premises both discharged. -/
theorem Hypotheses.smallThree_moved (h : Hypotheses ρ)
    (hfive : ∀ A ∈ QhatStar ρ, ⁅pCore 5 G,A⁆ = ⊥)
    (hq : cubicRatio ρ = 2)
    (hne : ∃ X : Subgroup G, X ≤ pCore 3 G ∧ Nat.card X = 3 ∧
      Module.finrank (ZMod 2) (subspaceCommutator ρ ⊤ X) = 2) :
    let := BinaryGroupAction.action ρ
    subspaceCommutator ρ ⊤ (smallSupportGroup G (Multiplicative V) 1) = ⊤ := by
  apply canonical_moved_of_fixed_complement ρ h hq
  · let := BinaryGroupAction.action ρ
    obtain ⟨X,hX⟩ := hne
    exact ⟨X,(x1_eq_canonical ρ) ▸ hX⟩
  · let := BinaryGroupAction.action ρ
    dsimp only
    intro t ht
    exact h.toCoreHypotheses.fixed_smallThree_complement ρ h.moved hfive hq ht

end CFSG.Quasithin.ChapterD.CyclicSource