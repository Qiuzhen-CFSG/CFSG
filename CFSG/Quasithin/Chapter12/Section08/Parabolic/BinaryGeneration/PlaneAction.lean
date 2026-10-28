module

public import CFSG.Quasithin.Chapter12.Section08.Parabolic.Basic
public import Theory.Representation.BinaryFlagPlaneAction

/-!
# The full action of the literal minimal parabolic on its plane

The full action is assumed only for LT, as supplied by 12.8.3, including
its rank-two alternative. Extending a plane automorphism by the identity
on one complement preserves every retained flag cut. A representative in
LT consequently belongs to the original P. This supplies the action-image
premise of the G₂ normal-closure and relative-normality theorems.

Source: Aschbacher–Smith, Lemma 12.8.9(1), printed pp.852–853.
-/

@[expose] public section
open Subgroup
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section08.InvariantFlag
variable {G : Type*} [Group G] {T : Sylow 2 G} {V : Subgroup G} {n : ℕ}

/-- The actual LT conjugation action; surjectivity need not hold for L. -/
def binarySeedAction (F : InvariantFlag T V n) (L : Subgroup G)
    (hL : L ≤ normalizer (V : Set G)) :
    (L ⊔ (T : Subgroup G) : Subgroup G) →* MulAut V :=
  V.normalizerMonoidHom.comp (inclusion (sup_le hL (by
    simpa only [F.last] using F.invariant n)))

@[simp] theorem binarySeedAction_apply (F : InvariantFlag T V n) (L : Subgroup G)
    (hL : L ≤ normalizer (V : Set G))
    (x : (L ⊔ (T : Subgroup G) : Subgroup G)) (v : V) :
    (F.binarySeedAction L hL x v : G) = (x : G) * (v : G) * (x : G)⁻¹ := rfl

/-- The literal plane action, with left conjugation on elements. The source
subgroup conjugation Aᵍ remains right conjugation. -/
def binaryPlaneAction (F : InvariantFlag T V n) (hn : 2 ≤ n) (L : Subgroup G)
    (hL : L ≤ normalizer (V : Set G)) : F.P L →* MulAut (F.Vi 2) :=
  (F.Vi 2).normalizerMonoidHom.comp (inclusion (F.P_le_G₂ hn L hL))

@[simp] theorem binaryPlaneAction_apply (F : InvariantFlag T V n) (hn : 2 ≤ n)
    (L : Subgroup G) (hL : L ≤ normalizer (V : Set G)) (x : F.P L) (v : F.Vi 2) :
    (F.binaryPlaneAction hn L hL x v : G) = (x : G) * (v : G) * (x : G)⁻¹ := rfl

/-- Full LT action gives all plane automorphisms inside the actual P. -/
theorem binaryPlaneAction_surjective (F : InvariantFlag T V n) [IsElementaryAbelian 2 V]
    (hn : 2 ≤ n) (L : Subgroup G) (hL : L ≤ normalizer (V : Set G))
    (hfull : Function.Surjective (F.binarySeedAction L hL)) :
    Function.Surjective (F.binaryPlaneAction hn L hL) := by
  intro a
  let A := (F.Vi 2).subgroupOf V
  let e : A ≃* F.Vi 2 := subgroupOfEquivOfLe (F.le_seed 2)
  obtain ⟨b, hb, hcuts⟩ := BinaryFlagPlaneAction.exists_extension A (MulAut.congr e.symm a)
  obtain ⟨x, hx⟩ := hfull b
  have hxV : (x : G) ∈ normalizer (V : Set G) :=
    (sup_le hL (by simpa only [F.last] using F.invariant n)) x.property
  have hxP : (x : G) ∈ F.P L := by
    refine ⟨x.property, mem_iInf.mpr fun i => mem_iInf.mpr fun hi => ?_⟩
    rw [Gi, mem_normalizer_iff]
    intro v
    have hc := hcuts ((F.Vi i).subgroupOf V) (fun z hz => F.monotone hi.1 hz)
    constructor
    · intro hv
      have hh := (hc ⟨v, F.le_seed i hv⟩).mpr hv
      rw [← hx] at hh
      exact hh
    · intro hv
      have hvV : v ∈ V := (mem_normalizer_iff.mp hxV v).mpr (F.le_seed i hv)
      apply (hc ⟨v,hvV⟩).mp
      rw [← hx]
      exact hv
  refine ⟨⟨x, hxP⟩, ?_⟩
  ext v
  have hh := hb (e.symm v)
  rw [← hx] at hh
  have hhG := congrArg (fun y : V => (y : G)) hh
  change (x : G) * (v : G) * (x : G)⁻¹ =
    ((e.symm (a (e (e.symm v))) : A) : V).val at hhG
  rw [e.apply_symm_apply] at hhG
  exact hhG

/-- All G₂ plane actions have representatives in P. -/
theorem binaryPlaneAction_image (F : InvariantFlag T V n) [IsElementaryAbelian 2 V]
    (hn : 2 ≤ n) (L : Subgroup G) (hL : L ≤ normalizer (V : Set G))
    (hfull : Function.Surjective (F.binarySeedAction L hL)) :
    ∀ k ∈ F.Gi 2, ∃ p ∈ F.P L,
      ∀ v ∈ F.Vi 2, k * v * k⁻¹ = p * v * p⁻¹ := by
  intro k hk
  obtain ⟨p, hp⟩ := F.binaryPlaneAction_surjective hn L hL hfull
    ((F.Vi 2).normalizerMonoidHom ⟨k,hk⟩)
  refine ⟨p, p.property, fun v hv => ?_⟩
  exact (congrArg (fun a : MulAut (F.Vi 2) => (a ⟨v,hv⟩ : G)) hp).symm

/-- Discharge the actual image premise in the existing source span consumer. -/
theorem binary_parabolic_span_normality (F : InvariantFlag T V n)
    [IsElementaryAbelian 2 V] (hn : 2 ≤ n) (L : Subgroup G)
    (hL : L ≤ normalizer (V : Set G))
    (hfull : Function.Surjective (F.binarySeedAction L hL))
    (hcomm : ⁅F.U, F.U⁆ ≤ F.Vi 1) :
    F.I₂ L = conjugateSpanBy F.U (F.Gi 2) ∧ F.I₂ L ≤ F.Gi 2 ∧
      ((F.I₂ L).subgroupOf (F.Gi 2)).Normal :=
  F.parabolic_span_normality hn L hL hcomm (F.binaryPlaneAction_image hn L hL hfull)

end CFSG.Quasithin.Chapter12.Section08.InvariantFlag
