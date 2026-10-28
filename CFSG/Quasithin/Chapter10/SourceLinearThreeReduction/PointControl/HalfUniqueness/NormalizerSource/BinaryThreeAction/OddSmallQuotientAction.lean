module

public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.HalfUniqueness.NormalizerSource.BinaryThreeAction.OddSmallDetectedAction

/-!
# The original module acts faithfully on the containing quotient

Keep E = ⟨N_G(T₁),H⟩, K = ⟨O²(H)^E⟩, Q = O₂(K), and the
original module V. The image of V on Q/Φ(Q) normalizes the image of K/Q
on that same section. The common-kernel generation theorem makes its
conjugation action faithful. Transporting through the original faithful
K/Q action gives an embedding into Aut(K/Q), fixing the original cubic
image pointwise.

This permits automorphism calculations without assuming V ≤ K. It does
not assert that the module image is nontrivial or consists of inner
automorphisms, and does not close the original normalizer obstruction.
Source: Aschbacher--Smith 10.2.4--5, printed pp.747--748.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter10.PointControl.HalfUniqueness.BinaryThreeAction.Parabolics
open Chapter3.Section02 Chapter1 Chapter1.XiEmbedding
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L H P I : Subgroup G}
  {D : FundamentalSetup KnownSimple.IsKnownSimple T L}
  {s : NaturalData D} {hz : D.fullModule ⊓ centralizer (localOrbit T L : Set G) = ⊥}

/-- The entire original module action normalizes the faithful containing
quotient image, regardless of placement of V in K. -/
theorem Data.moduleFrattiniImage_normalizes_quotientImage (h : Data D H)
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G)) :
    moduleFrattiniImage D H ≤
      normalizer ((h.coreQuotientFrattiniAction hn).range : Set _) := by
  let E := enlargement T L H
  let K := enlargedResidual T L H
  let a := coreFrattiniAction T L H
  have he : (h.coreQuotientFrattiniAction hn).range = (K.subgroupOf E).map a := by
    ext b
    constructor
    · rintro ⟨x,rfl⟩
      obtain ⟨k,rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 K) x
      exact ⟨inclusion h.enlargedResidual_le_enlargement k,k.property,rfl⟩
    · rintro ⟨k,hk,rfl⟩
      exact ⟨QuotientGroup.mk' _ (⟨k,hk⟩ : K),rfl⟩
  let : (K.subgroupOf E).Normal := h.enlargedResidual_normal
  rw [he]
  apply le_trans (map_mono (show D.fullModule.subgroupOf E ≤
    normalizer (K.subgroupOf E : Set E) from ?_)) (le_normalizer_map a)
  rw [normalizer_eq_top]
  exact le_top

/-- The actual module image embeds in automorphisms of the original K/Q,
with the same conjugation marking and pointwise-fixed cubic image. No
containment V ≤ K and no nontriviality premise is needed. -/
theorem Data.exists_faithful_moduleQuotientAction (h : Data D H) (f : LiftData s hz)
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hs : SwappedSylowInput KnownSimple.IsKnownSimple 3 (T : Subgroup G)
      (residual H) P (enlargement T L H) I)
    (hK : enlargedResidual T L H = componentOrbit I (T : Subgroup G))
    {p : ℕ} (hp : p.Prime) (ho : Odd p)
    (hm : ClassicalGroup.IsPSL (XiQuotient I) 2 p) (hlarge : 11 ≤ p)
    (hP : Nat.card P = 9)
    (hc : (residual H).pCoreIn 2 ≤ (enlargedResidual T L H).pCoreIn 2) :
    ∃ φ : moduleFrattiniImage D H →* MulAut (XiQuotient (enlargedResidual T L H)),
      Function.Injective φ ∧
      (∀ a x, h.coreQuotientFrattiniAction hn (φ a x) =
        (a : MulAut (CoreFrattiniSection T L H)) *
          h.coreQuotientFrattiniAction hn x * (a : MulAut (CoreFrattiniSection T L H))⁻¹) ∧
      ∀ a x, x ∈ quotientImage (enlargedResidual T L H) P → φ a x = x := by
  let b := h.coreQuotientFrattiniAction hn
  let B := b.range
  let A := moduleFrattiniImage D H
  have hAB : A ≤ normalizer (B : Set _) := h.moduleFrattiniImage_normalizes_quotientImage hn
  let r : A →* MulAut B := B.normalizerMonoidHom.comp (inclusion hAB)
  have hr : Function.Injective r := by
    apply r.ker_eq_bot_iff.mp
    apply bot_unique
    intro a ha
    apply Subtype.ext
    change inclusion hAB a ∈ B.normalizerMonoidHom.ker at ha
    rw [normalizerMonoidHom_ker] at ha
    exact (h.collapsed_moduleFrattiniImage_disjoint_centralizer f hn hs hK hp ho hm
      hlarge hP hc).le_bot ⟨a.property,ha⟩
  let e : XiQuotient (enlargedResidual T L H) ≃* B :=
    MonoidHom.ofInjective (h.coreQuotientFrattiniAction_injective hn)
  let φ : A →* MulAut (XiQuotient (enlargedResidual T L H)) :=
    (MulAut.congr e.symm).toMonoidHom.comp r
  have hmark (a : A) (x : XiQuotient (enlargedResidual T L H)) :
      b (φ a x) = (a : MulAut (CoreFrattiniSection T L H)) * b x *
        (a : MulAut (CoreFrattiniSection T L H))⁻¹ := by
    change b (e.symm (r a (e x))) = _
    rw [MonoidHom.apply_ofInjective_symm]
    rfl
  refine ⟨φ,(MulAut.congr e.symm).injective.comp hr,hmark,?_⟩
  intro a x hx
  apply h.coreQuotientFrattiniAction_injective hn
  rw [hmark]
  obtain ⟨k,hk,rfl⟩ := hx
  have hcent := h.collapsed_cubic_centralizes_moduleFrattiniImage s.full_eq_local hn
    hs.toLocalInput hc
  have hp : coreFrattiniAction T L H (inclusion h.enlargedResidual_le_enlargement k) ∈
      (P.subgroupOf (enlargement T L H)).map (coreFrattiniAction T L H) :=
    mem_map_of_mem _ hk
  have he := hcent hp _ a.property
  rw [h.coreQuotientFrattiniAction_mk]
  change (a : MulAut (CoreFrattiniSection T L H)) *
      coreFrattiniAction T L H (inclusion h.enlargedResidual_le_enlargement k) *
        (a : MulAut (CoreFrattiniSection T L H))⁻¹ = _
  rw [he,mul_inv_cancel_right]

end CFSG.Quasithin.Chapter10.PointControl.HalfUniqueness.BinaryThreeAction.Parabolics

namespace CFSG.Quasithin.Chapter10.PointControl.HalfUniqueness
open Subgroup Theory.GroupTheory
open Chapter3.Section02 Chapter1 Chapter1.XiEmbedding BinaryThreeAction BinaryThreeAction.Parabolics
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}

/-- The original collapsed obstruction supplies its own faithful quotient
automorphisms and cubic marking. The possible trivial image remains explicit. -/
theorem SourceCubicNormalizerEnlargement.exists_faithful_moduleQuotientAction
    {D : FundamentalSetup KnownSimple.IsKnownSimple T L}
    (hc : SourceCubicNormalizerEnlargement D) :
    ∃ H P : Subgroup G, ∃ h : Data D H,
      ∃ hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G),
      LocalInput 3 (T : Subgroup G) (residual H) P (enlargement T L H) ∧
      (moduleFrattiniImage D H = ⊥ ∨ Nat.card (moduleFrattiniImage D H) = 4) ∧
      ∃ φ : moduleFrattiniImage D H →* MulAut (XiQuotient (enlargedResidual T L H)),
        Function.Injective φ ∧
        (∀ a x, h.coreQuotientFrattiniAction hn (φ a x) =
          (a : MulAut (CoreFrattiniSection T L H)) *
            h.coreQuotientFrattiniAction hn x * (a : MulAut (CoreFrattiniSection T L H))⁻¹) ∧
        ∀ a x, x ∈ quotientImage (enlargedResidual T L H) P → φ a x = x := by
  obtain ⟨_,_,hfull,hn,_,hmodel,hzero,hJ,H,P,I,p,h,hs,hK,hp,ho,hm,_,h24,_,_,_,hcollapse⟩ := hc
  obtain ⟨t,ht,htn,_,_⟩ := source_nonnormal_pair D.simpleQTKE D.maximal.1 hn
  have hcross := Selection.ModuleChoice.crossed_of_local_thompson D (hfull ▸ hJ) ht htn
  obtain ⟨s,_⟩ := exists_naturalData D hmodel hzero hfull ht htn hcross
  let f := originalLift s s.fixed_zero
  obtain ⟨e,_,_,_⟩ := h.swapped_quotient_intersection hn hs hK
  have hP := (hs.toLocalInput.complement_elementary_of_commutative
    (SwappedFactorsProof.complement_commutative hs.toSwappedInput (hK ▸ e))).2
  have hlarge : 11 ≤ p := by have := Nat.mod_le p 24; omega
  exact ⟨H,P,h,hn,hs.toLocalInput,
    h.collapsed_moduleFrattiniImage_bot_or_four f hn hs.toLocalInput hP hcollapse,
    h.exists_faithful_moduleQuotientAction f hn hs hK hp ho hm hlarge hP hcollapse⟩

end CFSG.Quasithin.Chapter10.PointControl.HalfUniqueness
