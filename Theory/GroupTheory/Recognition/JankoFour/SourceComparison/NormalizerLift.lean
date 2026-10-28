module
public import Theory.GroupTheory.Recognition.JankoFour.SourceComparison.NormalizerCore
import all Theory.GroupTheory.Recognition.JankoFour.SourceComparison.CentralTwist

/-!
# The central ambiguity in lifting the splitting actor

Compare N_H(A)/Z(H) with N_H'(A')/Z(H') through the same native H/Q
coordinates. Every fiber consists of n and zn, and these have equal squares.
The constructed comparison of the core and six-cover intertwines both
normalizer actions. Lifting the image of the original splitting involution
therefore gives an actor with square 1 or the actual marked z'.

Source: Aschbacher–Segev, Invent. Math. 105 (1991), (8.3), p.606.
The remaining square-one implication is deliberately not asserted. Changing
the lift by z' cannot prove it. The internal import of CentralTwist is only
for the public value equation of its original marker; its definition and
existing public boundary are unchanged.
-/

@[expose] public section
namespace Theory.GroupTheory.Recognition.JankoFour.SourceComparison
open Subgroup SourceRecognition LocalGeometry Sporadic.Mathieu PerfectCentralCovering
variable {G : Type*} [Group G] [Finite G] {z : G}
variable (h : IsTypeJ4 z)
variable (e : CubicAutomorphismQuotient (centralizer z ⧸ core z))
variable (X : Sylow 3 (CubicLift.subgroup e))

omit [Finite G] in
/-- Value of the original marked involution in the ambient group. -/
theorem planeMarker_val : (planeMarker (z := z) : G) = z := by rfl

include h in
/-- The two elements of the actual plane center, with the marker retained. -/
theorem planeCenter_cases (g : centralizer z) (hg : g ∈ center (centralizer z)) :
    g = 1 ∨ g = planeMarker (z := z) := by
  by_cases hg1 : g = 1
  · exact Or.inl hg1
  · have hm : planeMarker (z := z) ≠ 1 := by
      intro he
      have hz : z = 1 := by simpa only [planeMarker_val,Subgroup.coe_one] using congrArg Subtype.val he
      have ho := h.involution
      rw [hz,orderOf_one] at ho
      contradiction
    obtain ⟨w,_,hw⟩ := (Nat.card_eq_two_iff' (1 : center (centralizer z))).mp
      (centralizer_center_card h)
    exact Or.inr (congrArg Subtype.val
      ((hw ⟨g,hg⟩ (fun he => hg1 (congrArg Subtype.val he))).trans
        (hw ⟨planeMarker,planeMarker_central⟩ (fun he => hm (congrArg Subtype.val he))).symm))

include h in
/-- Matching the literal quotient leaves exactly multiplication by z. -/
theorem cubicNormalizer_fiber (m n : cubicNormalizerInH e X) :
    cubicNormalizerToCore e X m = cubicNormalizerToCore e X n ↔
      m.val = n.val ∨ m.val = planeMarker * n.val := by
  constructor
  · intro he
    have hk : m*n⁻¹ ∈ (cubicNormalizerToCore e X).ker := by
      change cubicNormalizerToCore e X (m*n⁻¹)=1
      rw [map_mul,map_inv,he,mul_inv_cancel]
    rw [cubicNormalizerToCore_ker h e X] at hk
    rcases planeCenter_cases h (m.val*n.val⁻¹) hk with h1 | hz
    · exact Or.inl (mul_inv_eq_one.mp h1)
    · exact Or.inr (mul_inv_eq_iff_eq_mul.mp hz)
  · intro he
    change QuotientGroup.mk' (core z) m.val = QuotientGroup.mk' (core z) n.val
    rcases he with he | he
    · rw [he]
    · rw [he,map_mul,show QuotientGroup.mk' (core z) planeMarker = 1 from
        (QuotientGroup.eq_one_iff _).mpr (centralizer_center_le_core h planeMarker_central),one_mul]

include h in
/-- The residual central correction cannot change the square of a lift. -/
theorem cubicNormalizer_same_fiber_square (m n : cubicNormalizerInH e X)
    (he : cubicNormalizerToCore e X m = cubicNormalizerToCore e X n) :
    m.val*m.val = n.val*n.val := by
  rcases (cubicNormalizer_fiber h e X m n).mp he with hm | hm
  · rw [hm]
  · rw [hm]
    calc
      _ = (planeMarker*planeMarker)*(n.val*n.val) := by
        rw [mul_assoc,←mul_assoc n.val planeMarker n.val,
          mem_center_iff.mp planeMarker_central n.val]
        group
      _ = _ := by rw [planeMarker_sq h,one_mul]

variable {G' : Type*} [Group G'] [Finite G'] {z' : G'}
variable (h' : IsTypeJ4 z')
variable (e' : CubicAutomorphismQuotient (centralizer z' ⧸ core z'))
variable (X' : Sylow 3 (CubicLift.subgroup e'))
variable [IsExtraspecial 2 (core z)] [IsExtraspecial 2 (core z')]

/-- The normalizer central quotients are compared by the same full H/Q map. -/
noncomputable def normalizerCentralComparison :
    (cubicNormalizerInH e X ⧸ (center (centralizer z)).subgroupOf (cubicNormalizerInH e X)) ≃*
      (cubicNormalizerInH e' X' ⧸ (center (centralizer z')).subgroupOf (cubicNormalizerInH e' X')) :=
  (cubicNormalizerCentralQuotientEquiv h e X).trans
    ((coreQuotientComparison h e X h' e' X').trans
      (cubicNormalizerCentralQuotientEquiv h' e' X').symm)

/-- Its equality criterion is the actual quotient marking, not a selected actor map. -/
theorem normalizerCentralComparison_mk_iff
    (n : cubicNormalizerInH e X) (n' : cubicNormalizerInH e' X') :
    normalizerCentralComparison h e X h' e' X'
        (QuotientGroup.mk' ((center (centralizer z)).subgroupOf (cubicNormalizerInH e X)) n) =
      QuotientGroup.mk' ((center (centralizer z')).subgroupOf (cubicNormalizerInH e' X')) n' ↔
    cubicNormalizerToCore e' X' n' =
      coreQuotientComparison h e X h' e' X' (cubicNormalizerToCore e X n) := by
  rw [←(cubicNormalizerCentralQuotientEquiv h' e' X').injective.eq_iff]
  change cubicNormalizerCentralQuotientEquiv h' e' X'
    ((cubicNormalizerCentralQuotientEquiv h' e' X').symm
      (coreQuotientComparison h e X h' e' X' (cubicNormalizerToCore e X n))) =
    cubicNormalizerToCore e' X' n' ↔ _
  rw [MulEquiv.apply_symm_apply,eq_comm]

/-- The only unresolved square of a lift of a source involution is the
original marked central involution. -/
theorem cubicNormalizer_matching_square
    (s : cubicNormalizerInH e X) (hs : s*s=1)
    (n' : cubicNormalizerInH e' X')
    (hn : cubicNormalizerToCore e' X' n' =
      coreQuotientComparison h e X h' e' X' (cubicNormalizerToCore e X s)) :
    n'.val*n'.val=1 ∨ n'.val*n'.val=planeMarker (z := z') := by
  have hk : n'*n' ∈ (cubicNormalizerToCore e' X').ker := by
    change cubicNormalizerToCore e' X' (n'*n')=1
    rw [map_mul,hn,←map_mul,←map_mul,hs,map_one,map_one]
  rw [cubicNormalizerToCore_ker h' e' X'] at hk
  exact planeCenter_cases h' _ hk

/-- The full conclusion of matching the original splitting actor, including
both actions and its central square. The construction is proved below. -/
def CubicSplittingActorComparison (s : cubicNormalizerInH e X) : Prop :=
    ∃ (φ : cubicCentralizerInH e X ≃* cubicCentralizerInH e' X')
      (ψ : core z ≃* core z') (n' : cubicNormalizerInH e' X'),
      (∀ c, cubicNativeProjection h' e' X' (φ c) = cubicNativeProjection h e X c) ∧
      φ (cubicMarker e X) = cubicMarker e' X' ∧
      ψ (coreMarker h) = coreMarker h' ∧
      cubicNormalizerToCore e' X' n' =
        coreQuotientComparison h e X h' e' X' (cubicNormalizerToCore e X s) ∧
      (n'.val*n'.val=1 ∨ n'.val*n'.val=planeMarker (z := z')) ∧
      (∀ c, φ (cubicNormalizerAction e X s c) = cubicNormalizerAction e' X' n' (φ c)) ∧
      (∀ q, ψ (MulAut.conjNormal s.val q) = MulAut.conjNormal n'.val (ψ q)) ∧
      ∀ m' : cubicNormalizerInH e' X',
        cubicNormalizerToCore e' X' m' = cubicNormalizerToCore e' X' n' →
        m'.val*m'.val=n'.val*n'.val

/-- Construct matching actors on both original groups, with their precise
central square and without treating elementwise selection as a homomorphism. -/
theorem exists_cubic_splitting_actor
    (hp : Group.IsPerfect (cubicCentralizerInH e X))
    (hp' : Group.IsPerfect (cubicCentralizerInH e' X'))
    (s : cubicNormalizerInH e X) (hs : s*s=1) :
    CubicSplittingActorComparison h e X h' e' X' s := by
  obtain ⟨φ,ψ,hφ,hφz,hψ,hψz,hψc,hnorm⟩ :=
    exists_cubic_coreGroup_equiv_normalizer h e X h' e' X' hp hp'
  obtain ⟨n',hn'⟩ := QuotientGroup.mk'_surjective
    ((center (centralizer z')).subgroupOf (cubicNormalizerInH e' X'))
    (normalizerCentralComparison h e X h' e' X'
      (QuotientGroup.mk' ((center (centralizer z)).subgroupOf (cubicNormalizerInH e X)) s))
  have hn := (normalizerCentralComparison_mk_iff h e X h' e' X' s n').mp hn'.symm
  exact ⟨φ,ψ,n',hφ,hφz,hψz,hn,cubicNormalizer_matching_square h e X h' e' X' s hs n' hn,
    (hnorm s n' hn).1,(hnorm s n' hn).2,
    fun m' hm' => cubicNormalizer_same_fiber_square h' e' X' m' n' hm'⟩

omit [IsExtraspecial 2 (core z)] [IsExtraspecial 2 (core z')] in
/-- The actual six-cover actor and its central square, without module instances
in the statement used by the original chapter application. -/
theorem exists_cubic_splitting_cover_actor
    (hp : Group.IsPerfect (cubicCentralizerInH e X))
    (hp' : Group.IsPerfect (cubicCentralizerInH e' X'))
    (s : cubicNormalizerInH e X) (hs : s*s=1) :
    ∃ (φ : cubicCentralizerInH e X ≃* cubicCentralizerInH e' X')
      (n' : cubicNormalizerInH e' X'),
      (∀ c, cubicNativeProjection h' e' X' (φ c) = cubicNativeProjection h e X c) ∧
      φ (cubicMarker e X) = cubicMarker e' X' ∧
      (n'.val*n'.val=1 ∨ n'.val*n'.val=planeMarker (z := z')) ∧
      (∀ c, φ (cubicNormalizerAction e X s c) = cubicNormalizerAction e' X' n' (φ c)) ∧
      ∀ m' : cubicNormalizerInH e' X',
        cubicNormalizerToCore e' X' m' = cubicNormalizerToCore e' X' n' →
        m'.val*m'.val=n'.val*n'.val := by
  let := h.extraspecial
  let := h'.extraspecial
  obtain ⟨φ,ψ,n',hφ,hφz,_,_,hsq,hc,_,hf⟩ :=
    exists_cubic_splitting_actor h e X h' e' X' hp hp' s hs
  exact ⟨φ,n',hφ,hφz,hsq,hc,hf⟩

end Theory.GroupTheory.Recognition.JankoFour.SourceComparison
