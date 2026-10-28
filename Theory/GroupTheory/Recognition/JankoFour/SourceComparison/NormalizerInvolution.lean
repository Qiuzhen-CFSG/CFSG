module
public import Theory.GroupTheory.Recognition.JankoFour.SourceComparison.NormalizerLift
public import Theory.GroupTheory.Recognition.JankoFour.SourceComparison.OuterSquare

/-!
# Involutory lifts in the original cubic normalizer

Quotient the original normalizer by its scalar cubic only. The residual
kernel is the actual central involution. The two outer M22 involution
classes have equal lift squares, so the supplied section 4 splitting
involution forces every outer fiber to have square one. The inner fibers
use the genuine M22 double-cover involution theorem. Lift back through
the cubic using its coprimality with the original central involution.

Source: Aschbacher–Segev (1991), (4.9) and the normalizer step of (8.3), p.606.
-/

@[expose] public section
namespace Theory.GroupTheory.Recognition.JankoFour.SourceComparison
open Subgroup SourceRecognition LocalGeometry Sporadic.Mathieu

variable {G : Type*} [Group G] [Finite G] {z : G}
variable (h : IsTypeJ4 z)
variable (e : CubicAutomorphismQuotient (centralizer z ⧸ core z))
variable (X : Sylow 3 (CubicLift.subgroup e))

noncomputable abbrev normalizerScalars :=
  (cubicSylowImage e X).subgroupOf (cubicNormalizerInH e X)

instance normalizerScalars_normal : (normalizerScalars e X).Normal :=
  (cubicSylowImage e X).normal_in_normalizer

include h in
theorem normalizerScalars_le_ker :
    normalizerScalars e X ≤ (cubicNormalizerProjection e X).ker := by
  rw [cubicNormalizerProjection_ker h e X]
  exact fun n hn => (le_sup_left : cubicSylowImage e X ≤ cubicCenterInH e X) hn

include h in
/-- The original full normalizer map after removing precisely its scalar cubic. -/
noncomputable def normalizerDoubleProjection :
    (cubicNormalizerInH e X ⧸ normalizerScalars e X) →* MulAut M22 :=
  QuotientGroup.lift _ (cubicNormalizerProjection e X) (normalizerScalars_le_ker h e X)

@[simp] theorem normalizerDoubleProjection_mk (n : cubicNormalizerInH e X) :
    normalizerDoubleProjection h e X (QuotientGroup.mk' (normalizerScalars e X) n) =
      cubicNormalizerProjection e X n := rfl

/-- Removing the scalar cubic leaves a surjection onto the full original Aut(M22). -/
theorem normalizerDoubleProjection_surjective :
    Function.Surjective (normalizerDoubleProjection h e X) := by
  intro y
  obtain ⟨n,hn⟩ := cubicNormalizerProjection_surjective h e X y
  exact ⟨QuotientGroup.mk' (normalizerScalars e X) n,hn⟩

/-- Its remaining kernel is of order two, not a discarded central attachment. -/
theorem normalizerDoubleProjection_kernel_card :
    Nat.card (normalizerDoubleProjection h e X).ker = 2 := by
  have hc : Nat.card (cubicNormalizerProjection e X).ker = 6 := by
    rw [cubicNormalizerProjection_ker h e X,
      Nat.card_congr (subgroupOfEquivOfLe
        ((cubicCenterInH_le h e X).trans (centralizer_le_normalizer _))).toEquiv,
      cubicCenterInH_card h e X]
  have ha : Nat.card (normalizerScalars e X) = 3 := by
    rw [Nat.card_congr (subgroupOfEquivOfLe (cubicSylowImage e X).le_normalizer).toEquiv,
      cubicSylowImage_card h e X]
  have hcard := kernel_card_eq_mul_of_surjective_factor (cubicNormalizerProjection e X)
    (normalizerDoubleProjection h e X) (QuotientGroup.mk' (normalizerScalars e X))
    (normalizerDoubleProjection_surjective h e X) (QuotientGroup.mk'_surjective _) rfl
  rw [hc,QuotientGroup.ker_mk',ha] at hcard
  omega

/-- A normal two-element kernel is central. -/
theorem normalizerDoubleProjection_kernel_central :
    (normalizerDoubleProjection h e X).ker ≤
      center (cubicNormalizerInH e X ⧸ normalizerScalars e X) := by
  let K := (normalizerDoubleProjection h e X).ker
  have hc : Nat.card K = 2 := normalizerDoubleProjection_kernel_card h e X
  intro k hk
  apply mem_center_iff.mpr
  intro y
  have hconj : y*k*y⁻¹=k := by
    by_cases hk1 : k=1
    · simp [hk1]
    obtain ⟨a,_,ha⟩ := (Nat.card_eq_two_iff' (1 : K)).mp hc
    have hmem : y*k*y⁻¹ ∈ K := Subgroup.Normal.conj_mem inferInstance k hk y
    have hneq : (⟨y*k*y⁻¹,hmem⟩ : K) ≠ 1 := by
      intro he
      have he' : y*k*y⁻¹=1 := congrArg Subtype.val he
      have hk' : k = 1 := by
        calc
          k = y⁻¹ * (y*k*y⁻¹) * y := by group
          _ = 1 := by rw [he']; group
      exact hk1 hk'
    have hkneq : (⟨k,hk⟩ : K) ≠ 1 := by
      intro he
      exact hk1 (congrArg Subtype.val he)
    have heq : (⟨y*k*y⁻¹,hmem⟩ : K) = ⟨k,hk⟩ :=
      (ha _ hneq).trans (ha _ hkneq).symm
    exact congrArg Subtype.val heq
  exact (mul_inv_eq_iff_eq_mul.mp hconj)

include h in
/-- The inner automorphism preimage in N is exactly the original cubic centralizer. -/
theorem cubicNormalizer_inner_iff (n : cubicNormalizerInH e X) :
    cubicNormalizerProjection e X n ∈ MulAut.innerSubgroup M22 ↔
      n.val ∈ cubicCentralizerInH e X := by
  constructor
  · intro hn
    have hi : QuotientGroup.mk' (core z) n.val ∈ innerPreimage e := hn
    obtain ⟨c,hc,he⟩ := (cubicCentralizer_map_coreQuotient h e X).ge hi
    have hk : n.val*c⁻¹ ∈ core z := (QuotientGroup.eq_one_iff _).mp (by
      change QuotientGroup.mk' (core z) (n.val*c⁻¹)=1
      rw [map_mul,map_inv,he,mul_inv_cancel])
    have hN : n.val*c⁻¹ ∈ cubicNormalizerInH e X :=
      mul_mem n.property (inv_mem (centralizer_le_normalizer _ hc))
    have hz := (core_inf_cubicNormalizer h e X).le ⟨hk,hN⟩
    simpa only [inv_mul_cancel_right] using
      (cubicCentralizerInH e X).mul_mem (center_le_centralizer _ hz) hc
  · intro hn
    change CubicLift.projection e n.val ∈ MulAut.innerSubgroup M22
    exact (show MulAut.conj (cubicCentralizerProjection h e X ⟨n.val,hn⟩) =
        CubicLift.projection e n.val from cubicCentralizerProjection_conj h e X ⟨n.val,hn⟩) ▸
      ⟨cubicCentralizerProjection h e X ⟨n.val,hn⟩, rfl⟩

end Theory.GroupTheory.Recognition.JankoFour.SourceComparison

namespace Theory.GroupTheory.Recognition.JankoFour.SourceComparison
open Subgroup SourceRecognition LocalGeometry Sporadic.Mathieu
variable {G : Type*} [Group G] [Finite G] {z : G}
variable (h : IsTypeJ4 z)
variable (e : CubicAutomorphismQuotient (centralizer z ⧸ core z))
variable (X : Sylow 3 (CubicLift.subgroup e))

include h in
/-- The original split normalizer has involutory lifts of every square-one
H/Q actor. The central square ambiguity is discharged, with no change of marking. -/
theorem cubicNormalizer_square_one
    (s : cubicNormalizerInH e X) (hs : s*s=1)
    (hso : s.val ∉ cubicCentralizerInH e X)
    (n : cubicNormalizerInH e X) (hn : (cubicNormalizerToCore e X n)^2=1) :
    n*n=1 := by
  let q := QuotientGroup.mk' (normalizerScalars e X)
  let f := normalizerDoubleProjection h e X
  have hs' : (q s)^2=1 := by rw [←map_pow,pow_two,hs,map_one]
  have hso' : f (q s) ∉ MulAut.innerSubgroup M22 := by
    intro he
    exact hso ((cubicNormalizer_inner_iff h e X s).mp he)
  have hn' : (f (q n))^2=1 := by
    change (e.projection (cubicNormalizerToCore e X n))^2=1
    rw [←map_pow,hn,map_one]
  have hq := OuterSquare.aut_square_one f (normalizerDoubleProjection_surjective h e X)
    (normalizerDoubleProjection_kernel_central h e X)
    (normalizerDoubleProjection_kernel_card h e X) (q s) hs' hso' (q n) hn'
  have hA : (n*n).val ∈ cubicSylowImage e X := by
    have hq' : q (n*n)=1 := by
      rw [map_mul]
      simpa [pow_two] using hq
    change (n*n : cubicNormalizerInH e X) ∈ normalizerScalars e X
    exact (QuotientGroup.eq_one_iff _).mp hq'
  have hZ : (n*n).val ∈ center (centralizer z) := by
    have he : n*n ∈ (cubicNormalizerToCore e X).ker := by
      change cubicNormalizerToCore e X (n*n)=1
      rw [map_mul]
      simpa [pow_two] using hn
    rw [cubicNormalizerToCore_ker h e X] at he
    exact he
  have hd : Disjoint (cubicSylowImage e X) (center (centralizer z)) := by
    apply disjoint_of_coprime_natCard
    rw [cubicSylowImage_card h e X,centralizer_center_card h]
    decide
  exact Subtype.ext (mem_bot.mp ((disjoint_iff_inf_le.mp hd) ⟨hA,hZ⟩))

variable {G' : Type*} [Group G'] [Finite G'] {z' : G'}
variable (h' : IsTypeJ4 z')
variable (e' : CubicAutomorphismQuotient (centralizer z' ⧸ core z'))
variable (X' : Sylow 3 (CubicLift.subgroup e'))
variable [IsExtraspecial 2 (core z)] [IsExtraspecial 2 (core z')]

/-- Matching the original source splitting actor now gives an actual involution
on the target side, equivariant on both the core and the full six-cover. -/
theorem exists_cubic_involutory_actor
    (hp : Group.IsPerfect (cubicCentralizerInH e X))
    (hp' : Group.IsPerfect (cubicCentralizerInH e' X'))
    (s : cubicNormalizerInH e X) (hs : s*s=1)
    (s' : cubicNormalizerInH e' X') (hs' : s'*s'=1)
    (hs'C : s'.val ∉ cubicCentralizerInH e' X') :
    ∃ (φ : cubicCentralizerInH e X ≃* cubicCentralizerInH e' X')
      (ψ : core z ≃* core z') (n' : cubicNormalizerInH e' X'),
      (∀ c, cubicNativeProjection h' e' X' (φ c)=cubicNativeProjection h e X c) ∧
      φ (cubicMarker e X)=cubicMarker e' X' ∧
      ψ (coreMarker h)=coreMarker h' ∧
      cubicNormalizerToCore e' X' n' =
        coreQuotientComparison h e X h' e' X' (cubicNormalizerToCore e X s) ∧
      n'*n'=1 ∧
      (∀ c, φ (cubicNormalizerAction e X s c)=cubicNormalizerAction e' X' n' (φ c)) ∧
      ∀ q, ψ (MulAut.conjNormal s.val q)=MulAut.conjNormal n'.val (ψ q) := by
  obtain ⟨φ,ψ,n',hφ,hφz,hψz,hn,_,hc,hq,_⟩ :=
    exists_cubic_splitting_actor h e X h' e' X' hp hp' s hs
  have hn2 : (cubicNormalizerToCore e' X' n')^2=1 := by
    rw [hn,←map_pow,←map_pow,pow_two,hs,map_one,map_one]
  exact ⟨φ,ψ,n',hφ,hφz,hψz,hn,cubicNormalizer_square_one h' e' X' s' hs' hs'C n' hn2,hc,hq⟩

end Theory.GroupTheory.Recognition.JankoFour.SourceComparison

namespace Theory.GroupTheory.Recognition.JankoFour.SourceComparison
open Subgroup SourceRecognition LocalGeometry Sporadic.Mathieu
variable {G : Type*} [Group G] [Finite G] {z : G}
variable (h : IsTypeJ4 z)
variable (e : CubicAutomorphismQuotient (centralizer z ⧸ core z))
variable (X : Sylow 3 (CubicLift.subgroup e))
variable {G' : Type*} [Group G'] [Finite G'] {z' : G'}
variable (h' : IsTypeJ4 z')
variable (e' : CubicAutomorphismQuotient (centralizer z' ⧸ core z'))
variable (X' : Sylow 3 (CubicLift.subgroup e'))

/-- The involutory cover-actor comparison without quadratic-module instances
in the public type, for the original chapter application. -/
theorem exists_cubic_involutory_cover_actor
    (hp : Group.IsPerfect (cubicCentralizerInH e X))
    (hp' : Group.IsPerfect (cubicCentralizerInH e' X'))
    (s : cubicNormalizerInH e X) (hs : s*s=1)
    (s' : cubicNormalizerInH e' X') (hs' : s'*s'=1)
    (hs'C : s'.val ∉ cubicCentralizerInH e' X') :
    ∃ (φ : cubicCentralizerInH e X ≃* cubicCentralizerInH e' X')
      (n' : cubicNormalizerInH e' X'),
      (∀ c, cubicNativeProjection h' e' X' (φ c)=cubicNativeProjection h e X c) ∧
      φ (cubicMarker e X)=cubicMarker e' X' ∧ n'*n'=1 ∧
      ∀ c, φ (cubicNormalizerAction e X s c)=cubicNormalizerAction e' X' n' (φ c) := by
  let := h.extraspecial
  let := h'.extraspecial
  obtain ⟨φ,ψ,n',hφ,hφz,_,_,hn,hc,_⟩ :=
    exists_cubic_involutory_actor h e X h' e' X' hp hp' s hs s' hs' hs'C
  exact ⟨φ,n',hφ,hφz,hn,hc⟩

end Theory.GroupTheory.Recognition.JankoFour.SourceComparison
