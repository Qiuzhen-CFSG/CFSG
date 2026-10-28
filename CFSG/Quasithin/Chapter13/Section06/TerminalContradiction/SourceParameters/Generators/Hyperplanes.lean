module
public import CFSG.Quasithin.Chapter13.Section06.TerminalContradiction.SourceParameters.WeakClosure
public import CFSG.Quasithin.ChapterE.Section03.Offenders.Basic
/-!
# The hyperplane argument in source 13.6.25

Lift every subgroup of the induced automizer to its full preimage in A.
Binary coranks add, so a lifted hyperplane has corank at most two in Vᵍ.
Since r=3 its centralizer normalizes Vᵍ. The commutator with A then lies
in V ∩ Vᵍ; the commuting-conjugate conclusion of 13.6.24 makes it trivial.
Thus a noncentral A would have its actual automizer image in A₂, contrary
to a=1. The source application in Generators discharges r=3 and 13.6.24
using the earlier marked A₅ coordinates.

Source: Aschbacher–Smith, combined manuscript (1 March 2004),
13.6.25, printed p.934. The private corank/image transport arguments are
adapted from ChapterE/Section03/Parameters.lean in this repository.
-/

@[expose] public section
namespace CFSG.Quasithin.Chapter13.Section06.TerminalContradiction.SourceParameters.Generators
open Subgroup Representation.BinaryOffender
open _root_.CFSG.Quasithin.ChapterE
open scoped IsMulCommutative
variable {G : Type*} [Group G] [Finite G]
private theorem corank_add {W A B : Subgroup G} [IsElementaryAbelian 2 W]
    (hBA : B ≤ A) (hAW : A ≤ W) :
    subgroupCorank W B = subgroupCorank A B + subgroupCorank W A := by
  let _ : IsElementaryAbelian 2 A := {
    toIsMulCommutative := isMulCommutative_iff.mpr (fun a b =>
      (Subgroup.inclusion_injective hAW) (by
        simpa only [map_mul] using mul_comm (Subgroup.inclusion hAW a) (Subgroup.inclusion hAW b)))
    exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr (fun a =>
      Subtype.ext (elemPow_eq_one_of_isElementaryAbelian (a : G) (hAW a.property))) }
  have h := Subgroup.relIndex_mul_relIndex B A W hBA hAW
  have hp (T U : Subgroup G) [IsElementaryAbelian 2 T] :
      U.relIndex T = 2 ^ subgroupCorank T U := by
    rw [subgroupCorank_eq_quotient_finrank]
    exact Subgroup.relIndex_eq_two_pow_quotient_finrank T U
  rw [hp A B, hp W A, hp W B, ← pow_add] at h
  exact ((Nat.pow_right_injective (by decide : 2 ≤ 2)) h).symm

omit [Finite G] in
private theorem lift_image_subgroup {V A : Subgroup G}
    (hA : A ≤ normalizer (V : Set G))
    (D : Subgroup (Automizer V)) (hD : D ≤ inducedAutomizer V A) :
    ∃ B ≤ A, inducedAutomizer V B = D ∧
      subgroupCorank A B = Nat.log 2 (D.relIndex (inducedAutomizer V A)) := by
  let N := normalizer (V : Set G)
  let f := V.normalizerMonoidHom.rangeRestrict
  let C := A.subgroupOf N
  let L := C ⊓ D.comap f
  let B := L.map N.subtype
  have hBA : B ≤ A := by
    rintro _ ⟨x, hx, rfl⟩
    exact hx.1
  have hBN : B.subgroupOf N = L := by
    exact Subgroup.comap_map_eq_self_of_injective N.subtype_injective L
  have hmap : L.map f = D := by
    apply le_antisymm
    · rintro _ ⟨x, hx, rfl⟩
      exact hx.2
    · intro d hd
      obtain ⟨x, hx, he⟩ := hD hd
      exact ⟨x, ⟨hx, (show f x ∈ D from he.symm ▸ hd)⟩, he⟩
  refine ⟨B, hBA, ?_, ?_⟩
  · change (B.subgroupOf N).map f = D
    rw [hBN, hmap]
  · unfold subgroupCorank
    congr 1
    rw [← Subgroup.relIndex_subgroupOf (H := B) hA, hBN]
    exact (Subgroup.inf_relIndex_left C (D.comap f)).trans
      (Subgroup.relIndex_comap D f C)

omit [Finite G] in
private theorem fixedSpace_eq_of_centralizer_eq {V A B : Subgroup G}
    [IsElementaryAbelian 2 V]
    (hA : A ≤ normalizer (V : Set G)) (hB : B ≤ normalizer (V : Set G))
    (h : V ⊓ centralizer (A : Set G) = V ⊓ centralizer (B : Set G)) :
    fixedSpace (automizerRepresentation V) (inducedAutomizer V A) =
      fixedSpace (automizerRepresentation V) (inducedAutomizer V B) := by
  ext v
  rw [mem_fixedSpace_inducedAutomizer V A hA, mem_fixedSpace_inducedAutomizer V B hB]
  have hv := congrArg (fun S : Subgroup G => (v.toMul : G) ∈ S) h
  simpa only [Subgroup.mem_inf, v.toMul.property, true_and] using (iff_of_eq hv)


omit [Finite G] in
private theorem hyperplane_centralizer {V A B : Subgroup G}
    [IsElementaryAbelian 2 V] (g : G)
    (hAV : A ≤ V.map (MulAut.conj g).toMonoidHom)
    (hAN : A ≤ normalizer (V : Set G)) (hBA : B ≤ A)
    (hr : globalR V = 3)
    (hcorank : subgroupCorank (V.map (MulAut.conj g).toMonoidHom) B ≤ 2)
    (hinter : ∀ g : G, g ∉ normalizer (V : Set G) →
      V ⊓ V.map (MulAut.conj g).toMonoidHom ≠ ⊥ →
      ⁅V, V.map (MulAut.conj g).toMonoidHom⁆ = ⊥) :
    V ⊓ centralizer (B : Set G) ≤ centralizer (A : Set G) := by
  let W := V.map (MulAut.conj g).toMonoidHom
  by_cases hg : g ∈ normalizer (V : Set G)
  · have hW : W = V := mem_normalizer_iff_map_conj_eq.mp hg
    have hVV : V ≤ centralizer (V : Set G) :=
      commutator_eq_bot_iff_le_centralizer.mp (commutator_self_eq_bot_iff.mpr inferInstance)
    exact inf_le_left.trans (hVV.trans (centralizer_le (hAV.trans hW.le)))
  by_cases hi : V ⊓ W = ⊥
  · have hN : centralizer (B : Set G) ≤ normalizer (W : Set G) := by
      apply centralizer_le_normalizer_of_corank_lt_globalR (hBA.trans hAV)
      rw [globalR_map_equiv, hr]
      exact lt_of_le_of_lt (show (subgroupCorank W B : ℕ∞) ≤ 2 by exact_mod_cast hcorank) (by norm_num)
    apply commutator_eq_bot_iff_le_centralizer.mp
    apply le_bot_iff.mp
    rw [← hi]
    apply le_inf
    · exact (commutator_mono inf_le_left le_rfl).trans
        (le_normalizer_iff_commutator_le_left.mp hAN)
    · exact (commutator_mono le_rfl hAV).trans
        (le_normalizer_iff_commutator_le_right.mp (inf_le_right.trans hN))
  · exact inf_le_left.trans
      ((commutator_eq_bot_iff_le_centralizer.mp (hinter g hg hi)).trans
        (centralizer_le hAV))

/-- The source hyperplane argument on the literal induced automizer. -/
theorem induced_mem_A2 {V A : Subgroup G} [IsElementaryAbelian 2 V] (g : G)
    (hAV : A ≤ V.map (MulAut.conj g).toMonoidHom)
    (hAN : A ≤ normalizer (V : Set G))
    (hr : globalR V = 3)
    (hc : subgroupCorank (V.map (MulAut.conj g).toMonoidHom) A ≤ 1)
    (hinter : ∀ g : G, g ∉ normalizer (V : Set G) →
      V ⊓ V.map (MulAut.conj g).toMonoidHom ≠ ⊥ →
      ⁅V, V.map (MulAut.conj g).toMonoidHom⁆ = ⊥)
    (hnot : ¬ A ≤ centralizer (V : Set G)) :
    inducedAutomizer V A ∈ fixedSpaceFamily (automizerRepresentation V) 2 := by
  let W := V.map (MulAut.conj g).toMonoidHom
  let _ : IsElementaryAbelian 2 W := IsElementaryAbelian.map _
  let _ : IsElementaryAbelian 2 A := {
    toIsMulCommutative := isMulCommutative_iff.mpr (fun a b =>
      (Subgroup.inclusion_injective hAV) (by
        simpa only [map_mul] using mul_comm (Subgroup.inclusion hAV a) (Subgroup.inclusion hAV b)))
    exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr (fun a =>
      Subtype.ext (elemPow_eq_one_of_isElementaryAbelian (a : G) (hAV a.property))) }
  refine ⟨by decide, ⟨fun h => hnot ((inducedAutomizer_eq_bot_iff hAN).mp h),
    inducedAutomizer_elementary V A hAN⟩, ?_⟩
  intro D hD hcD
  obtain ⟨B, hBA, hBD, hcB⟩ := lift_image_subgroup hAN D hD
  have hb : subgroupCorank W B ≤ 2 := by
    rw [corank_add hBA hAV, hcB]
    omega
  have hcent : V ⊓ centralizer (A : Set G) = V ⊓ centralizer (B : Set G) := by
    apply le_antisymm (inf_le_inf_left _ (centralizer_le hBA))
    exact le_inf inf_le_left (hyperplane_centralizer g hAV hAN hBA hr hb hinter)
  rw [← hBD]
  exact fixedSpace_eq_of_centralizer_eq hAN (hBA.trans hAN) hcent

/-- Every generator at corank zero or one centralizes V. The normalizer
hypothesis is on T; no overgroup of T is assumed to normalize T. -/
theorem generator_central {V T A : Subgroup G} [IsElementaryAbelian 2 V]
    (hT : T ≤ normalizer (V : Set G))
    (hr : globalR V = 3) (ha : localA V = 1)
    (hinter : ∀ g : G, g ∉ normalizer (V : Set G) →
      V ⊓ V.map (MulAut.conj g).toMonoidHom ≠ ⊥ →
      ⁅V, V.map (MulAut.conj g).toMonoidHom⁆ = ⊥)
    {i : ℕ} (hi : i ≤ 1) (hA : A ∈ conjugateCorankFamily V i) (hAT : A ≤ T) :
    A ≤ centralizer (V : Set G) := by
  obtain ⟨g, hAV, hindex⟩ := hA
  by_contra hn
  have hc : subgroupCorank (V.map (MulAut.conj g).toMonoidHom) A ≤ 1 := by
    simpa only [subgroupCorank, hindex, Nat.log_pow (by decide : 1 < 2)] using hi
  have hf := induced_mem_A2 g hAV (hAT.trans hT) hr hc hinter hn
  have hle : (2 : ℕ∞) ≤ localA V := le_moduleA_of_mem _ hf
  rw [ha] at hle
  norm_num at hle

/-- The actual weak closure is contained in C_T(V). -/
theorem weakClosure_le_centralizer {V T : Subgroup G} [IsElementaryAbelian 2 V]
    (hT : T ≤ normalizer (V : Set G))
    (hr : globalR V = 3) (ha : localA V = 1)
    (hinter : ∀ g : G, g ∉ normalizer (V : Set G) →
      V ⊓ V.map (MulAut.conj g).toMonoidHom ≠ ⊥ →
      ⁅V, V.map (MulAut.conj g).toMonoidHom⁆ = ⊥)
    {i : ℕ} (hi : i ≤ 1) :
    indexedWeakClosure V T i ≤ T ⊓ centralizer (V : Set G) := by
  refine le_inf (indexedWeakClosure_le V T i) ?_
  rw [weakClosure_eq_sSup_gamma]
  exact sSup_le fun A hA => generator_central hT hr ha hinter hi hA.1 hA.2

/-- Both small weak closures centralize V, hence the minimum escape index
is greater than one, including when the minimizing family is empty. -/
theorem globalW_gt_one {V T : Subgroup G} [IsElementaryAbelian 2 V]
    (hT : T ≤ normalizer (V : Set G))
    (hr : globalR V = 3) (ha : localA V = 1)
    (hinter : ∀ g : G, g ∉ normalizer (V : Set G) →
      V ⊓ V.map (MulAut.conj g).toMonoidHom ≠ ⊥ →
      ⁅V, V.map (MulAut.conj g).toMonoidHom⁆ = ⊥) :
    1 < globalW V T := by
  have htwo : (2 : ℕ∞) ≤ globalW V T := by
    apply le_iInf
    intro i
    apply le_iInf
    intro hnot
    have hi : 2 ≤ i := by
      by_contra hn
      exact hnot (weakClosure_le_centralizer hT hr ha hinter (by omega))
    exact_mod_cast hi
  exact lt_of_lt_of_le (by norm_num) htwo

end CFSG.Quasithin.Chapter13.Section06.TerminalContradiction.SourceParameters.Generators
