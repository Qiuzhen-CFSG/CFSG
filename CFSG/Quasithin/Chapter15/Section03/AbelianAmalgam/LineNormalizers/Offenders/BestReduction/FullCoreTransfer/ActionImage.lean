module
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.LineNormalizers.Offenders.BestReduction.FullCoreTransfer
public import Theory.GroupTheory.SylowKernelCoprime
public import Theory.Representation.BinaryOffender.ActionImage

/-!
# The compatible Sylow subgroup and the odd action kernel

Intersect the supplied Sylow of the centralizer factor with the normal
Thompson image. This is the compatible Sylow, unlike an arbitrary Sylow
containing J(S_E). Triviality of the actual action kernel on the supplied
Sylow then makes the restricted action kernel odd.

The local application uses the exact paired kernel and Q=C_T(U/E), preserving
the literal full core and Thompson image. Source: Aschbacher–Smith, proof of
15.3.67, printed pp.1153–1154 (combined 1 March 2004 manuscript).
-/

public section
open Subgroup Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.Offenders.BestReduction.FullCoreTransfer
variable {G D W : Type*} [Group G] [Group D] [Finite G] [Finite D]
  [AddCommGroup W] [Module (ZMod 2) W]

omit [Finite G] in
/-- Choose the intrinsic Sylow by intersection with the specified ambient
Sylow, retaining membership in that specified subgroup. -/
theorem compatible_sylow_and_odd_kernel
    (ρ : Representation (ZMod 2) D W) (C I : Subgroup D) [I.Normal]
    (hIC : I ≤ C) (S : Sylow 2 C)
    (hfaith : ∀ s ∈ (S : Subgroup C), (∀ w, ρ (s : D) w = w) → (s : D) = 1) :
    ∃ P : Sylow 2 I,
      (P : Subgroup I) = ((S : Subgroup C).map C.subtype).subgroupOf I ∧
      Odd (Nat.card (actionHom (ρ.comp I.subtype)).ker) := by
  let I' := I.subgroupOf C
  obtain ⟨P', hP'⟩ := S.exists_subgroupOf_eq_of_normal I'
  let e := subgroupOfEquivOfLe hIC
  let P := P'.mapSurjective (f := e.toMonoidHom) e.surjective
  have hP : (P : Subgroup I) = ((S : Subgroup C).map C.subtype).subgroupOf I := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      rw [hP'] at hy
      exact ⟨y.val, hy, rfl⟩
    · rintro ⟨s, hs, he⟩
      have he' : (s : D) = (x : D) := he
      let y : I' := ⟨s, show (s : D) ∈ I from he'.symm ▸ x.property⟩
      refine ⟨y, ?_, ?_⟩
      · rw [hP']
        exact hs
      · exact Subtype.ext he
  refine ⟨P, hP, ?_⟩
  apply Nat.coprime_two_left.mp
  apply MonoidHom.coprime_card_ker_of_sylow (actionHom (ρ.comp I.subtype)) P
  intro s hs hk
  rw [hP] at hs
  obtain ⟨t, ht, he⟩ := hs
  change (t : D) = (s : D) at he
  apply Subtype.ext
  change (s : D) = 1
  rw [← he]
  apply hfaith t ht
  intro w
  rw [he]
  exact (actionHom_eq_one_iff (ρ.comp I.subtype) s).mp hk w

/-- The exact paired kernel and actual core equality give faithfulness on
q(S_E). These are raw source equalities, not a faithfulness assumption on I. -/
theorem temporary_sylow_action_kernel_trivial
    (Y T V E : Subgroup G) [IsMulCommutative V]
    (d : Replacement.Transvections.TemporaryData Y T V E)
    (σ : Representation (ZMod 2)
      ((temporaryLineNormalizer T V E) ⧸ Replacement.Transvections.localCore T V E) W)
    (hker : (σ.comp ((QuotientGroup.mk' (Replacement.Transvections.localCore T V E)).comp
        (localCentralizer T V E).subtype)).ker =
      ((Descent.sectionKernel V E).subgroupOf (temporaryLineNormalizer T V E)).subgroupOf
        (localCentralizer T V E))
    (x : temporaryLineNormalizer T V E)
    (hxT : (x : G) ∈ lineT T E) (hxC : x ∈ localCentralizer T V E)
    (hfix : ∀ w, σ (QuotientGroup.mk' (Replacement.Transvections.localCore T V E) x) w = w) :
    QuotientGroup.mk' (Replacement.Transvections.localCore T V E) x = 1 := by
  have hxker : (⟨x, hxC⟩ : localCentralizer T V E) ∈
      (σ.comp ((QuotientGroup.mk' (Replacement.Transvections.localCore T V E)).comp
        (localCentralizer T V E).subtype)).ker := by
    apply LinearMap.ext
    exact hfix
  rw [hker] at hxker
  apply (QuotientGroup.eq_one_iff _).mpr
  change (x : G) ∈ temporaryCore T V E
  rw [d.core_eq Y T V E]
  apply (mem_lineQuotientCentralizer_iff T V E
    (lineV_le_lineNormalizer V E d.line_le) x).mpr
  refine ⟨hxT, ?_⟩
  exact (Descent.mem_sectionKernel_iff V E
    (lineV_le_lineNormalizer V E d.line_le) x).mp hxker |>.2

/-- The actual normal Thompson image meets the supplied centralizer Sylow in
its compatible Sylow, and its first-summand action kernel has odd order. -/
theorem temporary_compatible_sylow_and_odd_kernel
    (Y T V E : Subgroup G) [IsMulCommutative V]
    (d : Replacement.Transvections.TemporaryData Y T V E)
    (σ : Representation (ZMod 2)
      ((temporaryLineNormalizer T V E) ⧸ Replacement.Transvections.localCore T V E) W)
    (hker : (σ.comp ((QuotientGroup.mk' (Replacement.Transvections.localCore T V E)).comp
        (localCentralizer T V E).subtype)).ker =
      ((Descent.sectionKernel V E).subgroupOf (temporaryLineNormalizer T V E)).subgroupOf
        (localCentralizer T V E))
    (S : Sylow 2 ((localCentralizer T V E).map
      (QuotientGroup.mk' (Replacement.Transvections.localCore T V E))))
    (hST : (S : Subgroup _).map ((localCentralizer T V E).map
      (QuotientGroup.mk' (Replacement.Transvections.localCore T V E))).subtype ≤
        ((lineT T E).subgroupOf (temporaryLineNormalizer T V E)).map
          (QuotientGroup.mk' (Replacement.Transvections.localCore T V E))) :
    ∃ P : Sylow 2 (thompsonImage T V E),
      (P : Subgroup _) = ((S : Subgroup _).map ((localCentralizer T V E).map
        (QuotientGroup.mk' (Replacement.Transvections.localCore T V E))).subtype).subgroupOf
          (thompsonImage T V E) ∧
      Odd (Nat.card (actionHom (σ.comp (thompsonImage T V E).subtype)).ker) := by
  let q := QuotientGroup.mk' (Replacement.Transvections.localCore T V E)
  let C := localCentralizer T V E
  let I := thompsonImage T V E
  let : I.Normal := thompsonImage_normal T V E
    (line_le_temporary T V E d.line_le d.span_le_sylow)
  have hIC : I ≤ C.map q := map_mono (sSup_le (fun A hA => hA.1))
  apply compatible_sylow_and_odd_kernel σ (C.map q) I hIC S
  intro s hs hfix
  obtain ⟨x, hxT, he⟩ := hST (mem_map_of_mem (C.map q).subtype hs)
  change q x = (s : _) at he
  have hQC : q.ker ≤ C := by
    rw [QuotientGroup.ker_mk']
    intro x hx
    exact ⟨x.property, d.core_centralizes_line Y T V E hx⟩
  have hxC : x ∈ C := by
    have hm : x ∈ (C.map q).comap q := by
      change q x ∈ C.map q
      rw [he]
      exact s.property
    rwa [comap_map_eq_self hQC] at hm
  rw [← he]
  exact temporary_sylow_action_kernel_trivial Y T V E d σ hker x hxT hxC
    (fun w => he.symm ▸ hfix w)

end CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.Offenders.BestReduction.FullCoreTransfer
