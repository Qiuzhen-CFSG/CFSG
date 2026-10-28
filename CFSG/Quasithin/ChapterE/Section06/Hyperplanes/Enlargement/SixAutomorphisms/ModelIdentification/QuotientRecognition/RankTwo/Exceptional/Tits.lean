module

public import CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.SixAutomorphisms.ModelIdentification.QuotientRecognition.RankTwo.Exceptional.Transport
public import Theory.SpecificGroups.Tits.InvolutionRootGeometry.Reduction
public import Theory.SpecificGroups.ReeF4.ParabolicAmalgam.BinaryLocals
public import Theory.AtlasPort.ExceptionalIsomorphisms.Support
public import Theory.GroupTheory.Simple

/-!
# The Tits root-parabolic obstruction to A₆

The two full binary Ree seeds have two-group kernels and quotient orders
20 and 6. A homomorphism from simple A₆ to either quotient is trivial;
an embedding into the kernel would force 3 to divide a power of 2.
The actual marked Tits embedding therefore excludes A₆ from each Tits
root parabolic and every conjugate of it.

Only the automorphism fixed-group containment remains an input. Its existing
owner must discharge full binary automorphism coverage, involution coverage,
and the representative centralizer containments. No assertion about odd
outer order is made for the Tits group.

Source: Aschbacher–Smith E.6.23, printed p.254, and 16.1.4(1), p.1171,
`refs/quasithin.pdf`; the concrete root embedding retains the Parrott/GLS
references of `Tits.InvolutionRootGeometry.MarkedModel`.
-/

public section
open Subgroup Theory.GroupTheory
open alternatingGroup.SixSubgroupObstructions
open Tits.InvolutionRootGeometry ReeF4 ReeF4.Parabolics
namespace CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.SixAutomorphisms.ModelIdentification.QuotientScreen.RankTwo.Exceptional.Tits

private theorem not_injective_of_small_two_kernel {G H : Type*}
    [Group G] [Group H] [Finite H] (π : G →* H) (hk : IsPGroup 2 π.ker)
    (hc : Nat.card H < 360) (f : alternatingGroup (Fin 6) →* G)
    (hf : Function.Injective f) : False := by
  let : IsSimpleGroup (alternatingGroup (Fin 6)) := alternatingGroup.isSimpleGroup (by simp)
  have hz : π.comp f = 1 := (π.comp f).eq_one_of_isSimpleGroup_of_card_lt
    (by rwa [card_six])
  let j : alternatingGroup (Fin 6) →* π.ker :=
    f.codRestrict π.ker (fun x => DFunLike.congr_fun hz x)
  have hj : Function.Injective j := fun x y h => hf (congrArg Subtype.val h)
  have hp := hk.of_injective j hj
  obtain ⟨n, hn⟩ := hp.exists_card_eq
  rw [card_six] at hn
  have hd : 3 ∣ 2 ^ n := hn ▸ (by decide : 3 ∣ 360)
  exact (by decide : ¬ 3 ∣ 2) (Nat.prime_three.dvd_of_dvd_pow hd)

/-- Neither full binary Ree parabolic admits an A₆ embedding. -/
theorem not_injective_binary_parabolic (s : LargeLocalSeeds.Side)
    (f : alternatingGroup (Fin 6) →* Parabolics.parabolic 0 s) :
    ¬ Function.Injective f := by
  revert f
  rw [Parabolics.parabolic_zero]
  intro f hf
  cases s with
  | suzuki =>
    apply not_injective_of_small_two_kernel BinarySuzuki.projection
      (by rw [BinarySuzuki.projection_ker]; exact radicalInSeed_isPGroup 0 .suzuki) ?_ f hf
    rw [BenderSuzuki.MatrixGroups.suzukiZero_card]
    decide
  | linear =>
    apply not_injective_of_small_two_kernel BinaryLinear.projection
      (by rw [BinaryLinear.projection_ker]; exact radicalInSeed_isPGroup 0 .linear) ?_ f hf
    have h := Atlas.ExceptionalSupport.card_psl_mul (F := CoefficientField 0) 2
    have hc : Nat.card (LargeLocalSeeds.LinearQuotient 0) = 6 := by
      simpa [← Nat.card_eq_fintype_card, field_card, Fin.prod_univ_succ] using h
    rw [hc]
    decide

/-- This applies to the actual inverse-image parabolics in the Tits carrier,
not to a family label or an assumed parabolic isomorphism. -/
theorem not_injective_root_parabolic (P : Subgroup _root_.Tits.ParrottGroup)
    (hP : IsRootParabolic P) (f : alternatingGroup (Fin 6) →* P) :
    ¬ Function.Injective f := by
  obtain ⟨s, g, rfl⟩ := hP
  let e := (MulAut.conj g).subgroupMap (rootParabolic s)
  let j : rootParabolic s →* Parabolics.parabolic 0 s :=
    (embedding.comp (rootParabolic s).subtype).codRestrict _ (fun x => x.property)
  have hj : Function.Injective j := by
    intro x y h
    exact Subtype.ext (embedding_injective (congrArg Subtype.val h))
  intro hf
  exact not_injective_binary_parabolic s (j.comp (e.symm.toMonoidHom.comp f))
    (hj.comp (e.symm.injective.comp hf))

/-- The precise remaining table input, supplied by the existing Tits owner. -/
@[expose] def FixedParabolics : Prop :=
  ∀ a : MulAut _root_.Tits.ParrottGroup, orderOf a = 2 →
    ∃ P : Subgroup _root_.Tits.ParrottGroup, IsRootParabolic P ∧ a.fixedSubgroup ≤ P

/-- Root-parabolic containment alone now finishes the fixed-component exclusion. -/
theorem excludesFixedSix_of_fixedParabolics (h : FixedParabolics) :
    ExcludesFixedSix _root_.Tits.ParrottGroup := by
  intro a ha S hS hs
  obtain ⟨P, hP, hC⟩ := h a ha
  obtain ⟨e⟩ := hs
  let f : alternatingGroup (Fin 6) →* P :=
    (inclusion (hS.1.trans hC)).comp e.symm.toMonoidHom
  exact not_injective_root_parabolic P hP f
    ((inclusion_injective (hS.1.trans hC)).comp e.symm.injective)

/-- Direct connection to the existing table reduction. Its four concrete
coverage/containment premises are not silently discharged by the parabolic
obstruction proved above. -/
theorem fixedParabolics_of_representatives
    (hbij : Function.Bijective ReeF4.Parabolics.OuterLocal.binaryDerivedAction)
    (hcover : BinaryInvolutionCoverage)
    (hlong : ∃ P : Subgroup _root_.Tits.ParrottGroup, IsRootParabolic P ∧ P < ⊤ ∧
      centralizer {_root_.Tits.parrottGenerator .s1} ≤ P)
    (hshort : ∃ P : Subgroup _root_.Tits.ParrottGroup, IsRootParabolic P ∧ P < ⊤ ∧
      centralizer {_root_.Tits.parrottGenerator .s4} ≤ P) : FixedParabolics := by
  intro a ha
  have hsq : a ^ 2 = 1 := by simpa only [ha] using pow_orderOf_eq_one a
  have hne : a ≠ 1 := by intro h; simp only [h, orderOf_one] at ha; omega
  obtain ⟨x, P, _, _, hP, _, hC, _⟩ :=
    involution_table_of_representatives hbij hcover hlong hshort a hsq hne
  exact ⟨P, hP, hC⟩

end CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.SixAutomorphisms.ModelIdentification.QuotientScreen.RankTwo.Exceptional.Tits
