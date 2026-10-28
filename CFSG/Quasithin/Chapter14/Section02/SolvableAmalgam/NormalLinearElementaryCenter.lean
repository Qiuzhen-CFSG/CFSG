module
public import CFSG.Quasithin.Chapter14.Section02.SolvableAmalgam.NormalLinearStructure
public import CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels.QuadraticOrbit
public import Theory.GroupTheory.PGroup.SmallFrattiniSingularCenter

/-!
# The elementary center of the actual normal binary closure

The original selected source supplies U/Φ(U), a singular seed and its
spanning conjugation orbit. The marked PSL₂ Borel realizes this orbit on
five or nine coordinates. The uniform polar radical is singular, so the
actual square map vanishes on the center image. Hence Z(U) is elementary,
including the order-64 and order-1024 central-extension alternatives.

Source: Aschbacher–Smith 14.2.16 and F.1.12, pp.985–986 and 262–264.
-/

public section
open Subgroup Stellmacher Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section02.LocalBinary
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06 ChapterE
open Chapter12.Section08
open ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels
variable {G : Type*} [Group G] [Finite G]

/-- The literal normal binary closure has an elementary center over
the four- or eight-element field. -/
theorem source_nonabelian_linear_closure_center_elementary
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (H : Subgroup G) (hH : H ∈ Chapter1.HOutside G (T : Set G) (M : Set G))
    (hne : ¬ IsMulCommutative (conjugateSpanBy (localModule T M) H))
    (K : Subgroup H) [K.Normal]
    (hgen : K ⊔ (T.subtype hH.1.2 : Subgroup H) = ⊤)
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    (n : ℕ) (hn : n = 2 ∨ n = 3) (hF : Nat.card F = 2^n)
    (hm : ModelBorelPair ((H ⊓ M).subgroupOf H) K (BenderSuzuki.Converse.PBorel F)) :
    IsElementaryAbelian 2 (center (conjugateSpanBy (localModule T M) H)) := by
  let D : ChapterG.Section02.Setup G :=
    { V := localModule T M, V₁ := centralInvolutions T, L := sourceResidual M Mc,
      T := T, H := H }
  obtain ⟨h,hphi,hphic,w,hw,hfix,hspan,hzero,hpolar⟩ :=
    source_frattini_seed_orbit hG T hempty hM hu hmany hcard e H hH hne
  let := SmallFrattini.quotientElementary h.U_isPGroup
  let ρ := frattiniRepresentation D h.U_isPGroup
  let B := SmallFrattini.quotientBilinearForm h.U_isPGroup hphic
  let Q := SmallFrattini.quotientQuadraticForm h.U_isPGroup hphic
  have hMN : M ≤ normalizer (D.V : Set G) :=
    (InitialSource.UniformControl.source_local_eq_normalizer hG T hM.1).le
  have hfixed (g : H) (hg : g ∈ (H ⊓ M).subgroupOf H) :
      ρ g (Additive.ofMul w) = Additive.ofMul w := by
    change Additive.ofMul (frattiniActor D g w) = Additive.ofMul w
    exact congrArg Additive.ofMul (hfix g (hMN hg.2))
  have hSM : (T.subtype hH.1.2 : Subgroup H) ≤ (H ⊓ M).subgroupOf H := by
    intro t ht
    exact ⟨t.property,hM.1.2 ht⟩
  obtain ⟨f,hf,hpull,hcoord⟩ := hm.linear_quadratic_realization _ K _ hgen hSM n hF
    ρ (Additive.ofMul w) hfixed hspan B
    (SmallFrattini.quotientBilinearForm_isAlt _ _) hpolar
    (fun g x y => SmallFrattini.quotientBilinearForm_invariant
      h.U_isPGroup hphic (closureActor D g) x.toMul y.toMul)
    Q hzero (fun g x => SmallFrattini.quotientQuadraticForm_invariant
      h.U_isPGroup hphic (closureActor D g) x.toMul)
  have hdegree : 2^n+1 = 5 ∨ 2^n+1 = 9 := by
    rcases hn with rfl | rfl <;> norm_num
  exact SmallFrattini.center_elementary_of_uniform_quadratic_quotient
    h.U_isPGroup hphic (2^n+1) hdegree f hf hpull hcoord

/-- Apply singularity of the actual square-form radical to the original
normal Bender row. The existing source restriction discharges the field
exponent, so no extra elementary-center premise is retained. -/
theorem source_normal_bender_closure_center_elementary
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (H : Subgroup G) (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (hnH : 1 < generationParameter H)
    (hne : ¬ IsMulCommutative (conjugateSpanBy (localModule T M) H))
    (K : Subgroup H) (hK : K.IsCComponent) [K.Normal]
    (hqK : IsQuasisimple (K ⧸ pCore 2 K))
    (hgen : K ⊔ (T.subtype hH.1.1.2 : Subgroup H) = ⊤)
    (f : ℕ) (hm : BenderModel ((H ⊓ M).subgroupOf H) K f) :
    IsElementaryAbelian 2 (center (conjugateSpanBy (localModule T M) H)) := by
  obtain ⟨hr,F,hfield,hfinite,hchar,hF,hmodel⟩ :=
    source_normal_bender_nonabelian_models hG T hempty hM hu hmany hcard e
      H hH hnH hne K hK hqK hgen f hm
  let := hfield
  let := hfinite
  let := hchar
  exact source_nonabelian_linear_closure_center_elementary hG T hempty hM hu hmany hcard e
    H hH.1 hne K hgen f hr hF hmodel
end CFSG.Quasithin.Chapter14.Section02.LocalBinary
