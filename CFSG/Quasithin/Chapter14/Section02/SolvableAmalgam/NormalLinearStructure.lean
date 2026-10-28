module
public import CFSG.Quasithin.Chapter14.Section02.ReducedLargeAmalgamSource
public import CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels.PolarOrbit
public import Theory.GroupTheory.PGroup.SmallFrattiniPolarOrder

/-!
# The actual normal closure's order and center

The marked PSL₂ Borel gives a spanning projective orbit in U/Φ(U).
Its invariant commutator polar is the uniform binary polar. The odd orbit
degree gives either its nondegenerate quotient or the full space with a
one-dimensional radical. Consequently the closure has order 32 or 64
over the four-element field, and 512 or 1024 over the eight-element field;
its center has order two or four respectively. The possible central
extension is retained for the opposite-parabolic recognition argument.

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

/-- The literal closure retains the exact order of its polar radical. -/
theorem source_nonabelian_linear_closure_structure
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
    (n : ℕ) (hn : 0 < n) (hF : Nat.card F = 2^n)
    (hm : ModelBorelPair ((H ⊓ M).subgroupOf H) K (BenderSuzuki.Converse.PBorel F)) :
    let U := conjugateSpanBy (localModule T M) H
    (Nat.card U = 2^(2^n+1) ∧ Nat.card (center U) = 2) ∨
      (Nat.card U = 2^(2^n+2) ∧ Nat.card (center U) = 4) := by
  let D : ChapterG.Section02.Setup G :=
    { V := localModule T M, V₁ := centralInvolutions T, L := sourceResidual M Mc,
      T := T, H := H }
  obtain ⟨h,hphi,hphic,w,hw,hfix,hspan,hzero,hpolar⟩ :=
    source_frattini_seed_orbit hG T hempty hM hu hmany hcard e H hH hne
  let := SmallFrattini.quotientElementary h.U_isPGroup
  let ρ := frattiniRepresentation D h.U_isPGroup
  let B := SmallFrattini.quotientBilinearForm h.U_isPGroup hphic
  have hMN : M ≤ normalizer (D.V : Set G) :=
    (InitialSource.UniformControl.source_local_eq_normalizer hG T hM.1).le
  have hfixed (g : H) (hg : g ∈ (H ⊓ M).subgroupOf H) :
      ρ g (Additive.ofMul w) = Additive.ofMul w := by
    change Additive.ofMul (frattiniActor D g w) = Additive.ofMul w
    exact congrArg Additive.ofMul (hfix g (hMN hg.2))
  have hSM : (T.subtype hH.1.2 : Subgroup H) ≤ (H ⊓ M).subgroupOf H := by
    intro t ht
    exact ⟨t.property,hM.1.2 ht⟩
  obtain ⟨f,hf,hpull⟩ := hm.linear_polar_realization _ K _ hgen hSM n hF
    ρ (Additive.ofMul w) hfixed hspan B
    (SmallFrattini.quotientBilinearForm_isAlt _ _) hpolar
    (fun g x y => SmallFrattini.quotientBilinearForm_invariant
      h.U_isPGroup hphic (closureActor D g) x.toMul y.toMul)
  have hodd : Odd (2^n+1) := (Nat.even_pow.mpr ⟨even_two,by omega⟩).add_odd odd_one
  have hh := SmallFrattini.order_and_center_of_odd_polar_quotient
    h.U_isPGroup hphic (2^n+1) hodd f hf (fun x y =>
      (congrArg (fun C : LinearMap.BilinForm (ZMod 2) (UniformBinaryPolar.V (2^n+1)) =>
        C x y) hpull).symm)
  exact hh

/-- Apply the intrinsic closure calculation to the normal row of the
original selected large-parabolic alternatives. No model or rank bound
beyond that row's actual Bender marking is needed. -/
theorem source_normal_bender_closure_structure
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
    let U := conjugateSpanBy (localModule T M) H
    (f = 2 ∧ ((Nat.card U = 32 ∧ Nat.card (center U) = 2) ∨
      (Nat.card U = 64 ∧ Nat.card (center U) = 4))) ∨
    (f = 3 ∧ ((Nat.card U = 512 ∧ Nat.card (center U) = 2) ∨
      (Nat.card U = 1024 ∧ Nat.card (center U) = 4))) := by
  obtain ⟨hr,F,hfield,hfinite,hchar,hF,hmodel⟩ :=
    source_normal_bender_nonabelian_models hG T hempty hM hu hmany hcard e
      H hH hnH hne K hK hqK hgen f hm
  let := hfield
  let := hfinite
  let := hchar
  have hf : 0 < f := by rcases hr with rfl | rfl <;> decide
  have hc := source_nonabelian_linear_closure_structure hG T hempty hM hu hmany hcard e
    H hH.1 hne K hgen f hf hF hmodel
  rcases hr with rfl | rfl
  · exact Or.inl ⟨rfl,by simpa using hc⟩
  · exact Or.inr ⟨rfl,by simpa using hc⟩
end CFSG.Quasithin.Chapter14.Section02.LocalBinary
