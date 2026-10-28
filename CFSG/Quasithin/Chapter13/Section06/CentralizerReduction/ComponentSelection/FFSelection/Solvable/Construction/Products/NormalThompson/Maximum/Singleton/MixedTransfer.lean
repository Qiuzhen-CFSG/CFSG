module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.FFSelection.Solvable.Construction.Products.NormalThompson.Maximum.Singleton.MixedTransfer.Models
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.FFSelection.Solvable.Construction.Products.NormalThompson.Maximum.Singleton.MixedTransfer.SharpTransfer
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.FFSelection.Solvable.Construction.Products.NormalThompson.Maximum.Singleton.MixedTransfer.NativeThree

/-!
# Moving maximum elementary subgroups in the mixed singleton case

For either selected S₃ coordinate, the full native complementary clause gives
one of two outputs: an actual global maximum meeting that coordinate and
satisfying equality in B.2.4, or a single/doubled natural SL₃ complementary
action with its field, odd degree, moved-space equality and intertwiner intact.

The SL₂, S₅ and exceptional four-dimensional alternatives produce sharp
maxima. `SharpTransfer` replaces these by moving maxima in the literal full
preimage. For the SL₃ alternatives, `NativeThree` proves the stronger marked
seed result: the normal selected S₃ is the whole star group, so a global
moving maximum already lies in its full preimage. No splitting or elementary
lifting assumption is made on an arbitrary quotient offender.

The final marked-kernel applications retain the actual action kernel O₂(L).
The earlier residual calculation supplies |Lᵥ/O₂(Lᵥ)| = 3 from that kernel;
the flag applications discharge the kernel input on the identical marking.
Thus no cubic quotient, strong-offender exclusion or maximum-lifting premise
remains in the flag witnesses. The moved-space order four remains explicit,
as supplied independently by the product-support construction. The support
identity, local SQTK hypothesis and non-S₃ condition on the other factor are
unnecessary once the native two-factor action and marked inputs are supplied.
The singleton parent retains assembly with its other branches.

Source: Aschbacher–Smith B.2.4, B.5.6(3), and 13.6.13, printed pp.75–76,
105 and 929, combined manuscript of 1 March 2004.
-/

@[expose] public section
open Subgroup Stellmacher Representation Representation.BinaryOffender
open scoped IsMulCommutative
open CFSG.Quasithin.ChapterB.SourceInduction CFSG.Quasithin.ChapterB.QuasisimpleSource
open CFSG.Quasithin.Chapter13.Section08.Components.Swapped.LinearTwo.ModuleAlternatives
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.Solvable.Construction.Products
variable {G : Type*} [Group G] [Finite G]

/-- The first mixed coordinate reduces to a sharp global maximum or a native
SL₃ action. This is an exhaustive reduction using every source factor clause. -/
theorem minimalSolvable_twoFactor_first_sharp_or_linearThree_complement
    (L T : Subgroup G) (z v : G) (hz : z ∈ Gv v)
    [IsElementaryAbelian 2 (Uv z v)]
    (S : Sylow 2 (Gv v))
    (hS : (S : Subgroup (Gv v)).map (Gv v).subtype = Tv T v)
    {X : Subgroup (Gstar z v)} (hX : MinimalSolvable L T z v X)
    (c : SourceTwoFactorCase (FFFactors.offenderRepresentation (starRepresentation z v)))
    (e : c.first ≃* Equiv.Perm (Fin 3))
    (hF : X.subgroupOf (FFFactors.offenderActor (starRepresentation z v)) =
      @Subgroup.map c.first _ (FFFactors.offenderActor (starRepresentation z v)) _
        c.first.subtype (pResidual 2 c.first)) :
    let I := FFFactors.offenderActor (starRepresentation z v)
    (∃ E ∈ elementaryAbelianMaxSubgroups (⊤ : Subgroup (Gv v)),
      E.map (starMk z v) ⊓ c.first.map I.subtype ≠ ⊥ ∧
      fixedCodim (starRepresentation z v) (E.map (starMk z v)) =
        rank (E.map (starMk z v))) ∨
      NormalThompson.Maximum.Singleton.MixedTransfer.Models.LinearThreeFactor
        (FFFactors.offenderRepresentation (starRepresentation z v)) c.second c.secondSpace := by
  dsimp only
  rcases NormalThompson.Maximum.Singleton.MixedTransfer.Models.sourceFactor_nonstrong_or_linearThree
    _ c.second c.secondSpace c.secondCase with hn | hn
  · exact Or.inl
      (minimalSolvable_twoFactor_first_global_maximum_sharp_of_nonstrong_complement
        L T z v hz S hS hX c e hn hF)
  · exact Or.inr hn

/-- The symmetric reduction retains the original second coordinate and maps. -/
theorem minimalSolvable_twoFactor_second_sharp_or_linearThree_complement
    (L T : Subgroup G) (z v : G) (hz : z ∈ Gv v)
    [IsElementaryAbelian 2 (Uv z v)]
    (S : Sylow 2 (Gv v))
    (hS : (S : Subgroup (Gv v)).map (Gv v).subtype = Tv T v)
    {X : Subgroup (Gstar z v)} (hX : MinimalSolvable L T z v X)
    (c : SourceTwoFactorCase (FFFactors.offenderRepresentation (starRepresentation z v)))
    (e : c.second ≃* Equiv.Perm (Fin 3))
    (hF : X.subgroupOf (FFFactors.offenderActor (starRepresentation z v)) =
      @Subgroup.map c.second _ (FFFactors.offenderActor (starRepresentation z v)) _
        c.second.subtype (pResidual 2 c.second)) :
    let I := FFFactors.offenderActor (starRepresentation z v)
    (∃ E ∈ elementaryAbelianMaxSubgroups (⊤ : Subgroup (Gv v)),
      E.map (starMk z v) ⊓ c.second.map I.subtype ≠ ⊥ ∧
      fixedCodim (starRepresentation z v) (E.map (starMk z v)) =
        rank (E.map (starMk z v))) ∨
      NormalThompson.Maximum.Singleton.MixedTransfer.Models.LinearThreeFactor
        (FFFactors.offenderRepresentation (starRepresentation z v)) c.first c.firstSpace := by
  dsimp only
  rcases NormalThompson.Maximum.Singleton.MixedTransfer.Models.sourceFactor_nonstrong_or_linearThree
    _ c.first c.firstSpace c.firstCase with hn | hn
  · exact Or.inl
      (minimalSolvable_twoFactor_second_global_maximum_sharp_of_nonstrong_complement
        L T z v hz S hS hX c e hn hF)
  · exact Or.inr hn

/-- The selected first native factor has a moving maximum in its full
star preimage. The actual marking's action kernel supplies the earlier cubic
quotient. This also covers the mixed case without a restriction on the other
factor or an assumption about lifting its offenders. -/
theorem minimalSolvable_twoFactor_first_maximum_of_mixed_marked_kernel
    {L V : Subgroup G} (s : A5Module.Marking L V) (T : Subgroup G)
    (hk : s.action.ker = pCore 2 L)
    [IsElementaryAbelian 2 (Uv (A5Module.markedZ s) (A5Module.markedV s))]
    (S : Sylow 2 (Gv (A5Module.markedV s)))
    (hS : (S : Subgroup (Gv (A5Module.markedV s))).map (Gv (A5Module.markedV s)).subtype =
      Tv T (A5Module.markedV s))
    (hfix : Tv T (A5Module.markedV s) ≤ centralizer ({A5Module.markedZ s} : Set G))
    (hL : Tv T (A5Module.markedV s) ≤ normalizer (Lv L (A5Module.markedV s) : Set G))
    {X : Subgroup (Gstar (A5Module.markedZ s) (A5Module.markedV s))}
    (hX : MinimalSolvable L T (A5Module.markedZ s) (A5Module.markedV s) X)
    (c : SourceTwoFactorCase (FFFactors.offenderRepresentation
      (starRepresentation (A5Module.markedZ s) (A5Module.markedV s))))
    (e : c.first ≃* Equiv.Perm (Fin 3))
    (hF : X.subgroupOf (FFFactors.offenderActor
      (starRepresentation (A5Module.markedZ s) (A5Module.markedV s))) =
      (pResidual 2 c.first).map c.first.subtype) :
    let I := FFFactors.offenderActor (starRepresentation (A5Module.markedZ s) (A5Module.markedV s))
    let H := c.first.map I.subtype
    Nat.card (movedSubgroup (A5Module.markedZ s) (A5Module.markedV s) H) = 4 →
      ∃ E ∈ elementaryAbelianMaxSubgroups
        (H.comap (starMk (A5Module.markedZ s) (A5Module.markedV s))),
        E.map (starMk (A5Module.markedZ s) (A5Module.markedV s)) ≠ ⊥ := by
  intro I H hcard
  rcases minimalSolvable_twoFactor_first_sharp_or_linearThree_complement
    L T _ _ (A5Module.markedZ_mem_Gv s) S hS hX c e hF with hsharp | hlinear
  · obtain ⟨E, hE, hne, heq⟩ := hsharp
    let : H.Normal := minimalSolvable_twoFactor_first_normal
      L T _ _ (A5Module.markedZ_mem_Gv s) S hS hfix hX c e hF
    exact star_maximum_of_singleton_sharp _ _ (A5Module.markedZ_mem_Gv s) H
      ((c.first.equivMapOfInjective I.subtype I.subtype_injective).symm.trans e)
      hcard E hE hne heq
  · exact minimalSolvable_twoFactor_first_maximum_of_marked_source
      s T S hS hfix hL (A5Module.residualQuotient_card s hk) hX c e hF hcard

/-- The selected second native factor has a moving maximum in its full
star preimage. The actual marking's action kernel supplies the earlier cubic
quotient. This also covers the mixed case without a restriction on the other
factor or an assumption about lifting its offenders. -/
theorem minimalSolvable_twoFactor_second_maximum_of_mixed_marked_kernel
    {L V : Subgroup G} (s : A5Module.Marking L V) (T : Subgroup G)
    (hk : s.action.ker = pCore 2 L)
    [IsElementaryAbelian 2 (Uv (A5Module.markedZ s) (A5Module.markedV s))]
    (S : Sylow 2 (Gv (A5Module.markedV s)))
    (hS : (S : Subgroup (Gv (A5Module.markedV s))).map (Gv (A5Module.markedV s)).subtype =
      Tv T (A5Module.markedV s))
    (hfix : Tv T (A5Module.markedV s) ≤ centralizer ({A5Module.markedZ s} : Set G))
    (hL : Tv T (A5Module.markedV s) ≤ normalizer (Lv L (A5Module.markedV s) : Set G))
    {X : Subgroup (Gstar (A5Module.markedZ s) (A5Module.markedV s))}
    (hX : MinimalSolvable L T (A5Module.markedZ s) (A5Module.markedV s) X)
    (c : SourceTwoFactorCase (FFFactors.offenderRepresentation
      (starRepresentation (A5Module.markedZ s) (A5Module.markedV s))))
    (e : c.second ≃* Equiv.Perm (Fin 3))
    (hF : X.subgroupOf (FFFactors.offenderActor
      (starRepresentation (A5Module.markedZ s) (A5Module.markedV s))) =
      (pResidual 2 c.second).map c.second.subtype) :
    let I := FFFactors.offenderActor (starRepresentation (A5Module.markedZ s) (A5Module.markedV s))
    let H := c.second.map I.subtype
    Nat.card (movedSubgroup (A5Module.markedZ s) (A5Module.markedV s) H) = 4 →
      ∃ E ∈ elementaryAbelianMaxSubgroups
        (H.comap (starMk (A5Module.markedZ s) (A5Module.markedV s))),
        E.map (starMk (A5Module.markedZ s) (A5Module.markedV s)) ≠ ⊥ := by
  intro I H hcard
  rcases minimalSolvable_twoFactor_second_sharp_or_linearThree_complement
    L T _ _ (A5Module.markedZ_mem_Gv s) S hS hX c e hF with hsharp | hlinear
  · obtain ⟨E, hE, hne, heq⟩ := hsharp
    let : H.Normal := minimalSolvable_twoFactor_second_normal
      L T _ _ (A5Module.markedZ_mem_Gv s) S hS hfix hX c e hF
    exact star_maximum_of_singleton_sharp _ _ (A5Module.markedZ_mem_Gv s) H
      ((c.second.equivMapOfInjective I.subtype I.subtype_injective).symm.trans e)
      hcard E hE hne heq
  · exact minimalSolvable_twoFactor_second_maximum_of_marked_source
      s T S hS hfix hL (A5Module.residualQuotient_card s hk) hX c e hF hcard

/-- Final first-coordinate mixed-case witness on the actual source flag.
The flag supplies its action kernel; the proved residual quotient calculation
and the two transfer branches discharge every other auxiliary premise. -/
theorem minimalSolvable_twoFactor_first_maximum_of_mixed_flag
    {T : Sylow 2 G} {L V V₁ V₂ : Subgroup G}
    (f : A5Module.FlagMarking T L V V₁ V₂)
    [IsElementaryAbelian 2 (Uv (A5Module.markedZ f.module) (A5Module.markedV f.module))]
    (S : Sylow 2 (Gv (A5Module.markedV f.module)))
    (hS : (S : Subgroup (Gv (A5Module.markedV f.module))).map
      (Gv (A5Module.markedV f.module)).subtype = Tv (T : Subgroup G) (A5Module.markedV f.module))
    (hfix : Tv (T : Subgroup G) (A5Module.markedV f.module) ≤
      centralizer ({A5Module.markedZ f.module} : Set G))
    (hL : Tv (T : Subgroup G) (A5Module.markedV f.module) ≤
      normalizer (Lv L (A5Module.markedV f.module) : Set G))
    {X : Subgroup (Gstar (A5Module.markedZ f.module) (A5Module.markedV f.module))}
    (hX : MinimalSolvable L (T : Subgroup G) (A5Module.markedZ f.module) (A5Module.markedV f.module) X)
    (c : SourceTwoFactorCase (FFFactors.offenderRepresentation
      (starRepresentation (A5Module.markedZ f.module) (A5Module.markedV f.module))))
    (e : c.first ≃* Equiv.Perm (Fin 3))
    (hF : X.subgroupOf (FFFactors.offenderActor
      (starRepresentation (A5Module.markedZ f.module) (A5Module.markedV f.module))) =
      (pResidual 2 c.first).map c.first.subtype) :
    let I := FFFactors.offenderActor
      (starRepresentation (A5Module.markedZ f.module) (A5Module.markedV f.module))
    let H := c.first.map I.subtype
    Nat.card (movedSubgroup (A5Module.markedZ f.module) (A5Module.markedV f.module) H) = 4 →
      ∃ E ∈ elementaryAbelianMaxSubgroups
        (H.comap (starMk (A5Module.markedZ f.module) (A5Module.markedV f.module))),
        E.map (starMk (A5Module.markedZ f.module) (A5Module.markedV f.module)) ≠ ⊥ := by
  exact minimalSolvable_twoFactor_first_maximum_of_mixed_marked_kernel
    f.module (T : Subgroup G) f.action_kernel S hS hfix hL hX c e hF

/-- Final second-coordinate mixed-case witness on the actual source flag.
The flag supplies its action kernel; the proved residual quotient calculation
and the two transfer branches discharge every other auxiliary premise. -/
theorem minimalSolvable_twoFactor_second_maximum_of_mixed_flag
    {T : Sylow 2 G} {L V V₁ V₂ : Subgroup G}
    (f : A5Module.FlagMarking T L V V₁ V₂)
    [IsElementaryAbelian 2 (Uv (A5Module.markedZ f.module) (A5Module.markedV f.module))]
    (S : Sylow 2 (Gv (A5Module.markedV f.module)))
    (hS : (S : Subgroup (Gv (A5Module.markedV f.module))).map
      (Gv (A5Module.markedV f.module)).subtype = Tv (T : Subgroup G) (A5Module.markedV f.module))
    (hfix : Tv (T : Subgroup G) (A5Module.markedV f.module) ≤
      centralizer ({A5Module.markedZ f.module} : Set G))
    (hL : Tv (T : Subgroup G) (A5Module.markedV f.module) ≤
      normalizer (Lv L (A5Module.markedV f.module) : Set G))
    {X : Subgroup (Gstar (A5Module.markedZ f.module) (A5Module.markedV f.module))}
    (hX : MinimalSolvable L (T : Subgroup G) (A5Module.markedZ f.module) (A5Module.markedV f.module) X)
    (c : SourceTwoFactorCase (FFFactors.offenderRepresentation
      (starRepresentation (A5Module.markedZ f.module) (A5Module.markedV f.module))))
    (e : c.second ≃* Equiv.Perm (Fin 3))
    (hF : X.subgroupOf (FFFactors.offenderActor
      (starRepresentation (A5Module.markedZ f.module) (A5Module.markedV f.module))) =
      (pResidual 2 c.second).map c.second.subtype) :
    let I := FFFactors.offenderActor
      (starRepresentation (A5Module.markedZ f.module) (A5Module.markedV f.module))
    let H := c.second.map I.subtype
    Nat.card (movedSubgroup (A5Module.markedZ f.module) (A5Module.markedV f.module) H) = 4 →
      ∃ E ∈ elementaryAbelianMaxSubgroups
        (H.comap (starMk (A5Module.markedZ f.module) (A5Module.markedV f.module))),
        E.map (starMk (A5Module.markedZ f.module) (A5Module.markedV f.module)) ≠ ⊥ := by
  exact minimalSolvable_twoFactor_second_maximum_of_mixed_marked_kernel
    f.module (T : Subgroup G) f.action_kernel S hS hfix hL hX c e hF

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.Solvable.Construction.Products
end
