module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.FFSelection.Solvable.Construction.Products.NormalThompson.Maximum.Singleton.MixedTransfer.Models
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.FFSelection.Solvable.Construction.Products.NormalThompson.Maximum.Singleton.MixedTransfer.NativeThree.ActionBounds

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.FFSelection.Solvable.Construction.Products.NormalThompson.Maximum.Singleton.MixedTransfer.NativeThree.SeedCollapse
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.LocalSetup.Configuration.ResidualModule.Quotient

/-!
# Moving maxima for the marked native SL₃ branch

The doubled natural SL₃ clause is incompatible with a strong complementary
action. Thus the remaining branch has an actual single natural action,
with its odd field degree and moved-space identity unchanged. Every strong
offender in that action fixes an F-hyperplane and has binary rank in (m,2m].

The action reductions retain the original first and second quotient summands.
The final maximum witnesses use a stronger marked-source argument: the
normal selected S₃ is the whole star group, by `SeedCollapse`, so its full
preimage is Gᵥ. An actual global maximum moving X is therefore sufficient.
Every native two-factor action and residual-selection clause is retained;
no assumption on the complementary action is needed for this stronger route.

The source quotient |Lᵥ/O₂(Lᵥ)| = 3 is explicit in the general marked
applications. The flag applications discharge it with the already proved
`FlagMarking.residualQuotient_card`, on the identical marking. This earlier
p.926 input comes from the genuine action kernel O₂(L); a bare `Marking`
without that kernel does not supply it. No later characteristic-two,
solvable-exclusion, Thompson-equality or lifting premise is used.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, B.5.6(3),
printed p.105, and 13.6.13, p.929.
-/

@[expose] public section
open Subgroup Representation Representation.BinaryOffender
open scoped IsMulCommutative
open CFSG.Quasithin.ChapterB.SourceInduction CFSG.Quasithin.ChapterB.QuasisimpleSource

namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.Solvable.Construction.Products.NormalThompson.Maximum.Singleton.MixedTransfer.NativeThree
variable {D V : Type*} [Group D] [AddCommGroup V] [Module (ZMod 2) V]
  (ρ : Representation (ZMod 2) D V)

/-- Strongness eliminates the doubled alternative while retaining the exact
native quotient, moved space, field and action isomorphism. -/
theorem factor_natural_of_strong (A : Subgroup D) (U : Subrepresentation ρ)
    (hmodel : Models.LinearThreeFactor ρ A U)
    (hstrong : IsStrongFFModule
      (((fixed ρ).quotientImage U).toRepresentation.comp A.subtype)) :
    ∃ F : BinaryField, Odd F.degree ∧ U.toSubmodule = moved ρ A ∧
      IsLinearNatural (((fixed ρ).quotientImage U).toRepresentation.comp A.subtype) F 3 ∧
      ∀ B : Subgroup A,
        IsStrongOffender (((fixed ρ).quotientImage U).toRepresentation.comp A.subtype) B →
        fixedCodim (((fixed ρ).quotientImage U).toRepresentation.comp A.subtype) B =
            F.degree ∧ F.degree < rank B ∧ rank B ≤ 2 * F.degree := by
  obtain ⟨F, ho, hm, hn | hd⟩ := hmodel
  · exact ⟨F, ho, hm, hn, linearThree_strong_bounds _ F ho hn⟩
  · exact (repeatedLinearThree_not_strong _ F ho hd hstrong).elim

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.Solvable.Construction.Products.NormalThompson.Maximum.Singleton.MixedTransfer.NativeThree

namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.Solvable.Construction.Products
open NormalThompson.Maximum.Singleton.MixedTransfer
open CFSG.Quasithin.Chapter13.Section08.Components.Swapped.LinearTwo.ModuleAlternatives
variable {G : Type*} [Group G]

/-- For a selected first coordinate, the strong complementary branch uses
one natural module on the literal second quotient summand. The intrinsic
calculation applies before any maximum-elementary lifting is undertaken. -/
theorem twoFactor_second_natural_of_strong (z v : G)
    [IsElementaryAbelian 2 (Uv z v)] :
    let ρ := FFFactors.offenderRepresentation (starRepresentation z v)
    ∀ (c : SourceTwoFactorCase ρ),
      Models.LinearThreeFactor ρ c.second c.secondSpace →
      IsStrongFFModule
        (((fixed ρ).quotientImage c.secondSpace).toRepresentation.comp c.second.subtype) →
      let σ := ((fixed ρ).quotientImage c.secondSpace).toRepresentation.comp c.second.subtype
      ∃ F : BinaryField, Odd F.degree ∧ c.secondSpace.toSubmodule = moved ρ c.second ∧
        IsLinearNatural σ F 3 ∧
        ∀ A : Subgroup c.second, IsStrongOffender σ A →
          fixedCodim σ A = F.degree ∧ F.degree < rank A ∧ rank A ≤ 2 * F.degree := by
  intro ρ c hmodel hstrong
  exact NativeThree.factor_natural_of_strong ρ c.second c.secondSpace hmodel hstrong

/-- The symmetric reduction keeps the actual first summand and its original
inclusion, rather than replacing the actor by an unconnected SL₃ model. -/
theorem twoFactor_first_natural_of_strong (z v : G)
    [IsElementaryAbelian 2 (Uv z v)] :
    let ρ := FFFactors.offenderRepresentation (starRepresentation z v)
    ∀ (c : SourceTwoFactorCase ρ),
      Models.LinearThreeFactor ρ c.first c.firstSpace →
      IsStrongFFModule
        (((fixed ρ).quotientImage c.firstSpace).toRepresentation.comp c.first.subtype) →
      let σ := ((fixed ρ).quotientImage c.firstSpace).toRepresentation.comp c.first.subtype
      ∃ F : BinaryField, Odd F.degree ∧ c.firstSpace.toSubmodule = moved ρ c.first ∧
        IsLinearNatural σ F 3 ∧
        ∀ A : Subgroup c.first, IsStrongOffender σ A →
          fixedCodim σ A = F.degree ∧ F.degree < rank A ∧ rank A ≤ 2 * F.degree := by
  intro ρ c hmodel hstrong
  exact NativeThree.factor_natural_of_strong ρ c.first c.firstSpace hmodel hstrong


variable [Finite G]
open Stellmacher

/-- The marked normal S₃ fills the star group, so the genuine global
maximum moving X is a maximum in its literal full preimage. -/
theorem marked_normal_s3_maximum
    {L V : Subgroup G} (s : A5Module.Marking L V) (T : Subgroup G)
    [IsElementaryAbelian 2 (Uv (A5Module.markedZ s) (A5Module.markedV s))]
    (S : Sylow 2 (Gv (A5Module.markedV s)))
    (hS : (S : Subgroup (Gv (A5Module.markedV s))).map (Gv (A5Module.markedV s)).subtype =
      Tv T (A5Module.markedV s))
    (hfix : Tv T (A5Module.markedV s) ≤ centralizer ({A5Module.markedZ s} : Set G))
    (hL : Tv T (A5Module.markedV s) ≤ normalizer (Lv L (A5Module.markedV s) : Set G))
    (hcubic : Nat.card (Lv L (A5Module.markedV s) ⧸ pCore 2 (Lv L (A5Module.markedV s))) = 3)
    {X : Subgroup (Gstar (A5Module.markedZ s) (A5Module.markedV s))}
    (hX : MinimalSolvable L T (A5Module.markedZ s) (A5Module.markedV s) X)
    (H : Subgroup (Gstar (A5Module.markedZ s) (A5Module.markedV s))) [H.Normal]
    (e : H ≃* Equiv.Perm (Fin 3)) (hXH : X ≤ H)
    (hcard : Nat.card (movedSubgroup (A5Module.markedZ s) (A5Module.markedV s) H) = 4) :
    ∃ E ∈ elementaryAbelianMaxSubgroups (H.comap (starMk (A5Module.markedZ s) (A5Module.markedV s))),
      E.map (starMk (A5Module.markedZ s) (A5Module.markedV s)) ≠ ⊥ := by
  have htop := NativeThree.SeedCollapse.marked_normal_s3_eq_top s T S hS hfix hL
    hcubic hX.1 H e hXH hcard
  obtain ⟨E, hE, hmove⟩ := minimalSolvable_exists_global_maximum_moving
    L T _ _ (A5Module.markedZ_mem_Gv s) S hS hX
  refine ⟨E, ?_, ?_⟩
  · simpa only [htop, comap_top] using hE
  · intro hb
    exact hmove (by rw [hb, commutator_bot_right])

/-- The selected first native coordinate has a moving maximum in its
actual full preimage. The marked-source proof also covers a strong SL₃
complement without restricting or replacing its native action. -/
theorem minimalSolvable_twoFactor_first_maximum_of_marked_source
    {L V : Subgroup G} (s : A5Module.Marking L V) (T : Subgroup G)
    [IsElementaryAbelian 2 (Uv (A5Module.markedZ s) (A5Module.markedV s))]
    (S : Sylow 2 (Gv (A5Module.markedV s)))
    (hS : (S : Subgroup (Gv (A5Module.markedV s))).map (Gv (A5Module.markedV s)).subtype =
      Tv T (A5Module.markedV s))
    (hfix : Tv T (A5Module.markedV s) ≤ centralizer ({A5Module.markedZ s} : Set G))
    (hL : Tv T (A5Module.markedV s) ≤ normalizer (Lv L (A5Module.markedV s) : Set G))
    (hcubic : Nat.card (Lv L (A5Module.markedV s) ⧸ pCore 2 (Lv L (A5Module.markedV s))) = 3)
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
      ∃ E ∈ elementaryAbelianMaxSubgroups (H.comap (starMk (A5Module.markedZ s) (A5Module.markedV s))),
        E.map (starMk (A5Module.markedZ s) (A5Module.markedV s)) ≠ ⊥ := by
  intro I H hcard
  let : H.Normal := minimalSolvable_twoFactor_first_normal
    L T _ _ (A5Module.markedZ_mem_Gv s) S hS hfix hX c e hF
  have hXH : X ≤ H := by
    rw [← minimalSolvable_selected_residual
      L T _ _ (A5Module.markedZ_mem_Gv s) S hS hX c.first hF]
    exact map_subtype_le _
  exact marked_normal_s3_maximum s T S hS hfix hL hcubic hX H
    ((c.first.equivMapOfInjective I.subtype I.subtype_injective).symm.trans e) hXH hcard

/-- The selected second native coordinate has a moving maximum in its
actual full preimage. The marked-source proof also covers a strong SL₃
complement without restricting or replacing its native action. -/
theorem minimalSolvable_twoFactor_second_maximum_of_marked_source
    {L V : Subgroup G} (s : A5Module.Marking L V) (T : Subgroup G)
    [IsElementaryAbelian 2 (Uv (A5Module.markedZ s) (A5Module.markedV s))]
    (S : Sylow 2 (Gv (A5Module.markedV s)))
    (hS : (S : Subgroup (Gv (A5Module.markedV s))).map (Gv (A5Module.markedV s)).subtype =
      Tv T (A5Module.markedV s))
    (hfix : Tv T (A5Module.markedV s) ≤ centralizer ({A5Module.markedZ s} : Set G))
    (hL : Tv T (A5Module.markedV s) ≤ normalizer (Lv L (A5Module.markedV s) : Set G))
    (hcubic : Nat.card (Lv L (A5Module.markedV s) ⧸ pCore 2 (Lv L (A5Module.markedV s))) = 3)
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
      ∃ E ∈ elementaryAbelianMaxSubgroups (H.comap (starMk (A5Module.markedZ s) (A5Module.markedV s))),
        E.map (starMk (A5Module.markedZ s) (A5Module.markedV s)) ≠ ⊥ := by
  intro I H hcard
  let : H.Normal := minimalSolvable_twoFactor_second_normal
    L T _ _ (A5Module.markedZ_mem_Gv s) S hS hfix hX c e hF
  have hXH : X ≤ H := by
    rw [← minimalSolvable_selected_residual
      L T _ _ (A5Module.markedZ_mem_Gv s) S hS hX c.second hF]
    exact map_subtype_le _
  exact marked_normal_s3_maximum s T S hS hfix hL hcubic hX H
    ((c.second.equivMapOfInjective I.subtype I.subtype_injective).symm.trans e) hXH hcard

/-- On the actual marked flag, the earlier local construction discharges
the cubic quotient premise of the first-coordinate witness. -/
theorem minimalSolvable_twoFactor_first_maximum_of_marked_flag
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
  exact minimalSolvable_twoFactor_first_maximum_of_marked_source f.module (T : Subgroup G)
    S hS hfix hL f.residualQuotient_card hX c e hF

/-- On the actual marked flag, the earlier local construction discharges
the cubic quotient premise of the second-coordinate witness. -/
theorem minimalSolvable_twoFactor_second_maximum_of_marked_flag
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
  exact minimalSolvable_twoFactor_second_maximum_of_marked_source f.module (T : Subgroup G)
    S hS hfix hL f.residualQuotient_card hX c e hF

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.Solvable.Construction.Products
end
