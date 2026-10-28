module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.FFSelection.Solvable.Construction.Products.NormalThompson.Normality
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.FFSelection.Solvable.Construction.Products.NormalThompson.Witness
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.FFSelection.Solvable.Construction.Products.NormalThompson.Maximum.Double
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.FFSelection.Solvable.Construction.Products.NormalThompson.Maximum.Singleton.Assembly

/-!
# Normality and Thompson closure for the selected S₃ products

The native two-factor and hyperplane selections have ambient-normal S₃
overgroups. Their embedded residuals are the original X. A maximum elementary
subgroup of the full star preimage with nontrivial coordinate image suffices
to prove the literal Thompson equality; two such witnesses cover the product.

The constructed maximum-elementary witnesses now discharge all four branches.
The singleton branches retain the moved-space order four from the independent
product-support construction; the double branch needs no extra support premise.
The original conditional closing lemmas remain available unchanged.

For the mixed singleton branch, the earlier marked action has kernel O₂(L).
The marked-kernel versions expose this input, while the actual source-flag
applications supply it on the identical marking. It is retained by the checked
`LocalSetup.Configuration` construction (producer
`qt-13-06-char2-local-configuration`); a bare module marking does not assert it.
No characteristic-two, decomposition, irreducibility or solvable-exclusion
conclusion is assumed. The parent product-branch construction retains the
support discharge and final `NormalS3Decomposition` assembly.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
13.6.13, printed p.929.
-/

@[expose] public section
open Subgroup Stellmacher
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.Solvable.Construction.Products
open CFSG.Quasithin.ChapterB.SourceInduction
open CFSG.Quasithin.Chapter13.Section08.Components.Swapped.LinearTwo.ModuleAlternatives
variable {G : Type*} [Group G] [Finite G]

/-- The first native product branch, conditional on a moving maximum elementary
subgroup of the full preimage. Normality and the model transport are discharged here. -/
theorem minimalSolvable_twoFactor_first_thompson_of_maximum
    (L T : Subgroup G) (z v : G) (hz : z ∈ Gv v)
    [IsElementaryAbelian 2 (Uv z v)]
    (S : Sylow 2 (Gv v))
    (hS : (S : Subgroup (Gv v)).map (Gv v).subtype = Tv T v)
    (hfix : Tv T v ≤ centralizer ({z} : Set G))
    {X : Subgroup (Gstar z v)} (hX : MinimalSolvable L T z v X)
    (c : SourceTwoFactorCase (FFFactors.offenderRepresentation (starRepresentation z v)))
    (e : c.first ≃* Equiv.Perm (Fin 3))
    (hF : X.subgroupOf (FFFactors.offenderActor (starRepresentation z v)) =
      @Subgroup.map c.first _ (FFFactors.offenderActor (starRepresentation z v)) _
        c.first.subtype (pResidual 2 c.first)) :
    let I := FFFactors.offenderActor (starRepresentation z v)
    let H := c.first.map I.subtype
    (∃ E ∈ elementaryAbelianMaxSubgroups (H.comap (starMk z v)),
      E.map (starMk z v) ≠ ⊥) →
    starImage z v (elementaryAbelianMaxJ (starPreimage z v H)) = H := by
  intro I H ⟨E, hE, hne⟩
  let : H.Normal := minimalSolvable_twoFactor_first_normal L T z v hz S hS hfix hX c e hF
  exact star_thompson_eq_of_maximum z v H
    ((c.first.equivMapOfInjective I.subtype I.subtype_injective).symm.trans e) E hE hne

/-- The second native product branch, conditional on a moving maximum elementary
subgroup of the full preimage. Normality and the model transport are discharged here. -/
theorem minimalSolvable_twoFactor_second_thompson_of_maximum
    (L T : Subgroup G) (z v : G) (hz : z ∈ Gv v)
    [IsElementaryAbelian 2 (Uv z v)]
    (S : Sylow 2 (Gv v))
    (hS : (S : Subgroup (Gv v)).map (Gv v).subtype = Tv T v)
    (hfix : Tv T v ≤ centralizer ({z} : Set G))
    {X : Subgroup (Gstar z v)} (hX : MinimalSolvable L T z v X)
    (c : SourceTwoFactorCase (FFFactors.offenderRepresentation (starRepresentation z v)))
    (e : c.second ≃* Equiv.Perm (Fin 3))
    (hF : X.subgroupOf (FFFactors.offenderActor (starRepresentation z v)) =
      @Subgroup.map c.second _ (FFFactors.offenderActor (starRepresentation z v)) _
        c.second.subtype (pResidual 2 c.second)) :
    let I := FFFactors.offenderActor (starRepresentation z v)
    let H := c.second.map I.subtype
    (∃ E ∈ elementaryAbelianMaxSubgroups (H.comap (starMk z v)),
      E.map (starMk z v) ≠ ⊥) →
    starImage z v (elementaryAbelianMaxJ (starPreimage z v H)) = H := by
  intro I H ⟨E, hE, hne⟩
  let : H.Normal := minimalSolvable_twoFactor_second_normal L T z v hz S hS hfix hX c e hF
  exact star_thompson_eq_of_maximum z v H
    ((c.second.equivMapOfInjective I.subtype I.subtype_injective).symm.trans e) E hE hne

/-- The native hyperplane selection discharges normality; only the maximum-elementary
witness is additional to the branch inputs. -/
theorem minimalSolvable_hyperplane_thompson_of_maximum
    (L T : Subgroup G) (z v : G) (hz : z ∈ Gv v)
    [IsElementaryAbelian 2 (Uv z v)]
    (S : Sylow 2 (Gv v))
    (hS : (S : Subgroup (Gv v)).map (Gv v).subtype = Tv T v)
    (hfix : Tv T v ≤ centralizer ({z} : Set G))
    {X : Subgroup (Gstar z v)} (hX : MinimalSolvable L T z v X)
    (c : HyperplaneCase (FFFactors.offenderRepresentation (starRepresentation z v))) :
    let I := FFFactors.offenderActor (starRepresentation z v)
    let H := c.second.map I.subtype
    (∃ E ∈ elementaryAbelianMaxSubgroups (H.comap (starMk z v)),
      E.map (starMk z v) ≠ ⊥) →
    starImage z v (elementaryAbelianMaxJ (starPreimage z v H)) = H := by
  intro I H ⟨E, hE, hne⟩
  obtain ⟨⟨e⟩, hF⟩ := minimalSolvable_hyperplane_choice L T z v hz S hS hX c
  let : H.Normal := minimalSolvable_hyperplane_second_normal L T z v hz S hS hfix hX c e hF
  exact star_thompson_eq_of_maximum z v H
    ((c.second.equivMapOfInjective I.subtype I.subtype_injective).symm.trans e) E hE hne

omit [Finite G] in
/-- Two maximum-elementary coordinate witnesses close the full double-S₃ branch
on the actual offender actor. Ambient normality follows from offender normality. -/
theorem twoFactor_thompson_eq_of_maxima (z v : G) [IsElementaryAbelian 2 (Uv z v)]
    (c : SourceTwoFactorCase (FFFactors.offenderRepresentation (starRepresentation z v)))
    (e₁ : c.first ≃* Equiv.Perm (Fin 3)) (e₂ : c.second ≃* Equiv.Perm (Fin 3)) :
    let I := FFFactors.offenderActor (starRepresentation z v)
    let H₁ := c.first.map I.subtype
    let H₂ := c.second.map I.subtype
    (∃ E₁ E₂ : Subgroup (Gv v),
      E₁ ∈ elementaryAbelianMaxSubgroups (I.comap (starMk z v)) ∧
      E₂ ∈ elementaryAbelianMaxSubgroups (I.comap (starMk z v)) ∧
      E₁.map (starMk z v) ⊓ H₁ ≠ ⊥ ∧
      E₂.map (starMk z v) ⊓ H₂ ≠ ⊥) →
    starImage z v (elementaryAbelianMaxJ (starPreimage z v I)) = I := by
  intro I H₁ H₂ ⟨E₁, E₂, hE₁, hE₂, hne₁, hne₂⟩
  have hgen : H₁ ⊔ H₂ = I := by
    change c.first.map I.subtype ⊔ c.second.map I.subtype = I
    rw [← Subgroup.map_sup, c.product.sup_eq_top, ← MonoidHom.range_eq_map, range_subtype]
  exact star_thompson_eq_of_two_intersections z v I H₁ H₂
    ((c.first.equivMapOfInjective I.subtype I.subtype_injective).symm.trans e₁)
    ((c.second.equivMapOfInjective I.subtype I.subtype_injective).symm.trans e₂)
    hgen E₁ E₂ hE₁ hE₂ hne₁ hne₂

/-- The first selected S₃ satisfies the literal Thompson equality. The
earlier action kernel supplies the cubic quotient needed in the mixed branch;
the only remaining support input is the order of the actual moved subgroup. -/
theorem minimalSolvable_twoFactor_first_thompson_of_marked_kernel
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
    let z := A5Module.markedZ s
    let v := A5Module.markedV s
    let I := FFFactors.offenderActor (starRepresentation z v)
    let H := c.first.map I.subtype
    Nat.card (movedSubgroup z v H) = 4 →
      starImage z v (elementaryAbelianMaxJ (starPreimage z v H)) = H := by
  intro z v I H hcard
  exact minimalSolvable_twoFactor_first_thompson_of_maximum
    L T z v (A5Module.markedZ_mem_Gv s) S hS hfix hX c e hF
    (minimalSolvable_twoFactor_first_maximum_of_mixed_marked_kernel
      s T hk S hS hfix hL hX c e hF hcard)

/-- The second selected S₃ satisfies the same equality on its full preimage,
with the original coordinate inclusion and residual selection. -/
theorem minimalSolvable_twoFactor_second_thompson_of_marked_kernel
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
    let z := A5Module.markedZ s
    let v := A5Module.markedV s
    let I := FFFactors.offenderActor (starRepresentation z v)
    let H := c.second.map I.subtype
    Nat.card (movedSubgroup z v H) = 4 →
      starImage z v (elementaryAbelianMaxJ (starPreimage z v H)) = H := by
  intro z v I H hcard
  exact minimalSolvable_twoFactor_second_thompson_of_maximum
    L T z v (A5Module.markedZ_mem_Gv s) S hS hfix hX c e hF
    (minimalSolvable_twoFactor_second_maximum_of_mixed_marked_kernel
      s T hk S hS hfix hL hX c e hF hcard)

/-- On the actual source flag, the first-factor Thompson equality has no
additional action-kernel or maximum-elementary witness premise. -/
theorem minimalSolvable_twoFactor_first_thompson
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
    (hX : MinimalSolvable L (T : Subgroup G)
      (A5Module.markedZ f.module) (A5Module.markedV f.module) X)
    (c : SourceTwoFactorCase (FFFactors.offenderRepresentation
      (starRepresentation (A5Module.markedZ f.module) (A5Module.markedV f.module))))
    (e : c.first ≃* Equiv.Perm (Fin 3))
    (hF : X.subgroupOf (FFFactors.offenderActor
      (starRepresentation (A5Module.markedZ f.module) (A5Module.markedV f.module))) =
      (pResidual 2 c.first).map c.first.subtype) :
    let z := A5Module.markedZ f.module
    let v := A5Module.markedV f.module
    let I := FFFactors.offenderActor (starRepresentation z v)
    let H := c.first.map I.subtype
    Nat.card (movedSubgroup z v H) = 4 →
      starImage z v (elementaryAbelianMaxJ (starPreimage z v H)) = H := by
  exact minimalSolvable_twoFactor_first_thompson_of_marked_kernel
    f.module (T : Subgroup G) f.action_kernel S hS hfix hL hX c e hF

/-- On the identical source flag, the second-factor Thompson equality
discharges the earlier kernel input and the maximum-elementary construction. -/
theorem minimalSolvable_twoFactor_second_thompson
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
    (hX : MinimalSolvable L (T : Subgroup G)
      (A5Module.markedZ f.module) (A5Module.markedV f.module) X)
    (c : SourceTwoFactorCase (FFFactors.offenderRepresentation
      (starRepresentation (A5Module.markedZ f.module) (A5Module.markedV f.module))))
    (e : c.second ≃* Equiv.Perm (Fin 3))
    (hF : X.subgroupOf (FFFactors.offenderActor
      (starRepresentation (A5Module.markedZ f.module) (A5Module.markedV f.module))) =
      (pResidual 2 c.second).map c.second.subtype) :
    let z := A5Module.markedZ f.module
    let v := A5Module.markedV f.module
    let I := FFFactors.offenderActor (starRepresentation z v)
    let H := c.second.map I.subtype
    Nat.card (movedSubgroup z v H) = 4 →
      starImage z v (elementaryAbelianMaxJ (starPreimage z v H)) = H := by
  exact minimalSolvable_twoFactor_second_thompson_of_marked_kernel
    f.module (T : Subgroup G) f.action_kernel S hS hfix hL hX c e hF

/-- The hyperplane branch supplies its own S₃ model and residual selection.
Its native fixed-part estimate proves the maximum witness, leaving just the
actual moved-space order four from the support construction. -/
theorem minimalSolvable_hyperplane_thompson
    {L V : Subgroup G} (s : A5Module.Marking L V) (T : Subgroup G)
    [IsElementaryAbelian 2 (Uv (A5Module.markedZ s) (A5Module.markedV s))]
    (S : Sylow 2 (Gv (A5Module.markedV s)))
    (hS : (S : Subgroup (Gv (A5Module.markedV s))).map (Gv (A5Module.markedV s)).subtype =
      Tv T (A5Module.markedV s))
    (hfix : Tv T (A5Module.markedV s) ≤ centralizer ({A5Module.markedZ s} : Set G))
    {X : Subgroup (Gstar (A5Module.markedZ s) (A5Module.markedV s))}
    (hX : MinimalSolvable L T (A5Module.markedZ s) (A5Module.markedV s) X)
    (c : HyperplaneCase (FFFactors.offenderRepresentation
      (starRepresentation (A5Module.markedZ s) (A5Module.markedV s)))) :
    let z := A5Module.markedZ s
    let v := A5Module.markedV s
    let I := FFFactors.offenderActor (starRepresentation z v)
    let H := c.second.map I.subtype
    Nat.card (movedSubgroup z v H) = 4 →
      starImage z v (elementaryAbelianMaxJ (starPreimage z v H)) = H := by
  intro z v I H hcard
  exact minimalSolvable_hyperplane_thompson_of_maximum
    L T z v (A5Module.markedZ_mem_Gv s) S hS hfix hX c
    (marked_minimalSolvable_hyperplane_maximum_of_support s T S hS hfix hX c hcard)

/-- If both S₃ factors are selected, the full offender actor is its literal
preimage Thompson image. The native coordinate witnesses need no extra support,
splitting, or ambient-normality premise for the individual factors. -/
theorem minimalSolvable_twoFactor_thompson
    (L T : Subgroup G) (z v : G) (hz : z ∈ Gv v)
    [IsElementaryAbelian 2 (Uv z v)]
    (S : Sylow 2 (Gv v))
    (hS : (S : Subgroup (Gv v)).map (Gv v).subtype = Tv T v)
    {X : Subgroup (Gstar z v)} (hX : MinimalSolvable L T z v X)
    (c : SourceTwoFactorCase (FFFactors.offenderRepresentation (starRepresentation z v)))
    (e₁ : c.first ≃* Equiv.Perm (Fin 3)) (e₂ : c.second ≃* Equiv.Perm (Fin 3))
    (hF : X.subgroupOf (FFFactors.offenderActor (starRepresentation z v)) =
      pResidual 2 (FFFactors.offenderActor (starRepresentation z v))) :
    let I := FFFactors.offenderActor (starRepresentation z v)
    starImage z v (elementaryAbelianMaxJ (starPreimage z v I)) = I := by
  exact NormalThompson.Maximum.Double.minimalSolvable_twoFactor_thompson
    L T z v hz S hS hX c e₁ e₂ hF

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.Solvable.Construction.Products
end
