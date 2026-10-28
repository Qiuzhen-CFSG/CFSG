module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.FFSelection.Solvable.Construction.Products.NormalThompson.Maximum.Singleton.TwoFactorIndex
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.FFSelection.Solvable.Construction.Transport
public import Theory.Representation.BinaryPlaneNormalizer

/-!
# The centralizer of the selected S₃ fixed part

For the faithful star action, a normal subgroup marked as S₃ with a
four-element moved subgroup splits U_v into its moved plane and its fixed
space. The cubic averaging argument in `BinaryPlaneNormalizer` proves the
splitting and faithfulness on the plane. Its invertible binary operators
have order six, so the selected S₃ supplies every operator on the plane.
An ambient element fixing the complementary fixed space therefore agrees
with an element of S₃ on all of U_v. Faithfulness identifies their star images.

The result retains the original star quotient and the internal subgroup
`singletonFixed`. The first and second native product applications transport
their actual coordinate markings and discharge the centralizer premise of
the maximum-elementary replacement theorem. Their global maximum and
nontrivial coordinate-intersection premises remain explicit.

Only the order-four support conclusion is needed here: faithfulness already
supplies faithfulness on the moved space, so the separate self-commutator
conclusion is unnecessary. The exact two-support-premise interface is also
provided for the construction owner. These support conclusions are owned by
the product-support construction; maximum selection and the final singleton
assembly remain with the parent construction.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
B.5.6, printed p.105, and the normal S₃ product in 13.6.13, printed p.929.
-/

@[expose] public section
open Subgroup Representation Representation.BinaryOffender
open scoped IsMulCommutative

namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.Solvable.Construction.Products.NormalThompson.Maximum.Singleton.CentralizerGeometry

variable {D V : Type*} [Group D] [Finite D] [AddCommGroup V] [Module (ZMod 2) V]

private theorem fixed_stabilizer (ρ : Representation (ZMod 2) D V)
    (hf : Function.Injective ρ) (H : Subgroup D) [H.Normal]
    (e : H ≃* Equiv.Perm (Fin 3))
    (hd : Module.finrank (ZMod 2) (Coinvariants.ker (ρ.comp H.subtype)) = 2)
    (g : D) (hg : ∀ w ∈ (Representation.invariants (ρ.comp H.subtype)), ρ g w = w) : g ∈ H := by
  let W := Coinvariants.ker (ρ.comp H.subtype)
  let σ := Representation.toCoinvariantsKer ρ H
  have hsplit := BinaryPlaneNormalizer.symmetric_three_split
    (ρ.comp H.subtype) (hf.comp H.subtype_injective) e hd
  have hext (a b : D) (hw : σ a = σ b)
      (hc : ∀ c ∈ Representation.invariants (ρ.comp H.subtype), ρ a c = ρ b c) : a = b := by
    apply hf
    ext v
    obtain ⟨w, hwW, c, hcC, rfl⟩ := Submodule.mem_sup.mp
      (show v ∈ W ⊔ Representation.invariants (ρ.comp H.subtype) from
        hsplit.sup_eq_top ▸ Submodule.mem_top)
    have hwa : ρ a w = ρ b w :=
      congrArg Subtype.val (LinearMap.congr_fun hw (⟨w, hwW⟩ : W))
    rw [map_add, map_add, hwa, hc c hcC]
  let := Module.finite_of_finrank_pos (R := ZMod 2) (M := W) (by
    change 0 < Module.finrank (ZMod 2) (Coinvariants.ker (ρ.comp H.subtype))
    rw [hd]
    decide)
  let b := Module.finBasisOfFinrankEq (ZMod 2) W hd
  let f : H →* Matrix.GeneralLinearGroup (Fin 2) (ZMod 2) :=
    (Matrix.GeneralLinearGroup.toLin' b).symm.toMonoidHom.comp
      (Representation.asGroupHom (σ.comp H.subtype))
  have hinj : Function.Injective f := by
    intro x y h
    apply H.subtype_injective
    have h' := (Matrix.GeneralLinearGroup.toLin' b).symm.injective h
    exact hext x y (congrArg Units.val h') (fun c hc => (hc x).trans (hc y).symm)
  have hc : Nat.card H = Nat.card (Matrix.GeneralLinearGroup (Fin 2) (ZMod 2)) := by
    rw [Nat.card_congr e.toEquiv, Matrix.card_GL_field]
    norm_num [Nat.card_eq_fintype_card, Fintype.card_perm, Fin.prod_univ_succ]
  have hsurj := ((Nat.bijective_iff_injective_and_card f).mpr ⟨hinj, hc⟩).surjective
  obtain ⟨h, hh⟩ := hsurj ((Matrix.GeneralLinearGroup.toLin' b).symm (σ.asGroupHom g))
  have heq : σ h = σ g := congrArg Units.val
    ((Matrix.GeneralLinearGroup.toLin' b).symm.injective hh)
  have he := hext g h heq.symm (fun c hc => (hg c hc).trans (hc h).symm)
  exact he ▸ h.property

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.Solvable.Construction.Products.NormalThompson.Maximum.Singleton.CentralizerGeometry

namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.Solvable.Construction.Products
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
private theorem moved_coinvariants (z v : G) [IsElementaryAbelian 2 (Uv z v)]
    (H : Subgroup (Gstar z v)) :
    subspaceCommutator (starRepresentation z v) ⊤ H =
      Coinvariants.ker ((starRepresentation z v).comp H.subtype) := by
  unfold subspaceCommutator Coinvariants.ker
  congr 1
  ext w
  constructor
  · rintro ⟨g, hg, u, _, rfl⟩
    exact ⟨(⟨g, hg⟩, u), rfl⟩
  · rintro ⟨⟨g, u⟩, rfl⟩
    exact ⟨g, g.property, u, Submodule.mem_top, rfl⟩

private theorem moved_finrank (z v : G) [IsElementaryAbelian 2 (Uv z v)]
    (H : Subgroup (Gstar z v)) (hcard : Nat.card (movedSubgroup z v H) = 4) :
    Module.finrank (ZMod 2) (Coinvariants.ker ((starRepresentation z v).comp H.subtype)) = 2 := by
  have hc : Nat.card (Coinvariants.ker ((starRepresentation z v).comp H.subtype)) = 4 := by
    rw [← moved_coinvariants, ← ambientSpace_card, moved_ambientSpace, hcard]
  rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod] at hc
  exact Nat.pow_right_injective (by decide : 1 < 2) hc

/-- The full centralizer of the selected S₃ fixed part is its original star
preimage. No Thompson or maximum-elementary hypothesis is used. -/
theorem singletonFixed_centralizer_eq (z v : G) (hz : z ∈ Gv v)
    [IsElementaryAbelian 2 (Uv z v)]
    (H : Subgroup (Gstar z v)) [H.Normal] (e : H ≃* Equiv.Perm (Fin 3))
    (hcard : Nat.card (movedSubgroup z v H) = 4) :
    centralizer (singletonFixed z v H : Set (Gv v)) = H.comap (starMk z v) := by
  apply le_antisymm
  · intro g hg
    apply NormalThompson.Maximum.Singleton.CentralizerGeometry.fixed_stabilizer (starRepresentation z v)
      (starRepresentation_injective z v) H e (moved_finrank z v H hcard) (starMk z v g)
    intro w hw
    let u : Gv v := ⟨w.toMul, Uv_le_Gv z v hz w.toMul.property⟩
    have hu : u ∈ singletonFixed z v H := by
      refine ⟨w.toMul.property, ?_⟩
      intro a ha
      have hh := hw ⟨starMk z v a, ha⟩
      have he := congrArg (fun t : Additive (Uv z v) => (t.toMul : G)) hh
      change ((starRepresentation z v (starMk z v a) w).toMul : G) = (w.toMul : G) at he
      rw [starRepresentation_mk_apply] at he
      exact Subtype.ext (mul_inv_eq_iff_eq_mul.mp he)
    apply Additive.toMul.injective
    apply Subtype.ext
    rw [starRepresentation_mk_apply]
    exact mul_inv_eq_iff_eq_mul.mpr (congrArg Subtype.val (hg u hu).symm)
  · exact le_centralizer_iff.mpr (show singletonFixed z v H ≤
      centralizer (H.comap (starMk z v) : Set (Gv v)) from inf_le_right)

/-- The original vector carrier splits into the selected moved plane and
the vectors fixed by its S₃ actor. -/
theorem singleton_moved_fixed_isCompl (z v : G) [IsElementaryAbelian 2 (Uv z v)]
    (H : Subgroup (Gstar z v)) (e : H ≃* Equiv.Perm (Fin 3))
    (hcard : Nat.card (movedSubgroup z v H) = 4) :
    IsCompl (subspaceCommutator (starRepresentation z v) ⊤ H)
      (Representation.invariants ((starRepresentation z v).comp H.subtype)) := by
  rw [moved_coinvariants]
  exact BinaryPlaneNormalizer.symmetric_three_split
    ((starRepresentation z v).comp H.subtype)
    ((starRepresentation_injective z v).comp H.subtype_injective) e
    (moved_finrank z v H hcard)

/-- The two support conclusions requested by the singleton construction
discharge its fixed-part centralizer premise. -/
theorem singletonFixed_centralizer_le (z v : G) (hz : z ∈ Gv v)
    [IsElementaryAbelian 2 (Uv z v)]
    (H : Subgroup (Gstar z v)) [H.Normal] (e : H ≃* Equiv.Perm (Fin 3))
    (_hself : factorSupport z v H H = movedSubgroup z v H)
    (hcard : Nat.card (movedSubgroup z v H) = 4) :
    centralizer (singletonFixed z v H : Set (Gv v)) ≤ H.comap (starMk z v) :=
  (singletonFixed_centralizer_eq z v hz H e hcard).le

open CFSG.Quasithin.ChapterB.SourceInduction
open CFSG.Quasithin.Chapter13.Section08.Components.Swapped.LinearTwo.ModuleAlternatives

/-- The first native coordinate supplies ambient normality and its actual
S₃ marking. Its support order identifies the fixed centralizer. -/
theorem minimalSolvable_twoFactor_first_fixed_centralizer
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
    Nat.card (movedSubgroup z v H) = 4 →
      centralizer (singletonFixed z v H : Set (Gv v)) = H.comap (starMk z v) := by
  intro I H hcard
  let : H.Normal := minimalSolvable_twoFactor_first_normal L T z v hz S hS hfix hX c e hF
  exact singletonFixed_centralizer_eq z v hz H
    ((c.first.equivMapOfInjective I.subtype I.subtype_injective).symm.trans e) hcard

/-- The same centralizer identification for the actual second coordinate. -/
theorem minimalSolvable_twoFactor_second_fixed_centralizer
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
    Nat.card (movedSubgroup z v H) = 4 →
      centralizer (singletonFixed z v H : Set (Gv v)) = H.comap (starMk z v) := by
  intro I H hcard
  let : H.Normal := minimalSolvable_twoFactor_second_normal L T z v hz S hS hfix hX c e hF
  exact singletonFixed_centralizer_eq z v hz H
    ((c.second.equivMapOfInjective I.subtype I.subtype_injective).symm.trans e) hcard

/-- Discharge the centralizer premise of the first-coordinate maximum
replacement. The actual global maximum and nontrivial intersection remain
the selection owner's premises. -/
theorem minimalSolvable_twoFactor_first_maximum_of_support
    (L T : Subgroup G) (z v : G) (hz : z ∈ Gv v)
    [IsElementaryAbelian 2 (Uv z v)]
    (S : Sylow 2 (Gv v))
    (hS : (S : Subgroup (Gv v)).map (Gv v).subtype = Tv T v)
    (hfix : Tv T v ≤ centralizer ({z} : Set G))
    {X : Subgroup (Gstar z v)} (hX : MinimalSolvable L T z v X)
    (c : SourceTwoFactorCase (FFFactors.offenderRepresentation (starRepresentation z v)))
    (e₁ : c.first ≃* Equiv.Perm (Fin 3)) (e₂ : c.second ≃* Equiv.Perm (Fin 3))
    (hF : X.subgroupOf (FFFactors.offenderActor (starRepresentation z v)) =
      @Subgroup.map c.first _ (FFFactors.offenderActor (starRepresentation z v)) _
        c.first.subtype (pResidual 2 c.first)) :
    let I := FFFactors.offenderActor (starRepresentation z v)
    let H := c.first.map I.subtype
    Nat.card (movedSubgroup z v H) = 4 →
    ∀ E ∈ Stellmacher.elementaryAbelianMaxSubgroups (⊤ : Subgroup (Gv v)),
      E.map (starMk z v) ⊓ H ≠ ⊥ →
      ∃ B ∈ Stellmacher.elementaryAbelianMaxSubgroups (H.comap (starMk z v)),
        B.map (starMk z v) ≠ ⊥ := by
  intro I H hcard
  exact minimalSolvable_twoFactor_first_maximum_of_centralizer
    L T z v hz S hS hfix hX c e₁ e₂ hF
    (minimalSolvable_twoFactor_first_fixed_centralizer
      L T z v hz S hS hfix hX c e₁ hF hcard).le

/-- Discharge the corresponding second-coordinate centralizer premise,
retaining the same genuine maximum and intersection inputs. -/
theorem minimalSolvable_twoFactor_second_maximum_of_support
    (L T : Subgroup G) (z v : G) (hz : z ∈ Gv v)
    [IsElementaryAbelian 2 (Uv z v)]
    (S : Sylow 2 (Gv v))
    (hS : (S : Subgroup (Gv v)).map (Gv v).subtype = Tv T v)
    (hfix : Tv T v ≤ centralizer ({z} : Set G))
    {X : Subgroup (Gstar z v)} (hX : MinimalSolvable L T z v X)
    (c : SourceTwoFactorCase (FFFactors.offenderRepresentation (starRepresentation z v)))
    (e₁ : c.first ≃* Equiv.Perm (Fin 3)) (e₂ : c.second ≃* Equiv.Perm (Fin 3))
    (hF : X.subgroupOf (FFFactors.offenderActor (starRepresentation z v)) =
      @Subgroup.map c.second _ (FFFactors.offenderActor (starRepresentation z v)) _
        c.second.subtype (pResidual 2 c.second)) :
    let I := FFFactors.offenderActor (starRepresentation z v)
    let H := c.second.map I.subtype
    Nat.card (movedSubgroup z v H) = 4 →
    ∀ E ∈ Stellmacher.elementaryAbelianMaxSubgroups (⊤ : Subgroup (Gv v)),
      E.map (starMk z v) ⊓ H ≠ ⊥ →
      ∃ B ∈ Stellmacher.elementaryAbelianMaxSubgroups (H.comap (starMk z v)),
        B.map (starMk z v) ≠ ⊥ := by
  intro I H hcard
  exact minimalSolvable_twoFactor_second_maximum_of_centralizer
    L T z v hz S hS hfix hX c e₁ e₂ hF
    (minimalSolvable_twoFactor_second_fixed_centralizer
      L T z v hz S hS hfix hX c e₂ hF hcard).le

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.Solvable.Construction.Products
end
