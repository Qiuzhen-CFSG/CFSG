module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.FFSelection.Solvable.Construction.Products.NormalThompson.Maximum.Singleton.CentralizerGeometry
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.FFSelection.Solvable.Construction.Products.NormalThompson.Maximum.Double.ProjectionCodimension

/-!
# Singleton maximum transfer with an S₃ complement

The additive coordinate bound forces each global maximum's star image to
split across the two native S₃ factors. A maximum moving the selected
residual must therefore meet the selected coordinate nontrivially. The
fixed-part centralizer and the index-two replacement then give a moving
maximum in the FULL preimage of that single factor.

The residual is that of the selected factor, not the full product residual.
Only the selected support's order-four premise remains; its producer is the
product-support construction. Both coordinate witnesses use the literal star
map and can be passed to the parent's Thompson closing lemmas. The mixed
factor and hyperplane branches are not claimed here.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, B.2.4,
printed pp.75–76, B.5.6(3), p.105, and 13.6.13, p.929.
The private cardinal splitting calculation follows the checked double-factor
reduction, whose full-residual selection theorem does not apply to a singleton.
-/

@[expose] public section
open Subgroup Stellmacher Representation Representation.BinaryOffender
open scoped IsMulCommutative
open CFSG.Quasithin.ChapterB.SourceInduction
open CFSG.Quasithin.Chapter13.Section08.Components.Swapped.LinearTwo.ModuleAlternatives
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.Solvable.Construction.Products.NormalThompson.Maximum.Singleton.DoubleFactor

private theorem elementary_card_pow_rank {D : Type*} [Group D] [Finite D]
    (A : Subgroup D) (hA : IsElementaryAbelian 2 A) : Nat.card A = 2 ^ rank A := by
  let : IsElementaryAbelian 2 A := hA
  obtain ⟨n, hn⟩ := (IsElementaryAbelian.isPGroup 2 A).exists_card_eq
  rw [rank, hn, Nat.log_pow Nat.one_lt_two]

private theorem offender_splits_of_projection_bound
    {D V : Type*} [Group D] [Finite D] [AddCommGroup V] [Module (ZMod 2) V]
    (ρ : Representation (ZMod 2) D V) {F K : Subgroup D} (h : InternalProduct F K)
    (A : Subgroup D) (hA : IsOffender ρ A)
    (hbound : rank (A.map h.fst) + rank (A.map h.snd) ≤ fixedCodim ρ A) :
    A = (A ⊓ F) ⊔ (A ⊓ K) := by
  let : IsElementaryAbelian 2 A := hA.1.2
  let R := ((A.map h.fst).prod (A.map h.snd)).map h.equiv.toMonoidHom
  have hAR : A ≤ R := by
    intro a ha
    exact ⟨h.equiv.symm a, ⟨mem_map_of_mem h.fst ha, mem_map_of_mem h.snd ha⟩,
      h.equiv.apply_symm_apply a⟩
  have heq : A = R := by
    apply eq_of_le_of_card_ge hAR
    change Nat.card (((A.map h.fst).prod (A.map h.snd)).map h.equiv.toMonoidHom) ≤ _
    rw [card_map_of_injective h.equiv.injective,
      Nat.card_congr (Subgroup.prodEquiv (A.map h.fst) (A.map h.snd)).toEquiv, Nat.card_prod,
      elementary_card_pow_rank _ (hA.1.2.map h.fst),
      elementary_card_pow_rank _ (hA.1.2.map h.snd),
      elementary_card_pow_rank _ hA.1.2, ← pow_add]
    exact Nat.pow_le_pow_right Nat.zero_lt_two (hbound.trans hA.2)
  apply le_antisymm _ (sup_le inf_le_left inf_le_left)
  intro a ha
  obtain ⟨⟨x,y⟩, ⟨hx,hy⟩, hxy⟩ := heq ▸ ha
  have hxA : (x : D) ∈ A := by
    rw [heq]
    exact ⟨(x, 1), ⟨hx, one_mem _⟩, by
      change h.equiv (x, 1) = (x : D)
      simp only [h.apply_eq, OneMemClass.coe_one, mul_one]⟩
  have hyA : (y : D) ∈ A := by
    rw [heq]
    exact ⟨(1, y), ⟨one_mem _, hy⟩, by
      change h.equiv (1, y) = (y : D)
      simp only [h.apply_eq, OneMemClass.coe_one, one_mul]⟩
  change h.equiv (x,y) = a at hxy
  rw [← hxy, h.apply_eq]
  exact ((A ⊓ F) ⊔ (A ⊓ K)).mul_mem
    ((le_sup_left : A ⊓ F ≤ (A ⊓ F) ⊔ (A ⊓ K)) ⟨hxA, x.property⟩)
    ((le_sup_right : A ⊓ K ≤ (A ⊓ F) ⊔ (A ⊓ K)) ⟨hyA, y.property⟩)


private theorem factors_centralize {D Y : Type*} [Group D] [Group Y]
    {F K : Subgroup D} (h : InternalProduct F K) (f : D →* Y) :
    F.map f ≤ centralizer (K.map f : Set Y) := by
  rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
  rw [← map_mul, ← map_mul]
  apply congrArg f
  have hc := congrArg h.equiv
    (show (1, (⟨b, hb⟩ : K)) * ((⟨a, ha⟩ : F), 1) =
      ((⟨a, ha⟩ : F), 1) * (1, (⟨b, hb⟩ : K)) by simp)
  rw [map_mul, map_mul] at hc
  simpa only [h.apply_eq, OneMemClass.coe_one, one_mul, mul_one] using hc

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.Solvable.Construction.Products.NormalThompson.Maximum.Singleton.DoubleFactor

namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.Solvable.Construction.Products
variable {G : Type*} [Group G] [Finite G]

/-- Every actual global maximum splits across the two native S₃ coordinates.
No full-product residual selection is needed for this assertion. -/
theorem minimalSolvable_twoFactor_maximum_image_split
    (L T : Subgroup G) (z v : G) (hz : z ∈ Gv v)
    [IsElementaryAbelian 2 (Uv z v)]
    (S : Sylow 2 (Gv v))
    (hS : (S : Subgroup (Gv v)).map (Gv v).subtype = Tv T v)
    {X : Subgroup (Gstar z v)} (hX : MinimalSolvable L T z v X)
    (c : SourceTwoFactorCase (FFFactors.offenderRepresentation (starRepresentation z v)))
    (e₁ : c.first ≃* Equiv.Perm (Fin 3)) (e₂ : c.second ≃* Equiv.Perm (Fin 3))
    (E : Subgroup (Gv v))
    (hE : E ∈ elementaryAbelianMaxSubgroups (⊤ : Subgroup (Gv v))) :
    let I := FFFactors.offenderActor (starRepresentation z v)
    E.map (starMk z v) = (E.map (starMk z v) ⊓ c.first.map I.subtype) ⊔
      (E.map (starMk z v) ⊓ c.second.map I.subtype) := by
  intro I
  by_cases he : E.map (starMk z v) = ⊥
  · simp only [he, bot_inf_eq, bot_sup_eq]
  have hmap : (elementaryAbelianMaxJ (⊤ : Subgroup (Gv v))).map (starMk z v) =
      JGstar z v := starImage_intrinsic_thompson z v ⊤ (Gv v)
        (by rw [← MonoidHom.range_eq_map, range_subtype])
  have hEI : E.map (starMk z v) ≤ I := by
    apply (map_mono (le_sSup hE)).trans
    change (elementaryAbelianMaxJ (⊤ : Subgroup (Gv v))).map (starMk z v) ≤ I
    rw [hmap]
    exact (minimalSolvable_global_thompson L T z v hz S hS hX).1
  have hEP : E ∈ elementaryAbelianMaxSubgroups (I.comap (starMk z v)) :=
    ⟨map_le_iff_le_comap.mp hEI, hE.2.1, fun A _ hA => hE.2.2 A le_top hA⟩
  have hoff := (NormalThompson.Maximum.Double.maxElementary_star_isOffender
    z v hz I E hEP he).subgroupOf (starRepresentation z v) hEI
  have hs := NormalThompson.Maximum.Singleton.DoubleFactor.offender_splits_of_projection_bound
    _ c.product _ hoff
    (NormalThompson.Maximum.Double.star_twoFactor_projection_rank_le_fixedCodim
      z v c e₁ e₂ _ hoff.1.2)
  have hh := congrArg (Subgroup.map I.subtype) hs
  simpa only [Subgroup.map_sup, Subgroup.map_inf _ _ _ I.subtype_injective,
    map_subgroupOf_eq_of_le hEI] using hh

private theorem selected_le (L T : Subgroup G) (z v : G) (hz : z ∈ Gv v)
    [IsElementaryAbelian 2 (Uv z v)]
    (S : Sylow 2 (Gv v))
    (hS : (S : Subgroup (Gv v)).map (Gv v).subtype = Tv T v)
    {X : Subgroup (Gstar z v)} (hX : MinimalSolvable L T z v X) :
    let I := FFFactors.offenderActor (starRepresentation z v)
    ∀ F : Subgroup I, X.subgroupOf I = (pResidual 2 F).map F.subtype →
      X ≤ F.map I.subtype := by
  intro I F hF
  rw [← minimalSolvable_selected_residual L T z v hz S hS hX F hF]
  exact map_subtype_le _

/-- A global maximum meeting the selected first coordinate, using
its own residual selection and the actual double-S₃ action. -/
theorem minimalSolvable_twoFactor_first_global_maximum_intersection
    (L T : Subgroup G) (z v : G) (hz : z ∈ Gv v)
    [IsElementaryAbelian 2 (Uv z v)]
    (S : Sylow 2 (Gv v))
    (hS : (S : Subgroup (Gv v)).map (Gv v).subtype = Tv T v)
    {X : Subgroup (Gstar z v)} (hX : MinimalSolvable L T z v X)
    (c : SourceTwoFactorCase (FFFactors.offenderRepresentation (starRepresentation z v)))
    (e₁ : c.first ≃* Equiv.Perm (Fin 3)) (e₂ : c.second ≃* Equiv.Perm (Fin 3))
    (hF : X.subgroupOf (FFFactors.offenderActor (starRepresentation z v)) =
      @Subgroup.map c.first _ (FFFactors.offenderActor (starRepresentation z v)) _
        c.first.subtype (pResidual 2 c.first)) :
    let I := FFFactors.offenderActor (starRepresentation z v)
    ∃ E ∈ elementaryAbelianMaxSubgroups (⊤ : Subgroup (Gv v)),
      E.map (starMk z v) ⊓ c.first.map I.subtype ≠ ⊥ := by
  intro I
  obtain ⟨E, hE, hmove⟩ := minimalSolvable_exists_global_maximum_moving L T z v hz S hS hX
  refine ⟨E, hE, ?_⟩
  intro hzero
  have hs := minimalSolvable_twoFactor_maximum_image_split L T z v hz S hS hX c e₁ e₂ E hE
  have hEK : E.map (starMk z v) ≤ c.second.map I.subtype := by
    rw [hs, hzero, bot_sup_eq]
    exact inf_le_right
  have hXH := selected_le L T z v hz S hS hX c.first hF
  have hc := NormalThompson.Maximum.Singleton.DoubleFactor.factors_centralize c.product I.subtype
  apply hmove
  exact commutator_eq_bot_iff_le_centralizer.mpr
    (hXH.trans (hc.trans (centralizer_le hEK)))

/-- The selected first full preimage has a moving maximum. The only
support premise is its order four; both quotient factors are marked S₃. -/
theorem minimalSolvable_twoFactor_first_maximum_of_s3_complement
    (L T : Subgroup G) (z v : G) (hz : z ∈ Gv v)
    [IsElementaryAbelian 2 (Uv z v)]
    (S : Sylow 2 (Gv v))
    (hS : (S : Subgroup (Gv v)).map (Gv v).subtype = Tv T v)
    {X : Subgroup (Gstar z v)} (hX : MinimalSolvable L T z v X)
    (c : SourceTwoFactorCase (FFFactors.offenderRepresentation (starRepresentation z v)))
    (e₁ : c.first ≃* Equiv.Perm (Fin 3)) (e₂ : c.second ≃* Equiv.Perm (Fin 3))
    (hF : X.subgroupOf (FFFactors.offenderActor (starRepresentation z v)) =
      @Subgroup.map c.first _ (FFFactors.offenderActor (starRepresentation z v)) _
        c.first.subtype (pResidual 2 c.first))
    (hfix : Tv T v ≤ centralizer ({z} : Set G)) :
    let I := FFFactors.offenderActor (starRepresentation z v)
    let H := c.first.map I.subtype
    Nat.card (movedSubgroup z v H) = 4 →
    ∃ E ∈ elementaryAbelianMaxSubgroups (H.comap (starMk z v)),
      E.map (starMk z v) ≠ ⊥ := by
  intro I H hcard
  obtain ⟨E, hE, hne⟩ := minimalSolvable_twoFactor_first_global_maximum_intersection
    L T z v hz S hS hX c e₁ e₂ hF
  exact minimalSolvable_twoFactor_first_maximum_of_support
    L T z v hz S hS hfix hX c e₁ e₂ hF hcard E hE hne

/-- A global maximum meeting the selected second coordinate, using
its own residual selection and the actual double-S₃ action. -/
theorem minimalSolvable_twoFactor_second_global_maximum_intersection
    (L T : Subgroup G) (z v : G) (hz : z ∈ Gv v)
    [IsElementaryAbelian 2 (Uv z v)]
    (S : Sylow 2 (Gv v))
    (hS : (S : Subgroup (Gv v)).map (Gv v).subtype = Tv T v)
    {X : Subgroup (Gstar z v)} (hX : MinimalSolvable L T z v X)
    (c : SourceTwoFactorCase (FFFactors.offenderRepresentation (starRepresentation z v)))
    (e₁ : c.first ≃* Equiv.Perm (Fin 3)) (e₂ : c.second ≃* Equiv.Perm (Fin 3))
    (hF : X.subgroupOf (FFFactors.offenderActor (starRepresentation z v)) =
      @Subgroup.map c.second _ (FFFactors.offenderActor (starRepresentation z v)) _
        c.second.subtype (pResidual 2 c.second)) :
    let I := FFFactors.offenderActor (starRepresentation z v)
    ∃ E ∈ elementaryAbelianMaxSubgroups (⊤ : Subgroup (Gv v)),
      E.map (starMk z v) ⊓ c.second.map I.subtype ≠ ⊥ := by
  intro I
  obtain ⟨E, hE, hmove⟩ := minimalSolvable_exists_global_maximum_moving L T z v hz S hS hX
  refine ⟨E, hE, ?_⟩
  intro hzero
  have hs := minimalSolvable_twoFactor_maximum_image_split L T z v hz S hS hX c e₁ e₂ E hE
  have hEK : E.map (starMk z v) ≤ c.first.map I.subtype := by
    rw [hs, hzero, sup_bot_eq]
    exact inf_le_right
  have hXH := selected_le L T z v hz S hS hX c.second hF
  have hc := NormalThompson.Maximum.Singleton.DoubleFactor.factors_centralize c.product I.subtype
  apply hmove
  exact commutator_eq_bot_iff_le_centralizer.mpr
    (hXH.trans ((le_centralizer_iff.mp hc).trans (centralizer_le hEK)))

/-- The selected second full preimage has a moving maximum. The only
support premise is its order four; both quotient factors are marked S₃. -/
theorem minimalSolvable_twoFactor_second_maximum_of_s3_complement
    (L T : Subgroup G) (z v : G) (hz : z ∈ Gv v)
    [IsElementaryAbelian 2 (Uv z v)]
    (S : Sylow 2 (Gv v))
    (hS : (S : Subgroup (Gv v)).map (Gv v).subtype = Tv T v)
    {X : Subgroup (Gstar z v)} (hX : MinimalSolvable L T z v X)
    (c : SourceTwoFactorCase (FFFactors.offenderRepresentation (starRepresentation z v)))
    (e₁ : c.first ≃* Equiv.Perm (Fin 3)) (e₂ : c.second ≃* Equiv.Perm (Fin 3))
    (hF : X.subgroupOf (FFFactors.offenderActor (starRepresentation z v)) =
      @Subgroup.map c.second _ (FFFactors.offenderActor (starRepresentation z v)) _
        c.second.subtype (pResidual 2 c.second))
    (hfix : Tv T v ≤ centralizer ({z} : Set G)) :
    let I := FFFactors.offenderActor (starRepresentation z v)
    let H := c.second.map I.subtype
    Nat.card (movedSubgroup z v H) = 4 →
    ∃ E ∈ elementaryAbelianMaxSubgroups (H.comap (starMk z v)),
      E.map (starMk z v) ≠ ⊥ := by
  intro I H hcard
  obtain ⟨E, hE, hne⟩ := minimalSolvable_twoFactor_second_global_maximum_intersection
    L T z v hz S hS hX c e₁ e₂ hF
  exact minimalSolvable_twoFactor_second_maximum_of_support
    L T z v hz S hS hfix hX c e₁ e₂ hF hcard E hE hne

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.Solvable.Construction.Products
end
