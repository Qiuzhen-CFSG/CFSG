module

public import CFSG.Quasithin.Chapter2.Section01To03.ComponentRefinement.SurvivingIntersections.MathieuCovers.Source
public import CFSG.Quasithin.Chapter2.Section01To03.LocalStructure.Native115
public import CFSG.Quasithin.Chapter2.Section01To03.ComponentRefinement.SurvivingIntersections.MathieuCovers.M22Reduction
public import Theory.Mathieu.M22.Properties.ElementarySylowFixers
public import Theory.GroupTheory.PerfectCentralCoverAutomorphisms
public import Theory.GroupTheory.PGroup.OmegaCenterIn
public import Theory.GroupTheory.PGroup.AbelianOmega

/-!
# Cyclicity of the ambient Sylow center over an M₂₂ component

The original source hypotheses apply to every involution in Z(T), not just
the selected one. Therefore Ω₁(Z(T)) acts faithfully on L: a nonidentity
kernel element would put L inside its involution centralizer and hence M.
This action fixes the literal component Sylow pointwise. Faithful descent
through the original perfect central cover embeds it in an elementary group
of pointwise Sylow fixers of M₂₂, of order at most two. Thus Z(T) is cyclic.

This uses the full Γ₀ and unique ambient two-local source context. It does
not assert that the covering kernel is invariant under T.
Source: Aschbacher–Smith 2.3.9(3–7), printed pp.525–526.
-/

public section
namespace CFSG.Quasithin.Chapter2.ComponentRefinement
open Subgroup Theory.GroupTheory Sporadic.Mathieu
variable {G : Type*} [Group G] [Finite G] {C : GroupClass}
variable {H L M : Subgroup G} {S : Sylow 2 H} {z : G}

/-- Every central involution of the same ambient Sylow supplies the original
source setup, so its centralizer restriction is available without a new premise. -/
theorem MathieuSourceSetup.central_omega_faithful_action
    (c : MathieuSourceSetup H L M S z) (hG : IsSimpleQTKE C G)
    (sourceC : LocalC129Input C G) :
    ∃ f : omegaCenterIn (c.T : Subgroup G) →* MulAut L,
      Function.Injective f ∧
      (∀ a x, (f a x : G) = (a : G) * (x : G) * (a : G)⁻¹) ∧
      ∃ R : Sylow 2 L,
        (R : Subgroup L) = ((S : Subgroup H).map H.subtype).subgroupOf L ∧
        ∀ a x, x ∈ R → f a x = x := by
  let E := omegaCenterIn (c.T : Subgroup G)
  have hEZ : E ≤ (center (c.T : Subgroup G)).map (c.T : Subgroup G).subtype :=
    map_mono (map_subtype_le _)
  have hlocal (a : G) (ha : a ∈ E) (hne : a ≠ 1) : LocalSetup H L M S a := by
    have ho : orderOf a = 2 := orderOf_eq_prime
      (elemPow_eq_one_of_isElementaryAbelian a ha) hne
    let ca : MathieuSourceSetup H L M S a :=
      { c with mem_center := hEZ ha, involution := ho }
    exact ca.localSetup hG structural115Input sourceC
  have hEN : E ≤ normalizer (L : Set G) := by
    intro a ha
    by_cases h1 : a = 1
    · simpa only [h1] using (normalizer (L : Set G)).one_mem
    exact (hlocal a ha h1).normalizes
  let f : E →* MulAut L := L.normalizerMonoidHom.comp (inclusion hEN)
  have hfval (a : E) (x : L) :
      (f a x : G) = (a : G) * (x : G) * (a : G)⁻¹ := rfl
  have hfi : Function.Injective f := by
    apply (injective_iff_map_eq_one f).mpr
    intro a ha
    by_contra hne
    have ha1 : (a : G) ≠ 1 := fun he => hne (Subtype.ext he)
    have hl := hlocal a a.property ha1
    apply hl.outside
    intro x hx
    apply hl.centralizer_le
    apply mem_centralizer_singleton_iff.mpr
    have hh := congrArg Subtype.val (DFunLike.congr_fun ha (⟨x,hx⟩ : L))
    change (a : G) * x * (a : G)⁻¹ = x at hh
    exact (mul_inv_eq_iff_eq_mul.mp hh).symm
  obtain ⟨R,hR⟩ := (c.localSetup hG structural115Input sourceC).component_sylow
  refine ⟨f,hfi,hfval,R,hR,?_⟩
  intro a x hx
  apply Subtype.ext
  rw [hfval]
  have hxT : (x : G) ∈ (c.T : Subgroup G) := by
    apply c.sylow_lt.le
    change x ∈ ((S : Subgroup H).map H.subtype).subgroupOf L
    rwa [← hR]
  have haC := (mem_omegaCenterIn_iff (c.T : Subgroup G) a).mp a.property
  rw [← haC.2.1 x hxT,mul_inv_cancel_right]

/-- The original M₂₂ quotient forces first Omega of the selected ambient
Sylow center to have at most two elements, including for nontrivial covers. -/
theorem MathieuSourceSetup.mathieuTwentyTwo_ambient_center_omega_card_le_two
    (c : MathieuSourceSetup H L M S z) (hG : IsSimpleQTKE C G)
    (sourceC : LocalC129Input C G)
    (e : (L ⧸ pCore 2 L) ≃* M22) :
    Nat.card (omega₁ (center (c.T : Subgroup G)) (p := 2)) ≤ 2 := by
  let h := c.localSetup hG structural115Input sourceC
  let q := h.componentQuotientCover e
  have hk : q.toMonoidHom.ker = center L :=
    (h.componentQuotientCover_ker e).trans (h.mathieuTwentyTwo_center_eq e).symm
  obtain ⟨f,hf,_,R,_,hfix⟩ := c.central_omega_faithful_action hG sourceC
  let a := (q.autMap hk).comp f
  have ha : Function.Injective a := (q.autMap_injective hk).comp hf
  let P : Sylow 2 M22 := R.mapSurjective q.surjective
  let A : Subgroup (MulAut M22) := a.range
  let : IsElementaryAbelian 2 A := IsElementaryAbelian.of_surjective a.rangeRestrict
    a.rangeRestrict_surjective
  have hpoint : ∀ b ∈ A, ∀ x ∈ P, b x = x := by
    rintro b ⟨t,rfl⟩ x ⟨y,hy,rfl⟩
    change q.autMap hk (f t) (q.toMonoidHom y) = q.toMonoidHom y
    rw [q.autMap_apply,hfix t y hy]
  have hb := m22_elementary_sylow_fixer_card_le_two m22_center_eq_bot P A hpoint
  rw [← Nat.card_congr (MonoidHom.ofInjective ha).toEquiv] at hb
  change Nat.card (((omega₁ (center (c.T : Subgroup G)) (p := 2)).map
    (center (c.T : Subgroup G)).subtype).map (c.T : Subgroup G).subtype) ≤ 2 at hb
  rw [card_map_of_injective (c.T : Subgroup G).subtype_injective,
    card_map_of_injective (center (c.T : Subgroup G)).subtype_injective] at hb
  exact hb

/-- The selected ambient Sylow has cyclic center in every surviving M₂₂
cover branch; this is an ambient source conclusion, not an intrinsic shortcut. -/
theorem MathieuSourceSetup.mathieuTwentyTwo_ambient_center_isCyclic
    (c : MathieuSourceSetup H L M S z) (hG : IsSimpleQTKE C G)
    (sourceC : LocalC129Input C G)
    (e : (L ⧸ pCore 2 L) ≃* M22) : IsCyclic (center (c.T : Subgroup G)) :=
  (c.T.isPGroup'.to_subgroup _).isCyclic_of_card_omega_one_le_two
    (c.mathieuTwentyTwo_ambient_center_omega_card_le_two hG sourceC e)

end CFSG.Quasithin.Chapter2.ComponentRefinement
