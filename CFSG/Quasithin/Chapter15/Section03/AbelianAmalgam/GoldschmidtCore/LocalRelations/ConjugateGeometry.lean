module

public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.LocalRelations.SylowGeneration
public import CFSG.Quasithin.Chapter15.Section03.Preliminaries.OrthogonalLocal.Action
public import Theory.SpecificGroups.OrthogonalFourBinary.NaturalAction

/-!
# The second singular line in the terminal amalgam

The distinct index-two stabilizers in 15.3.66 give an element
`s ∈ S − T_E`. Right conjugation by this element preserves `V` and
its quadratic form through the compatible `NaturalAction`. It also
fixes the actual central involutions of `T`. Thus `F=Eˢ` is a distinct
singular four-subgroup containing `Ω₁(Z(T))`; the existing conjugation
lemma gives `T_F=T_E`.

The input `V₁` remains the chosen definite plane from the earlier
setup; its stabilizer is the actual `planeStabilizer T V₁`. Only its
earlier index and distinction from `T_E` are needed here.

Source: Aschbacher–Smith, combined manuscript (1 March 2004),
construction preceding Lemma 15.3.68, printed p.1154, PDF p.1171.
-/

public section

open Subgroup
namespace CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.LocalRelations
variable {G : Type*} [Group G]

theorem otherLine_le_module (V M E : Subgroup G)
    (d : OrthogonalFourBinary.NaturalAction V M) (hEV : E ≤ V) (s : G) (hs : s ∈ M) :
    otherLine E s ≤ V := by
  have hV : V.map (MulAut.conj s⁻¹).toMonoidHom = V :=
    mem_normalizer_iff_map_conj_eq.mp (d.normalizes (M.inv_mem hs))
  exact (map_mono hEV).trans_eq hV

theorem centralInvolutions_le_otherLine (T : Sylow 2 G) (E : Subgroup G)
    (hZE : centralInvolutions T ≤ E) (s : G) (hs : s ∈ T) :
    centralInvolutions T ≤ otherLine E s := by
  intro z hz
  refine mem_map.mpr ⟨z, hZE hz, ?_⟩
  have hc := centralInvolutions_le_centralizer_sylow T hz s hs
  change s⁻¹ * z * (s⁻¹)⁻¹ = z
  rw [inv_inv]
  calc
    s⁻¹ * z * s = s⁻¹ * (s * z) := by rw [mul_assoc, hc]
    _ = z := inv_mul_cancel_left _ _

theorem otherLine_totally_singular (V M E : Subgroup G)
    (d : OrthogonalFourBinary.NaturalAction V M) (hEV : E ≤ V)
    (hE : ∀ e : E, d.singular ⟨e, hEV e.property⟩) (s : G) (hs : s ∈ M) :
    ∀ f : otherLine E s,
      d.singular ⟨f, otherLine_le_module V M E d hEV s hs f.property⟩ := by
  intro f
  obtain ⟨e, he, hef⟩ := f.property
  let m : M := ⟨s⁻¹, M.inv_mem hs⟩
  let v : V := ⟨e, hEV he⟩
  have hv := d.intertwines m v
  have hfv : (⟨(f : G), otherLine_le_module V M E d hEV s hs f.property⟩ : V) =
      d.coordinates.symm (Multiplicative.ofAdd
        ((d.action m).val (Multiplicative.toAdd (d.coordinates v)))) := by
    apply Subtype.ext
    exact hef.symm.trans hv.symm
  rw [hfv]
  unfold OrthogonalFourBinary.NaturalAction.singular
  rw [d.coordinates.apply_symm_apply]
  have hpres := (Theory.AlgebraicGroup.mem_quadraticIsometrySubgroup
    OrthogonalFourBinary.form (d.action m).val).mp (d.action m).property
  exact (hpres _).trans (hE ⟨e, he⟩)

variable [Finite G]

theorem exists_other_singular_four (T : Sylow 2 G) (V M V₁ E : Subgroup G)
    (d : OrthogonalFourBinary.NaturalAction V M)
    (hTM : (T : Subgroup G) ≤ M) (hEV : E ≤ V)
    (hcard : Nat.card E = 4)
    (hfour : Nonempty (E ≃* Multiplicative (ZMod 2 × ZMod 2)))
    (hE : ∀ e : E, d.singular ⟨e, hEV e.property⟩)
    (hZE : centralInvolutions T ≤ E)
    (hS : (planeStabilizer T V₁).relIndex (T : Subgroup G) = 2)
    (hD : (lineT (T : Subgroup G) E).relIndex (T : Subgroup G) = 2)
    (hne : planeStabilizer T V₁ ≠ lineT (T : Subgroup G) E) :
    ∃ s ∈ planeStabilizer T V₁, s ∉ lineT (T : Subgroup G) E ∧
      ∃ hFV : otherLine E s ≤ V,
        centralInvolutions T ≤ otherLine E s ∧
        Nat.card (otherLine E s) = 4 ∧
        Nonempty (otherLine E s ≃* Multiplicative (ZMod 2 × ZMod 2)) ∧
        (∀ f : otherLine E s, d.singular ⟨f, hFV f.property⟩) ∧
        otherLine E s ≠ E ∧ lineT (T : Subgroup G) (otherLine E s) = lineT (T : Subgroup G) E := by
  obtain ⟨s, hs, hsE⟩ := exists_plane_element_outside_lineT T V₁ E hS hD hne
  have hsT : s ∈ T := hs.1
  have hsM := hTM hsT
  refine ⟨s, hs, hsE, otherLine_le_module V M E d hEV s hsM,
    centralInvolutions_le_otherLine T E hZE s hsT, ?_, ?_,
    otherLine_totally_singular V M E d hEV hE s hsM,
    otherLine_ne (T : Subgroup G) E s hsT hsE,
    lineT_otherLine (T : Subgroup G) E s hsT hD⟩
  · exact (card_map_of_injective (MulAut.conj s⁻¹).injective).trans hcard
  · obtain ⟨e⟩ := hfour
    exact ⟨(E.equivMapOfInjective (MulAut.conj s⁻¹).toMonoidHom
      (MulAut.conj s⁻¹).injective).symm.trans e⟩
end CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.LocalRelations
