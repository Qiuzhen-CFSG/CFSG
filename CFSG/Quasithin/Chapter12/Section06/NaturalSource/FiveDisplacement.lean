module
public import CFSG.Quasithin.Chapter12.Section06.NaturalSource.FiveFrattini
public import CFSG.Quasithin.Chapter12.Section06.Nonabelian.BinarySection
public import Theory.Representation.ExtraspecialQuinticActor

/-!
# Excluding the original extraspecial five-core model

The faithful action of H/O₂(H) on the literal U_H/V₁ has V-star displacement
at most four. A nontrivial action on an embedded extraspecial exponent-five
group of order 125 would instead give displacement at least eight. Thus
V-star centralizes every such characteristic five-core subgroup, and a moved
supercritical five-core has the actual E25 model, retaining both original
V-star and L₁ actions.

Source: Aschbacher--Smith, proof of 12.6.26, printed p.832.
-/

public section
open Subgroup Theory.GroupTheory Representation
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section06
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V : Subgroup G} [IsElementaryAbelian 2 V]
  (S : SourceHypothesis KnownSimple.IsKnownSimple T L V)
  (D : OrthogonalMarking L V S.chosen.normalizes) (hZ : ZV L V = ⊥) (z : V)

/-- An original V-star actor cannot move an extraspecial exponent-five
characteristic subgroup of O5(H-star), by the literal rank-four section. -/
theorem SourceHypothesis.original_extraspecial_five_action_trivial
    (hz : z ≠ 1)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
    (hTz : (T : Subgroup G) ≤ normalizer ((D.fullSetup hZ T z).V₁ : Set G))
    (hbound : ∀ g : G, g ∉ normalizer (V : Set G) →
      Nat.card (V ⊓ V.map (MulAut.conj g).toMonoidHom : Subgroup G) ≤ 2 ^ 3)
    {H : Subgroup G} (hH : H ∈ (D.fullSetup hZ T z).Hz)
    (hn : ¬ IsMulCommutative ((D.fullSetup hZ T z).VH H))
    (Y : Subgroup (pCore 5 (H ⧸ pCore 2 H))) [Y.Characteristic]
    [IsExtraspecial 5 Y] (hY : Nat.card Y = 125)
    (e : Y ≃* HeisenbergPrime 5) :
    (Nonabelian.Setup.star H V).map ((MulAut.characteristic Y).comp
      (MulAut.conjNormal : (H ⧸ pCore 2 H) →* MulAut (pCore 5 (H ⧸ pCore 2 H)))) = ⊥ := by
  let E := D.fullSetup hZ T z
  let R := pCore 5 (H ⧸ pCore 2 H)
  let a := (MulAut.characteristic Y).comp
    (MulAut.conjNormal : (H ⧸ pCore 2 H) →* MulAut R)
  have h := S.original_f9_of_earlier_geometry D hZ z hz hTV hTz hbound hH
  let := h.point_normal_in_UH
  let := h.point_quotient_elementary
  obtain ⟨σ,c,hσ,_⟩ := h.faithful_point_quotient
  have hr := S.original_binary_displacement_bound D hZ z hz hTV hTz hbound hH hn σ c
  let j : Y →* (H ⧸ pCore 2 H) := R.subtype.comp Y.subtype
  have hj : Function.Injective j := R.subtype_injective.comp Y.subtype_injective
  have hexp (x : Y) : x ^ 5 = 1 := by
    apply e.injective
    rw [map_pow,map_one]
    exact HeisenbergPrime.pow_prime (by decide : 5 ≠ 2) (e x)
  apply (Subgroup.map_eq_bot_iff _).mpr
  intro v hv
  change a v = 1
  by_contra hm
  have hl := ExtraspecialQuinticActor.eight_le_displacement_of_movement
    σ hσ j hj hY hexp v (a v) hm (fun x => rfl)
  have hu := hr v hv
  omega

/-- The moved original five-core has the actual elementary order-25 model;
the extraspecial case is excluded on the faithful original section. -/
theorem SourceHypothesis.original_five_supercritical_elementary
    (hz : z ≠ 1)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
    (hTz : (T : Subgroup G) ≤ normalizer ((D.fullSetup hZ T z).V₁ : Set G))
    (hbound : ∀ g : G, g ∉ normalizer (V : Set G) →
      Nat.card (V ⊓ V.map (MulAut.conj g).toMonoidHom : Subgroup G) ≤ 2 ^ 3)
    (hns : ∀ w : V, D.Nonsingular w → Gv w.val ≤ M L)
    {H : Subgroup G} (hH : H ∈ (D.fullSetup hZ T z).Hz)
    (hn : ¬ IsMulCommutative ((D.fullSetup hZ T z).VH H))
    (hm : ¬ Nonabelian.Setup.star H V ≤
      centralizer (pCore 5 (H ⧸ pCore 2 H) : Set (H ⧸ pCore 2 H))) :
    let E := D.fullSetup hZ T z
    let R := pCore 5 (H ⧸ pCore 2 H)
    ∃ (Y : Subgroup R) (hY : IsSupercriticalPSubgroup 5 Y),
      let : Y.Characteristic := hY.characteristic
      let a := (MulAut.characteristic Y).comp
        (MulAut.conjNormal : (H ⧸ pCore 2 H) →* MulAut R)
      (Nat.card Y = 25 ∧ Nonempty (Y ≃* (Multiplicative (ZMod 5) × Multiplicative (ZMod 5)))) ∧
      (Nonabelian.Setup.star H V).map a ≠ ⊥ ∧
      (Nonabelian.Setup.star H E.L₁).map a ≠ ⊥ := by
  obtain ⟨Y,hY,hmodels,hV,hL⟩ :=
    S.original_five_supercritical_models D hZ z hz hTV hTz hbound hns hH hn hm
  let : Y.Characteristic := hY.characteristic
  rcases hmodels with he | ⟨hc,hs,⟨e⟩⟩
  · exact ⟨Y,hY,he,hV,hL⟩
  · let : IsExtraspecial 5 Y := hs
    exact (hV (S.original_extraspecial_five_action_trivial D hZ z hz hTV hTz hbound hH hn Y hc e)).elim
end CFSG.Quasithin.Chapter12.Section06
