module
public import Theory.GroupAction.FixedComponentNormalizer
public import CFSG.Quasithin.Chapter2.Section05.Overcomponents.MarkedOrdinarySource

/-!
# Normalizer control on the original invariant component

Elements of the source Sylow centralizer commute with the marked involution and act on the normal containing component. Uniqueness of the quotient fixed component then normalizes the actual original K.

Source: Aschbacher–Smith 2.5.19, printed pp.560–563.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter2.Section05.Overcomponents.Prime
open ComponentRefinement ComponentSelection
variable {G : Type*} [Group G] [Finite G]
  {H K M : Subgroup G} {S : Sylow 2 H} {z : G}

omit [Finite G] in
theorem source_invariant_normalizes_component
    (t i : G) (htZ : t ∈ centerIn ((S : Subgroup H).map H.subtype))
    (hKi : K ≤ centralizer ({i} : Set G))
    (X : Subgroup (centralizer ({i} : Set G))) [X.Normal]
    (hKX : K.subgroupOf (centralizer ({i} : Set G)) ≤ X)
    (a : MulAut X)
    (hact : ∀ x : X, ((a x : centralizer ({i} : Set G)) : G) =
      t * ((x : centralizer ({i} : Set G)) : G) * t⁻¹)
    (hB : IsComponentIn ((K.subgroupOf (centralizer ({i} : Set G))).subgroupOf X) a.fixedSubgroup)
    (hunique : ∀ D₁ D₂ : Subgroup (X ⧸ center X),
      IsComponentIn D₁ (quotientAut (center X) a).fixedSubgroup →
      IsComponentIn D₂ (quotientAut (center X) a).fixedSubgroup → D₁ = D₂) :
    (S : Subgroup H).map H.subtype ⊓ centralizer ({i} : Set G) ≤ normalizer (K : Set G) := by
  let Gi := centralizer ({i} : Set G)
  let D := K.subgroupOf Gi
  let B := D.subgroupOf X
  let f : X →* G := Gi.subtype.comp X.subtype
  have hfi : Function.Injective f := Gi.subtype_injective.comp X.subtype_injective
  have hBmap : B.map f = K := by
    rw [show f = Gi.subtype.comp X.subtype from rfl, ← map_map,
      map_subgroupOf_eq_of_le hKX, map_subgroupOf_eq_of_le hKi]
  have hne : B.map (QuotientGroup.mk' (center X)) ≠ ⊥ := by
    intro hb
    have hcent : B ≤ center X := by
      simpa only [QuotientGroup.ker_mk'] using (map_eq_bot_iff B).mp hb
    have hcc : B ≤ centralizer (B : Set X) := by
      intro x hx y hy
      exact mem_center_iff.mp (hcent hx) y
    let : IsQuasisimple B := hB.quasisimple
    have hbot : B = ⊥ := by
      simpa only [commutator_eq_self] using commutator_eq_bot_iff_le_centralizer.mpr hcc
    exact hB.ne_bot hbot
  intro b hb
  let bi : Gi := ⟨b,hb.2⟩
  have hbN : bi ∈ normalizer (X : Set Gi) := by
    rw [normalizer_eq_top]
    trivial
  let e : MulAut X := X.normalizerMonoidHom ⟨bi,hbN⟩
  have he (x : X) : f (e x) = b * f x * b⁻¹ := rfl
  have hea : Commute e a := by
    apply MulEquiv.ext
    intro x
    apply hfi
    change f (e (a x)) = f (a (e x))
    rw [he]
    have ha (y : X) : f (a y) = t * f y * t⁻¹ := hact y
    rw [ha, ha, he]
    have hbt : b * t = t * b := htZ.2 b hb.1
    calc
      _ = (b * t) * f x * (b * t)⁻¹ := by group
      _ = (t * b) * f x * (t * b)⁻¹ := by rw [hbt]
      _ = _ := by group
  have hBn := MulAut.normalizes_fixed_component_of_central_quotient_unique a e hea B hB hne hunique
  apply mem_normalizer_iff_map_conj_eq.mpr
  rw [← hBmap, map_map]
  have hcomp : (MulAut.conj b).toMonoidHom.comp f = f.comp e.toMonoidHom :=
    MonoidHom.ext fun x => (he x).symm
  change B.map ((MulAut.conj b).toMonoidHom.comp f) = B.map f
  rw [hcomp, ← map_map, hBn]
end CFSG.Quasithin.Chapter2.Section05.Overcomponents.Prime
