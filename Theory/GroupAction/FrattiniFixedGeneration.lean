module
public import Theory.GroupAction.AbelianCoprimeFixedGeneration
public import Theory.GroupTheory.SubgroupConjugation
public import Theory.GroupTheory.CharacteristicCentralizerFusion
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Tactic.Group

/-!
# Fixed-point generation below the Frattini quotient

A coprime action whose kernel contains the Frattini subgroup factors through
that quotient. When the quotient is abelian, its cyclic-quotient fixed
subgroups generate the acted-on prime-power group. The theorem retains the
original action and takes fixed points under the literal quotient preimages.

Two elementary companions lift a cyclic generator across the Frattini
subgroup and turn inversion modulo an action kernel into trivial odd action.
These support the fixed-layer argument in Aschbacher--Smith, 12.2.23,
printed p.803, using Generation by Centralizers of Hyperplanes (A.1.17).
-/

public section

open Subgroup
open scoped IsMulCommutative

theorem isCyclic_of_isCyclic_frattini_quotient {P : Type*} [Group P] [Finite P] [IsCyclic (P ⧸ frattini P)] :
    IsCyclic P := by
  obtain ⟨xbar, hxbar⟩ := isCyclic_iff_exists_zpowers_eq_top.mp
    (inferInstance : IsCyclic (P ⧸ frattini P))
  obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (frattini P) xbar
  have hmap : (zpowers x).map (QuotientGroup.mk' (frattini P)) = ⊤ := by
    simpa only [MonoidHom.map_zpowers] using hxbar
  have hsup : zpowers x ⊔ frattini P = ⊤ := by
    have hh := congrArg (fun B : Subgroup (P ⧸ frattini P) =>
      B.comap (QuotientGroup.mk' (frattini P))) hmap
    simpa only [comap_map_eq, QuotientGroup.ker_mk', comap_top] using hh
  exact isCyclic_iff_exists_zpowers_eq_top.mpr ⟨x, frattini_nongenerating hsup⟩

theorem odd_centralizes_of_centralizing_inverter {G : Type*} [Group G] (P X : Subgroup G) [Finite P]
    (hodd : Odd (Nat.card P)) (v : G)
    (hPX : P ≤ normalizer (X : Set G))
    (hv : v ∈ centralizer (X : Set G))
    (hinv : ∀ a ∈ P, v * a * v⁻¹ * a ∈ centralizer (X : Set G)) :
    P ≤ centralizer (X : Set G) := by
  have hsquare (a : P) : (a : G) ^ 2 ∈ centralizer (X : Set G) := by
    have hn := (normalizer_le_normalizer_centralizer X) (hPX a.property)
    have hc : (a : G) * v⁻¹ * (a : G)⁻¹ ∈ centralizer (X : Set G) :=
      (mem_normalizer_iff.mp hn _).mp ((centralizer _).inv_mem hv)
    have hh := (centralizer (X : Set G)).mul_mem
      ((centralizer _).inv_mem ((centralizer _).mul_mem hv hc)) (hinv a a.property)
    convert hh using 1
    simp only [pow_two]
    group
  intro a ha
  obtain ⟨b, hb⟩ := hodd.coprime_two_right.pow_left_bijective.surjective (⟨a, ha⟩ : P)
  have he := congrArg Subtype.val hb
  change (b : G) ^ 2 = a at he
  rw [← he]
  exact hsquare b

section
variable {A X : Type*} [Group A] [Group X] [Finite A] [Finite X]
variable {q : ℕ} [Fact q.Prime]
variable [IsMulCommutative (A ⧸ frattini A)]
variable [Fact (IsPGroup q X)] [MulDistribMulAction A X]

theorem iSup_frattini_fixedPoints_cyclicQuot_eq_top (hcop : Nat.Coprime (Nat.card A) q)
    (hphi : frattini A ≤ (MulDistribMulAction.toMulAut A X).ker) :
    (⨆ (Y : Subgroup (A ⧸ frattini A))
      (_ : IsCyclic ((A ⧸ frattini A) ⧸ Y)),
      FixedPoints.subgroup (Y.comap (QuotientGroup.mk' (frattini A))) X) = ⊤ := by
  let E := A ⧸ frattini A
  let : CommGroup E := IsMulCommutative.instCommGroup
  let f : E →* MulAut X := QuotientGroup.lift (frattini A)
    (MulDistribMulAction.toMulAut A X) hphi
  let : MulDistribMulAction E X := MulDistribMulAction.compHom X f
  have he : Nat.Coprime (Nat.card E) q :=
    hcop.of_dvd_left (card_quotient_dvd_card (frattini A))
  have hg := iSup_fixedPoints_cyclicQuot_eq_top_of_coprime_abelian_pGroup
    (A := E) (G := X) (q := q) he
  have hfixed (Y : Subgroup E) : FixedPoints.subgroup Y X =
      FixedPoints.subgroup (Y.comap (QuotientGroup.mk' (frattini A))) X := by
    ext x
    constructor
    · intro hx a
      exact hx ⟨QuotientGroup.mk' (frattini A) a, a.property⟩
    · intro hx y
      obtain ⟨a, ha⟩ := QuotientGroup.mk'_surjective (frattini A) (y : E)
      have hy : a ∈ Y.comap (QuotientGroup.mk' (frattini A)) := by
        change QuotientGroup.mk' (frattini A) a ∈ Y
        rw [ha]
        exact y.property
      have hh := hx (⟨a, hy⟩ : Y.comap (QuotientGroup.mk' (frattini A)))
      change f (y : E) x = x
      rw [← ha]
      exact hh
  simpa only [hfixed] using hg
end
