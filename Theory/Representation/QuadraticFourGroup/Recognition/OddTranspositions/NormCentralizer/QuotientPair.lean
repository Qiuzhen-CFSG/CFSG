module

public import Theory.Representation.QuadraticFourGroup.Recognition.OddTranspositions.NormCentralizer.NormImages

/-!
# The literal diagonal map modulo the orbit center

The norm on the first component, followed by E → E/Z(E), has kernel Z(L).
Indeed, if l lᵃ is central in E, commutation with L and the commutation of
L with Lᵃ show that l is central in L. Conversely Z(L) centralizes every
component of E, as does its conjugate. The first isomorphism theorem then
identifies L/Z(L) with the actual norm image in E/Z(E).

The displayed coordinate formula and the equivalence's value on quotient
classes retain the original embeddings and quotient map. Together with
`conjugate_norm_range`, this describes every two-element component orbit.

Source: GLS2, Chapter B, Lemma 3.27(i)--(v), and Chapter G, Theorem 25.14,
Step 2. No split-product or component-recognition hypothesis is used.
-/

@[expose] public section

open Subgroup Theory.GroupTheory
namespace Representation.QuadraticFourGroup
variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  {ρ : Representation (ZMod 2) G V} {L B : Subgroup G} {a : G}

private theorem component_center_centralizes_orbit (hL : IsComponent G L) (B : Subgroup G)
    (x : L) (hx : x ∈ center L) :
    (x : G) ∈ Subgroup.centralizer (componentOrbit L B : Set G) := by
  have he : componentOrbit L B ≤ centralizer ({(x : G)} : Set G) := by
    apply iSup_le
    intro b
    by_cases hb : L.map (MulAut.conj (b : G)).toMonoidHom = L
    · rw [hb]
      intro y hy
      exact mem_centralizer_singleton_iff.mpr
        (congrArg Subtype.val (mem_center_iff.mp hx (⟨y,hy⟩ : L)))
    · intro y hy
      exact mem_centralizer_singleton_iff.mpr
        ((mem_centralizer_iff.mp
          (commutator_eq_bot_iff_le_centralizer.mp
            ((hL.map_conj (b : G)).commutator_eq_bot_of_ne hL hb) hy) x x.property).symm)
  exact mem_centralizer_iff.mpr fun y hy => mem_centralizer_singleton_iff.mp (he hy)

/-- The component norm homomorphism into the literal orbit E. -/
def Hypotheses.componentNormIntoOrbit (h : Hypotheses ρ L B a) :
    L →* componentOrbit L B :=
  (componentSwapNorm h.component h.moves).codRestrict (componentOrbit L B)
    (fun x => componentSwapNorm_range_le_orbit h.component h.moves h.mem ⟨x,rfl⟩)

/-- The diagonal map into the literal central quotient of the full component orbit. -/
def Hypotheses.componentNormModCenter (h : Hypotheses ρ L B a) :
    L →* componentOrbit L B ⧸ center (componentOrbit L B) :=
  (QuotientGroup.mk' (center (componentOrbit L B))).comp h.componentNormIntoOrbit

/-- The two coordinates of the diagonal are the original component element
and its marked conjugate, followed by the literal quotient map. -/
theorem Hypotheses.componentNormModCenter_apply (h : Hypotheses ρ L B a) (x : L) :
    h.componentNormModCenter x =
      QuotientGroup.mk' (center (componentOrbit L B))
        ⟨x, le_componentOrbit L B x.property⟩ *
      QuotientGroup.mk' (center (componentOrbit L B))
        ⟨a * (x : G) * a⁻¹,
          (le_iSup (fun b : B => L.map (MulAut.conj (b : G)).toMonoidHom)
            ⟨a,h.mem⟩) (mem_map_of_mem _ x.property)⟩ :=
  by
    change QuotientGroup.mk' (center (componentOrbit L B))
      ((⟨x, le_componentOrbit L B x.property⟩ : componentOrbit L B) *
        ⟨a * (x : G) * a⁻¹,
          (le_iSup (fun b : B => L.map (MulAut.conj (b : G)).toMonoidHom)
            ⟨a,h.mem⟩) (mem_map_of_mem _ x.property)⟩) = _
    exact map_mul _ _ _

/-- Modulo the orbit center, a component norm vanishes exactly on the
component center. Thus central overlaps have not been replaced by a split product. -/
theorem Hypotheses.componentNormModCenter_ker (h : Hypotheses ρ L B a) :
    h.componentNormModCenter.ker = center L := by
  ext x
  change QuotientGroup.mk' (center (componentOrbit L B)) (h.componentNormIntoOrbit x) = 1 ↔ _
  rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  constructor
  · intro hx
    apply mem_center_iff.mpr
    intro y
    apply Subtype.ext
    have hn := congrArg Subtype.val (mem_center_iff.mp hx
      (⟨y,le_componentOrbit L B y.property⟩ : componentOrbit L B))
    change (y : G) * ((x : G) * (a*x*a⁻¹)) = ((x : G) * (a*x*a⁻¹)) * y at hn
    have hc : Commute (y : G) (a*x*a⁻¹) :=
      (mem_centralizer_iff.mp
        (commutator_eq_bot_iff_le_centralizer.mp h.commuting_conjugate y.property)
        _ (mem_map_of_mem _ x.property)).symm
    apply (mul_right_cancel_iff (a := a*(x : G)*a⁻¹)).mp
    calc
      (y : G) * x * (a*x*a⁻¹) = y * ((x : G) * (a*x*a⁻¹)) := by group
      _ = ((x : G) * (a*x*a⁻¹)) * y := hn
      _ = ((x : G) * y) * (a*x*a⁻¹) := by rw [mul_assoc, ← hc.eq, ← mul_assoc]
  · intro hx
    have hxc := component_center_centralizes_orbit h.component B x hx
    have hnE : a ∈ normalizer (componentOrbit L B : Set G) :=
      le_normalizer_componentOrbit L B h.mem
    have haxc : a * (x : G) * a⁻¹ ∈ Subgroup.centralizer (componentOrbit L B : Set G) := by
      apply mem_centralizer_iff.mpr
      intro y hy
      have hy' : a⁻¹ * y * a ∈ componentOrbit L B := by
        simpa using (mem_normalizer_iff.mp ((normalizer (componentOrbit L B : Set G)).inv_mem hnE) y).mp hy
      have hc := mem_centralizer_iff.mp hxc _ hy'
      have he := congrArg (MulAut.conj a) hc
      simpa [MulAut.conj_apply, mul_assoc] using he
    have hn := mul_mem hxc haxc
    apply mem_center_iff.mpr
    intro y
    apply Subtype.ext
    exact mem_centralizer_iff.mp hn y y.property

/-- The source diagonal is the actual image of L/Z(L) in E/Z(E), with the
comparison induced by the original norm map. -/
noncomputable def Hypotheses.componentQuotientEquivNormImage (h : Hypotheses ρ L B a) :
    L ⧸ center L ≃* h.componentNormModCenter.range :=
  (QuotientGroup.quotientMulEquivOfEq h.componentNormModCenter_ker.symm).trans
    (QuotientGroup.quotientKerEquivRange h.componentNormModCenter)

/-- The quotient equivalence is induced by the norm map itself. -/
@[simp] theorem Hypotheses.componentQuotientEquivNormImage_mk
    (h : Hypotheses ρ L B a) (x : L) :
    (h.componentQuotientEquivNormImage (QuotientGroup.mk' (center L) x) :
      componentOrbit L B ⧸ center (componentOrbit L B)) = h.componentNormModCenter x := by
  rfl

end Representation.QuadraticFourGroup

end
