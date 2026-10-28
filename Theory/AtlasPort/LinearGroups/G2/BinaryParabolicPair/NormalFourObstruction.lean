module

public import Theory.AtlasPort.LinearGroups.G2.BinaryParabolicPair.InvolutionCentralizer
public import Theory.AtlasPort.LinearGroups.G2.EvenInvolutionGeometry.RootElements

/-!
# Normal elementary subgroups of a binary derived G₂ involution centralizer

The first parabolic of the actual commutator group G₂(2)′ has two-core
Q₈ ◦ C₄. In its five-root coordinates, a square-one element commuting with
its cubic conjugate is either the identity or the distinguished involution.
Thus every normal elementary abelian two-subgroup of this parabolic lies
in the distinguished order-two subgroup. Sylow conjugacy and the existing
long-root calculation transport the obstruction to every central involution
of a Sylow subgroup of G₂(2)′.

This is the concrete first-parabolic inspection used in Aschbacher--Smith,
15.3.43, printed p.1140 of the combined 1 March 2004 manuscript. The core
and cubic are those of Lemma 14.2.21, printed p.988. Coordinates are inherited
from the licensed ATLAS port; see LICENSES/ATLAS.txt and
LICENSES/ATLAS-CITATION.cff.
-/

public section

open Subgroup
namespace Atlas.G2.BinaryParabolicPair
open BinaryCore

set_option maxRecDepth 100000 in
private theorem elementary_cubic_coordinate : ∀ x : Coordinates,
    x.c = x.d → x ^ 2 = 1 →
    x * cubicConjugate x = cubicConjugate x * x → x = 1 ∨ x = involution := by
  decide +kernel

/-- A normal elementary subgroup of the first derived parabolic has order at most two. -/
theorem elementary_normal_first_le (V : Subgroup DerivedModel)
    [IsElementaryAbelian 2 V] (hV : V ≤ derivedFirst)
    (hn : derivedFirst ≤ normalizer (V : Set DerivedModel)) :
    V ≤ zpowers derivedInvolution := by
  have hcore := le_pCoreIn_of_normalizes (IsElementaryAbelian.isPGroup 2 V) hV hn
  intro x hx
  have hxc : x.val ∈ derivedCore := by
    rw [← derivedFirst_pCore_in_model]
    exact mem_map_of_mem DerivedModel.subtype (hcore hx)
  obtain ⟨t, ht, htx⟩ := hxc
  have hs : t ^ 2 = 1 := embedding_injective (by
    rw [map_pow, map_one, htx, ← DerivedModel.coe_pow]
    exact congrArg Subtype.val (elemPow_eq_one_of_isElementaryAbelian (p := 2) x hx))
  let a : DerivedModel := ⟨cubicActor, cubicActor_mem_derived⟩
  have hay : a * x * a⁻¹ ∈ V :=
    (mem_normalizer_iff.mp (hn cubicActor_mem_derivedFirst) x).mp hx
  have hc : t * cubicConjugate t = cubicConjugate t * t := by
    apply embedding_injective
    rw [map_mul, map_mul, ← cubic_conjugate, htx]
    exact congrArg (fun y : V => y.val.val)
      ((inferInstance : IsMulCommutative V).is_comm.comm ⟨x, hx⟩ ⟨a*x*a⁻¹, hay⟩)
  rcases elementary_cubic_coordinate t ht hs hc with ht1 | htz
  · have hx1 : x = 1 := Subtype.ext (by rw [← htx, ht1, map_one]; rfl)
    rw [hx1]; exact one_mem _
  · have hxz : x = derivedInvolution := Subtype.ext (by
      rw [← htx, htz, embedding_involution]; rfl)
    rw [hxz]; exact mem_zpowers _

/-- The actual first derived parabolic has no normal elementary abelian four-group. -/
theorem no_normal_four_first (V : Subgroup DerivedModel)
    [IsElementaryAbelian 2 V] (hV : V ≤ derivedFirst)
    (hn : derivedFirst ≤ normalizer (V : Set DerivedModel))
    (hc : Nat.card V = 4) : False := by
  have hb := card_le_of_le (elementary_normal_first_le V hV hn)
  rw [hc, Nat.card_zpowers, derivedInvolution_order] at hb
  omega

/-- The centralizer of a Sylow-central involution in G₂(2)′ has no normal four-group. -/
theorem no_normal_four_centralizer (T : Sylow 2 DerivedModel)
    {x : DerivedModel} (hx : x ∈ T) (hsq : x ^ 2 = 1)
    (hcentral : ∀ y ∈ T, Commute x y) (hne : x ≠ 1)
    (V : Subgroup DerivedModel) [IsElementaryAbelian 2 V]
    (hV : V ≤ centralizer ({x} : Set DerivedModel))
    (hn : centralizer ({x} : Set DerivedModel) ≤ normalizer (V : Set DerivedModel))
    (hcard : Nat.card V = 4) : False := by
  obtain ⟨g, a, ha, hxg⟩ :=
    EvenInvolutionGeometry.binary_central_involution_isLongRoot T hx hsq hcentral hne
  have ha1 : a = 1 := (by decide : ∀ a : ZMod 2, a ≠ 0 → a = 1) a ha
  rw [ha1] at hxg
  let e : MulAut DerivedModel := (MulAut.conjNormal g).symm
  have hex : e x = derivedInvolution := by
    apply Subtype.ext
    change g⁻¹ * x.val * g = z
    rw [hxg]
    change g⁻¹ * (g * z * g⁻¹) * g = z
    group
  have hC : (centralizer ({x} : Set DerivedModel)).map e.toMonoidHom = derivedFirst := by
    rw [← centralizer_derivedInvolution_eq_first, ← hex]
    ext y
    constructor
    · rintro ⟨b, hb, rfl⟩
      apply mem_centralizer_singleton_iff.mpr
      change e b * e x = e x * e b
      simpa only [map_mul] using congrArg e (mem_centralizer_singleton_iff.mp hb)
    · intro hy
      refine ⟨e.symm y, ?_, e.apply_symm_apply y⟩
      apply mem_centralizer_singleton_iff.mpr
      apply e.injective
      simpa only [map_mul, e.apply_symm_apply] using
        (mem_centralizer_singleton_iff.mp hy)
  let W := V.map e.toMonoidHom
  let : IsElementaryAbelian 2 W := IsElementaryAbelian.map e.toMonoidHom
  apply no_normal_four_first W
  · exact (map_mono hV).trans hC.le
  · rw [← hC]
    exact (map_mono hn).trans (V.le_normalizer_map e.toMonoidHom)
  · exact (card_map_of_injective e.injective).trans hcard

end Atlas.G2.BinaryParabolicPair
