module

public import CFSG.Quasithin.ChapterJ.Section01To02.ParabolicStructure.ConjugateIntersections.Basic
public import Theory.Representation.PSL3Two.NaturalOrbits

/-!
# The stabilizer orbit in J.2.2(5)

Two distinct nonzero binary vectors are independent. Extending the map
between two such pairs gives an element of the literal natural SL₃(2)
action, since every invertible binary matrix has determinant one. The
Ru1 marking transports this to conjugation by L. As |Z| = 2, fixing its
nonidentity element is exactly membership in H = C_G(Z).

Consequently H ∩ L transports any conjugate indexed outside H to any
other such conjugate. The proof retains the left-conjugation convention
of `conjugateU` and uses the relative H-normality of U.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
J.2.2(5), printed pp.432–433 (PDF pp.443–444).
-/

public section
noncomputable section
open Subgroup Representation

namespace CFSG.Quasithin.ChapterJ.ConjugateIntersections
open BinaryLinearThree
private theorem binary_pair_independent (z u : Vector) (hz : z ≠ 0)
    (hu : u ≠ 0) (huz : u ≠ z) : LinearIndependent (ZMod 2) ![z, u] := by
  rw [linearIndependent_fin2]
  refine ⟨hu, ?_⟩
  intro a
  rcases (by decide : ∀ a : ZMod 2, a = 0 ∨ a = 1) a with rfl | rfl
  · simpa using hz.symm
  · simpa using huz

private theorem natural_stabilizer_transitive (z u v : Vector) (hz : z ≠ 0) (hu : u ≠ 0) (hv : v ≠ 0)
    (huz : u ≠ z) (hvz : v ≠ z) :
    ∃ g : BinaryLinearThree.Group, W g z = z ∧ W g u = v := by
  have hu' := binary_pair_independent z u hz hu huz
  have hv' := binary_pair_independent z v hz hv hvz
  let f := hu'.linearCombinationEquiv.symm.trans hv'.linearCombinationEquiv
  obtain ⟨g, hg⟩ := Submodule.exists_linearEquiv_restrict_eq f
  have hg0 : g z = z := by
    have h := hg (hu'.linearCombinationEquiv (Finsupp.single 0 1))
    simpa [f] using h.symm
  have hg1 : g u = v := by
    have h := hg (hu'.linearCombinationEquiv (Finsupp.single 1 1))
    simpa [f] using h.symm
  have hdet : (LinearMap.toMatrix' g.toLinearMap).det = 1 := by
    rw [LinearMap.det_toMatrix']
    exact (by decide : ∀ x : ZMod 2, x ≠ 0 → x = 1) _ g.isUnit_det'.ne_zero
  refine ⟨⟨LinearMap.toMatrix' g.toLinearMap, hdet⟩, ?_, ?_⟩
  · change Matrix.toLin' (LinearMap.toMatrix' g.toLinearMap) z = z
    rwa [Matrix.toLin'_toMatrix']
  · change Matrix.toLin' (LinearMap.toMatrix' g.toLinearMap) u = v
    rwa [Matrix.toLin'_toMatrix']


variable {G : Type*} [_root_.Group G] [Finite G]

private theorem natural_coordinates_injective (d : LocalSetup G) :
    Function.Injective d.ru1.natural.coordinates := by
  apply (MonoidHom.ker_eq_bot_iff _).mp
  rw [d.ru1.natural.kernel_eq, bot_subgroupOf]

private theorem mem_H_iff_conjugate_z (d : LocalSetup G) (z : d.toTypeRuSetup.Z)
    (hz : z ≠ 1) (g : G) :
    g ∈ d.toTypeRuSetup.H ↔ g * (z : G) * g⁻¹ = z := by
  constructor
  · intro hg
    rw [← hg z z.property, mul_inv_cancel_right]
  · intro hg w hw
    obtain ⟨z₀, _, huniq⟩ := (Nat.card_eq_two_iff' (1 : d.toTypeRuSetup.Z)).mp d.card_Z
    by_cases hw1 : w = 1
    · simp [hw1]
    have hwz : w = (z : G) := congrArg Subtype.val
      ((huniq ⟨w, hw⟩ (fun he => hw1 (congrArg Subtype.val he))).trans (huniq z hz).symm)
    rw [hwz]
    exact (mul_inv_eq_iff_eq_mul.mp hg).symm

/-- In the marked natural action, the stabilizer of Z is transitive away from Z. -/
theorem exists_stabilizer_conjugator (d : LocalSetup G) (z : d.toTypeRuSetup.Z) (hz : z ≠ 1)
    (u v : d.V) (hu : u ≠ 1) (hv : v ≠ 1)
    (huz : (u : G) ≠ (z : G)) (hvz : (v : G) ≠ (z : G)) :
    ∃ h : G, h ∈ d.L ∧ h ∈ d.toTypeRuSetup.H ∧ h * (u : G) * h⁻¹ = v := by
  let zV : d.V := ⟨z, (d.center_eq.le.trans inf_le_left) z.property⟩
  have hinj := natural_coordinates_injective d
  have hzero (a : d.V) (ha : a ≠ 1) : (d.ru1.natural.coordinates a).toAdd ≠ 0 := by
    intro he
    apply ha
    apply hinj
    apply Multiplicative.toAdd.injective
    simpa only [map_one, toAdd_one] using he
  have hzV : zV ≠ 1 := by
    intro he
    have he' : (z : G) = 1 := congrArg (fun a : d.V => (a : G)) he
    exact hz (Subtype.ext he')
  have hune : (d.ru1.natural.coordinates u).toAdd ≠ (d.ru1.natural.coordinates zV).toAdd := by
    intro he
    exact huz (congrArg Subtype.val (hinj he))
  have hvne : (d.ru1.natural.coordinates v).toAdd ≠ (d.ru1.natural.coordinates zV).toAdd := by
    intro he
    exact hvz (congrArg Subtype.val (hinj he))
  obtain ⟨g, hgz, hgu⟩ := natural_stabilizer_transitive
    (d.ru1.natural.coordinates zV).toAdd (d.ru1.natural.coordinates u).toAdd
    (d.ru1.natural.coordinates v).toAdd (hzero zV hzV) (hzero u hu) (hzero v hv) hune hvne
  obtain ⟨h, hh⟩ := d.ru1.quotient_surjective g
  have hconj (a b : d.V)
      (he : BinaryLinearThree.W g (d.ru1.natural.coordinates a).toAdd =
        (d.ru1.natural.coordinates b).toAdd) :
      (h : G) * (a : G) * (h : G)⁻¹ = b := by
    have hc := d.ru1.natural.equivariant h a
    rw [MonoidHom.comp_apply, hh, he] at hc
    exact congrArg Subtype.val (hinj hc)
  exact ⟨h, h.property, (mem_H_iff_conjugate_z d z hz h).mpr (hconj zV zV hgz), hconj u v hgu⟩

private theorem conjugateU_mul (d : LocalSetup G) (a b : G) :
    conjugateU d (a * b) = (conjugateU d b).map (MulAut.conj a).toMonoidHom := by
  rw [conjugateU, conjugateU, map_map]
  congr 1
  ext x
  change (a * b) * x * (a * b)⁻¹ = a * (b * x * b⁻¹) * a⁻¹
  group

/-- All conjugates indexed outside H form a single orbit under H ∩ L. -/
theorem exists_conjugateU_transport (d : LocalSetup G) (l k : G) (hl : l ∈ d.L) (hk : k ∈ d.L)
    (hlH : l ∉ d.toTypeRuSetup.H) (hkH : k ∉ d.toTypeRuSetup.H) :
    ∃ h : G, h ∈ d.L ∧ h ∈ d.toTypeRuSetup.H ∧
      conjugateU d k = (conjugateU d l).map (MulAut.conj h).toMonoidHom := by
  obtain ⟨z, hz, _⟩ := (Nat.card_eq_two_iff' (1 : d.toTypeRuSetup.Z)).mp d.card_Z
  have hzV : (z : G) ∈ d.V := (d.center_eq.le.trans inf_le_left) z.property
  let za (x : G) (hx : x ∈ d.L) : d.V := ⟨x * (z : G) * x⁻¹,
    (mem_normalizer_iff.mp (show x ∈ normalizer d.V from d.ru1.normalizer_eq ▸ hx) z).mp hzV⟩
  have hza (x : G) (hx : x ∈ d.L) : za x hx ≠ 1 := by
    intro he
    apply hz
    apply Subtype.ext
    have he' := congrArg (fun a : d.V => x⁻¹ * (a : G) * x) he
    simpa [za, mul_assoc] using he'
  obtain ⟨h, hhL, hhH, hh⟩ := exists_stabilizer_conjugator d z hz
    (za l hl) (za k hk) (hza l hl) (hza k hk)
    (fun he => hlH ((mem_H_iff_conjugate_z d z hz l).mpr he))
    (fun he => hkH ((mem_H_iff_conjugate_z d z hz k).mpr he))
  have hbH : k⁻¹ * h * l ∈ d.toTypeRuSetup.H := by
    apply (mem_H_iff_conjugate_z d z hz _).mpr
    calc
      (k⁻¹ * h * l) * (z : G) * (k⁻¹ * h * l)⁻¹ =
          k⁻¹ * (h * (l * (z : G) * l⁻¹) * h⁻¹) * k := by group
      _ = k⁻¹ * (k * (z : G) * k⁻¹) * k := by rw [hh]
      _ = z := by group
  refine ⟨h, hhL, hhH, ?_⟩
  calc
    conjugateU d k = conjugateU d (k * (k⁻¹ * h * l)) := by
      rw [conjugateU_mul, conjugateU_eq_of_mem_H d _ hbH]
    _ = conjugateU d (h * l) := by congr 1; group
    _ = (conjugateU d l).map (MulAut.conj h).toMonoidHom := conjugateU_mul d h l

end CFSG.Quasithin.ChapterJ.ConjugateIntersections
