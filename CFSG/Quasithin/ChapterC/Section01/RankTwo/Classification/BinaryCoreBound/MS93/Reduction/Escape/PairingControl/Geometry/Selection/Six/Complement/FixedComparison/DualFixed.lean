module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.RankOnePairing.Source

/-!
# Equal natural displacements give equal opposite fixed images

Pair the natural U coordinates with the compatible inverse-transpose
coordinates on V/B. A vector fixed by an actor modulo B annihilates the
actual commutator of U with that actor. Two nonzero binary covectors which
annihilate the same plane of order four are equal: the common kernel of
two distinct nonzero covectors in F₂³ has only two elements. The latter
small calculation is checked by the kernel; the action and subgroup
transport are proved structurally.

Thus equal order-four natural displacements place both fixed images on the
same dual line, and any nonfixed subgroup on that line covers the other
modulo B. This is the opposite-module comparison used in
Meierfrankenfeld--Stellmacher, *Pushing up weak BN-pairs of rank two* (1993),
(4.3.2)(5), printed p.884.
-/

public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
open scoped commutatorElement
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.PairingControl.Geometry.Selection.Six.Complement.FixedComparison
open RankOnePairing

private theorem two_covectors : ∀ f g : Fin 3 → ZMod 2,
    f ≠ 0 → g ≠ 0 → f ≠ g →
      Fintype.card {u : Fin 3 → ZMod 2 // dotProduct f u = 0 ∧ dotProduct g u = 0} = 2 := by
  decide +kernel

private def pairingMap {G : Type*} [Group G] {π : G →* SL} {U : Subgroup G}
    (n : NaturalFactor π ⊤ U ⊥) (f : Fin 3 → ZMod 2) : U →* Multiplicative (ZMod 2) where
  toFun u := Multiplicative.ofAdd (dotProduct f (n.coordinates u).toAdd)
  map_one' := by simp
  map_mul' u v := by
    change Multiplicative.ofAdd (dotProduct f (n.coordinates (u*v)).toAdd) = _
    rw [map_mul, toAdd_mul, dotProduct_add]
    rfl

private theorem fixed_annihilates_commutator {G : Type*} [Group G] {π : G →* SL}
    {U V B : Subgroup G} (n : NaturalFactor π ⊤ U ⊥)
    (d : DualFactor π ⊤ V B U n) (A : Subgroup G) (x : V)
    (hfixed : ∀ a ∈ A, ⁅a, (x : G)⁆ ∈ B) :
    ∀ u ∈ ⁅U, A⁆, ∀ hu : u ∈ U,
      dotProduct (d.coordinates x).toAdd (n.coordinates ⟨u, hu⟩).toAdd = 0 := by
  let f := (d.coordinates x).toAdd
  let k := pairingMap n f
  have hcomm : ⁅U, A⁆ ≤ k.ker.map U.subtype := by
    rw [commutator_comm]
    apply commutator_le.mpr
    intro a ha u hu
    let u₀ : U := ⟨u, hu⟩
    let u₁ : U := ⟨a * u * a⁻¹, le_normalizer_iff.mp n.normalized a (mem_top _) u hu⟩
    let y : V := ⟨a⁻¹ * (x : G) * a,
      by simpa using le_normalizer_iff.mp d.normalized a⁻¹ (mem_top _) (x : G) x.property⟩
    have hy : y * x⁻¹ ∈ d.coordinates.ker := by
      rw [d.kernel]
      change a⁻¹ * (x : G) * a * (x : G)⁻¹ ∈ B
      simpa only [commutatorElement_def, inv_inv] using hfixed a⁻¹ (A.inv_mem ha)
    have he : d.coordinates y = d.coordinates x := by
      apply mul_inv_eq_one.mp
      simpa only [MonoidHom.mem_ker, map_mul, map_inv] using hy
    have hact := d.action a⁻¹ (mem_top _) x y (by simp only [inv_inv]; rfl)
    rw [he] at hact
    simp only [map_inv, inv_inv] at hact
    refine ⟨u₁ * u₀⁻¹, ?_, rfl⟩
    change k (u₁ * u₀⁻¹) = 1
    rw [map_mul, map_inv, mul_inv_eq_one]
    change Multiplicative.ofAdd (dotProduct f (n.coordinates u₁).toAdd) =
      Multiplicative.ofAdd (dotProduct f (n.coordinates u₀).toAdd)
    congr 1
    rw [n.action a (mem_top _) u₀ u₁ rfl, Matrix.dotProduct_mulVec,
      ← Matrix.mulVec_transpose, ← hact]
  intro u hu hU
  obtain ⟨w, hw, he⟩ := hcomm hu
  have hw' : w = (⟨u, hU⟩ : U) := Subtype.ext he
  rw [hw'] at hw
  exact hw

/-- Equal natural displacements of order four determine the same dual fixed
line. A nonfixed subgroup on that line covers every other such subgroup
modulo the exact coordinate kernel. -/
theorem cover_of_equal_displacements {G : Type*} [Group G] {π : G →* SL}
    {U V B : Subgroup G} (n : NaturalFactor π ⊤ U ⊥)
    (d : DualFactor π ⊤ V B U n)
    (A₁ A₂ X Y : Subgroup G) (hX : X ≤ V) (hY : Y ≤ V)
    (hx : ⁅X, A₁⁆ ≤ B) (hy : ⁅Y, A₂⁆ ≤ B)
    (hedges : ⁅U, A₁⁆ = ⁅U, A₂⁆) (hcard : Nat.card (⁅U, A₁⁆ : Subgroup G) = 4)
    (hne : ¬ Y ≤ B) : X ≤ Y ⊔ B := by
  obtain ⟨y, hyY, hyB⟩ := SetLike.not_le_iff_exists.mp hne
  let y₀ : V := ⟨y, hY hyY⟩
  let g := (d.coordinates y₀).toAdd
  have hg : g ≠ 0 := by
    intro h
    have hh : y₀ ∈ d.coordinates.ker := h
    rw [d.kernel] at hh
    exact hyB hh
  have hfixedY : ∀ a ∈ A₂, ⁅a, y⁆ ∈ B := by
    intro a ha
    rw [commutator_comm] at hy
    exact hy (commutator_mem_commutator ha hyY)
  have hEU : ⁅U, A₁⁆ ≤ U :=
    le_normalizer_iff_commutator_le_left.mp (le_top.trans n.normalized)
  have hginv := fixed_annihilates_commutator n d A₂ y₀ hfixedY
  rw [← hedges] at hginv
  intro x hxX
  let x₀ : V := ⟨x, hX hxX⟩
  let f := (d.coordinates x₀).toAdd
  by_cases hf : f = 0
  · have hh : x₀ ∈ d.coordinates.ker := hf
    rw [d.kernel] at hh
    exact mem_sup_right hh
  have hfixedX : ∀ a ∈ A₁, ⁅a, x⁆ ∈ B := by
    intro a ha
    rw [commutator_comm] at hx
    exact hx (commutator_mem_commutator ha hxX)
  have hfinv := fixed_annihilates_commutator n d A₁ x₀ hfixedX
  have heq : f = g := by
    by_contra hfg
    let j : (⁅U, A₁⁆ : Subgroup G) → {u : Fin 3 → ZMod 2 // dotProduct f u = 0 ∧ dotProduct g u = 0} :=
      fun u => ⟨(n.coordinates ⟨u, hEU u.property⟩).toAdd,
        hfinv u u.property _, hginv u u.property _⟩
    have hinj : Function.Injective j := by
      intro u v huv
      have hc : n.coordinates ⟨u, hEU u.property⟩ =
          n.coordinates ⟨v, hEU v.property⟩ := congrArg Multiplicative.ofAdd (congrArg Subtype.val huv)
      have he := n.equivOfBot.injective hc
      exact Subtype.ext (congrArg (fun z : U => (z : G)) he)
    have hc := Nat.card_le_card_of_injective j hinj
    rw [hcard, Nat.card_eq_fintype_card, two_covectors f g hf hg hfg] at hc
    omega
  have hxy : x₀ * y₀⁻¹ ∈ d.coordinates.ker := by
    change d.coordinates (x₀ * y₀⁻¹) = 1
    rw [map_mul, map_inv, mul_inv_eq_one]
    exact congrArg Multiplicative.ofAdd heq
  rw [d.kernel] at hxy
  have hprod := (Y ⊔ B).mul_mem (mem_sup_right hxy) (mem_sup_left hyY)
  change (x * y⁻¹) * y ∈ Y ⊔ B at hprod
  simpa only [inv_mul_cancel_right] using hprod

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.PairingControl.Geometry.Selection.Six.Complement.FixedComparison
