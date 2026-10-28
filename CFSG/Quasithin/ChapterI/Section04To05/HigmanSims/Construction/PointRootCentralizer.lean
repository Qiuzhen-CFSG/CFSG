module

public import CFSG.Quasithin.ChapterI.Section04To05.HigmanSims.Construction.PointCoreCommutator
public import CFSG.Quasithin.ChapterI.Section04To05.HigmanSims.Construction.LinearEndpoints.PairedRadicalAction
import all CFSG.Quasithin.ChapterI.Section04To05.HigmanSims.Construction.LinearEndpoints.PairedRadicalAction

/-!
# A point-core involution cannot fix an independent cyclic-four root

The proof retains the whole original normalizer core. An involution outside
that core moves a seed point; its displacement on a square root has square
the marked point-core involution. Fixing a square root of a different fixed
seed point would give a cyclic-four frame of determinant minus one, contrary
to the original determinant-one action.

The internal import deliberately reuses the ambient core coordinates,
displacement identities, and matrix action from the paired-radical proof.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped commutatorElement
namespace CFSG.Quasithin.HigmanSims
variable {G : Type*} [Group G] [Finite G] {z : G} {V : Subgroup G}

private theorem seed_square_root (h : TypeAt z V) (x : G) (hx : x ∈ V) :
    ∃ d : G, d ∈ (normalizer (V : Set G)).pCoreIn 2 ∧ d ^ 2 = x := by
  let P := (normalizer (V : Set G)).pCoreIn 2
  let q : P := ⟨x, ambient_seed_le_core h hx⟩
  let e := coordinates h
  have hq : q ^ 2 = 1 := by
    apply Subtype.ext
    let := h.elementary
    exact elemPow_eq_one_of_isElementaryAbelian (p := 2) x hx
  have cert : ∀ a : Multiplicative (ZMod 4), a ^ 2 = 1 → ∃ b, b ^ 2 = a := by
    decide +kernel
  have hs (i : Fin 3) : ∃ b : Multiplicative (ZMod 4), b ^ 2 = e q i := by
    apply cert
    have he := congrArg (fun a : P => e a i) hq
    simpa only [map_pow, map_one, Pi.pow_apply, Pi.one_apply] using he
  choose d hd using hs
  refine ⟨e.symm d, (e.symm d).property, ?_⟩
  have he : (e.symm d) ^ 2 = q := by
    apply e.injective
    apply funext
    intro i
    simpa only [map_pow, e.apply_symm_apply, Pi.pow_apply] using hd i
  exact congrArg Subtype.val he

/-- An involution of an original point core, outside the whole normalizer
core, cannot centralize a core element whose square is a different
nonidentity seed point fixed by that involution. -/
theorem TypeAt.point_core_involution_not_commute_root (h : TypeAt z V)
    (w v r c : G) (hw : w ∈ V) (hw1 : w ≠ 1) (_hv : v ∈ V) (hv1 : v ≠ 1)
    (hwv : w ≠ v) (hrQ : r ∈ (involutionCentralizer w).pCoreIn 2)
    (hr2 : r ^ 2 = 1) (hrP : r ∉ (normalizer (V : Set G)).pCoreIn 2)
    (hrv : Commute r v) (hcP : c ∈ (normalizer (V : Set G)).pCoreIn 2)
    (hc2 : c ^ 2 = v) : ¬ Commute r c := by
  classical
  let P := (normalizer (V : Set G)).pCoreIn 2
  let hwT := h.at_seed_point w hw hw1
  have hrM := (hwT.local_cores_le_intersection.1 hrQ).2
  have hrw : Commute r w := mem_centralizer_singleton_iff.mp
    (hwT.local_cores_le_intersection.1 hrQ).1
  have hVQ : V ≤ (involutionCentralizer w).pCoreIn 2 := by
    change V ≤ (pCore 2 (involutionCentralizer w)).map (involutionCentralizer w).subtype
    rw [← hwT.centralizer_fitting]
    exact hwT.seed_le_core
  obtain ⟨x, hx, hrx⟩ : ∃ x ∈ V, ¬ Commute r x := by
    by_contra hn
    push Not at hn
    apply hrP
    change r ∈ (pCore 2 (normalizer (V : Set G))).map (normalizer (V : Set G)).subtype
    rw [← h.seed_centralizer]
    exact fun x hx => (hn x hx).eq.symm
  have hxcomm : ⁅r, x⁆ = w := by
    have hh := hwT.point_core_commutator_mem r x hrQ (hVQ hx)
    rw [mem_zpowers_iff_mem_range_orderOf, hwT.involution] at hh
    obtain ⟨n, hn, he⟩ := Finset.mem_image.mp hh
    have hn2 : n < 2 := Finset.mem_range.mp hn
    interval_cases n
    · have hh : ⁅r,x⁆ = 1 := by simpa using he.symm
      exact (hrx (commutatorElement_eq_one_iff_commute.mp hh)).elim
    · simpa using he.symm
  obtain ⟨d, hdP, hd2⟩ := seed_square_root h x hx
  let a : P := ⟨⁅r,d⁆, displacement_core h r d hrM hdP⟩
  let b : P := ⟨c, hcP⟩
  let p : P := ⟨d, hdP⟩
  have ha2 : (a : G) ^ 2 = w := by
    change ⁅r,d⁆ ^ 2 = w
    rw [displacement_square h r d hrM hdP, hd2, hxcomm]
  intro hrc
  have hri : r⁻¹ = r := inv_eq_of_mul_eq_one_left (by simpa only [pow_two] using hr2)
  have hra : r * (a : G) * r⁻¹ = (a : G)⁻¹ := by
    change r * ⁅r,d⁆ * r⁻¹ = ⁅r,d⁆⁻¹
    have hrr : r * r = 1 := by simpa only [pow_two] using hr2
    simp only [commutatorElement_def, mul_inv_rev, inv_inv, hri]
    simp only [← mul_assoc, hrr, one_mul]
  have hrb : r * (b : G) * r⁻¹ = b := by
    change r * c * r⁻¹ = c
    rw [hrc.eq, mul_inv_cancel_right]
  have hrp : r * d * r⁻¹ = (a : G) * d := by
    simp only [a, commutatorElement_def, mul_assoc, inv_mul_cancel, mul_one]
  obtain ⟨e, X, hX, hact⟩ := ambient_matrix h r hrM
  have haX : X.mulVec (e a).toAdd = -(e a).toAdd := by
    simpa only [map_inv, toAdd_inv] using hact a a⁻¹ hra
  have hbX : X.mulVec (e b).toAdd = (e b).toAdd := hact b b hrb
  have hpX : X.mulVec (e p).toAdd = (e p).toAdd + (e a).toAdd := by
    simpa only [map_mul, toAdd_mul, add_comm] using hact p (a*p) hrp
  have hinj : Function.Injective (fun q : P => (e q).toAdd) :=
    fun _ _ he => e.injective (congrArg Multiplicative.ofAdd he)
  have hs (q : P) : (e (q ^ 2)).toAdd = (e q).toAdd + (e q).toAdd := by
    simp only [pow_two, map_mul, toAdd_mul]
  have h1 : (e 1).toAdd = 0 := by rw [map_one]; rfl
  apply ZModFourDeterminantObstruction.no_negated_fixed_shear X (e a).toAdd (e b).toAdd
    (e p).toAdd hX haX hbX hpX
  · intro he
    have hh := congrArg Subtype.val (hinj (show (e (a^2)).toAdd = (e 1).toAdd by
      rwa [hs, h1]))
    exact hw1 (ha2.symm.trans hh)
  · intro he
    have hh := congrArg Subtype.val (hinj (show (e (b^2)).toAdd = (e 1).toAdd by
      rwa [hs, h1]))
    exact hv1 (hc2.symm.trans hh)
  · intro he
    have hh := congrArg Subtype.val (hinj (show (e (a^2)).toAdd = (e (b^2)).toAdd by
      rwa [hs, hs]))
    exact hwv (ha2.symm.trans (hh.trans hc2))
  · intro he
    have hh := congrArg Subtype.val (hinj (show (e (p^2)).toAdd = (e 1).toAdd by
      rwa [hs, h1]))
    exact hrx ((hd2.symm.trans hh) ▸ Commute.one_right r)
  · intro he
    have hh := congrArg Subtype.val (hinj (show (e (p^2)).toAdd = (e (a^2)).toAdd by
      rwa [hs, hs]))
    exact hrx ((hd2.symm.trans (hh.trans ha2)) ▸ hrw)
  · intro he
    have hh := congrArg Subtype.val (hinj (show (e (p^2)).toAdd = (e (b^2)).toAdd by
      rwa [hs, hs]))
    exact hrx ((hd2.symm.trans (hh.trans hc2)) ▸ hrv)
  · intro he
    have hh := congrArg Subtype.val (hinj (show (e (p^2)).toAdd = (e (a^2*b^2)).toAdd by
      simpa only [hs, map_mul, toAdd_mul] using he))
    have hxwv : x = w * v := hd2.symm.trans (hh.trans (congrArg₂ (·*·) ha2 hc2))
    exact hrx (hxwv ▸ hrw.mul_right hrv)

end CFSG.Quasithin.HigmanSims
