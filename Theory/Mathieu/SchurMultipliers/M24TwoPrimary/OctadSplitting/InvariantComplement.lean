module

public import Theory.Mathieu.SchurMultipliers.M24TwoPrimary.Reduction
public import Theory.Mathieu.SchurMultipliers.M24TwoPrimary.OctadSplitting.InvariantComplement.Functional
public import Theory.Mathieu.M24.ChapterHStabilizers.OctadAction
public import Theory.Mathieu.M24.LocalGeometry.OctadCharacteristicTwo
public import Theory.ElementaryAbelian.VectorSpace

/-!
# An invariant complement in the native octad-kernel preimage

Let q be a central double extension of the actual native octad stabilizer and
assume the preimage N of its pointwise kernel has exponent two. Then N is
abelian, so its conjugation action factors through L/N. The checked native core
coordinates identify that quotient with SL₄(2), and identify the image of N
with its natural binary four-space. The relative kernel is precisely ker(q)
and is fixed by the full action.

The vanishing of H¹ on the dual natural module supplies an invariant functional
nonzero on this central line. Its kernel, mapped back into L, is normal in all
of L, disjoint from ker(q), and maps onto the literal pointwise octad kernel.
The proof uses neither a section of the native stabilizer nor an involutory
root lift. The dual cohomology calculation uses inverse transpose, not an
identification of the natural representation with its dual.

Source: Aschbacher–Smith, I.1.5–I.1.6(6), printed p.408 (PDF p.419),
and the E₁₆.A₈ entry in GLS3, Table 5.3e.
-/

public section

open Subgroup Representation Representation.OneCohomology
open Sporadic.Mathieu.M24LocalGeometry
open Sporadic.Mathieu.M24LocalGeometry.LinearFourCore
open scoped IsMulCommutative
namespace Sporadic.Mathieu.SchurMultipliers.M24TwoPrimary
noncomputable section
local instance : octadKernel.Normal := by
  change (action seedOctad).ker.Normal
  infer_instance
namespace InvariantComplement
private def kernelCoordinates : octadKernel ≃* Multiplicative Four :=
  (MulEquiv.subgroupCongr seed_core_eq_kernel.symm).trans
    (M24ChapterHStabilizers.OctadAction.coreCoordinates seedOctad)

private theorem kernelCoordinates_conjugation (g : OctadGroup) (x : octadKernel) :
    (kernelCoordinates (MulAut.conjNormal g x)).toAdd =
      M24ChapterHStabilizers.OctadAction.linearAction seedOctad g
        (kernelCoordinates x).toAdd := by
  have hc : (MulEquiv.subgroupCongr seed_core_eq_kernel.symm) (MulAut.conjNormal g x) =
      M24ChapterHStabilizers.OctadAction.coreConjugate seedOctad g
        ((MulEquiv.subgroupCongr seed_core_eq_kernel.symm) x) := by
    apply Subtype.ext
    exact (M24ChapterHStabilizers.OctadAction.coreConjugate_coe seedOctad g
      ((MulEquiv.subgroupCongr seed_core_eq_kernel.symm) x)).symm
  change (M24ChapterHStabilizers.OctadAction.coreCoordinates seedOctad
    ((MulEquiv.subgroupCongr seed_core_eq_kernel.symm) (MulAut.conjNormal g x))).toAdd = _
  rw [hc]
  exact (M24ChapterHStabilizers.OctadAction.coreCoordinates_conjugation seedOctad g
    ((MulEquiv.subgroupCongr seed_core_eq_kernel.symm) x)).trans
      (congrArg (fun a => a (kernelCoordinates x).toAdd)
        (M24ChapterHStabilizers.OctadAction.naturalAction_quotientEquiv seedOctad g))
end InvariantComplement
open InvariantComplement

/-- An elementary preimage of the native octad kernel has a complement to the
central double kernel invariant under the full extension group. -/
theorem octad_invariant_kernel_complement {L : Type*} [Group L] [Finite L]
    (q : L →* OctadGroup) (hq : Function.Surjective q)
    (hcentral : q.ker ≤ Subgroup.center L) (hcard : Nat.card q.ker = 2)
    (helem : ElementaryKernelPreimage q) :
    ∃ T : Subgroup L, T.Normal ∧ Disjoint q.ker T ∧ T.map q = octadKernel := by
  let N := octadKernel.comap q
  have hpow (x : N) : x ^ 2 = 1 := Subtype.ext (helem x.val x.property)
  have hinv (x : N) : x⁻¹ = x := inv_eq_of_mul_eq_one_right (by simpa [pow_two] using hpow x)
  let : IsMulCommutative N := ⟨⟨fun x y => by
    calc
      x * y = (x * y)⁻¹ := (hinv _).symm
      _ = y * x := by rw [mul_inv_rev, hinv, hinv]⟩⟩
  let : IsElementaryAbelian 2 N := {
    toIsMulCommutative := inferInstance
    exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr hpow }
  let qN : N →* octadKernel := (q.comp N.subtype).codRestrict _ (fun x => x.property)
  have hqN : Function.Surjective qN := by
    intro v
    obtain ⟨x, hx⟩ := hq v.val
    exact ⟨⟨x, by change q x ∈ octadKernel; rw [hx]; exact v.property⟩, Subtype.ext hx⟩
  let e := BinaryLinear.OuterCyclic.slEquivLinear 4
  let π : L →* SL := e.symm.toMonoidHom.comp
    ((M24ChapterHStabilizers.OctadAction.linearAction seedOctad).comp q)
  have hπ : Function.Surjective π := e.symm.surjective.comp
    ((M24ChapterHStabilizers.OctadAction.linearAction_surjective seedOctad).comp hq)
  have hπker (x : L) : π x = 1 ↔ x ∈ N := by
    change e.symm (M24ChapterHStabilizers.OctadAction.linearAction seedOctad (q x)) = 1 ↔
      q x ∈ octadKernel
    rw [map_eq_one_iff e.symm e.symm.injective]
    change q x ∈ (M24ChapterHStabilizers.OctadAction.linearAction seedOctad).ker ↔ _
    rw [M24ChapterHStabilizers.OctadAction.linearAction_ker]
    change q x ∈ pCore 2 OctadGroup ↔ _
    rw [seed_core_eq_kernel]
    rfl
  let α : L →* MulAut N := MulAut.conjNormal
  have hαker : π.ker ≤ α.ker := by
    intro x hx
    have hxN : x ∈ N := (hπker x).mp hx
    apply MonoidHom.mem_ker.mpr
    apply MulEquiv.ext
    intro y
    apply Subtype.ext
    change x * y.val * x⁻¹ = y.val
    have hc : x * y.val = y.val * x := congrArg Subtype.val (mul_comm (⟨x, hxN⟩ : N) y)
    rw [hc, mul_inv_cancel_right]
  let β : SL →* MulAut N := π.liftOfSurjective hπ ⟨α, hαker⟩
  have hβ (x : L) : β (π x) = α x :=
    π.liftOfRightInverse_comp_apply _ _ _ x
  let σ : Representation (ZMod 2) SL (Additive N) := {
    toFun := fun a => (β a).toMonoidHom.toAdditive.toZModLinearMap 2
    map_one' := by
      apply LinearMap.ext
      intro x
      exact congrArg (fun a : MulAut N => a x.toMul) β.map_one
    map_mul' := by
      intro a b
      apply LinearMap.ext
      intro x
      exact congrArg (fun c : MulAut N => c x.toMul) (β.map_mul a b) }
  let coord : Additive N →+ Four := {
    toFun := fun x => (kernelCoordinates (qN x.toMul)).toAdd
    map_zero' := by simp
    map_add' := by
      intro x y
      change (kernelCoordinates (qN (x.toMul * y.toMul))).toAdd = _
      rw [map_mul, map_mul]
      rfl }
  have hnat (x : L) (v : Four) : natural (π x) v =
      M24ChapterHStabilizers.OctadAction.linearAction seedOctad (q x) v := by
    change e (e.symm (M24ChapterHStabilizers.OctadAction.linearAction seedOctad (q x))) v = _
    rw [e.apply_symm_apply]
  have hqconj (a : L) (x : N) :
      qN (α a x) = MulAut.conjNormal (q a) (qN x) := by
    apply Subtype.ext
    change q (a * x.val * a⁻¹) = q a * q x.val * (q a)⁻¹
    rw [map_mul, map_mul, map_inv]
  let p : σ.IntertwiningMap natural := {
    toLinearMap := coord.toZModLinearMap 2
    isIntertwining' := by
      intro a
      obtain ⟨l, rfl⟩ := hπ a
      apply LinearMap.ext
      intro x
      change (kernelCoordinates (qN (β (π l) x.toMul))).toAdd =
        natural (π l) (kernelCoordinates (qN x.toMul)).toAdd
      rw [hβ, hqconj, kernelCoordinates_conjugation, hnat] }
  have hp : Function.Surjective p := by
    intro v
    obtain ⟨x, hx⟩ := hqN (kernelCoordinates.symm (Multiplicative.ofAdd v))
    refine ⟨Additive.ofMul x, ?_⟩
    change (kernelCoordinates (qN x)).toAdd = v
    rw [hx, kernelCoordinates.apply_symm_apply]
    rfl
  have hpker (x : N) : p (Additive.ofMul x) = 0 ↔ q x.val = 1 := by
    change kernelCoordinates (qN x) = 1 ↔ q x.val = 1
    rw [map_eq_one_iff kernelCoordinates kernelCoordinates.injective]
    exact ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩
  have hfixed : p.toLinearMap.ker ≤ fixed σ := by
    intro x hx a
    obtain ⟨l, rfl⟩ := hπ a
    have hqx : q x.toMul.val = 1 := (hpker x.toMul).mp hx
    apply Additive.toMul.injective
    change β (π l) x.toMul = x.toMul
    rw [hβ]
    apply Subtype.ext
    change l * x.toMul.val * l⁻¹ = x.toMul.val
    rw [mem_center_iff.mp (hcentral hqx) l, mul_inv_cancel_right]
  obtain ⟨z₀, hz₀, huniq⟩ := (Nat.card_eq_two_iff' (1 : q.ker)).mp hcard
  let z : N := ⟨z₀.val, by
    change q z₀.val ∈ octadKernel
    rw [z₀.property]
    exact octadKernel.one_mem⟩
  have hzq : q z.val = 1 := z₀.property
  have hzne : (Additive.ofMul z : Additive N) ≠ 0 := by
    intro h
    apply hz₀
    apply Subtype.ext
    exact congrArg (fun n : Additive N => n.toMul.val) h
  obtain ⟨ψ, hψz, hψ⟩ := exists_fixed_functional σ p hp hfixed
    (Additive.ofMul z) ((hpker z).mpr hzq) hzne
  let S : Subgroup N := {
    carrier := {x | ψ (Additive.ofMul x) = 0}
    one_mem' := map_zero ψ
    mul_mem' := by
      intro x y hx hy
      change ψ (Additive.ofMul x + Additive.ofMul y) = 0
      rw [map_add, hx, hy, add_zero]
    inv_mem' := by
      intro x hx
      change ψ (-Additive.ofMul x) = 0
      rw [map_neg, hx, neg_zero] }
  let T : Subgroup L := S.map N.subtype
  have hTnormal : T.Normal := by
    constructor
    intro x hx l
    obtain ⟨y, hy, rfl⟩ := hx
    refine ⟨α l y, ?_, rfl⟩
    change ψ (Additive.ofMul (α l y)) = 0
    rw [← hβ l]
    exact (hψ (π l) (Additive.ofMul y)).trans hy
  have hdisj : Disjoint q.ker T := by
    apply Subgroup.disjoint_def.mpr
    intro x hx hxt
    obtain ⟨y, hy, rfl⟩ := hxt
    by_cases hx1 : y.val = 1
    · exact hx1
    let w : q.ker := ⟨y.val, hx⟩
    have hw : w ≠ 1 := fun h => hx1 (congrArg Subtype.val h)
    have hwz : w = z₀ := huniq w hw
    have hyz : y = z := Subtype.ext (congrArg (fun t : q.ker => (t : L)) hwz)
    change ψ (Additive.ofMul y) = 0 at hy
    rw [hyz, hψz] at hy
    exact (one_ne_zero hy).elim
  have hmap : T.map q = octadKernel := by
    apply le_antisymm
    · rintro x ⟨y, ⟨v, hv, rfl⟩, rfl⟩
      exact v.property
    · intro v hv
      obtain ⟨x, hx⟩ := hqN ⟨v, hv⟩
      have hxq : q x.val = v := congrArg Subtype.val hx
      by_cases hψx : ψ (Additive.ofMul x) = 0
      · exact ⟨x.val, ⟨x, hψx, rfl⟩, hxq⟩
      have hψx1 : ψ (Additive.ofMul x) = 1 := by
        have hh : ∀ t : ZMod 2, t = 0 ∨ t = 1 := by decide
        exact (hh _).resolve_left hψx
      refine ⟨(x * z).val, ⟨x * z, ?_, rfl⟩, ?_⟩
      · change ψ (Additive.ofMul x + Additive.ofMul z) = 0
        rw [map_add, hψx1, hψz]
        decide
      · change q (x.val * z.val) = v
        rw [map_mul, hxq, hzq, mul_one]
  exact ⟨T, hTnormal, hdisj, hmap⟩
end
end Sporadic.Mathieu.SchurMultipliers.M24TwoPrimary
