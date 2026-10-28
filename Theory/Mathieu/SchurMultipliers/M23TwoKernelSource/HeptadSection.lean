module

public import Theory.Mathieu.SchurMultipliers.M23TwoKernelSource.AlternatingLift
public import Theory.Mathieu.SchurMultipliers.M23TwoKernelSource.HeptadFunctional
public import Theory.ElementaryAbelian.VectorSpace
public import Theory.SpecificGroups.SymplecticFour.CentralCovers.TwoPrimary.Transfer

/-!
# The marked heptad section in a double cover of M₂₃

The lifted alternating complement acts on the elementary translation
preimage. The fixed-functional theorem splits its central kernel line.
The kernel of that functional maps isomorphically to the original
translation group and is invariant under the same alternating complement.
The two maps combine through the actual heptad semidirect equivalence.
-/

public section
noncomputable section
open Subgroup PerfectCentralCovering Theory.GroupTheory
open Representation Representation.OneCohomology
open scoped IsMulCommutative
namespace Sporadic.Mathieu.SchurMultipliers.M23TwoKernelSource
open M23Geometry M23Geometry.ChapterHLocalActions

/-- Every perfect central double cover splits on the actual odd-index
heptad stabilizer, with the literal inclusion as projection composite. -/
theorem exists_heptad_section {E : Type*} [Group E] [Finite E]
    (f : Cover E M23) (hcard : Nat.card f.toMonoidHom.ker = 2) :
    ∃ s : heptadStabilizer →* E,
      f.toMonoidHom.comp s = heptadStabilizer.subtype := by
  obtain ⟨r, hr⟩ := exists_alternating_section f hcard
  let P := heptadStabilizer.comap f.toMonoidHom
  let q : P →* heptadStabilizer :=
    (f.toMonoidHom.comp P.subtype).codRestrict _ (fun x => x.property)
  have hq : Function.Surjective q := by
    intro h
    obtain ⟨x, hx⟩ := f.surjective h.val
    exact ⟨⟨x, by change f.toMonoidHom x ∈ heptadStabilizer; rw [hx]; exact h.property⟩,
      Subtype.ext hx⟩
  let R : alternatingGroup (Fin 7) →* P := r.codRestrict P (by
    intro a
    change f.toMonoidHom (r a) ∈ heptadStabilizer
    rw [show f.toMonoidHom (r a) =
      (AlternatingSection.s a : M23) from DFunLike.congr_fun hr a]
    exact (AlternatingSection.s a).property)
  have hqR (a : alternatingGroup (Fin 7)) : q (R a) = AlternatingSection.s a :=
    Subtype.ext (DFunLike.congr_fun hr a)
  let N := heptadKernel.comap q
  let qN : N →* heptadKernel := (q.comp N.subtype).codRestrict _ (fun x => x.property)
  have hqN : Function.Surjective qN := by
    intro v
    obtain ⟨x, hx⟩ := hq v.val
    exact ⟨⟨x, by change q x ∈ heptadKernel; rw [hx]; exact v.property⟩, Subtype.ext hx⟩
  let N₀ := (heptadKernel.map heptadStabilizer.subtype).comap f.toMonoidHom
  let : IsElementaryAbelian 2 N₀ := translation_preimage_elementary f hcard
  let iN : N →* N₀ := {
    toFun := fun x => ⟨x.val.val, ⟨q x.val, x.property, rfl⟩⟩
    map_one' := rfl
    map_mul' := fun _ _ => rfl }
  have hiN : Function.Injective iN := by
    intro x y h
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun t : N₀ => (t : E)) h
  let : IsMulCommutative N := ⟨⟨fun x y => hiN (by rw [map_mul, map_mul, mul_comm])⟩⟩
  let : IsElementaryAbelian 2 N := {
    toIsMulCommutative := inferInstance
    exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr (fun x => by
      apply hiN
      rw [map_pow, map_one]
      exact Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
        (IsElementaryAbelian.exponent_dvd_p 2 N₀) (iN x)) }
  let α : alternatingGroup (Fin 7) →* MulAut N := MulAut.conjNormal.comp R
  have hα (a : alternatingGroup (Fin 7)) (x : N) :
      qN (α a x) = heptadConjugation a (qN x) := by
    apply Subtype.ext
    change q (R a * x.val * (R a)⁻¹) = (heptadConjugation a (qN x)).val
    rw [map_mul, map_mul, map_inv, hqR, heptadConjugation_coe]
    rfl
  let σ : Representation (ZMod 2) (alternatingGroup (Fin 7)) (Additive N) := {
    toFun := fun a => (α a).toMonoidHom.toAdditive.toZModLinearMap 2
    map_one' := by
      apply LinearMap.ext
      intro x
      exact congrArg (fun a : MulAut N => a x.toMul) α.map_one
    map_mul' := by
      intro a b
      apply LinearMap.ext
      intro x
      exact congrArg (fun c : MulAut N => c x.toMul) (α.map_mul a b) }
  let coord : Additive N →+ Four := {
    toFun := fun x => (heptadBinaryEquiv.symm (qN x.toMul)).toAdd
    map_zero' := by simp
    map_add' := by
      intro x y
      change (heptadBinaryEquiv.symm (qN (x.toMul * y.toMul))).toAdd = _
      rw [map_mul, map_mul]
      rfl }
  let p : σ.IntertwiningMap heptadRepresentation := {
    toLinearMap := coord.toZModLinearMap 2
    isIntertwining' := by
      intro a
      apply LinearMap.ext
      intro x
      apply Multiplicative.ofAdd.injective
      apply heptadBinaryEquiv.injective
      change heptadBinaryEquiv (heptadBinaryEquiv.symm (qN (α a x.toMul))) =
        heptadBinaryEquiv (heptadBinaryAction a
          (heptadBinaryEquiv.symm (qN x.toMul)))
      rw [heptadBinaryEquiv.apply_symm_apply, heptadBinaryAction_equivariant,
        heptadBinaryEquiv.apply_symm_apply, hα] }
  have hp : Function.Surjective p := by
    intro v
    obtain ⟨x, hx⟩ := hqN (heptadBinaryEquiv (Multiplicative.ofAdd v))
    refine ⟨Additive.ofMul x, ?_⟩
    change (heptadBinaryEquiv.symm (qN x)).toAdd = v
    rw [hx, heptadBinaryEquiv.symm_apply_apply]
    rfl
  have hpker (x : N) : p (Additive.ofMul x) = 0 ↔ qN x = 1 := by
    change heptadBinaryEquiv.symm (qN x) = 1 ↔ qN x = 1
    exact map_eq_one_iff heptadBinaryEquiv.symm heptadBinaryEquiv.symm.injective
  have hfixed : p.toLinearMap.ker ≤ fixed σ := by
    intro x hx a
    have hqx : qN x.toMul = 1 := (hpker x.toMul).mp hx
    have hfx : f.toMonoidHom x.toMul.val.val = 1 := congrArg
      (fun v : heptadKernel => (v.val : M23)) hqx
    apply Additive.toMul.injective
    apply Subtype.ext
    apply Subtype.ext
    change r a * x.toMul.val.val * (r a)⁻¹ = x.toMul.val.val
    rw [mem_center_iff.mp (f.ker_le_center hfx) (r a), mul_inv_cancel_right]
  obtain ⟨z₀, hz₀, huniq⟩ := (Nat.card_eq_two_iff' (1 : f.toMonoidHom.ker)).mp hcard
  let zp : P := ⟨z₀.val, by
    change f.toMonoidHom z₀.val ∈ heptadStabilizer
    rw [z₀.property]
    exact heptadStabilizer.one_mem⟩
  have hzpq : q zp = 1 := Subtype.ext z₀.property
  let z : N := ⟨zp, by
    change q zp ∈ heptadKernel
    rw [hzpq]
    exact heptadKernel.one_mem⟩
  have hzq : qN z = 1 := by apply Subtype.ext; apply Subtype.ext; exact z₀.property
  have hzne : (Additive.ofMul z : Additive N) ≠ 0 := by
    intro h
    apply hz₀
    apply Subtype.ext
    exact congrArg (fun n : Additive N => n.toMul.val.val) h
  obtain ⟨ψ, hψz, hψ⟩ := exists_fixed_functional σ p hp hfixed
    (Additive.ofMul z) ((hpker z).mpr hzq) hzne
  let T : Subgroup N := {
    carrier := {x | ψ (Additive.ofMul x) = 0}
    one_mem' := map_zero ψ
    mul_mem' := by
      intro x y hx hy
      change ψ (Additive.ofMul x) = 0 at hx
      change ψ (Additive.ofMul y) = 0 at hy
      change ψ (Additive.ofMul x + Additive.ofMul y) = 0
      rw [map_add, hx, hy, add_zero]
    inv_mem' := by
      intro x hx
      change ψ (Additive.ofMul x) = 0 at hx
      change ψ (-Additive.ofMul x) = 0
      rw [map_neg, hx, neg_zero] }
  have hT (a : alternatingGroup (Fin 7)) (x : N) (hx : x ∈ T) : α a x ∈ T := by
    change ψ (σ a (Additive.ofMul x)) = 0
    rw [hψ]
    exact hx
  let qT := qN.comp T.subtype
  have hqTi : Function.Injective qT := by
    apply qT.ker_eq_bot_iff.mp
    apply bot_unique
    intro x hx
    have hqx : qN x.val = 1 := hx
    have hfx : f.toMonoidHom x.val.val.val = 1 := congrArg
      (fun v : heptadKernel => (v.val : M23)) hqx
    by_cases hx1 : x.val = 1
    · exact Subtype.ext hx1
    let w : f.toMonoidHom.ker := ⟨x.val.val.val, hfx⟩
    have hw : w ≠ 1 := by
      intro h
      apply hx1
      apply Subtype.ext
      apply Subtype.ext
      exact congrArg (fun t : f.toMonoidHom.ker => (t : E)) h
    have hwz : w = z₀ := huniq w hw
    have hxz : x.val = z := by
      apply Subtype.ext
      apply Subtype.ext
      exact congrArg (fun t : f.toMonoidHom.ker => (t : E)) hwz
    have hzT : z ∈ T := hxz ▸ x.property
    change ψ (Additive.ofMul z) = 0 at hzT
    rw [hψz] at hzT
    exact (one_ne_zero hzT).elim
  have hqTs : Function.Surjective qT := by
    intro v
    obtain ⟨x, hx⟩ := hqN v
    by_cases hψx : ψ (Additive.ofMul x) = 0
    · exact ⟨⟨x, hψx⟩, hx⟩
    have hψx1 : ψ (Additive.ofMul x) = 1 := by
      have hh : ∀ t : ZMod 2, t = 0 ∨ t = 1 := by decide +kernel
      exact (hh _).resolve_left hψx
    refine ⟨⟨x * z, ?_⟩, ?_⟩
    · change ψ (Additive.ofMul x + Additive.ofMul z) = 0
      rw [map_add, hψx1, hψz]
      decide
    · change qN (x * z) = v
      rw [map_mul, hx, hzq, mul_one]
  let eT : T ≃* heptadKernel := MulEquiv.ofBijective qT ⟨hqTi, hqTs⟩
  let sN : heptadKernel →* E := P.subtype.comp (N.subtype.comp
    (T.subtype.comp eT.symm.toMonoidHom))
  have hsN (v : heptadKernel) : f.toMonoidHom (sN v) = (v.val : M23) := by
    exact congrArg (fun x : heptadKernel => (x.val : M23)) (eT.apply_symm_apply v)
  have hsNa (a : alternatingGroup (Fin 7)) (v : heptadKernel) :
      sN (heptadConjugation a v) = r a * sN v * (r a)⁻¹ := by
    let y : T := ⟨α a (eT.symm v).val, hT a _ (eT.symm v).property⟩
    have he : eT y = heptadConjugation a v := by
      change qN (α a (eT.symm v).val) = heptadConjugation a v
      rw [hα]
      exact congrArg (heptadConjugation a) (eT.apply_symm_apply v)
    have he' : eT.symm (heptadConjugation a v) = y := by
      apply eT.injective
      rw [eT.apply_symm_apply, he]
    change (eT.symm (heptadConjugation a v)).val.val.val = _
    rw [he']
    rfl
  let k : heptadKernel ⋊[heptadConjugation] alternatingGroup (Fin 7) →* E :=
    SemidirectProduct.lift sN r (by intro a; apply DFunLike.ext; intro v; exact hsNa a v)
  refine ⟨k.comp heptadSplitEquiv.symm.toMonoidHom, ?_⟩
  apply MonoidHom.ext
  intro h
  obtain ⟨w, rfl⟩ := heptadSplitEquiv.surjective h
  change f.toMonoidHom (k (heptadSplitEquiv.symm (heptadSplitEquiv w))) = _
  rw [heptadSplitEquiv.symm_apply_apply]
  change f.toMonoidHom (sN w.left * r w.right) = _
  rw [map_mul, hsN, show f.toMonoidHom (r w.right) =
    (AlternatingSection.s w.right : M23) from DFunLike.congr_fun hr w.right]
  rfl

/-- Odd-index transfer excludes a perfect central double cover of native M₂₃. -/
theorem double_cover_false {E : Type*} [Group E] [Finite E]
    (f : Cover E M23) (hcard : Nat.card f.toMonoidHom.ker = 2) : False := by
  obtain ⟨s, hs⟩ := exists_heptad_section f hcard
  exact not_dvd_card_kernel_of_section f (p := 2) heptadStabilizer
    (by rw [heptadStabilizer_index]; decide) s hs (by rw [hcard])

end Sporadic.Mathieu.SchurMultipliers.M23TwoKernelSource
