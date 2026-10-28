module

public import Theory.SpecificGroups.BinaryLinear.SixSylowActors.Five.FixedGeometry

/-!
# Embedding degree-four fixed groups in the degree-five fixed model

Extend a binary four-space by an orthogonal line. Extension by the identity
commutes with inverse transpose and reflects nonidentity transvections. An
outer involution is an inner twist of inverse transpose by a symmetric matrix;
extending that matrix gives a symmetric invertible five-matrix. The proved
five-dimensional Gram factorization conjugates its fixed group into the fixed
group of ordinary inverse transpose, with its compatible S₆ identification.

This constructs an injective homomorphism from the actual degree-four fixed
group to S₆, retaining the natural transvection action. It does not require
classifying the four-dimensional symmetric forms. The consuming actor argument
carries its given A₆ and Sylow subgroup through this same homomorphism.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), E.6.23,
printed p.254 (PDF p.265) of `refs/quasithin.pdf`. The Gram factorization and
compatible S₆ model are proved in `SixSylowActors.Five.FixedGeometry`.
-/

open Matrix
open BinaryLinear.OuterCyclic
namespace BinaryLinear.SixSylowActors.Four

private def coordinates : (ZMod 2 × Space 4) ≃ₗ[ZMod 2] Space 5 where
  toFun x := Fin.cons x.1 x.2
  invFun x := (x 0, Fin.tail x)
  left_inv x := rfl
  right_inv x := Fin.cons_self_tail x
  map_add' x y := by ext i; refine Fin.cases ?_ (fun j => ?_) i <;> rfl
  map_smul' r x := by ext i; refine Fin.cases ?_ (fun j => ?_) i <;> rfl

private theorem coordinates_dot (x y : ZMod 2 × Space 4) :
    dotProduct (coordinates x) (coordinates y) = x.1 * y.1 + dotProduct x.2 y.2 := by
  exact Fin.sum_univ_succ _

private def extension : LinearGroup 4 →* LinearGroup 5 where
  toFun g := coordinates.symm.trans
    (((LinearEquiv.refl (ZMod 2) (ZMod 2)).prodCongr g).trans coordinates)
  map_one' := by ext x i; simp [LinearEquiv.trans_apply]
  map_mul' g h := by ext x i; simp [LinearEquiv.trans_apply]

private theorem extension_coordinates (g : LinearGroup 4) (r : ZMod 2) (v : Space 4) :
    extension g (coordinates (r, v)) = coordinates (r, g v) := by
  simp [extension, LinearEquiv.trans_apply]

private theorem extension_injective : Function.Injective extension := by
  intro g h he
  apply LinearEquiv.ext
  intro v
  have hh := congrArg (fun k : LinearGroup 5 => k (coordinates (0, v))) he
  rw [extension_coordinates, extension_coordinates] at hh
  exact congrArg Prod.snd (coordinates.injective hh)

private theorem extension_graph (g : LinearGroup 4) :
    extension (graphLinear 4 g) = graphLinear 5 (extension g) := by
  apply LinearEquiv.ext
  intro x
  apply dotProduct_eq
  intro y
  obtain ⟨z, rfl⟩ := (extension g).surjective y
  rw [graphLinear_dotProduct]
  obtain ⟨⟨a, x⟩, rfl⟩ := coordinates.surjective x
  obtain ⟨⟨b, y⟩, rfl⟩ := coordinates.surjective z
  rw [extension_coordinates, extension_coordinates, coordinates_dot, coordinates_dot,
    graphLinear_dotProduct]

private def inclusion : Space 4 →ₗ[ZMod 2] Space 5 :=
  coordinates.toLinearMap.comp (LinearMap.inr (ZMod 2) (ZMod 2) (Space 4))

private def projection : Space 5 →ₗ[ZMod 2] Space 4 :=
  (LinearMap.snd (ZMod 2) (ZMod 2) (Space 4)).comp coordinates.symm.toLinearMap

private theorem projection_inclusion (v : Space 4) : projection (inclusion v) = v := by
  simp [projection, inclusion]

private theorem extension_isTransvection {g : LinearGroup 4}
    (ht : IsTransvection (extension g)) : IsTransvection g := by
  obtain ⟨w, f, hw, hf, hfw, ht⟩ := ht
  let w₀ := projection w
  let f₀ := f.comp inclusion
  have he (v : Space 4) : g v = v + f₀ v • w₀ := by
    have h := congrArg (fun k : LinearGroup 5 => projection (k (inclusion v))) ht
    change projection (extension g (coordinates (0, v))) =
      projection (inclusion v + f (inclusion v) • w) at h
    rw [extension_coordinates] at h
    simpa [projection, inclusion, w₀, f₀, map_add, map_smul] using h
  have hg : g ≠ 1 := by
    intro hg
    have hn := (show IsTransvection (extension g) from ⟨w, f, hw, hf, hfw, ht⟩).ne_one
    exact hn (hg ▸ extension.map_one)
  have hw₀ : w₀ ≠ 0 := by
    intro hh
    apply hg
    apply LinearEquiv.ext
    intro v
    change g v = v
    simpa only [hh, smul_zero, add_zero] using he v
  have hf₀ : f₀ ≠ 0 := by
    intro hh
    apply hg
    apply LinearEquiv.ext
    intro v
    change g v = v
    simpa only [hh, LinearMap.zero_apply, zero_smul, add_zero] using he v
  obtain ⟨v, hv⟩ : ∃ v, f₀ v ≠ 0 := by
    by_contra! h
    exact hf₀ (LinearMap.ext h)
  have hv1 : f₀ v = 1 := (by decide : ∀ a : ZMod 2, a ≠ 0 → a = 1) _ hv
  have hwim : inclusion w₀ = w := by
    have h := congrArg (fun k : LinearGroup 5 => k (inclusion v)) ht
    change extension g (coordinates (0, v)) = inclusion v + f₀ v • w at h
    rw [extension_coordinates, hv1, one_smul] at h
    change inclusion (g v) = inclusion v + w at h
    rw [he, hv1, one_smul, map_add] at h
    exact add_left_cancel h
  have hfw₀ : f₀ w₀ = 0 := by
    change f (inclusion w₀) = 0
    rwa [hwim]
  exact ⟨w₀, f₀, hw₀, hf₀, hfw₀, LinearEquiv.ext he⟩

end BinaryLinear.SixSylowActors.Four

open scoped MatrixGroups
namespace BinaryLinear.SixSylowActors.Four

private theorem twist_square {G : Type*} [Group G]
    (γ : MulAut G) (hγ : ∀ x, γ (γ x) = x) (g : G) :
    MulAut.conj (γ g * g) = (γ * MulAut.conj g) ^ 2 := by
  ext x : 1
  simp only [pow_two, MulAut.mul_apply, MulAut.conj_apply, map_mul, map_inv, hγ]

private theorem apply_apply_of_sq {G : Type*} [Group G]
    (γ : MulAut G) (hγ : γ ^ 2 = 1) (x : G) : γ (γ x) = x := by
  simpa only [pow_two, MulAut.mul_apply, MulAut.one_apply] using
    congrArg (fun a : MulAut G => a x) hγ

private theorem cocycle_of_twist_sq {G : Type*} [Group G]
    (hc : Subgroup.center G = ⊥) (γ : MulAut G) (hγ : γ ^ 2 = 1)
    (g : G) (h : (γ * MulAut.conj g) ^ 2 = 1) : γ g = g⁻¹ := by
  have he := twist_square γ (apply_apply_of_sq γ hγ) g
  apply mul_eq_one_iff_eq_inv.mp
  apply MulAut.conj_injective_of_center_eq_bot hc
  rw [he, h, map_one]

private theorem symmetric_of_twist {n : ℕ} (hn : 0 < n) (g : SL(n, ZMod 2))
    (h : (graphSL n * MulAut.conj g) ^ 2 = 1) : g.transpose = g := by
  have hi := cocycle_of_twist_sq (binary_center_eq_bot hn)
    (graphSL n) (graphSL_sq n) g h
  dsimp only [graphSL] at hi
  exact inv_injective hi

private theorem symmetric_twist (τ : MulAut (LinearGroup 4)) (hτ : τ ^ 2 = 1)
    (hout : τ ∉ MulAut.innerSubgroup (LinearGroup 4)) :
    ∃ g : SL(4, ZMod 2), g.transpose = g ∧
      τ = graphLinear 4 * MulAut.conj (slEquivLinear 4 g) := by
  obtain ⟨g, hi | hg⟩ := inner_graph (Or.inl rfl) τ
  · exact (hout (hi ▸ ⟨g, rfl⟩)).elim
  obtain ⟨k, rfl⟩ := (slEquivLinear 4).surjective g
  refine ⟨k, symmetric_of_twist (by decide) k ?_, hg⟩
  apply (MulAut.congr (slEquivLinear 4)).injective
  have he : MulAut.congr (slEquivLinear 4) (graphSL 4 * MulAut.conj k) = τ := by
    rw [hg]
    ext x : 1
    simp [graphLinear, MulAut.congr_apply]
  rw [map_pow, he, hτ, map_one]

/-- The actual fixed subgroup of an outer involution embeds in S₆ so that
any element mapping to a transposition is a transvection on the original four-space. -/
public theorem exists_fixedEmbedding (τ : MulAut (LinearGroup 4)) (hτ : τ ^ 2 = 1)
    (hout : τ ∉ MulAut.innerSubgroup (LinearGroup 4)) :
    ∃ j : τ.fixedSubgroup →* Equiv.Perm (Fin 6), Function.Injective j ∧
      ∀ b : τ.fixedSubgroup, (j b).IsSwap → IsTransvection (b : LinearGroup 4) := by
  obtain ⟨g, hs, hτg⟩ := symmetric_twist τ hτ hout
  let g₅ := (slEquivLinear 5).symm (extension (slEquivLinear 4 g))
  have hg₅ : slEquivLinear 5 g₅ = extension (slEquivLinear 4 g) :=
    (slEquivLinear 5).apply_symm_apply _
  have hs₅ : g₅.transpose = g₅ := by
    apply inv_injective
    apply (slEquivLinear 5).injective
    rw [← graphLinear_slEquivLinear, hg₅, ← extension_graph,
      graphLinear_slEquivLinear, hs, map_inv, map_inv, map_inv, hg₅]
  obtain ⟨h, hh⟩ := Five.symmetric_gram g₅ hs₅
  let a := MulAut.conj (slEquivLinear 5 h)
  let J := a.toMonoidHom.comp extension
  have hJ : Function.Injective J := a.injective.comp extension_injective
  have hinter (x : LinearGroup 4) : J (τ x) = graphLinear 5 (J x) := by
    have he : extension (τ x) =
        (graphLinear 5 * MulAut.conj (slEquivLinear 5 g₅)) (extension x) := by
      simp only [hτg, MulAut.mul_apply, MulAut.conj_apply, map_mul, map_inv,
        extension_graph, hg₅]
    change a (extension (τ x)) = graphLinear 5 (a (extension x))
    rw [he]
    exact Five.gram_intertwines g₅ h hh (extension x)
  have hfixed (x : τ.fixedSubgroup) : J x ∈ (graphLinear 5).fixedSubgroup := by
    rw [MulAut.mem_fixedSubgroup, ← hinter,
      (MulAut.mem_fixedSubgroup τ x).mp x.property]
  let j := (J.comp τ.fixedSubgroup.subtype).codRestrict _ hfixed
  have hj : Function.Injective j := by
    intro x y he
    exact Subtype.ext (hJ (congrArg Subtype.val he))
  obtain ⟨m⟩ := Five.graph_fixedModel
  refine ⟨m.equiv.toMonoidHom.comp j, m.equiv.injective.comp hj, ?_⟩
  intro b hb
  have ht : IsTransvection (J b) := by
    have ht := m.swap_isTransvection (m.equiv (j b)) hb
    rw [m.equiv.symm_apply_apply] at ht
    exact ht
  apply extension_isTransvection
  exact (isTransvection_map_linear (by decide : 2 ≤ 5) a (extension b)).mp ht

end BinaryLinear.SixSylowActors.Four
