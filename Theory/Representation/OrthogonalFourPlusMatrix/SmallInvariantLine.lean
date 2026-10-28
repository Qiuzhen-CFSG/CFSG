module
public import Theory.Representation.OrthogonalFourPlusMatrix.SylowSingularLine
public import Theory.Representation.OrthogonalFourPlusMatrix.NormalizerSingularity

/-!
# Small invariant subspaces in the binary determinant tensor

A four-element binary subspace invariant under a Sylow two-subgroup of
SL₂(4) × SL₂(4) is its full singular field line. For each root group,
a vector outside its fixed space would have four distinct translates
inside the three nonzero vectors of the subspace. Sylow conjugacy then
identifies the subspace with the standard singular coefficient line.

Every element of the full binary tensor normalizer is semilinear, so fixing
one nonzero vector of this line preserves the whole line. The final theorem
transports this bound through an actual normal component and equivariant
coordinates. Its original-section application is in
`LocalReduction.BinaryPlaneCentralizer`.

Source: Aschbacher–Smith, proof of 14.7.32, printed p.1057,
refs/quasithin.pdf, and the determinant model of 9.1.2, printed p.729.
-/

public noncomputable section
open Matrix Subgroup Representation Representation.BinaryOffender
open scoped Pointwise
namespace ClassicalOrthogonal.FourPlusMatrix.Binary

private theorem small_upper_stable (W : Submodule (ZMod 2) V) (hcard : Nat.card W = 4)
    (hstable : ∀ g ∈ (upperPairSylow : Subgroup G), ∀ v ∈ W, action g v ∈ W) :
    W ≤ point := by
  intro v hv
  have hu (a : F) : SpecialLinearGroup.transvection zero_ne_one a ∈
      SpecialLinearGroup.upperUnipotent F := ⟨Multiplicative.ofAdd a,rfl⟩
  have hrow (j : Fin 2) : v 1 j = 0 := by
    by_contra hn
    let f : F → W := fun a => ⟨action (SpecialLinearGroup.transvection zero_ne_one a,1) v-v,
      W.sub_mem (hstable _ ⟨hu a,one_mem _⟩ v hv) hv⟩
    have he (a : F) : (f a).val 0 j = a * v 1 j := by
      simp [f,action_apply,SpecialLinearGroup.transvection_coe,Matrix.mul_apply,Fin.sum_univ_two]
    have hi : Function.Injective f := by
      intro a b hab
      have hh := congrArg (fun x : W => x.val 0 j) hab
      rw [he,he] at hh
      exact mul_right_cancel₀ hn hh
    have hs := ((Nat.bijective_iff_injective_and_card f).mpr ⟨hi,by
      rw [hcard,Nat.card_eq_fintype_card]; exact SL2FourNatural.card_field⟩).2
    obtain ⟨a,ha⟩ := hs ⟨v,hv⟩
    have hh := congrArg (fun x : W => x.val 1 j) ha
    have hz : (f a).val 1 j = 0 := by
      simp [f,action_apply,SpecialLinearGroup.transvection_coe,Matrix.mul_apply,Fin.sum_univ_two]
    exact hn (hz.symm.trans hh).symm
  have hcol : v 0 0 = 0 := by
    by_contra hn
    let f : F → W := fun a => ⟨action (1,(SpecialLinearGroup.transvection zero_ne_one a)⁻¹) v-v,
      W.sub_mem (hstable _ ⟨one_mem _,(SpecialLinearGroup.upperUnipotent F).inv_mem (hu a)⟩ v hv) hv⟩
    have he (a : F) : (f a).val 0 1 = a * v 0 0 := by
      simp [f,action_apply,SpecialLinearGroup.transvection_coe,Matrix.mul_apply,Fin.sum_univ_two,mul_comm]
    have hi : Function.Injective f := by
      intro a b hab
      have hh := congrArg (fun x : W => x.val 0 1) hab
      rw [he,he] at hh
      exact mul_right_cancel₀ hn hh
    have hs := ((Nat.bijective_iff_injective_and_card f).mpr ⟨hi,by
      rw [hcard,Nat.card_eq_fintype_card]; exact SL2FourNatural.card_field⟩).2
    obtain ⟨a,ha⟩ := hs ⟨v,hv⟩
    have hh := congrArg (fun x : W => x.val 0 0) ha
    have hz : (f a).val 0 0 = 0 := by
      simp [f,action_apply,SpecialLinearGroup.transvection_coe,Matrix.mul_apply,Fin.sum_univ_two]
    exact hn (hz.symm.trans hh).symm
  refine ⟨v 0 1,?_⟩
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;> simp [pointMap,hrow,hcol]

/-- The only four-element binary subspace invariant under an inner Sylow is
its full fixed field line. -/
theorem four_space_eq_sylow_fixed (P : Sylow 2 G)
    (W : Submodule (ZMod 2) V) (hcard : Nat.card W = 4)
    (hstable : ∀ g ∈ P, ∀ v ∈ W, action g v ∈ W) :
    W = fixedSpace action (P : Subgroup G) := by
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq G upperPairSylow P
  let W' := W.map (action g⁻¹)
  have hc : Nat.card W' = 4 := by
    change Nat.card (W.map (linearAction g⁻¹).toLinearMap) = 4
    rw [Nat.card_congr ((linearAction g⁻¹).submoduleMap W).toEquiv.symm,hcard]
  have hm (a b : G) (v : V) : action (a*b) v = action a (action b v) :=
    congrArg (fun f : Module.End (ZMod 2) V => f v) (action.map_mul a b)
  have hw' : W' ≤ point := small_upper_stable W' hc (by
    intro a ha v hv
    obtain ⟨w,hw,rfl⟩ := hv
    have hconj : g*a*g⁻¹ ∈ P := by
      rw [←hg]
      change g*a*g⁻¹ ∈ MulAut.conj g • (upperPairSylow : Set G)
      exact ⟨a,ha,rfl⟩
    refine ⟨action (g*a*g⁻¹) w,hstable _ hconj w hw,?_⟩
    rw [←hm,←hm,mul_assoc g a g⁻¹,inv_mul_cancel_left])
  have hw : W ≤ fixedSpace action (P : Subgroup G) := by
    intro w hw a
    have hpoint : action g⁻¹ w ∈ point := hw' ⟨w,hw,rfl⟩
    have ha : (a : G) ∈ MulAut.conj g • (upperPairSylow : Set G) := by
      change a.val ∈ (g • upperPairSylow : Sylow 2 G)
      rw [hg]
      exact a.property
    obtain ⟨b,hb,he⟩ := ha
    change g*b*g⁻¹ = a.val at he
    have hfix := (fixedSpace_upperPair.ge hpoint) ⟨b,hb⟩
    change action b (action g⁻¹ w) = action g⁻¹ w at hfix
    change action a.val w = w
    rw [←he,hm,hm,hfix,←hm, mul_inv_cancel,action.map_one]
    rfl
  have hs := ((Nat.bijective_iff_injective_and_card (Submodule.inclusion hw)).mpr
    ⟨Submodule.inclusion_injective hw,by rw [hcard,card_fixedSpace_sylow]⟩).2
  apply le_antisymm hw
  intro w hw
  obtain ⟨v,hv⟩ := hs ⟨w,hw⟩
  have he : (v : V) = w := congrArg Subtype.val hv
  exact he ▸ v.property

/-- The fixed line of an inner Sylow is a singular coefficient line. -/
theorem sylow_fixed_field_line (P : Sylow 2 G) :
    ∃ v : V, v ≠ 0 ∧ v.det = 0 ∧ fixedSpace action (P : Subgroup G) =
      (Submodule.span F ({v} : Set V)).restrictScalars (ZMod 2) := by
  obtain ⟨g,hg⟩ := sylow_fixedSpace_conjugate_point P
  let v := action g (pointMap 1)
  have hv : v ≠ 0 := by
    intro hh
    have hz := (linearAction g).injective (hh.trans (map_zero (linearAction g)).symm)
    have he := congrArg (fun M : V => M 0 1) hz
    exact one_ne_zero he
  refine ⟨v,hv,?_,?_⟩
  · change (matrixAction g (pointMap 1)).det = 0
    rw [matrixAction_det]
    simp [pointMap,Matrix.det_fin_two]
  · rw [hg]
    ext w
    change (∃ x ∈ point, action g x = w) ↔ w ∈ Submodule.span F ({v} : Set V)
    have he (c : F) : action g (pointMap c) = c • v := by
      have hp : pointMap c = c • pointMap 1 := by
        apply Matrix.ext
        intro i j
        fin_cases i <;> fin_cases j <;> simp [pointMap]
      rw [hp]
      exact (matrixAction g).map_smul c _
    constructor
    · rintro ⟨_,⟨c,rfl⟩,rfl⟩
      exact Submodule.mem_span_singleton.mpr ⟨c,(he c).symm⟩
    · intro hw
      obtain ⟨c,rfl⟩ := Submodule.mem_span_singleton.mp hw
      exact ⟨pointMap c,⟨c,rfl⟩,he c⟩

/-- Fixing one nonzero vector of the marked Sylow line preserves that line,
including for semilinear elements of the full binary normalizer. -/
theorem normalizer_fixed_vector_preserves_sylow_line (P : Sylow 2 G)
    (W : Submodule (ZMod 2) V) (hcard : Nat.card W = 4)
    (hstable : ∀ g ∈ P, ∀ v ∈ W, action g v ∈ W)
    (t : V ≃ₗ[ZMod 2] V)
    (ht : t ∈ normalizer (linearAction.range : Set (V ≃ₗ[ZMod 2] V)))
    (w : V) (hw : w ∈ W) (hwn : w ≠ 0) (hfix : t w = w) :
    ∀ v ∈ W, t v ∈ W := by
  obtain ⟨v,hv,hvs,hline⟩ := sylow_fixed_field_line P
  have hW := (four_space_eq_sylow_fixed P W hcard hstable).trans hline
  have hmem : w ∈ Submodule.span F ({v} : Set V) := by
    have hh : w ∈ (Submodule.span F ({v} : Set V)).restrictScalars (ZMod 2) := hW ▸ hw
    exact hh
  obtain ⟨c,hc⟩ := Submodule.mem_span_singleton.mp hmem
  have hc0 : c ≠ 0 := by intro h; apply hwn; rw [←hc,h,zero_smul]
  have heq : Submodule.span F ({w} : Set V) = Submodule.span F ({v} : Set V) := by
    rw [←hc]
    exact Submodule.span_singleton_smul_eq (isUnit_iff_ne_zero.mpr hc0) v
  have hWw : W = (Submodule.span F ({w} : Set V)).restrictScalars (ZMod 2) :=
    hW.trans (congrArg (Submodule.restrictScalars (ZMod 2)) heq.symm)
  obtain ⟨σ,hσ⟩ := normalizer_semilinear t ht
  intro x hx
  rw [hWw] at hx ⊢
  obtain ⟨a,rfl⟩ := Submodule.mem_span_singleton.mp hx
  rw [hσ,hfix]
  exact Submodule.mem_span_singleton.mpr ⟨σ a,rfl⟩


/-- The small Sylow-line stabilizer calculation transfers to an original
ambient representation normalizing the full tensor component. -/
theorem normal_ambient_preserves_small_space
    {D U : Type*} [Group D] [Finite D] [AddCommGroup U] [Module (ZMod 2) U]
    (ρ : Representation (ZMod 2) D U) (N : Subgroup D) [N.Normal]
    (f : N ≃* G) (E : U ≃ₗ[ZMod 2] V)
    (he : ∀ (g : N) v, E (ρ g v) = action (f g) (E v))
    (S : Sylow 2 N) (W : Submodule (ZMod 2) U) (hc : Nat.card W = 4)
    (hs : ∀ g ∈ S, ∀ v ∈ W, ρ (g : D) v ∈ W)
    (g : D) (w : U) (hw : w ∈ W) (hwn : w ≠ 0) (hfix : ρ g w = w) :
    ∀ v ∈ W, ρ g v ∈ W := by
  let γ : Representation (ZMod 2) D V := E.conjRingEquiv.toMonoidHom.comp ρ
  let τ : D →* (V ≃ₗ[ZMod 2] V) :=
    (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) V).toMonoidHom.comp γ.asGroupHom
  have hτ (g : D) (v : U) : τ g (E v) = E (ρ g v) := by
    change E (ρ g (E.symm (E v))) = E (ρ g v)
    rw [E.symm_apply_apply]
  have hres (n : N) : τ n = linearAction (f n) := by
    apply LinearEquiv.ext
    intro v
    obtain ⟨w,rfl⟩ := E.surjective v
    rw [hτ,he]
    rfl
  have him : N.map τ = linearAction.range := by
    ext t
    constructor
    · rintro ⟨n,hn,rfl⟩
      exact ⟨f ⟨n,hn⟩,(hres ⟨n,hn⟩).symm⟩
    · rintro ⟨n,rfl⟩
      obtain ⟨n,rfl⟩ := f.surjective n
      exact ⟨n,n.property,hres n⟩
  have hnorm : τ g ∈ normalizer (linearAction.range : Set (V ≃ₗ[ZMod 2] V)) := by
    rw [←him]
    exact N.le_normalizer_map τ (mem_map_of_mem _ (le_normalizer_of_normal (mem_top g)))
  let P := S.mapSurjective (f := f.toMonoidHom) f.surjective
  let W' := W.map E.toLinearMap
  have hc' : Nat.card W' = 4 :=
    (Nat.card_congr (E.submoduleMap W).toEquiv.symm).trans hc
  have hs' : ∀ n ∈ P, ∀ v ∈ W', action n v ∈ W' := by
    intro n hn v hv
    obtain ⟨n,hn,rfl⟩ := hn
    obtain ⟨v,hv,rfl⟩ := hv
    exact ⟨ρ n v,hs n hn v hv,he n v⟩
  have hh := normalizer_fixed_vector_preserves_sylow_line P W' hc' hs' (τ g) hnorm
    (E w) ⟨w,hw,rfl⟩ (fun hz => hwn (E.injective (hz.trans E.map_zero.symm)))
    (by rw [hτ,hfix])
  intro v hv
  obtain ⟨u,hu,huv⟩ := hh (E v) ⟨v,hv,rfl⟩
  have heq : u = ρ g v := E.injective (huv.trans (hτ g v))
  exact heq ▸ hu

end ClassicalOrthogonal.FourPlusMatrix.Binary
