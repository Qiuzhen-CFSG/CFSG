module

public import Theory.GroupTheory.SpecificGroups.EvenCliffordSix.CoreExtension
public import Theory.GroupTheory.SpecificGroups.EvenCliffordSix.SignedAction
public import Theory.GroupTheory.SpecificGroups.EvenCliffordSix.Quotients
import Theory.GroupTheory.CentralBinaryKernelSquares
import Theory.Representation.BinaryPermutation.SixCoreExtension.Residual.Transport
import Theory.AtlasPort.OtherSporadic.Algebra.BinaryCocycleSplitting

/-!
# Recognition of marked central extensions of the six-letter core

A normalized section supplies a binary cocycle. Its diagonal is an A₆-invariant
quadratic function. The configurations of three overlapping pairs and three
disjoint pairs show that its values at weights two and four are respectively
one and zero, since its value at the constant vector is one. The two A₆ orbits
then identify every square with the even Clifford square formula.

The difference of the section cocycle and the Clifford cocycle is symmetric
with zero diagonal. Splitting this elementary abelian extension produces a
multiplicative equivalence over the original core projection. A final linear
sign change preserves that projection and the kernel, and matches the chosen
volume element exactly. No quaternion factors or nonabelianity are assumed.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, I.2.2(6),
printed pp.410 and 412 (PDF pp.421 and 423). This proves the intrinsic group
recognition used for the cyclic-four M₂₂ cover; comparison of the lifting
A₆ actions is a separate question.
-/

@[expose] public section
namespace EvenCliffordSix.CoreExtension
open BinaryPermutation Atlas.Algebra

variable {G : Type*} [Group G] (d : CoreExtension G)

private noncomputable def sec : V → G := fun v => if v = 0 then 1 else (d.surjective (Multiplicative.ofAdd v)).choose

private lemma sec_proj (v : V) : d.projection (sec d v) = Multiplicative.ofAdd v := by
  by_cases hv : v = 0
  · subst v; simp [sec]
  · simp [sec, hv, (d.surjective (Multiplicative.ofAdd v)).choose_spec]

private lemma sec_zero : sec d 0 = 1 := by simp [sec]

private noncomputable def signEmbed : Multiplicative F →* G where
  toFun a := d.sign ^ a.toAdd.val
  map_one' := by simp
  map_mul' a b := by
    change d.sign ^ (a.toAdd + b.toAdd).val = d.sign ^ a.toAdd.val * d.sign ^ b.toAdd.val
    rw [ZMod.val_add]
    have hla : a.toAdd.val < 2 := a.toAdd.isLt
    have hlb : b.toAdd.val < 2 := b.toAdd.isLt
    have ha : a.toAdd.val = 0 ∨ a.toAdd.val = 1 := by omega
    have hb : b.toAdd.val = 0 ∨ b.toAdd.val = 1 := by omega
    rcases ha with ha | ha <;> rcases hb with hb | hb
    · simp [ha, hb]
    · simp [ha, hb]
    · simp [ha, hb]
    · rw [ha, hb]
      have hpow := pow_orderOf_eq_one d.sign
      rw [d.sign_order] at hpow
      simpa [pow_two] using hpow.symm

private lemma signEmbed_zero : signEmbed d (Multiplicative.ofAdd (0 : F)) = 1 := by simp [signEmbed]
private lemma signEmbed_one : signEmbed d (Multiplicative.ofAdd (1 : F)) = d.sign := by
  change d.sign ^ 1 = d.sign
  simp

private lemma signEmbed_injective : Function.Injective (signEmbed d) := by
  intro a b hab
  have ha0 : a.toAdd = 0 ∨ a.toAdd = 1 := by
    have hla : a.toAdd.val < 2 := a.toAdd.isLt
    have hav : a.toAdd.val = 0 ∨ a.toAdd.val = 1 := by omega
    rcases hav with h | h
    · exact Or.inl ((ZMod.val_eq_zero _).mp h)
    · exact Or.inr ((ZMod.val_eq_one (by decide) _).mp h)
  have hb0 : b.toAdd = 0 ∨ b.toAdd = 1 := by
    have hlb : b.toAdd.val < 2 := b.toAdd.isLt
    have hbv : b.toAdd.val = 0 ∨ b.toAdd.val = 1 := by omega
    rcases hbv with h | h
    · exact Or.inl ((ZMod.val_eq_zero _).mp h)
    · exact Or.inr ((ZMod.val_eq_one (by decide) _).mp h)
  rcases ha0 with rfl | rfl <;> rcases hb0 with rfl | rfl
  · rfl
  · exfalso
    have hs : d.sign ≠ 1 := by
      intro hs
      have := d.sign_order
      rw [hs, orderOf_one] at this
      norm_num at this
    apply hs
    change signEmbed d (Multiplicative.ofAdd 0) = signEmbed d (Multiplicative.ofAdd 1) at hab
    rw [signEmbed_zero, signEmbed_one] at hab
    exact (hs hab.symm).elim
  · exfalso
    have hs : d.sign ≠ 1 := by
      intro hs
      have := d.sign_order
      rw [hs, orderOf_one] at this
      norm_num at this
    apply hs
    change signEmbed d (Multiplicative.ofAdd 1) = signEmbed d (Multiplicative.ofAdd 0) at hab
    rw [signEmbed_zero, signEmbed_one] at hab
    exact (hs hab).elim
  · rfl

private lemma kernel_eq_sign (x : G) (hx : x ∈ d.projection.ker) : x = 1 ∨ x = d.sign := by
  classical
  rw [d.kernel] at hx
  have hpow := pow_orderOf_eq_one d.sign
  rw [d.sign_order] at hpow
  have hfin : IsOfFinOrder d.sign := isOfFinOrder_iff_pow_eq_one.mpr ⟨2, by decide, hpow⟩
  rw [hfin.mem_zpowers_iff_mem_range_orderOf, d.sign_order] at hx
  obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hx
  have hn' : n = 0 ∨ n = 1 := by
    have hnlt : n < 2 := Finset.mem_range.mp hn
    omega
  rcases hn' with rfl | rfl <;> simp

private noncomputable def delta (u v : V) : F := by
  classical exact if h : sec d u * sec d v * (sec d (u + v))⁻¹ = 1 then 0 else 1

private lemma delta_eq (u v : V) : signEmbed d (Multiplicative.ofAdd (delta d u v)) =
    sec d u * sec d v * (sec d (u + v))⁻¹ := by
  have hk : sec d u * sec d v * (sec d (u + v))⁻¹ ∈ d.projection.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_mul, map_inv, sec_proj, sec_proj, sec_proj]
    change Multiplicative.ofAdd (u + v) * (Multiplicative.ofAdd (u + v))⁻¹ = 1
    simp
  by_cases h : sec d u * sec d v * (sec d (u + v))⁻¹ = 1
  · rw [show delta d u v = 0 by simp [delta, h], signEmbed_zero, h]
  · have hs : sec d u * sec d v * (sec d (u + v))⁻¹ = d.sign := (kernel_eq_sign d _ hk).resolve_left h
    rw [show delta d u v = 1 by simp [delta, h], signEmbed_one, hs]

private lemma factor_mem_kernel (u v : V) :
    sec d u * sec d v * (sec d (u + v))⁻¹ ∈ d.projection.ker := by
  rw [MonoidHom.mem_ker, map_mul, map_mul, map_inv, sec_proj, sec_proj, sec_proj]
  change Multiplicative.ofAdd (u + v) * (Multiplicative.ofAdd (u + v))⁻¹ = 1
  simp

private lemma delta_cocycle (u v w : V) :
    delta d u v + delta d (u + v) w =
      delta d v w + delta d u (v + w) := by
  apply Multiplicative.toAdd.injective
  apply (signEmbed_injective d)
  change signEmbed d (Multiplicative.ofAdd (delta d u v + delta d (u + v) w)) =
    signEmbed d (Multiplicative.ofAdd (delta d v w + delta d u (v + w)))
  change signEmbed d (Multiplicative.ofAdd (delta d u v) *
      Multiplicative.ofAdd (delta d (u + v) w)) =
    signEmbed d (Multiplicative.ofAdd (delta d v w) *
      Multiplicative.ofAdd (delta d u (v + w)))
  rw [map_mul, map_mul, delta_eq d u v, delta_eq d (u + v) w,
    delta_eq d v w, delta_eq d u (v + w)]
  have hc : Commute
      (sec d v * sec d w * (sec d (v + w))⁻¹) (sec d u) :=
    (Subgroup.mem_center_iff.mp (d.kernel_central (factor_mem_kernel d v w)) _).symm
  calc
    (sec d u * sec d v * (sec d (u + v))⁻¹) *
        (sec d (u + v) * sec d w * (sec d (u + v + w))⁻¹) =
      sec d u * sec d v * sec d w * (sec d (u + v + w))⁻¹ := by group
    _ = (sec d v * sec d w * (sec d (v + w))⁻¹) *
        (sec d u * sec d (v + w) * (sec d (u + (v + w)))⁻¹) := by
      rw [show u + v + w = u + (v + w) by abel]
      symm
      calc
        (sec d v * sec d w * (sec d (v + w))⁻¹) *
            (sec d u * sec d (v + w) * (sec d (u + (v + w)))⁻¹) =
          ((sec d v * sec d w * (sec d (v + w))⁻¹) * sec d u) *
            sec d (v + w) * (sec d (u + (v + w)))⁻¹ := by group
        _ = (sec d u * (sec d v * sec d w * (sec d (v + w))⁻¹)) *
            sec d (v + w) * (sec d (u + (v + w)))⁻¹ := by rw [hc.eq]
        _ = sec d u * sec d v * sec d w * (sec d (u + (v + w)))⁻¹ := by group

private lemma delta_zero_left (v : V) : delta d 0 v = 0 := by
  simp [delta, sec_zero d]

private lemma delta_zero_right (u : V) : delta d u 0 = 0 := by
  simp [delta, sec_zero d]

private lemma square_eq_of_projection_eq {x y : G}
    (hxy : d.projection x = d.projection y) : x ^ 2 = y ^ 2 := by
  apply MonoidHom.square_eq_of_map_eq_of_central_binary_kernel d.projection d.kernel_central
  intro z hz
  rcases kernel_eq_sign d z hz with rfl | rfl
  · simp
  · have hpow := pow_orderOf_eq_one d.sign
    rw [d.sign_order] at hpow
    exact hpow
  exact hxy

private lemma delta_square (v : V) :
    signEmbed d (Multiplicative.ofAdd (delta d v v)) = (sec d v) ^ 2 := by
  rw [delta_eq d v v]
  have hvv : v + v = 0 := by
    apply Subtype.ext
    funext i
    exact CharTwo.add_self_eq_zero _
  rw [hvv, sec_zero d]
  simp only [inv_one, mul_one]
  rw [pow_two]

private lemma delta_invariant (a : A) (v : V) :
    delta d (coreRepresentation (Fin 6) a.val v) (coreRepresentation (Fin 6) a.val v) =
      delta d v v := by
  apply Multiplicative.toAdd.injective
  apply signEmbed_injective d
  change signEmbed d (Multiplicative.ofAdd
      (delta d (coreRepresentation (Fin 6) a.val v) (coreRepresentation (Fin 6) a.val v))) =
    signEmbed d (Multiplicative.ofAdd (delta d v v))
  rw [delta_square d, delta_square d]
  have he : d.projection (d.actor a (sec d v)) =
      Multiplicative.ofAdd (coreRepresentation (Fin 6) a.val v) := by
    apply Multiplicative.toAdd.injective
    have he0 := d.equivariant a (sec d v)
    rw [sec_proj] at he0
    exact he0
  have he' : d.projection (sec d (coreRepresentation (Fin 6) a.val v)) =
      d.projection (d.actor a (sec d v)) := (sec_proj d _).trans he.symm
  have hs : (sec d (coreRepresentation (Fin 6) a.val v)) ^ 2 =
      (d.actor a (sec d v)) ^ 2 := square_eq_of_projection_eq d he'
  have hsign : d.actor a d.sign = d.sign := by
    apply (kernel_eq_sign d _ (by
      rw [MonoidHom.mem_ker]
      apply Multiplicative.toAdd.injective
      have hk : d.projection d.sign = 1 := by
        apply (MonoidHom.mem_ker).mp
        rw [d.kernel]
        exact ⟨1, by simp⟩
      have hkto : (d.projection d.sign).toAdd = 0 := by rw [hk]; rfl
      rw [d.equivariant]
      rw [hkto]
      simp)).resolve_left
    intro h
    have hne : d.sign ≠ 1 := by
      intro h1
      have ho := d.sign_order
      rw [h1, orderOf_one] at ho
      norm_num at ho
    apply (hne ?_).elim
    exact (d.actor a).injective (h.trans (d.actor a).map_one.symm)
  rw [hs]
  have hak (z : G) (hz : z ∈ d.projection.ker) : d.actor a z = z := by
    rcases kernel_eq_sign d z hz with rfl | rfl
    · simp
    · exact hsign
  rw [← map_pow]
  exact hak (sec d v ^ 2) (d.square_mem_kernel _)

private lemma delta_volume : delta d volumeVector volumeVector = 1 := by
  apply Multiplicative.toAdd.injective
  apply signEmbed_injective d
  change signEmbed d (Multiplicative.ofAdd (delta d volumeVector volumeVector)) =
    signEmbed d (Multiplicative.ofAdd 1)
  rw [delta_square d]
  have he : d.projection (d.volume) = Multiplicative.ofAdd volumeVector := d.volume_projection
  have hs : (sec d volumeVector) ^ 2 = d.volume ^ 2 :=
    square_eq_of_projection_eq d (sec_proj d volumeVector |>.trans he.symm)
  rw [hs, d.volume_square, signEmbed_one]

private def modelLift (v : V) : Model := ⟨0, v⟩

private lemma model_q_volume : cocycle volumeVector.val volumeVector.val = 1 := by
  have h := congrArg Model.sign (volume_sq)
  rw [square] at h
  simpa [involution, centralSign, EvenCliffordSix.volume, volumeVector] using h

private lemma model_q_invariant (a : A) (v : V) :
    cocycle (coreRepresentation (Fin 6) a.val v).val
      (coreRepresentation (Fin 6) a.val v).val = cocycle v.val v.val := by
  have hs : (action a (modelLift v)) ^ 2 = action a ((modelLift v) ^ 2) := by
    rw [map_pow]
  have hfix : action a ((modelLift v) ^ 2) = (modelLift v) ^ 2 := by
    rw [square, action_centralSign]
  have hsq := hs.trans hfix
  have hsign := congrArg Model.sign hsq
  rw [square (action a (modelLift v)), square (modelLift v)] at hsign
  change cocycle (action a (modelLift v)).vector.val (action a (modelLift v)).vector.val =
    cocycle v.val v.val at hsign
  have hv : (action a (modelLift v)).vector =
      coreRepresentation (Fin 6) a.val v := by
    apply Subtype.ext
    rfl
  rw [hv] at hsign
  exact hsign

private lemma lift_mul (u v : V) :
    sec d u * sec d v = signEmbed d (Multiplicative.ofAdd (delta d u v)) * sec d (u + v) := by
  rw [delta_eq d u v]
  group

private noncomputable def beta (u v : V) : F := delta d u v + delta d v u

private lemma add_self_cancel (a b : F) : b = (a + b) + a := by
  calc
    b = 0 + b := by rw [zero_add]
    _ = (a + a) + b := by rw [CharTwo.add_self_eq_zero, zero_add]
    _ = (a + b) + a := by abel

private lemma beta_add_left (u v w : V) :
    beta d (u + v) w = beta d u w + beta d v w := by
  have h1 := delta_cocycle d u v w
  have h2 := delta_cocycle d w u v
  have h1' : delta d (u + v) w =
      delta d u v + delta d v w + delta d u (v + w) := by
    calc
      delta d (u + v) w =
          (delta d u v + delta d (u + v) w) + delta d u v := by
            exact add_self_cancel _ _
      _ = (delta d v w + delta d u (v + w)) + delta d u v := by rw [h1]
      _ = _ := by abel
  have h2' : delta d w (u + v) =
      delta d w u + delta d (u + w) v + delta d u v := by
    calc
      delta d w (u + v) =
          (delta d u v + delta d w (u + v)) + delta d u v := by
            exact add_self_cancel _ _
      _ = (delta d w u + delta d (w + u) v) + delta d u v := by rw [h2]
      _ = _ := by rw [show w + u = u + w by abel]
  simp only [beta]
  rw [h1', h2']
  have h3 := delta_cocycle d u w v
  rw [show w + v = v + w by abel] at h3
  have h3' : delta d u (v + w) + delta d (u + w) v =
      delta d u w + delta d w v := by
    calc
      delta d u (v + w) + delta d (u + w) v =
          (delta d u w + delta d (u + w) v) +
            (delta d u w + delta d u (v + w)) := by
              rw [show delta d u (v + w) + delta d (u + w) v =
                (delta d (u + w) v + delta d u (v + w)) by ac_rfl]
              abel_nf
              rw [two_smul, CharTwo.add_self_eq_zero, add_zero]
      _ = (delta d w v + delta d u (v + w)) +
            (delta d u w + delta d u (v + w)) := by rw [h3]
      _ = _ := by
        calc
          _ = (delta d u w + delta d w v) +
                (delta d u (v + w) + delta d u (v + w)) := by abel
          _ = _ := by rw [CharTwo.add_self_eq_zero, add_zero]
  calc
    (delta d u v + delta d v w + delta d u (v + w)) +
        (delta d w u + delta d (u + w) v + delta d u v) =
      (delta d u v + delta d u v) + (delta d v w + delta d w u) +
        (delta d u (v + w) + delta d (u + w) v) := by abel
    _ = delta d u w + delta d w u + delta d v w + delta d w v := by
      rw [h3']
      simp only [CharTwo.add_self_eq_zero, zero_add]
      abel
    _ = beta d u w + beta d v w := by simp [beta]; abel

private lemma q_add (u v : V) :
    delta d (u + v) (u + v) = delta d u u + delta d v v + beta d u v := by
  have hvv : v + v = 0 := by
    apply Subtype.ext
    funext i
    exact CharTwo.add_self_eq_zero _
  have hvuv : v + (u + v) = u := by
    calc
      _ = u + (v + v) := by abel
      _ = u := by rw [hvv, add_zero]
  have hv : delta d (u + v) v = delta d u v + delta d v v := by
    have he := delta_cocycle d u v v
    rw [hvv, delta_zero_right, add_zero] at he
    calc
      delta d (u + v) v =
          (delta d u v + delta d (u + v) v) + delta d u v := add_self_cancel _ _
      _ = delta d v v + delta d u v := by rw [he]
      _ = _ := add_comm _ _
  have hvu : delta d v (u + v) = delta d v v + delta d v u := by
    have he := delta_cocycle d v u v
    rw [add_comm v u, hv] at he
    calc
      delta d v (u + v) =
          (delta d u v + delta d v (u + v)) + delta d u v := add_self_cancel _ _
      _ = (delta d v u + (delta d u v + delta d v v)) + delta d u v := by rw [← he]
      _ = (delta d v v + delta d v u) + (delta d u v + delta d u v) := by abel
      _ = _ := by rw [CharTwo.add_self_eq_zero, add_zero]
  have h1 := delta_cocycle d u v (u + v)
  rw [hvuv, hvu] at h1
  calc
    delta d (u + v) (u + v) =
        (delta d u v + delta d (u + v) (u + v)) + delta d u v := add_self_cancel _ _
    _ = (delta d v v + delta d v u + delta d u u) + delta d u v := by rw [h1]
    _ = _ := by unfold beta; abel

private lemma q_cube (u v w : V) :
    delta d (u + v + w) (u + v + w) + delta d (u + v) (u + v) +
      delta d (u + w) (u + w) + delta d (v + w) (v + w) +
        delta d u u + delta d v v + delta d w w = 0 := by
  rw [q_add, q_add, q_add, q_add, beta_add_left]
  abel_nf
  simp only [two_smul, show (4 : ℤ) = 2 + 2 from rfl, add_smul,
    CharTwo.add_self_eq_zero]

-- Identify invariant quadratic functions using two small three-dimensional configurations.
private def pr : V := BinaryPermutation.SixCoreExtension.pair
private def fr : V := BinaryPermutation.SixCoreExtension.four
private def p2 : V := ⟨![1,0,1,0,0,0], by rw [mem_core]; decide⟩
private def p3 : V := ⟨![1,0,0,1,0,0], by rw [mem_core]; decide⟩
private def p4 : V := ⟨![0,0,1,1,0,0], by rw [mem_core]; decide⟩
private def p5 : V := ⟨![0,0,0,0,1,1], by rw [mem_core]; decide⟩

private def mover (i j k l : Fin 6) (hij : i ≠ j) (hkl : k ≠ l) : A :=
  ⟨Equiv.swap i j * Equiv.swap k l, by simp [Equiv.Perm.mem_alternatingGroup, hij, hkl]⟩

private lemma q_invariant_configuration (q : V → F)
    (hi : ∀ a : A, ∀ v, q (coreRepresentation (Fin 6) a.val v) = q v) :
    q p2 = q pr ∧ q p3 = q pr ∧ q (pr + p2) = q pr ∧
      q (pr + p3) = q pr ∧ q (p2 + p3) = q pr ∧ q (pr + p2 + p3) = q fr ∧
      q p4 = q pr ∧ q p5 = q pr ∧ q (pr + p4) = q fr ∧
      q (pr + p5) = q fr ∧ q (p4 + p5) = q fr := by
  have transport (a : A) (v w : V)
      (h : coreRepresentation (Fin 6) a.val v = w) : q w = q v := h ▸ hi a v
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact transport (mover 1 2 4 5 (by decide) (by decide)) pr p2 (by decide)
  · exact transport (mover 1 3 4 5 (by decide) (by decide)) pr p3 (by decide)
  · exact transport (mover 0 2 4 5 (by decide) (by decide)) pr (pr + p2) (by decide)
  · exact transport (mover 0 3 4 5 (by decide) (by decide)) pr (pr + p3) (by decide)
  · exact transport (mover 0 2 1 3 (by decide) (by decide)) pr (p2 + p3) (by decide)
  · exact transport (mover 0 4 1 5 (by decide) (by decide)) fr (pr + p2 + p3) (by decide)
  · exact transport (mover 0 2 1 3 (by decide) (by decide)) pr p4 (by decide)
  · exact transport (mover 0 4 1 5 (by decide) (by decide)) pr p5 (by decide)
  · exact transport (mover 0 4 1 5 (by decide) (by decide)) fr (pr + p4) (by decide)
  · exact transport (mover 0 2 1 3 (by decide) (by decide)) fr (pr + p5) (by decide)
  · exact transport (1 : A) fr (p4 + p5) (by decide)

private lemma q_values (q : V → F)
    (hi : ∀ a : A, ∀ v, q (coreRepresentation (Fin 6) a.val v) = q v)
    (hc : ∀ u v w, q (u + v + w) + q (u + v) + q (u + w) + q (v + w) +
      q u + q v + q w = 0) (hvol : q volumeVector = 1) :
    q pr = 1 ∧ q fr = 0 := by
  obtain ⟨h2,h3,h12,h13,h23,h123,h4,h5,h14,h15,h45⟩ := q_invariant_configuration q hi
  have hf := hc pr p2 p3
  rw [h123,h12,h13,h23,h2,h3] at hf
  have hf0 : q fr = 0 := by
    convert hf using 1
    abel_nf
    simp only [show (6 : ℤ) = 2 + 2 + 2 from rfl, add_smul, two_smul,
      CharTwo.add_self_eq_zero, add_zero]
  refine ⟨?_, hf0⟩
  have hp := hc pr p4 p5
  rw [show pr + p4 + p5 = volumeVector by decide, hvol, h14,h15,h45,h4,h5,hf0] at hp
  have hp' : 1 + q pr = 0 := by
    convert hp using 1
    abel_nf
    simp only [show (3 : ℤ) = 2 + 1 from rfl, add_smul, two_smul,
      CharTwo.add_self_eq_zero, one_smul, zero_add]
  exact (eq_neg_of_add_eq_zero_right hp').trans (by decide)

private lemma diagonal_eq_model (v : V) : delta d v v = cocycle v.val v.val := by
  have hi := delta_invariant d
  have hp := q_values (fun v => delta d v v) hi (q_cube d) (delta_volume d)
  by_cases hn : coreToNatural (Fin 6) v = 0
  · have hc : v.val ∈ constants (Fin 6) :=
      (Submodule.Quotient.mk_eq_zero _).mp (congrArg Subtype.val hn)
    obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp hc
    have hcases : a = 0 ∨ a = 1 := (by decide : ∀ a : F, a = 0 ∨ a = 1) a
    rcases hcases with rfl | rfl
    · rw [zero_smul] at ha
      have hv : v = 0 := Subtype.ext ha.symm
      subst v
      rw [delta_zero_left]
      exact (cocycle_zero_left _).symm
    · rw [one_smul] at ha
      have hv : v = volumeVector := Subtype.ext (ha.symm.trans (by decide))
      subst v
      rw [delta_volume, model_q_volume]
  · obtain ⟨a, ha | ha⟩ := SixCoreExtension.exists_pair_or_four_transport v hn
    · rw [← ha, hi, model_q_invariant]
      exact hp.1.trans (by decide)
    · rw [← ha, hi, model_q_invariant]
      exact hp.2.trans (by decide)

private lemma beta_eq_model (u v : V) :
    beta d u v = cocycle u.val v.val + cocycle v.val u.val := by
  have h := q_add d u v
  simp only [diagonal_eq_model] at h
  change cocycle (u.val + v.val) (u.val + v.val) = _ at h
  rw [cocycle_add_left, cocycle_add_right, cocycle_add_right] at h
  have hh := congrArg (fun a : F => a + cocycle u.val u.val + cocycle v.val v.val) h
  have hc (a b c : F) : a + b + c + a + b = c := by
    calc
      _ = (a + a) + (b + b) + c := by abel
      _ = c := by rw [CharTwo.add_self_eq_zero, CharTwo.add_self_eq_zero, zero_add, zero_add]
  calc
    beta d u v = _ := (hc _ _ _).symm
    _ = _ := hh.symm
    _ = _ := by
      abel_nf
      simp only [two_smul, CharTwo.add_self_eq_zero, zero_add, add_zero]

private lemma exists_correction : ∃ η : V → F, η 0 = 0 ∧
    ∀ u v, η (u + v) + η u + η v = delta d u v + cocycle u.val v.val := by
  apply binary_cocycle_exists_correction
  · intro v
    rw [delta_zero_left, show (0 : V).val = 0 from rfl, cocycle_zero_left, add_zero]
  · intro u v
    have he := beta_eq_model d u v
    unfold beta at he
    have h := congrArg (fun a : F => a + delta d v u + cocycle u.val v.val) he
    calc
      delta d u v + cocycle u.val v.val =
          (delta d u v + delta d v u) + delta d v u + cocycle u.val v.val := by
        abel_nf
        simp only [two_smul, CharTwo.add_self_eq_zero, add_zero]
      _ = _ := h
      _ = delta d v u + cocycle v.val u.val := by
        abel_nf
        simp only [two_smul, CharTwo.add_self_eq_zero, zero_add]
  · intro v
    rw [diagonal_eq_model]
    exact CharTwo.add_self_eq_zero _
  · intro u v w
    change (delta d u v + cocycle u.val v.val) +
      (delta d (u + v) w + cocycle (u.val + v.val) w.val) +
      (delta d v w + cocycle v.val w.val) +
      (delta d u (v + w) + cocycle u.val (v.val + w.val)) = 0
    rw [cocycle_add_left, cocycle_add_right]
    calc
      _ = (delta d u v + delta d (u + v) w) +
            (delta d v w + delta d u (v + w)) +
            (cocycle u.val v.val + cocycle u.val w.val + cocycle v.val w.val) +
            (cocycle u.val v.val + cocycle u.val w.val + cocycle v.val w.val) := by abel
      _ = 0 := by rw [delta_cocycle, CharTwo.add_self_eq_zero]; simp [add_assoc, CharTwo.add_self_eq_zero]

private lemma signEmbed_central (a : F) : signEmbed d (Multiplicative.ofAdd a) ∈ Subgroup.center G :=
  (Subgroup.center G).pow_mem d.sign_central _

private lemma signEmbed_projection (a : F) : d.projection (signEmbed d (Multiplicative.ofAdd a)) = 1 := by
  have hk : d.projection d.sign = 1 := by
    apply MonoidHom.mem_ker.mp
    rw [d.kernel]
    exact ⟨1, by simp⟩
  change d.projection (d.sign ^ a.val) = 1
  rw [map_pow, hk, one_pow]

private lemma signEmbed_add (a b : F) :
    signEmbed d (Multiplicative.ofAdd (a + b)) =
      signEmbed d (Multiplicative.ofAdd a) * signEmbed d (Multiplicative.ofAdd b) :=
  (signEmbed d).map_mul _ _

private noncomputable def coordinateHom (η : V → F) (h0 : η 0 = 0)
    (hη : ∀ u v, η (u + v) + η u + η v = delta d u v + cocycle u.val v.val) :
    Model →* G where
  toFun x := signEmbed d (Multiplicative.ofAdd (x.sign + η x.vector)) * sec d x.vector
  map_one' := by
    change signEmbed d (Multiplicative.ofAdd (0 + η 0)) * sec d 0 = 1
    rw [h0, add_zero, signEmbed_zero, sec_zero, one_mul]
  map_mul' x y := by
    change signEmbed d (Multiplicative.ofAdd
        ((x.sign + y.sign + cocycle x.vector.val y.vector.val) + η (x.vector + y.vector))) *
          sec d (x.vector + y.vector) =
      (signEmbed d (Multiplicative.ofAdd (x.sign + η x.vector)) * sec d x.vector) *
        (signEmbed d (Multiplicative.ofAdd (y.sign + η y.vector)) * sec d y.vector)
    have hcomm := Subgroup.mem_center_iff.mp
      (signEmbed_central d (y.sign + η y.vector)) (sec d x.vector)
    have he : (x.sign + y.sign + cocycle x.vector.val y.vector.val) +
        η (x.vector + y.vector) =
      ((x.sign + η x.vector) + (y.sign + η y.vector)) + delta d x.vector y.vector := by
      have hh := hη x.vector y.vector
      calc
        _ = (x.sign + y.sign) + cocycle x.vector.val y.vector.val +
            ((η (x.vector + y.vector) + η x.vector + η y.vector) +
              (η x.vector + η y.vector)) := by
          abel_nf
          simp only [two_smul, CharTwo.add_self_eq_zero, add_zero]
        _ = (x.sign + y.sign) + cocycle x.vector.val y.vector.val +
            ((delta d x.vector y.vector + cocycle x.vector.val y.vector.val) +
              (η x.vector + η y.vector)) := by rw [hh]
        _ = _ := by
          abel_nf
          simp only [two_smul, CharTwo.add_self_eq_zero, zero_add]
    rw [he, signEmbed_add, signEmbed_add]
    rw [mul_assoc _ _ (sec d (x.vector + y.vector)), ← lift_mul]
    calc
      _ = signEmbed d (Multiplicative.ofAdd (x.sign + η x.vector)) *
          (signEmbed d (Multiplicative.ofAdd (y.sign + η y.vector)) * sec d x.vector) * sec d y.vector := by group
      _ = _ := by rw [← hcomm]; group

private lemma coordinateHom_projection (η : V → F) (h0 : η 0 = 0) (hη)
    (x : Model) : d.projection (coordinateHom d η h0 hη x) = EvenCliffordSix.projection x := by
  change d.projection (signEmbed d (Multiplicative.ofAdd (x.sign + η x.vector)) * sec d x.vector) = _
  rw [map_mul, signEmbed_projection, sec_proj, one_mul]
  rfl

private lemma coordinateHom_injective (η : V → F) (h0 : η 0 = 0) (hη) :
    Function.Injective (coordinateHom d η h0 hη) := by
  intro x y he
  have hv := congrArg d.projection he
  rw [coordinateHom_projection, coordinateHom_projection] at hv
  have hv' : x.vector = y.vector := congrArg Multiplicative.toAdd hv
  apply Model.ext
  · change signEmbed d (Multiplicative.ofAdd (x.sign + η x.vector)) * sec d x.vector =
      signEmbed d (Multiplicative.ofAdd (y.sign + η y.vector)) * sec d y.vector at he
    rw [hv', mul_left_inj] at he
    have hs := congrArg Multiplicative.toAdd (signEmbed_injective d he)
    exact add_right_cancel hs
  · exact hv'

/-- A linear sign change fixes the literal projection and the kernel. -/
private def signShift (a : F) : Model ≃* Model where
  toFun x := ⟨x.sign + a * x.vector.val 0, x.vector⟩
  invFun x := ⟨x.sign + a * x.vector.val 0, x.vector⟩
  left_inv x := by
    apply Model.ext
    · change (x.sign + a * x.vector.val 0) + a * x.vector.val 0 = x.sign
      rw [add_assoc, CharTwo.add_self_eq_zero, add_zero]
    · rfl
  right_inv x := by
    apply Model.ext
    · change (x.sign + a * x.vector.val 0) + a * x.vector.val 0 = x.sign
      rw [add_assoc, CharTwo.add_self_eq_zero, add_zero]
    · rfl
  map_mul' x y := by
    apply Model.ext
    · change x.sign + y.sign + cocycle x.vector.val y.vector.val +
        a * (x.vector.val 0 + y.vector.val 0) =
      (x.sign + a * x.vector.val 0) + (y.sign + a * y.vector.val 0) +
        cocycle x.vector.val y.vector.val
      ring
    · rfl

/-- Intrinsic recognition over the literal augmentation core, retaining the
specified kernel generator and the chosen lift of the constant vector. -/
theorem exists_markedEquiv [Finite G] : ∃ E : G ≃* Model,
    (∀ x, EvenCliffordSix.projection (E x) = d.projection x) ∧
      E d.sign = involution ∧ E d.volume = EvenCliffordSix.volume := by
  obtain ⟨η,h0,hη⟩ := exists_correction d
  let f := coordinateHom d η h0 hη
  have hf : Function.Bijective f :=
    (coordinateHom_injective d η h0 hη).bijective_of_nat_card_le (by rw [EvenCliffordSix.card, d.card])
  let e : Model ≃* G := MulEquiv.ofBijective f hf
  have he (x : Model) : d.projection (e x) = EvenCliffordSix.projection x := coordinateHom_projection d η h0 hη x
  have hei (x : G) : EvenCliffordSix.projection (e.symm x) = d.projection x := by
    rw [← he, e.apply_symm_apply]
  have hsign : e involution = d.sign := by
    change signEmbed d (Multiplicative.ofAdd (1 + η 0)) * sec d 0 = d.sign
    rw [h0, add_zero, sec_zero, mul_one, signEmbed_one]
  have hvector : (e.symm d.volume).vector = volumeVector := by
    exact congrArg Multiplicative.toAdd ((hei d.volume).trans d.volume_projection)
  let a := (e.symm d.volume).sign
  refine ⟨e.symm.trans (signShift a), ?_, ?_, ?_⟩
  · intro x
    exact hei x
  · change signShift a (e.symm d.sign) = involution
    rw [← hsign, e.symm_apply_apply]
    apply Model.ext
    · change 1 + a * (0 : F) = 1
      simp
    · rfl
  · change signShift a (e.symm d.volume) = EvenCliffordSix.volume
    apply Model.ext
    · change a + a * (e.symm d.volume).vector.val 0 = 0
      rw [hvector, volumeVector_apply, mul_one, CharTwo.add_self_eq_zero]
    · exact hvector


/-- The square formula is derived from the extension data alone. -/
theorem square_formula (x : G) :
    x ^ 2 = d.sign ^ (cocycle (d.projection x).toAdd.val (d.projection x).toAdd.val).val := by
  have he : d.projection x = d.projection (sec d (d.projection x).toAdd) :=
    (sec_proj d _).symm
  rw [square_eq_of_projection_eq d he, ← delta_square, diagonal_eq_model]
  rfl

/-- A chosen recognition equivalence with all three marks fixed. -/
noncomputable def modelEquiv [Finite G] : G ≃* Model := d.exists_markedEquiv.choose

@[simp] theorem modelEquiv_projection [Finite G] (x : G) :
    EvenCliffordSix.projection (d.modelEquiv x) = d.projection x :=
  d.exists_markedEquiv.choose_spec.1 x

@[simp] theorem modelEquiv_sign [Finite G] : d.modelEquiv d.sign = involution :=
  d.exists_markedEquiv.choose_spec.2.1

@[simp] theorem modelEquiv_volume [Finite G] : d.modelEquiv d.volume = EvenCliffordSix.volume :=
  d.exists_markedEquiv.choose_spec.2.2

end EvenCliffordSix.CoreExtension
