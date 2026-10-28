module

public import Theory.Representation.BinaryOffender.Defs
public import Theory.Representation.DisplacementProduct
public import Theory.SpecificGroups.PSL3Two.Parabolics.MarkedProduct
public import Theory.SpecificGroups.PSL3Two.Parabolics.MarkedAutomorphisms.Residuals

/-!
# Saturation of binary parabolic displacement

For the standard point parabolic of SL₃(2), a cubic moving at least four
binary dimensions forces every elementary transvection to move two dimensions.
A two-dimensional bound on the core commutator space therefore identifies the
displacement spaces of the two transvections in each row. Opposite rows have
disjoint displacement spaces. The elementary-matrix commutator relations then
show that a core-fixed vector is fixed by both Levi generators, hence by the
full point parabolic.

This argument works on arbitrary finite-dimensional modules, including
nonsplit extensions. It requires neither global fixed-point freeness nor a
semisimplicity or dimension-six theorem. The small matrix certificates are
checked by kernel reduction. The parabolic-generation calculation follows
`Recognition.Seed.Local.Linear.Group` with the same literal matrices.

Source application: Meierfrankenfeld–Stellmacher, *Pushing up weak BN-pairs
of rank two* (1993), (4.6.12)(4), printed p.911, with the flag conventions
of p.905. The general flag and diagram transport is in the parent module.
-/

public section

open Matrix Matrix.PSL3Two Representation Representation.BinaryOffender

namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.LargeBranch.RankOne.Escape.ParabolicLinear
private abbrev x01 : SL := ⟨!![1,1,0;0,1,0;0,0,1], by decide⟩
private abbrev x02 : SL := ⟨!![1,0,1;0,1,0;0,0,1], by decide⟩
private abbrev x10 : SL := ⟨!![1,0,0;1,1,0;0,0,1], by decide⟩
private abbrev x12 : SL := ⟨!![1,0,0;0,1,1;0,0,1], by decide⟩
private abbrev x20 : SL := ⟨!![1,0,0;0,1,0;1,0,1], by decide⟩
private abbrev x21 : SL := ⟨!![1,0,0;0,1,0;0,1,1], by decide⟩

private def roots : Fin 6 → SL := ![x01, x02, x10, x12, x20, x21]
private theorem roots_conj : ∀ i : Fin 6, ∃ j : Fin 6,
    roots i = Bruhat.perm j * x01 * (Bruhat.perm j)⁻¹ := by decide +kernel
private def pairs : Fin 3 → SL := ![x01*x10, x02*x20, x12*x21]
private theorem pairs_conj : ∀ i : Fin 3, ∃ j : Fin 6,
    pairs i = Bruhat.perm j * (x12*x21) * (Bruhat.perm j)⁻¹ := by decide +kernel

private theorem cubic_test : ∀ c : SL, c ∈ pointParabolicSL → c ^ 3 = 1 → c ≠ 1 →
    ∃ i : Fin 8, c * Bruhat.upper i = Bruhat.upper i * (x12 * x21) := by
  decide +kernel

private theorem point_generation (H : Subgroup SL)
    (hQ : MarkedAutomorphisms.pointV ≤ H) (ht : x12 ∈ H) (hu : x21 ∈ H) :
    pointParabolicSL ≤ H := by
  have hs : Bruhat.perm 1 ∈ H := by
    have he : Bruhat.perm 1 = x12 * x21 * x12 := by decide
    rw [he]
    exact H.mul_mem (H.mul_mem ht hu) ht
  have hupper (i : Fin 8) : Bruhat.upper i ∈ H := by
    have he : ∀ i : Fin 8, Bruhat.upper i ∈ MarkedAutomorphisms.pointV ∨
        Bruhat.upper i * x12 ∈ MarkedAutomorphisms.pointV := by decide
    rcases he i with hi | hi
    · exact hQ hi
    · have htt : x12 * x12 = 1 := by decide
      have hh := H.mul_mem (hQ hi) ht
      simpa only [mul_assoc, htt, mul_one] using hh
  intro x hx
  obtain ⟨i, j, k, rfl⟩ := Bruhat.decomposition x
  have hj : Bruhat.perm j ∈ pointParabolicSL := by
    have hi := (show borelSL ≤ pointParabolicSL from inf_le_left) (Bruhat.upper_mem i)
    have hk := (show borelSL ≤ pointParabolicSL from inf_le_left) (Bruhat.upper_mem k)
    exact (pointParabolicSL.mul_mem_cancel_left hi).mp
      ((pointParabolicSL.mul_mem_cancel_right hk).mp hx)
  have hj' : Bruhat.perm j = 1 ∨ Bruhat.perm j = Bruhat.perm 1 := by
    have he : ∀ j : Fin 6, Bruhat.perm j ∈ pointParabolicSL →
        Bruhat.perm j = 1 ∨ Bruhat.perm j = Bruhat.perm 1 := by decide
    exact he j hj
  apply H.mul_mem (H.mul_mem (hupper i) _) (hupper k)
  rcases hj' with hj' | hj'
  · rw [hj']; exact H.one_mem
  · rw [hj']; exact hs

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
  (ρ : Representation (ZMod 2) SL V)

private def D (g : SL) := LinearMap.range (ρ g - LinearMap.id)

private theorem D_conj (a g : SL) : D ρ (g * a * g⁻¹) = (D ρ a).map (ρ g) := by
  have he : ρ (g * a * g⁻¹) - LinearMap.id =
      (ρ g).comp ((ρ a - LinearMap.id).comp (ρ g⁻¹)) := by
    ext v
    simp only [LinearMap.sub_apply, LinearMap.id_apply, LinearMap.comp_apply,
      map_sub, map_mul, Module.End.mul_apply]
    rw [ρ.self_inv_apply]
  rw [D, he, LinearMap.range_comp,
    LinearMap.range_comp_of_range_eq_top _ (LinearMap.range_eq_top.mpr (ρ.apply_bijective g⁻¹).2)]
  rfl

private theorem D_mul_le (a b : SL) : D ρ (a * b) ≤ D ρ a ⊔ D ρ b := by
  rintro _ ⟨v, rfl⟩
  have he : ρ (a*b) v - v =
      (ρ a (ρ b v) - ρ b v) + (ρ b v - v) := by
    simp only [map_mul, Module.End.mul_apply]
    abel
  change ρ (a*b) v - v ∈ _
  rw [he]
  exact Submodule.add_mem _ (Submodule.mem_sup_left ⟨_, rfl⟩)
    (Submodule.mem_sup_right ⟨_, rfl⟩)

private theorem fix_range_of_commute_disjoint (a b : SL) (hab : a*b=b*a)
    (hd : Disjoint (D ρ a) (D ρ b)) :
    ∀ v ∈ D ρ b, ρ a v = v := by
  rintro v ⟨w, rfl⟩
  apply sub_eq_zero.mp
  have hc : ρ a (ρ b w - w) - (ρ b w - w) =
      ρ b (ρ a w - w) - (ρ a w - w) := by
    simp only [map_sub]
    have he := congrArg (fun g => ρ g w) hab
    simp only [map_mul, Module.End.mul_apply] at he
    rw [he]
    abel
  exact (Submodule.disjoint_def.mp hd) _ ⟨_, rfl⟩ ⟨_, hc.symm⟩

private theorem fix_commutator (a b : SL) (h : ∀ w ∈ D ρ a, ρ b w = w)
    (v : V) (hv : ρ b v = v) : ρ (a*b*a⁻¹*b⁻¹) v = v := by
  have hv' : ρ b⁻¹ v = v := by
    have := congrArg (ρ b⁻¹) hv
    simpa only [ρ.inv_self_apply] using this.symm
  have ha : ρ a⁻¹ v - v ∈ D ρ a := by
    refine ⟨-(ρ a⁻¹ v), ?_⟩
    simp only [LinearMap.sub_apply, LinearMap.id_apply, map_neg, ρ.self_inv_apply]
    abel
  have hh := h _ ha
  rw [map_sub, hv] at hh
  have he : ρ b (ρ a⁻¹ v) = ρ a⁻¹ v := sub_left_injective hh
  simp only [map_mul, Module.End.mul_apply, hv', he, ρ.self_inv_apply]

variable [FiniteDimensional (ZMod 2) V]

omit [FiniteDimensional (ZMod 2) V] in
private theorem rank_conj (a g : SL) :
    Module.finrank (ZMod 2) (D ρ (g*a*g⁻¹)) = Module.finrank (ZMod 2) (D ρ a) := by
  rw [D_conj]
  exact (Submodule.equivMapOfInjective (ρ g) (ρ.apply_bijective g).1 (D ρ a)).finrank_eq.symm

private theorem opposite_disjoint (a b : SL)
    (ha : Module.finrank (ZMod 2) (D ρ a) = 2)
    (hb : Module.finrank (ZMod 2) (D ρ b) = 2)
    (hab : 4 ≤ Module.finrank (ZMod 2) (D ρ (a*b))) : Disjoint (D ρ a) (D ρ b) := by
  rw [disjoint_iff]
  apply Submodule.finrank_eq_zero.mp
  have hle := Submodule.finrank_mono (D_mul_le ρ a b)
  have he := Submodule.finrank_sup_add_finrank_inf_eq (D ρ a) (D ρ b)
  omega

private theorem saturated (hcore : Module.finrank (ZMod 2) (D ρ x01 ⊔ D ρ x02 : Submodule (ZMod 2) V) ≤ 2)
    (hcubic : 4 ≤ Module.finrank (ZMod 2) (D ρ (x12*x21))) :
    D ρ x01 = D ρ x02 ∧ D ρ x10 = D ρ x12 ∧ D ρ x20 = D ρ x21 ∧
      Disjoint (D ρ x01) (D ρ x10) ∧ Disjoint (D ρ x02) (D ρ x20) := by
  have hr (i : Fin 6) : Module.finrank (ZMod 2) (D ρ (roots i)) =
      Module.finrank (ZMod 2) (D ρ x01) := by
    obtain ⟨j, hj⟩ := roots_conj i
    rw [hj, rank_conj]
  have hp (i : Fin 3) : 4 ≤ Module.finrank (ZMod 2) (D ρ (pairs i)) := by
    obtain ⟨j, hj⟩ := pairs_conj i
    rw [hj, rank_conj]
    exact hcubic
  have hle := Submodule.finrank_mono (show D ρ x01 ≤ D ρ x01 ⊔ D ρ x02 from le_sup_left)
  have hmul := Submodule.finrank_mono (D_mul_le ρ x12 x21)
  have hsum := Submodule.finrank_sup_add_finrank_inf_eq (D ρ x12) (D ρ x21)
  have h3 := hr 3
  have h5 := hr 5
  change Module.finrank (ZMod 2) (D ρ x12) = _ at h3
  change Module.finrank (ZMod 2) (D ρ x21) = _ at h5
  have htwo : Module.finrank (ZMod 2) (D ρ x01) = 2 := by omega
  have hrt (i : Fin 6) : Module.finrank (ZMod 2) (D ρ (roots i)) = 2 := (hr i).trans htwo
  have h01 : D ρ x01 = D ρ x02 := by
    have h1 := Submodule.eq_of_le_of_finrank_le
      (show D ρ x01 ≤ D ρ x01 ⊔ D ρ x02 from le_sup_left) (by omega)
    have h2 := Submodule.eq_of_le_of_finrank_le
      (show D ρ x02 ≤ D ρ x01 ⊔ D ρ x02 from le_sup_right)
      (by have := hrt 1; change Module.finrank (ZMod 2) (D ρ x02) = 2 at this; omega)
    exact h1.trans h2.symm
  have h10 : D ρ x10 = D ρ x12 := by
    have he1 : Bruhat.perm 2 * x01 * (Bruhat.perm 2)⁻¹ = x10 := by decide
    have he2 : Bruhat.perm 2 * x02 * (Bruhat.perm 2)⁻¹ = x12 := by decide
    rw [← he1, ← he2, D_conj, D_conj, h01]
  have h20 : D ρ x20 = D ρ x21 := by
    have he1 : Bruhat.perm 5 * x01 * (Bruhat.perm 5)⁻¹ = x21 := by decide
    have he2 : Bruhat.perm 5 * x02 * (Bruhat.perm 5)⁻¹ = x20 := by decide
    rw [← he1, ← he2, D_conj, D_conj, h01]
  exact ⟨h01, h10, h20, opposite_disjoint ρ x01 x10 (hrt 0) (hrt 2) (hp 0),
    opposite_disjoint ρ x02 x20 (hrt 1) (hrt 4) (hp 1)⟩

private theorem levi_fixes (hcore : Module.finrank (ZMod 2) (D ρ x01 ⊔ D ρ x02 : Submodule (ZMod 2) V) ≤ 2)
    (hcubic : 4 ≤ Module.finrank (ZMod 2) (D ρ (x12*x21)))
    (v : V) (h01 : ρ x01 v = v) (h02 : ρ x02 v = v) :
    ρ x12 v = v ∧ ρ x21 v = v := by
  obtain ⟨he0, he1, he2, hd01, hd02⟩ := saturated ρ hcore hcubic
  have hd1 : Disjoint (D ρ x02) (D ρ x12) := by rw [← he0, ← he1]; exact hd01
  have hd2 : Disjoint (D ρ x01) (D ρ x21) := by rw [he0, ← he2]; exact hd02
  have hf1 := fix_range_of_commute_disjoint ρ x02 x12 (by decide) hd1
  have hf2 := fix_range_of_commute_disjoint ρ x01 x21 (by decide) hd2
  rw [← he1] at hf1
  rw [← he2] at hf2
  constructor
  · have he : x10*x02*x10⁻¹*x02⁻¹ = x12 := by decide
    rw [← he]
    exact fix_commutator ρ x10 x02 hf1 v h02
  · have he : x20*x01*x20⁻¹*x01⁻¹ = x21 := by decide
    rw [← he]
    exact fix_commutator ρ x20 x01 hf2 v h01

omit [FiniteDimensional (ZMod 2) V] in
private theorem cubic_rank (c : SL) (hc : c ∈ pointParabolicSL) (ho : orderOf c = 3)
    (hr : 4 ≤ Module.finrank (ZMod 2) (D ρ c)) :
    4 ≤ Module.finrank (ZMod 2) (D ρ (x12*x21)) := by
  have hc3 : c^3 = 1 := by simpa only [ho] using pow_orderOf_eq_one c
  have hc1 : c ≠ 1 := by intro h; simp [h] at ho
  obtain ⟨i, hi⟩ := cubic_test c hc hc3 hc1
  have he : c = Bruhat.upper i * (x12*x21) * (Bruhat.upper i)⁻¹ := by
    rw [← hi, mul_inv_cancel_right]
  rwa [he, rank_conj] at hr

private theorem standard_fixation_of_join
    (hcore : Module.finrank (ZMod 2) (D ρ x01 ⊔ D ρ x02 : Submodule (ZMod 2) V) ≤ 2)
    (c : SL) (hc : c ∈ pointParabolicSL) (ho : orderOf c = 3)
    (hr : 4 ≤ Module.finrank (ZMod 2) (D ρ c)) :
    fixedSpace ρ MarkedAutomorphisms.pointV ≤ fixedSpace ρ pointParabolicSL := by
  intro v hv
  let H : Subgroup SL := {
    carrier := {g | ρ g v = v}
    one_mem' := by simp
    mul_mem' := by
      intro g h hg hh
      change ρ (g*h) v = v
      rw [map_mul, Module.End.mul_apply, hh, hg]
    inv_mem' := by
      intro g hg
      change ρ g⁻¹ v = v
      have he := congrArg (ρ g⁻¹) hg
      simpa only [ρ.inv_self_apply] using he.symm }
  have hQ : MarkedAutomorphisms.pointV ≤ H := fun g hg => hv ⟨g, hg⟩
  have h01 : ρ x01 v = v := hv ⟨x01, by decide⟩
  have h02 : ρ x02 v = v := hv ⟨x02, by decide⟩
  obtain ⟨ht, hu⟩ := levi_fixes ρ hcore (cubic_rank ρ c hc ho hr) v h01 h02
  exact fun g => point_generation H hQ ht hu g.property

/-- The literal point-core commutator bound and cubic displacement imply
fixation by the whole point parabolic, also for nonsplit modules. -/
theorem standard_fixation
    (hcore : Module.finrank (ZMod 2)
      (Submodule.span (ZMod 2) {w | ∃ g ∈ MarkedAutomorphisms.pointV,
        ∃ v ∈ (⊤ : Submodule (ZMod 2) V), ρ g v - v = w}) ≤ 2)
    (c : SL) (hc : c ∈ pointParabolicSL) (ho : orderOf c = 3)
    (hr : 4 ≤ Module.finrank (ZMod 2) (LinearMap.range (ρ c - LinearMap.id))) :
    fixedSpace ρ MarkedAutomorphisms.pointV ≤ fixedSpace ρ pointParabolicSL := by
  apply standard_fixation_of_join ρ ?_ c hc ho hr
  apply (Submodule.finrank_mono (sup_le ?_ ?_)).trans hcore
  · rintro _ ⟨v, rfl⟩
    exact Submodule.subset_span ⟨x01, by decide, v, Submodule.mem_top, rfl⟩
  · rintro _ ⟨v, rfl⟩
    exact Submodule.subset_span ⟨x02, by decide, v, Submodule.mem_top, rfl⟩


/-- A source subspace is fixed by the full point parabolic when each
involution has displacement rank at most two and the two natural sections
put every cubic fixed vector in that subspace with codimension at least four.
The whole core displacement space need not have dimension at most two. -/
theorem standard_fixedPreimage_of_pointwise_displacement
    (Y : Submodule (ZMod 2) V)
    (hYcore : Y ≤ fixedSpace ρ MarkedAutomorphisms.pointV)
    (hpoint : ∀ t : SL, orderOf t = 2 →
      Module.finrank (ZMod 2) (LinearMap.range (ρ t - LinearMap.id)) ≤ 2)
    (c : SL) (hc : c ∈ pointParabolicSL) (ho : orderOf c = 3)
    (hker : LinearMap.ker (ρ c - LinearMap.id) ≤ Y)
    (hcodim : 4 ≤ Module.finrank (ZMod 2) (V ⧸ Y)) :
    Y ≤ fixedSpace ρ pointParabolicSL := by
  have hc3 : c ^ 3 = 1 := by simpa only [ho] using pow_orderOf_eq_one c
  have hc1 : c ≠ 1 := by intro h; simp [h] at ho
  obtain ⟨i, hi⟩ := cubic_test c hc hc3 hc1
  let q := Bruhat.upper i
  let e : SL ≃* SL := MulAut.conj q
  let σ : Representation (ZMod 2) SL V := ρ.comp e.toMonoidHom
  have hq : q ∈ pointParabolicSL :=
    (show borelSL ≤ pointParabolicSL from inf_le_left) (Bruhat.upper_mem i)
  have hec : e (x12 * x21) = c := by
    change Bruhat.upper i * (x12 * x21) * (Bruhat.upper i)⁻¹ = c
    rw [← hi, mul_inv_cancel_right]
  have hker' : LinearMap.ker (σ (x12 * x21) - LinearMap.id) ≤ Y := by
    change LinearMap.ker (ρ (e (x12 * x21)) - LinearMap.id) ≤ Y
    rwa [hec]
  have ht : orderOf (e x12) = 2 := (e.orderOf_eq x12).trans
    (orderOf_eq_prime (by decide) (by decide))
  have hu : orderOf (e x21) = 2 := (e.orderOf_eq x21).trans
    (orderOf_eq_prime (by decide) (by decide))
  have hfix := Representation.fixed_of_product_displacement_budget σ Y x12 x21 2 2
    (hpoint (e x12) ht) (hpoint (e x21) hu) hker' hcodim
  have hN : pointParabolicSL ≤ Subgroup.normalizer
      (MarkedAutomorphisms.pointV : Set SL) := by
    rw [← MarkedProduct.pointParabolic_core]
    exact pointParabolicSL.le_normalizer.trans
      (Subgroup.normalizer_le_normalizer_characteristic_image
        pointParabolicSL (pCore 2 pointParabolicSL))
  intro v hv
  let H : Subgroup SL := {
    carrier := {g | σ g v = v}
    one_mem' := by simp
    mul_mem' := by
      intro g h hg hh
      change σ (g * h) v = v
      rw [map_mul, Module.End.mul_apply, hh, hg]
    inv_mem' := by
      intro g hg
      change σ g⁻¹ v = v
      have he := congrArg (σ g⁻¹) hg
      simpa only [σ.inv_self_apply] using he.symm }
  have hQ : MarkedAutomorphisms.pointV ≤ H := by
    intro g hg
    apply (hYcore hv) ⟨e g, ?_⟩
    exact (Subgroup.mem_normalizer_iff.mp (hN hq) g).mp hg
  have hP : pointParabolicSL ≤ H := point_generation H hQ
    (sub_eq_zero.mp (hfix hv).1) (sub_eq_zero.mp (hfix hv).2)
  intro p
  have hp : e.symm p.val ∈ pointParabolicSL := by
    change q⁻¹ * p.val * q ∈ pointParabolicSL
    exact pointParabolicSL.mul_mem
      (pointParabolicSL.mul_mem (pointParabolicSL.inv_mem hq) p.property) hq
  have hpfix := hP hp
  change ρ (e (e.symm p.val)) v = v at hpfix
  change ρ p.val v = v
  simpa only [e.apply_symm_apply] using hpfix

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.LargeBranch.RankOne.Escape.ParabolicLinear
