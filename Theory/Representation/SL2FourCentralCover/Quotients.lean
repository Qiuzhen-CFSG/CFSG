module
public import Theory.Representation.SL2FourCentralCover.Coordinates

/-!
# Upper-unipotent calculations on every central cover

The universal cover maps onto each original perfect central extension of the
natural SL₂(4) module. Its two-displacement formula therefore proves that the
whole upper four-group's commutator space is its fixed space. Fixed-point lifting
also identifies the kernel of every nonidentity upper displacement with the
kernel of the second natural coordinate. Rank-nullity gives displacement rank
two on the original module, including nonsplit covers.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
Lemma 14.7.69(a) and the initial module calculation in 14.7.70,
printed pp.1072–1073. The ambient fusion and critical-pair deductions are not
asserted here.
-/

@[expose] public section
noncomputable section
namespace Representation.SL2FourCentralCover
open Representation.OneCohomology SL2FourNatural Matrix.SpecialLinearGroup
variable {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
  {σ : Representation (ZMod 2) SL W}
  (p : σ.IntertwiningMap naturalRepresentation) (hp : IsCover p)

private theorem projection_equivariant (g : SL) (w : W) :
    p (σ g w) = g • p w := LinearMap.congr_fun (p.isIntertwining' g) w

include p hp

/-- On every central cover, each nonidentity upper element has the full upper
subgroup's fixed space. -/
theorem quotient_upper_fixed_iff (t : F) (ht : t ≠ 0) (w : W) :
    σ (upper t) w = w ↔ p w 1 = 0 := by
  constructor
  · intro hw
    have he : action (upper t) (p w) = p w :=
      (LinearMap.congr_fun (p.isIntertwining' (upper t)) w).symm.trans (congrArg p hw)
    rw [upper_action] at he
    have h : t * p w 1 = 0 := by simpa using congrFun he 0
    exact (mul_eq_zero.mp h).resolve_left ht
  · intro hw
    apply SL2NaturalFixedLifting.fixed_lift_of_fixed_kernel σ
      p.toLinearMap.toAddMonoidHom hp.1 (projection_equivariant p)
      (fun v hv g => hp.2.1 hv g)
    change p (σ (upper t) w) = p w
    rw [p.isIntertwining]
    change action (upper t) (p w) = p w
    rw [upper_action]
    funext i
    fin_cases i <;> simp [hw]

/-- The displacement rank is two; in particular no upper involution fixes a
binary hyperplane. This holds on the original cover, not only its natural quotient. -/
theorem quotient_upper_displacement_finrank [FiniteDimensional (ZMod 2) W]
    (t : F) (ht : t ≠ 0) :
    Module.finrank (ZMod 2) (σ (upper t) - LinearMap.id).range = 2 := by
  let d := σ (upper t) - LinearMap.id
  let f : W →ₗ[ZMod 2] F := (LinearMap.proj (1 : Fin 2) : V →ₗ[ZMod 2] F).comp p.toLinearMap
  have hk : d.ker = f.ker := by
    ext w
    change σ (upper t) w - w = 0 ↔ p w 1 = 0
    rw [sub_eq_zero]
    exact quotient_upper_fixed_iff p hp t ht w
  have hs : Function.Surjective f := by
    intro a
    obtain ⟨w, hw⟩ := hp.1 ![0, a]
    exact ⟨w, congrFun hw 1⟩
  have h1 := d.finrank_range_add_finrank_ker
  have h2 := f.finrank_range_add_finrank_ker
  rw [hk] at h1
  rw [LinearMap.range_eq_top.mpr hs, finrank_top,
    SL2NaturalH1.field_finrank 2 (by rw [Nat.card_eq_fintype_card, card_field]; rfl)] at h2
  exact Nat.add_right_cancel (h1.trans h2.symm)

/-- The whole upper four-group has fixed space equal to its commutator space
on every perfect central cover. This is the module identity 14.7.69(a). -/
theorem quotient_upper_moved_eq_fixed [FiniteDimensional (ZMod 2) W] :
    SL2CentralExtension.movedSpace σ (upperUnipotent F) ⊤ =
      SL2CentralExtension.upperFixed σ := by
  have hfixed (w : W) : w ∈ SL2CentralExtension.upperFixed σ ↔ p w 1 = 0 :=
    SL2CentralExtension.mem_upperFixed_iff σ p.toLinearMap hp.1
      (projection_equivariant p) (fun v hv g => hp.2.1 hv g) w
  let C := SL2CentralExtension.movedSpace σ (upperUnipotent F) ⊤
  have hgen (t : F) (v : W) : σ (upper t) v - v ∈ C := by
    let a : upperUnipotent F := ⟨upper t,
      (mem_upperUnipotent F _).mpr ⟨t, (upper_transvection t).symm⟩⟩
    apply Submodule.mem_iSup_of_mem a
    exact ⟨⟨v, Submodule.mem_top⟩, rfl⟩
  apply le_antisymm
  · apply iSup_le
    intro a
    rintro _ ⟨w, rfl⟩
    obtain ⟨t, ht⟩ := (mem_upperUnipotent F a.val).mp a.property
    have ha : a.val = upper t := ht.symm.trans (upper_transvection t).symm
    apply (hfixed _).mpr
    change p (σ a.val w - w) 1 = 0
    rw [map_sub, p.isIntertwining, ha]
    change (action (upper t) (p w) - p w) 1 = 0
    rw [upper_action]
    simp
  · obtain ⟨q, hq, hcompat⟩ := exists_quotient p hp
    intro w hw
    obtain ⟨u, rfl⟩ := hq w
    have hu : (coordinates u).2 1 = 0 := by
      change projection u 1 = 0
      rw [← hcompat]
      exact (hfixed _).mp hw
    obtain ⟨s, t, x, y, he⟩ := fixed_is_sum_of_upper_displacements u hu
    have he' := congrArg q he
    rw [map_add, map_sub, map_sub, q.isIntertwining, q.isIntertwining] at he'
    rw [he']
    exact C.add_mem (hgen s (q x)) (hgen t (q y))

/-- For a nonidentity upper involution, its commutator space complements the
fixed kernel in the upper fixed space. This is the direct-sum calculation in
14.7.70, transported to the original central cover. -/
theorem quotient_upper_complement (t : F) (ht : t ≠ 0) :
    Disjoint (σ (upper t) - LinearMap.id).range p.toLinearMap.ker ∧
      SL2CentralExtension.upperFixed σ =
        (σ (upper t) - LinearMap.id).range ⊔ p.toLinearMap.ker := by
  let d := σ (upper t) - LinearMap.id
  have hfixed (w : W) : w ∈ SL2CentralExtension.upperFixed σ ↔ p w 1 = 0 :=
    SL2CentralExtension.mem_upperFixed_iff σ p.toLinearMap hp.1
      (projection_equivariant p) (fun v hv g => hp.2.1 hv g) w
  constructor
  · apply Submodule.disjoint_def.mpr
    intro w hw hk
    obtain ⟨v, rfl⟩ := hw
    have he : p (σ (upper t) v) = p v := by
      apply sub_eq_zero.mp
      exact (map_sub p _ _).symm.trans hk
    have hv : σ (upper t) v = v :=
      SL2NaturalFixedLifting.fixed_lift_of_fixed_kernel σ p.toLinearMap.toAddMonoidHom
        hp.1 (projection_equivariant p) (fun u hu g => hp.2.1 hu g) (upper t) v he
    change σ (upper t) v - v = 0
    rw [hv, sub_self]
  · apply le_antisymm
    · intro w hw
      have hw1 := (hfixed w).mp hw
      obtain ⟨v, hv⟩ := hp.1 ![0, p w 0 / t]
      have hd : p (d v) = p w := by
        change p (σ (upper t) v - v) = p w
        rw [map_sub, p.isIntertwining]
        change action (upper t) (p v) - p v = p w
        rw [hv, upper_action]
        funext i
        fin_cases i
        · simpa using (mul_div_cancel₀ (p w 0) ht)
        · simpa using hw1.symm
      refine Submodule.mem_sup.mpr ⟨d v, ⟨v, rfl⟩, w - d v, ?_, ?_⟩
      · change p (w - d v) = 0
        rw [map_sub, hd, sub_self]
      · abel
    · apply sup_le
      · rintro _ ⟨v, rfl⟩
        apply (hfixed _).mpr
        change p (σ (upper t) v - v) 1 = 0
        rw [map_sub, p.isIntertwining]
        change (action (upper t) (p v) - p v) 1 = 0
        rw [upper_action]
        simp
      · intro w hw g
        exact hp.2.1 hw g.val

end Representation.SL2FourCentralCover
