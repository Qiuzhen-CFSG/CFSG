module
public import Theory.GroupTheory.Signalizer.Defs
public import Theory.GroupAction.TwoGroupFixedImage
public import Mathlib.GroupTheory.QuotientGroup.Basic

/-!
# Images and quotients of binary signalizer families

An equivariant homomorphism maps an odd solvable signalizer family for a
two-group actor to a signalizer family on its target. Signalizer subgroups
and complete families map to signalizer subgroups and complete families.
The quotient construction uses the caller's actual action on G/N and an
explicit equivariance equation for the quotient map.

If the normal kernel N is a signalizer subgroup, completeness of the
quotient family implies completeness upstairs. This is Kurzweil–Stellmacher,
*The Theory of Finite Groups*, §11.1.3–4, printed pp.306–307, specialized to
binary actors. No noncyclicity or rank hypothesis is needed for these results.

For balance in the image family, lift fixed points within the relevant odd
signalizer value using the two-group fixed-image theorem. To lift completeness,
restrict the quotient map to the actual generated subgroup. Its kernel embeds
in N, so the kernel and image give its odd order and solvability. A fixed
element has the same quotient image as an element of the corresponding
signalizer value; their ratio is a fixed element of N and belongs to that
same value. This argument avoids requiring N to lie in the generated subgroup.
The family constructors retain private bodies and expose their subgroup and
closure equations through public theorems.
-/

namespace Theory.GroupTheory.TwoSignalizerFamily

variable {A G H : Type*} [Group A] [Group G] [Group H] [Finite G]
    [MulDistribMulAction A G] [MulDistribMulAction A H]

omit [Finite G] in
private theorem invariant_map (f : G →* H)
    (hequiv : ∀ a : A, ∀ g : G, f (a • g) = a • f g)
    (U : Subgroup G) (hU : IsInvariant A G U) : IsInvariant A H (U.map f) := by
  have forward (a : A) (y : H) (hy : y ∈ U.map f) : a • y ∈ U.map f := by
    obtain ⟨x, hx, rfl⟩ := hy
    exact ⟨a • x, (hU.invariant a x).mp hx, hequiv a x⟩
  constructor
  intro a y
  exact ⟨forward a y, fun hy => by simpa using forward a⁻¹ (a • y) hy⟩

public def map (θ : TwoSignalizerFamily A G) (hA : IsPGroup 2 A)
    (f : G →* H) (hequiv : ∀ a : A, ∀ g : G, f (a • g) = a • f g) :
    TwoSignalizerFamily A H where
  subgroup a := (θ.subgroup a).map f
  odd a := (θ.odd a).of_dvd_nat ((θ.subgroup a).card_map_dvd f)
  solvable a := by
    let _ := θ.solvable a
    exact Group.isSolvable_of_surjective (f.subgroupMap_surjective (θ.subgroup a))
  invariant a := invariant_map f hequiv (θ.subgroup a) (θ.invariant a)
  le_fixed a := by
    rintro y ⟨x, hx, rfl⟩ b
    exact (hequiv b x).symm.trans (congrArg f (θ.le_fixed a hx b))
  balance a b := by
    let _ : IsInvariant (Subgroup.zpowers b.val) G (θ.subgroup a) :=
      ⟨fun c x => (θ.invariant a).invariant c x⟩
    rw [← Subgroup.map_inf_fixedPoints_eq_of_odd (hA.to_subgroup (Subgroup.zpowers b.val))
      f (fun c x => hequiv c x) (θ.subgroup a) (θ.odd a)]
    exact Subgroup.map_mono (θ.balance a b)

@[simp] public theorem map_subgroup (θ : TwoSignalizerFamily A G) (hA : IsPGroup 2 A)
    (f : G →* H) (hequiv : ∀ a : A, ∀ g : G, f (a • g) = a • f g)
    (a : {a : A // a ≠ 1}) :
    (θ.map hA f hequiv).subgroup a = (θ.subgroup a).map f := by rfl

public theorem map_closure (θ : TwoSignalizerFamily A G) (hA : IsPGroup 2 A)
    (f : G →* H) (hequiv : ∀ a : A, ∀ g : G, f (a • g) = a • f g) :
    (θ.map hA f hequiv).closure = θ.closure.map f := by
  simp only [closure, map_subgroup, Subgroup.map_iSup]

public theorem IsSignalizerSubgroup.map {θ : TwoSignalizerFamily A G} {U : Subgroup G}
    (hU : θ.IsSignalizerSubgroup U) (hA : IsPGroup 2 A)
    (f : G →* H) (hequiv : ∀ a : A, ∀ g : G, f (a • g) = a • f g) :
    (θ.map hA f hequiv).IsSignalizerSubgroup (U.map f) := by
  let _ := hU.2.1
  refine ⟨hU.1.of_dvd_nat (U.card_map_dvd f),
    Group.isSolvable_of_surjective (f.subgroupMap_surjective U),
    invariant_map f hequiv U hU.2.2.1, ?_⟩
  intro a
  let _ : IsInvariant (Subgroup.zpowers a.val) G U :=
    ⟨fun b x => hU.2.2.1.invariant b x⟩
  rw [map_subgroup, ← Subgroup.map_inf_fixedPoints_eq_of_odd
    (hA.to_subgroup (Subgroup.zpowers a.val)) f (fun b x => hequiv b x) U hU.1]
  exact Subgroup.map_mono (hU.2.2.2 a)

public theorem IsComplete.map {θ : TwoSignalizerFamily A G} (hθ : θ.IsComplete)
    (hA : IsPGroup 2 A) (f : G →* H)
    (hequiv : ∀ a : A, ∀ g : G, f (a • g) = a • f g) :
    (θ.map hA f hequiv).IsComplete := by
  change (θ.map hA f hequiv).IsSignalizerSubgroup _
  rw [map_closure]
  exact IsSignalizerSubgroup.map hθ hA f hequiv

public def quotient (θ : TwoSignalizerFamily A G) (hA : IsPGroup 2 A)
    (N : Subgroup G) [N.Normal] [MulDistribMulAction A (G ⧸ N)]
    (hequiv : ∀ a : A, ∀ g : G, QuotientGroup.mk' N (a • g) =
      a • QuotientGroup.mk' N g) : TwoSignalizerFamily A (G ⧸ N) :=
  θ.map hA (QuotientGroup.mk' N) hequiv

@[simp] public theorem quotient_subgroup (θ : TwoSignalizerFamily A G) (hA : IsPGroup 2 A)
    (N : Subgroup G) [N.Normal] [MulDistribMulAction A (G ⧸ N)]
    (hequiv : ∀ a : A, ∀ g : G, QuotientGroup.mk' N (a • g) =
      a • QuotientGroup.mk' N g) (a : {a : A // a ≠ 1}) :
    (θ.quotient hA N hequiv).subgroup a = (θ.subgroup a).map (QuotientGroup.mk' N) := by rfl

public theorem quotient_closure (θ : TwoSignalizerFamily A G) (hA : IsPGroup 2 A)
    (N : Subgroup G) [N.Normal] [MulDistribMulAction A (G ⧸ N)]
    (hequiv : ∀ a : A, ∀ g : G, QuotientGroup.mk' N (a • g) =
      a • QuotientGroup.mk' N g) :
    (θ.quotient hA N hequiv).closure = θ.closure.map (QuotientGroup.mk' N) :=
  θ.map_closure hA (QuotientGroup.mk' N) hequiv

public theorem isComplete_of_quotient (θ : TwoSignalizerFamily A G) (hA : IsPGroup 2 A)
    (N : Subgroup G) [N.Normal] [MulDistribMulAction A (G ⧸ N)]
    (hequiv : ∀ a : A, ∀ g : G, QuotientGroup.mk' N (a • g) =
      a • QuotientGroup.mk' N g)
    (hN : θ.IsSignalizerSubgroup N)
    (hquot : (θ.quotient hA N hequiv).IsComplete) : θ.IsComplete := by
  let f := (QuotientGroup.mk' N).comp θ.closure.subtype
  have hrange : f.range = (θ.quotient hA N hequiv).closure := by
    rw [θ.quotient_closure hA N hequiv]
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨x, x.property, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨⟨x, hx⟩, rfl⟩
  have hker : f.ker = N.subgroupOf θ.closure := by
    ext x
    simp [f, MonoidHom.mem_ker, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
  have hkerodd : Odd (Nat.card f.ker) := by
    rw [hker]
    exact hN.1.of_dvd_nat (Subgroup.card_comap_dvd_of_injective N
      θ.closure.subtype θ.closure.subtype_injective)
  have hodd : Odd (Nat.card θ.closure) := by
    have hcard : Nat.card θ.closure = Nat.card f.range * Nat.card f.ker := by
      rw [← Subgroup.index_ker, Subgroup.index_mul_card]
    rw [hcard, hrange]
    exact hquot.1.mul hkerodd
  let _ : Group.IsSolvable N := hN.2.1
  let _ : Group.IsSolvable f.ker := by
    rw [hker]
    let k : N.subgroupOf θ.closure →* N :=
      { toFun := fun x => ⟨x.val.val, x.property⟩
        map_one' := rfl
        map_mul' := fun _ _ => rfl }
    exact Group.isSolvable_of_isSolvable_injective (f := k)
      (by
        intro x y h
        have hval : x.val.val = y.val.val := congrArg (fun z : N => (z : G)) h
        exact Subtype.ext (Subtype.ext hval))
  let _ : Group.IsSolvable f.range := by rw [hrange]; exact hquot.2.1
  have hsolv : Group.IsSolvable θ.closure :=
    Group.isSolvable_of_ker_le_range f.ker.subtype f.rangeRestrict (by
      intro x hx
      exact ⟨⟨x, by exact congrArg Subtype.val hx⟩, rfl⟩)
  refine ⟨hodd, hsolv, θ.closure_invariant, ?_⟩
  intro a x hx
  have hbar : QuotientGroup.mk' N x ∈ (θ.quotient hA N hequiv).subgroup a := by
    apply hquot.2.2.2 a
    constructor
    · rw [θ.quotient_closure hA N hequiv]
      exact ⟨x, hx.1, rfl⟩
    · intro b
      exact (hequiv b x).symm.trans (congrArg (QuotientGroup.mk' N) (hx.2 b))
  rw [θ.quotient_subgroup hA N hequiv a] at hbar
  obtain ⟨y, hy, heq⟩ := hbar
  have hmemN : x * y⁻¹ ∈ N := by
    simpa only [div_eq_mul_inv] using QuotientGroup.eq_iff_div_mem.mp heq.symm
  have hfixed : x * y⁻¹ ∈ FixedPoints.subgroup (Subgroup.zpowers a.val) G :=
    (FixedPoints.subgroup (Subgroup.zpowers a.val) G).mul_mem hx.2
      ((FixedPoints.subgroup (Subgroup.zpowers a.val) G).inv_mem (θ.le_fixed a hy))
  have hxy := hN.2.2.2 a ⟨hmemN, hfixed⟩
  simpa only [inv_mul_cancel_right] using (θ.subgroup a).mul_mem hxy hy

public theorem quotient_isComplete_iff (θ : TwoSignalizerFamily A G) (hA : IsPGroup 2 A)
    (N : Subgroup G) [N.Normal] [MulDistribMulAction A (G ⧸ N)]
    (hequiv : ∀ a : A, ∀ g : G, QuotientGroup.mk' N (a • g) =
      a • QuotientGroup.mk' N g) (hN : θ.IsSignalizerSubgroup N) :
    (θ.quotient hA N hequiv).IsComplete ↔ θ.IsComplete := by
  exact ⟨θ.isComplete_of_quotient hA N hequiv hN,
    fun hθ => hθ.map hA (QuotientGroup.mk' N) hequiv⟩

end Theory.GroupTheory.TwoSignalizerFamily
