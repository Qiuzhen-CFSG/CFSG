module
public import Theory.GroupTheory.Signalizer.CoreQPrime
public import Theory.GroupAction.BinaryFixedFactorization

/-!
# Factoring a completed q-prime closure over a binary actor subgroup

Let K be the generated subgroup of a complete q-prime signalizer subfamily,
and let L be an original signalizer subgroup. Suppose each original value
indexed by a nonidentity element of B is the join of its mapped q-prime core
and its intersection with L, where B is an elementary binary actor subgroup
of order at least four. Let KB be the actual supremum of those mapped cores.
Then K is the ordered set product KB times K∩L.

Each mapped core lies in its q-prime value and hence in K; their supremum is
invariant. The core is normal in its original value, so the assumed join
is an ordered product. A B-actor-fixed point in K belongs to its original
value. Factoring it there gives a core point and a point of L; the latter
still belongs to K after removing the core factor. Both points lie in the
same original value, so both are fixed by that actor. Apply the binary fixed
product criterion inside K and map its set equality to the original group.
One canonical restriction of the supplied action to B on K is used throughout.

Source: Kurzweil–Stellmacher, *The Theory of Finite Groups*, §11.2.7,
step(4), printed pp.322–323, using §11.2.1. The standalone conclusion holds
for every such B and does not require a nontrivial fixed subgroup of any
additional q-group or completeness of the original family.
-/

open scoped Pointwise

namespace Theory.GroupTheory.TwoSignalizerFamily

private theorem invariant_iSup {A G : Type*} [Group A] [Group G]
    [MulDistribMulAction A G] {ι : Sort*} (V : ι → Subgroup G)
    (hV : ∀ i, IsInvariant A G (V i)) : IsInvariant A G (⨆ i, V i) := by
  have forward (a : A) (g : G) (hg : g ∈ ⨆ i, V i) : a • g ∈ ⨆ i, V i := by
    refine Subgroup.iSup_induction _ (C := fun x => a • x ∈ ⨆ i, V i) hg ?_ ?_ ?_
    · intro i x hx
      exact (show V i ≤ ⨆ i, V i from le_iSup _ i) (((hV i).invariant a x).mp hx)
    · simp
    · intro x y hx hy
      simpa only [smul_mul'] using Subgroup.mul_mem _ hx hy
  constructor
  intro a g
  exact ⟨forward a g, fun hg => by simpa only [inv_smul_smul] using forward a⁻¹ (a • g) hg⟩

public theorem qPrime_closure_set_mul_eq
    {A G : Type*} [Group A] [Finite A] [Group G] [Finite G]
    [IsElementaryAbelian 2 A] [MulDistribMulAction A G]
    (θ : TwoSignalizerFamily A G) (q : ℕ) [Fact q.Prime]
    (L : Subgroup G) (hL : θ.IsSignalizerSubgroup L)
    (hcomplete : (θ.qPrime q).IsComplete) (B : Subgroup A) (hB : 4 ≤ Nat.card B)
    (hfactor : ∀ a : {a : A // a ≠ 1}, a.val ∈ B →
      θ.subgroup a = (pPrimeCore q (θ.subgroup a)).map (θ.subgroup a).subtype ⊔
        (θ.subgroup a ⊓ L)) :
    let K := (θ.qPrime q).closure
    let KB := ⨆ (a : {a : A // a ≠ 1}) (_ : a.val ∈ B),
      (pPrimeCore q (θ.subgroup a)).map (θ.subgroup a).subtype
    (K : Set G) = (KB : Set G) * ((K ⊓ L : Subgroup G) : Set G) := by
  classical
  let K := (θ.qPrime q).closure
  let C (a : {a : A // a ≠ 1}) :=
    (pPrimeCore q (θ.subgroup a)).map (θ.subgroup a).subtype
  let KB : Subgroup G := ⨆ (a : {a : A // a ≠ 1}) (_ : a.val ∈ B), C a
  change (K : Set G) = (KB : Set G) * ((K ⊓ L : Subgroup G) : Set G)
  have hcoreK (a : {a : A // a ≠ 1}) : C a ≤ K :=
    (θ.core_le_qPrime_subgroup q a).trans ((θ.qPrime q).le_closure a)
  have hKBK : KB ≤ K := iSup₂_le fun a _ => hcoreK a
  have hKsig : θ.IsSignalizerSubgroup K := IsSignalizerSubgroup.of_qPrime q hcomplete
  have hKBInv : IsInvariant A G KB :=
    invariant_iSup _ fun a => invariant_iSup _ fun _ => θ.core_invariant q a
  let _ : IsElementaryAbelian 2 B :=
    { toIsMulCommutative := inferInstance
      exponent_dvd_p := by
        apply Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr
        intro b
        apply Subtype.ext
        exact Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
          (IsElementaryAbelian.exponent_dvd_p 2 A) b.val }
  let _ : IsInvariant B G K := ⟨fun b x => hKsig.2.2.1.invariant b.val x⟩
  let _ : IsInvariant B G KB := ⟨fun b x => hKBInv.invariant b.val x⟩
  let _ : IsInvariant B G L := ⟨fun b x => hL.2.2.1.invariant b.val x⟩
  let X := KB.subgroupOf K
  let Y := L.subgroupOf K
  let _ : IsInvariant B K X := isInvariant_subgroupOf KB K
  let _ : IsInvariant B K Y := isInvariant_subgroupOf L K
  have hfixed (b : B) (hb : b ≠ 1) :
      (FixedPoints.subgroup (Subgroup.zpowers b) K : Set K) =
        ((X ⊓ FixedPoints.subgroup (Subgroup.zpowers b) K : Subgroup K) : Set K) *
        ((Y ⊓ FixedPoints.subgroup (Subgroup.zpowers b) K : Subgroup K) : Set K) := by
    let a : {a : A // a ≠ 1} := ⟨b.val, fun heq => hb (Subtype.ext heq)⟩
    have haB : a.val ∈ B := b.property
    apply Set.Subset.antisymm
    · intro x hx
      have hxact : a.val • (x : G) = (x : G) :=
        congrArg Subtype.val (hx ⟨b, Subgroup.mem_zpowers b⟩)
      have hxvalue : (x : G) ∈ θ.subgroup a :=
        hKsig.2.2.2 a ⟨x.property, fun z => smul_eq_self_of_mem_zpowers z.property hxact⟩
      have hCvalue : C a ≤ θ.subgroup a := Subgroup.map_subtype_le _
      let _ : ((C a).subgroupOf (θ.subgroup a)).Normal :=
        Subgroup.normal_subgroupOf_of_le_normalizer (θ.value_le_normalizer_core q a)
      have hsup : (C a).subgroupOf (θ.subgroup a) ⊔
          (θ.subgroup a ⊓ L).subgroupOf (θ.subgroup a) = ⊤ := by
        rw [← Subgroup.subgroupOf_sup hCvalue inf_le_left, ← hfactor a haB,
          Subgroup.subgroupOf_self]
      obtain ⟨y, hy, z, hz, hyz⟩ := Subgroup.mem_sup_of_normal_left.mp
        (show (⟨(x : G), hxvalue⟩ : θ.subgroup a) ∈
          (C a).subgroupOf (θ.subgroup a) ⊔
            (θ.subgroup a ⊓ L).subgroupOf (θ.subgroup a) from by rw [hsup]; trivial)
      have hyK : (y : G) ∈ K := hcoreK a hy
      have hyzG : (y : G) * (z : G) = (x : G) := congrArg Subtype.val hyz
      have hzK : (z : G) ∈ K := by
        have h := K.mul_mem (K.inv_mem hyK) x.property
        simpa only [← hyzG, inv_mul_cancel_left] using h
      have hfix (w : θ.subgroup a) (hwK : (w : G) ∈ K) :
          (⟨(w : G), hwK⟩ : K) ∈ FixedPoints.subgroup (Subgroup.zpowers b) K := by
        intro t
        apply smul_eq_self_of_mem_zpowers t.property
        apply Subtype.ext
        exact θ.le_fixed a w.property ⟨a.val, Subgroup.mem_zpowers a.val⟩
      have hyKB : (y : G) ∈ KB :=
        (show C a ≤ KB from le_iSup_of_le a (le_iSup_of_le haB le_rfl)) hy
      exact Set.mem_mul.mpr ⟨⟨y, hyK⟩, ⟨hyKB, hfix y hyK⟩,
        ⟨z, hzK⟩, ⟨hz.2, hfix z hzK⟩, Subtype.ext hyzG⟩
    · rintro x ⟨y, hy, z, hz, rfl⟩
      exact (FixedPoints.subgroup (Subgroup.zpowers b) K).mul_mem hy.2 hz.2
  have hproduct := set_mul_eq_univ_of_binary_fixed_factorization hB hcomplete.1 X Y hfixed
  apply Set.Subset.antisymm
  · intro x hx
    have hxnative : (⟨x, hx⟩ : K) ∈ (X : Set K) * (Y : Set K) := by
      rw [hproduct]
      trivial
    obtain ⟨y, hy, z, hz, hyz⟩ := Set.mem_mul.mp hxnative
    exact Set.mem_mul.mpr ⟨y, hy, z, ⟨z.property, hz⟩, congrArg Subtype.val hyz⟩
  · rintro x ⟨y, hy, z, hz, rfl⟩
    exact K.mul_mem (hKBK hy) hz.1

end Theory.GroupTheory.TwoSignalizerFamily
