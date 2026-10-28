module

public import Theory.GroupTheory.SylowOuterAutomorphisms
public import Theory.GroupTheory.NormalSylowQuotientAction
public import Theory.GroupTheory.PPerfectHom

/-!
# Two-perfect actions preserving a self-normalizing Sylow subgroup

A Sylow stabilizer in the automorphism group is a p-group when the Sylow
subgroup is self-normalizing and the outer automorphism group is a p-group.
If K intersects a Sylow overgroup P in a p-group, that intersection is
Sylow in K and P-invariant. Thus a p-perfect subgroup of P acts trivially
on any equivariant quotient whose Sylow automorphism stabilizers are
p-groups.

Source application: the PSL₃(2) kernel row in Aschbacher–Smith 13.7.4(1),
printed p.937. The action theorem preserves the original quotient map.
-/

public section
open Subgroup
open scoped Pointwise

/-- Inner Sylow stabilizers and the outer quotient are both p-groups. -/
theorem MulAut.isPGroup_sylow_stabilizer_of_self_normalizing {G : Type*} [Group G] {p : ℕ} [Fact p.Prime]
    (P : Sylow p G) (hP : normalizer (P : Set G) = (P : Subgroup G))
    (ho : IsPGroup p (MulAut.Outer G)) :
    IsPGroup p (MulAction.stabilizer (MulAut G) (P : Subgroup G)) := by
  intro a
  obtain ⟨n, hn⟩ := ho (QuotientGroup.mk' (MulAut.innerSubgroup G) a.val)
  rw [← map_pow] at hn
  obtain ⟨g, hg⟩ := (QuotientGroup.eq_one_iff _).mp hn
  have hgN : g ∈ normalizer (P : Set G) := by
    apply mem_normalizer_iff_map_conj_eq.mpr
    change MulAut.conj g • (P : Subgroup G) = (P : Subgroup G)
    rw [hg]
    exact (a ^ (p ^ n)).property
  have hgP : g ∈ (P : Subgroup G) := hP ▸ hgN
  obtain ⟨m, hm⟩ := P.isPGroup' ⟨g, hgP⟩
  have hm' : g ^ (p ^ m) = 1 := congrArg Subtype.val hm
  refine ⟨n + m, ?_⟩
  apply Subtype.ext
  change (a.val) ^ (p ^ (n + m)) = 1
  rw [Nat.pow_add, pow_mul, ← hg, ← map_pow, hm', map_one]


/-- A p-perfect actor in the Sylow overgroup acts trivially on the quotient. -/
theorem Subgroup.NormalSylowQuotientAction.pPerfect_action_eq_one
    {G Q : Type*} [Group G] [Finite G] [Group Q] [Finite Q]
    {p : ℕ} [Fact p.Prime] (T : Sylow p G) (K P B : Subgroup G)
    (hPK : P ≤ normalizer (K : Set G)) (hTP : (T : Subgroup G) ≤ P)
    (hKP : IsPGroup p (K ⊓ P : Subgroup G)) (hBP : B ≤ P) (hB : IsPPerfect p B)
    (q : K →* Q) (hq : Function.Surjective q) (a : P →* MulAut Q)
    (ha : ∀ (x : P) (k : K), a x (q k) =
      q (K.normalizerMonoidHom ⟨x, hPK x.property⟩ k))
    (hQ : ∀ S : Sylow p Q,
      IsPGroup p (MulAction.stabilizer (MulAut Q) (S : Subgroup Q))) :
    ∀ b : B, a (inclusion hBP b) = 1 := by
  obtain ⟨S,hS⟩ := Subgroup.NormalSylowQuotientAction.intersection_sylow T K (hTP.trans hPK)
  have hPtwo : IsPGroup p (P.subgroupOf K) := by
    rw [← inf_subgroupOf_left P K]
    exact hKP.comap_subtype
  have hPS : P.subgroupOf K = (S : Subgroup K) :=
    S.is_maximal' hPtwo (by rw [hS]; exact comap_mono hTP)
  let R := S.mapSurjective hq
  have haR (x : P) : (R : Subgroup Q).map (a x).toMonoidHom = (R : Subgroup Q) := by
    apply eq_of_le_of_card_ge ?_ (by rw [card_map_of_injective (a x).injective])
    rintro z ⟨w,hw,rfl⟩
    obtain ⟨k,hk,rfl⟩ := hw
    change a x (q k) ∈ (R : Subgroup Q)
    rw [ha]
    apply mem_map_of_mem
    rw [← hPS] at hk ⊢
    change (x : G) * (k : G) * (x : G)⁻¹ ∈ P
    exact P.mul_mem (P.mul_mem x.property hk) (P.inv_mem x.property)
  let f : B →* MulAction.stabilizer (MulAut Q) (R : Subgroup Q) :=
    (a.comp (inclusion hBP)).codRestrict _ (fun b => haR (inclusion hBP b))
  have hf := hB.hom_eq_one_of_isPGroup (hQ R) f
  intro b
  exact congrArg Subtype.val (DFunLike.congr_fun hf b)
