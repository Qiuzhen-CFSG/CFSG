module
public import Theory.GroupAction.CentralCoverTwoCentral
public import Theory.GroupTheory.InnerInvolutionSylowCenter
public import Mathlib.Algebra.Group.Subgroup.Order

/-!
# Sylow-center centralizers in perfect central two-covers

The quotient Sylow center of order two detects every inner action from the
upstairs Sylow center. Faithfulness of automorphism descent identifies the
fixed subgroup of any marked nontrivial inner involution with the centralizer
of that entire center. Fixed-point lifting then identifies this subgroup with
the full preimage of the quotient involution centralizer, preserving maximality.

This supplies the central-cover step in Aschbacher--Smith 15.1.20(3d),
printed pp.1096--1097. The quotient map and the original Sylow are retained;
no splitting or triviality of the central two-kernel is assumed.
-/

public section
open Subgroup
namespace Theory.GroupTheory.SylowCenterCover
variable {L X : Type*} [Group L] [Group X] [Finite L] [Group.IsPerfect L]

private theorem two_values {H : Type*} [Group H] [Finite H]
    (hc : Nat.card H = 2) (z : H) (hz : z ≠ 1) (x : H) : x = 1 ∨ x = z := by
  classical
  by_contra h
  have hx1 : x ≠ 1 := fun hh => h (Or.inl hh)
  have hxz : x ≠ z := fun hh => h (Or.inr hh)
  let f : Fin 3 → H := ![1,z,x]
  have hf : Function.Injective f := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [f, Ne.symm]
  have hh := Nat.card_le_card_of_injective f hf
  rw [Nat.card_fin, hc] at hh
  omega

/-- In a perfect central two-cover with quotient Sylow center of order two,
a nontrivial inner involution fixing the Sylow has exactly the same fixed
group as the centralizer of the entire upstairs Sylow center. -/
theorem fixed_eq_center_centralizer
    (e : L ⧸ center L ≃* X) (hZ : IsPGroup 2 (center L))
    (P : Sylow 2 L) (α : MulAut L) (ha : α ^ 2 = 1) (hne : α ≠ 1)
    (hi : α ∈ (MulAut.conj (G := L)).range) (hfix : ∀ x ∈ P, α x = x)
    (hcard : ∀ Q : Sylow 2 X, Nat.card (center Q) = 2) :
    α.fixedSubgroup = centralizer ((center P).map (P : Subgroup L).subtype : Set L) := by
  let f := e.toMonoidHom.comp (QuotientGroup.mk' (center L))
  have hf : Function.Surjective f := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hk : f.ker = center L := by
    rw [MonoidHom.ker_comp_of_injective _ _ e.injective, QuotientGroup.ker_mk']
  let : Finite X := Finite.of_surjective f hf
  let Q := P.mapSurjective hf
  have hc (x : center P) : (⟨f (x : P), mem_map_of_mem f x.val.property⟩ : Q) ∈ center Q := by
    apply mem_center_iff.mpr
    intro y
    obtain ⟨v,hv,hv'⟩ := y.property
    apply Subtype.ext
    change (y : X) * f (x : P) = f (x : P) * (y : X)
    rw [← hv', ← f.map_mul, ← f.map_mul]
    exact congrArg f (congrArg (fun t : P => (t : L)) (mem_center_iff.mp x.property ⟨v,hv⟩))
  let c (x : center P) : center Q := ⟨⟨f (x : P), mem_map_of_mem f x.val.property⟩,hc x⟩
  obtain ⟨a,haZ,haα⟩ := MulAut.exists_center_sylow_conjugator_of_inner_involution P α ha hi hfix hZ
  let aZ : center P := ⟨a,haZ⟩
  have hca : c aZ ≠ 1 := by
    intro he
    have haz : (a : L) ∈ center L := hk ▸ congrArg (fun x : center Q => ((x : Q) : X)) he
    apply hne
    rw [← haα]
    ext x
    exact mul_inv_eq_iff_eq_mul.mpr (mem_center_iff.mp haz x).symm
  apply le_antisymm
  · intro x hx z hz
    obtain ⟨v,hv,rfl⟩ := hz
    rcases two_values (hcard Q) (c aZ) hca (c ⟨v,hv⟩) with hv1 | hva
    · have hvZ : (v : L) ∈ center L := hk ▸ congrArg (fun x : center Q => ((x : Q) : X)) hv1
      exact (mem_center_iff.mp hvZ x).symm
    · have he : f (v : L) = f (a : L) := congrArg (fun x : center Q => ((x : Q) : X)) hva
      have hconj : MulAut.conj (v : L) = α := by
        apply MulAut.centralQuotientAction_injective e
        rw [← haα, MulAut.centralQuotientAction_conj, MulAut.centralQuotientAction_conj]
        exact congrArg MulAut.conj he
      have hh : (MulAut.conj (v : L)) x = x := hconj ▸ (MulAut.mem_fixedSubgroup _ _).mp hx
      exact (mul_inv_eq_iff_eq_mul.mp hh)
  · intro x hx
    rw [MulAut.mem_fixedSubgroup, ← haα]
    exact mul_inv_eq_iff_eq_mul.mpr (hx a (mem_map_of_mem _ haZ))

/-- Maximality of the quotient two-central centralizers lifts without
removing any central two-cover. -/
theorem center_centralizer_isCoatom
    (e : L ⧸ center L ≃* X) (hZ : IsPGroup 2 (center L)) (hX : center X = ⊥)
    (P : Sylow 2 L) (α : MulAut L) (ho : orderOf α = 2)
    (hi : α ∈ (MulAut.conj (G := L)).range) (hfix : ∀ x ∈ P, α x = x)
    (hcard : ∀ Q : Sylow 2 X, Nat.card (center Q) = 2)
    (hmax : ∀ t : X, orderOf t = 2 → DoubleCoverCentralizer.TwoCentral t →
      IsCoatom (centralizer ({t} : Set X))) :
    IsCoatom (centralizer ((center P).map (P : Subgroup L).subtype : Set L)) := by
  have ha := (orderOf_eq_prime_iff.mp ho).1
  have hne := (orderOf_eq_prime_iff.mp ho).2
  rw [← fixed_eq_center_centralizer e hZ P α ha hne hi hfix hcard]
  let f := e.toMonoidHom.comp (QuotientGroup.mk' (center L))
  have hf : Function.Surjective f := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hk : f.ker = center L := by
    rw [MonoidHom.ker_comp_of_injective _ _ e.injective, QuotientGroup.ker_mk']
  obtain ⟨t,ht,htc,heq⟩ := MulAut.exists_twoCentral_model_of_central_cover f hf hk.le hX α hi ho P hfix
  have him : α.fixedSubgroup.map f = (MulAut.conj t).fixedSubgroup := by
    apply le_antisymm
    · rintro _ ⟨x,hx,rfl⟩
      rw [MulAut.mem_fixedSubgroup, ← heq, (MulAut.mem_fixedSubgroup _ _).mp hx]
    · intro y hy
      obtain ⟨x,hx⟩ := MulAut.fixedSubgroupMap_surjective_of_sylow_fixed α (MulAut.conj t) f hf hk.le heq ha P hfix ⟨y,hy⟩
      exact ⟨x,x.property,congrArg Subtype.val hx⟩
  have hker : f.ker ≤ α.fixedSubgroup := by
    obtain ⟨a,rfl⟩ := hi
    intro x hx
    rw [MulAut.mem_fixedSubgroup]
    exact mul_inv_eq_iff_eq_mul.mpr (mem_center_iff.mp (hk ▸ hx) a)
  have he : α.fixedSubgroup = (centralizer ({t} : Set X)).comap f := by
    rw [← MulAut.fixedSubgroup_conj, ← him, comap_map_eq_self hker]
  rw [he]
  exact isCoatom_comap_of_surjective hf (hmax t ht htc)
end Theory.GroupTheory.SylowCenterCover
