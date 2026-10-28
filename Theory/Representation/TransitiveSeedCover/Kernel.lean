module
public import Theory.Representation.TransitiveSeedCover

/-!
# Kernels of permutation tensor covers

An equivariant cover whose two marked slices are independent has only constant
kernel vectors. Subtracting a transposition isolates two coordinates, and full
permutation transitivity carries the marked independence to any pair. If the
first factor acts irreducibly on the seed, the kernel is therefore either zero
or the whole constant tensor subspace. The natural binary plane realizes the
full permutation group on its three nonzero vectors.

Source application: Aschbacher--Smith, The Classification of Quasithin Groups,
13.8.29(4), printed p.964. The source adapter retains the original disjoint
translate and obtains irreducibility from the literal subgroup interval.
-/

open scoped TensorProduct
open Representation QuadraticFourGroup.TensorClassification CyclicSeedTensor
namespace Representation.TransitiveSeedCover
@[expose] public noncomputable section

private theorem perm_three_ext {X : Type*} [Fintype X] [DecidableEq X]
    (hc : Fintype.card X = 3) (a b : X) (hab : a ≠ b)
    (p q : Equiv.Perm X) (ha : p a = q a) (hb : p b = q b) : p = q := by
  apply _root_.Equiv.ext
  intro x
  by_cases hxa : x = a
  · simpa [hxa] using ha
  by_cases hxb : x = b
  · simpa [hxb] using hb
  have hall : ({a,b,x} : Finset X) = Finset.univ := by
    apply Finset.eq_univ_of_card
    simp [hc,hab,Ne.symm hxa,Ne.symm hxb]
  have hmem : q.symm (p x) ∈ ({a,b,x} : Finset X) := by rw [hall]; simp
  simp only [Finset.mem_insert,Finset.mem_singleton] at hmem
  rcases hmem with h | h | h
  · have he : p x = q a := by simpa using congrArg q h
    exact (hxa (p.injective (he.trans ha.symm))).elim
  · have he : p x = q b := by simpa using congrArg q h
    exact (hxb (p.injective (he.trans hb.symm))).elim
  · simpa using congrArg q h

theorem pointAction_surjective {I : Type*} [Group I]
    (β : I →* ((Fin 2 → ZMod 2) ≃ₗ[ZMod 2] (Fin 2 → ZMod 2)))
    (hβ : Function.Surjective β) : Function.Surjective (pointAction β) := by
  intro p
  let a : PlanePoint := basePoint
  let b : PlanePoint := ⟨second,by decide⟩
  have hab : a ≠ b := by decide
  obtain ⟨r,hr,hr'⟩ := BinaryLinear.exists_linearEquiv_pair (a : Fin 2 → ZMod 2) b (p a) (p b)
    a.property b.property (p a).property (p b).property
    (fun he => hab (Subtype.ext he))
    (fun he => hab (p.injective (Subtype.ext he)))
  obtain ⟨i,hi⟩ := hβ r
  refine ⟨i,perm_three_ext planePoint_card a b hab _ p ?_ ?_⟩
  · apply Subtype.ext
    change β i a = p a
    rw [hi,hr]
  · apply Subtype.ext
    change β i b = p b
    rw [hi,hr']

variable {k K I U W X : Type*} [Field k] [Group K] [Group I]
  [AddCommGroup U] [Module k U] [AddCommGroup W] [Module k W]
  [Fintype X] [DecidableEq X]
  (ρ : Representation k (K × I) W) (σ : Representation k K U)
  (α : I →* Equiv.Perm X)
  (F : (externalTensor σ (permutation (k:=k) α)).IntertwiningMap ρ)

def coordinateCover : (X → U) →ₗ[k] W :=
  F.toLinearMap.comp (TensorProduct.piScalarRight k k U X).symm.toLinearMap

theorem coordinateCover_single (x : X) (u : U) :
    coordinateCover ρ σ α F (Pi.single x u) = F (u ⊗ₜ[k] Pi.single x 1) := by
  simp [coordinateCover,TensorProduct.piScalarRight_symm_single]

theorem coordinateCover_action (a : K) (i : I) (v : X → U) :
    coordinateCover ρ σ α F (fun x => σ a (v (α i⁻¹ x))) =
      ρ (a,i) (coordinateCover ρ σ α F v) := by
  let e := TensorProduct.piScalarRight k k U X
  have he (z : U ⊗[k] (X → k)) :
      e (externalTensor σ (permutation α) (a,i) z) =
        fun x => σ a (e z (α i⁻¹ x)) := by
    induction z using TensorProduct.induction_on with
    | zero => ext x; simp
    | tmul u w =>
      ext x
      change (permutation α i w) x • σ a u = σ a (w (α i⁻¹ x) • u)
      simp [permutation]
    | add z w hz hw =>
      simp only [map_add,hz,hw]
      ext x
      simp only [Pi.add_apply,map_add]
  have hh := IntertwiningMap.isIntertwining _ _ F (a,i) (e.symm v)
  change F (externalTensor σ (permutation α) (a,i) (e.symm v)) = ρ (a,i) (F (e.symm v)) at hh
  have hz : e.symm (fun x => σ a (v (α i⁻¹ x))) =
      externalTensor σ (permutation α) (a,i) (e.symm v) := by
    apply e.injective
    simp only [LinearEquiv.apply_symm_apply,he]
  change F (e.symm _) = ρ (a,i) (F (e.symm v))
  rw [hz,hh]

theorem coordinateCover_single_action (i : I) (x : X) (u : U) :
    coordinateCover ρ σ α F (Pi.single (α i x) u) =
      ρ (1,i) (coordinateCover ρ σ α F (Pi.single x u)) := by
  rw [←coordinateCover_action]
  congr 1
  ext y
  simp only [map_one,Module.End.one_apply,Pi.single_apply]
  have h : α i⁻¹ y = x ↔ y = α i x := by
    constructor
    · intro h; simpa using congrArg (α i) h
    · rintro rfl; simp
  simp only [h]

/-- Pairwise independence of slices propagates along the full permutation action. -/
theorem coordinateCover_pair_separation
    (hα : Function.Surjective α) (a b : X) (hab : a ≠ b)
    (hpair : ∀ u v, coordinateCover ρ σ α F (Pi.single a u) +
      coordinateCover ρ σ α F (Pi.single b v) = 0 → u = 0 ∧ v = 0)
    (x y : X) (hxy : x ≠ y) (u v : U)
    (h : coordinateCover ρ σ α F (Pi.single x u) +
      coordinateCover ρ σ α F (Pi.single y v) = 0) : u = 0 ∧ v = 0 := by
  obtain ⟨p,hp,hp'⟩ := MulAction.is_two_pretransitive_iff.mp
    (Equiv.Perm.isMultiplyPretransitive X 2) hxy hab
  obtain ⟨i,hi⟩ := hα p
  have hh := congrArg (ρ (1,i)) h
  rw [map_add,map_zero,←coordinateCover_single_action,←coordinateCover_single_action] at hh
  change p x = a at hp
  change p y = b at hp'
  rw [hi,hp,hp'] at hh
  exact hpair u v hh

/-- A kernel relation has equal coordinates: its difference with a transposition
is supported on two independent slices. -/
theorem coordinateCover_kernel_constant
    (hα : Function.Surjective α) (a b : X) (hab : a ≠ b)
    (hpair : ∀ u v, coordinateCover ρ σ α F (Pi.single a u) +
      coordinateCover ρ σ α F (Pi.single b v) = 0 → u = 0 ∧ v = 0)
    (v : X → U) (hv : coordinateCover ρ σ α F v = 0) :
    ∀ x y, v x = v y := by
  intro x y
  by_cases hxy : x = y
  · rw [hxy]
  obtain ⟨i,hi⟩ := hα (Equiv.swap x y)
  have hh := coordinateCover_action ρ σ α F 1 i v
  have hi' : α i⁻¹ = Equiv.swap x y := by rw [map_inv,hi,Equiv.swap_inv]
  simp only [map_one,Module.End.one_apply,hi',hv,map_zero] at hh
  have he : (fun z => v (Equiv.swap x y z)) - v =
      Pi.single x (v y - v x) + Pi.single y (v x - v y) := by
    ext z
    by_cases hzx : z = x
    · subst z; simp [hxy]
    by_cases hzy : z = y
    · subst z; simp [Ne.symm hxy]
    simp [Equiv.swap_apply_of_ne_of_ne hzx hzy,hzx,hzy]
  have hz : coordinateCover ρ σ α F (Pi.single x (v y - v x)) +
      coordinateCover ρ σ α F (Pi.single y (v x - v y)) = 0 := by
    rw [←map_add,←he,map_sub,hh,hv,sub_self]
  exact sub_eq_zero.mp (coordinateCover_pair_separation ρ σ α F hα a b hab hpair
    x y hxy _ _ hz).2

/-- The constant tensor subspace, without choosing a basis in the first factor. -/
def constantTensor : U →ₗ[k] U ⊗[k] (X → k) :=
  (TensorProduct.piScalarRight k k U X).symm.toLinearMap.comp LinearMap.const

theorem constantTensor_apply (u : U) :
    constantTensor (k:=k) (X:=X) u = u ⊗ₜ[k] (fun _ => 1) := by
  apply (TensorProduct.piScalarRight k k U X).injective
  simp only [constantTensor,LinearMap.comp_apply,LinearEquiv.coe_coe,
    LinearEquiv.apply_symm_apply]
  change (fun _ => u) = fun _ => (1 : k) • u
  simp only [one_smul]

/-- Irreducibility of the seed leaves exactly the zero and constant kernels. -/
theorem tensor_kernel_dichotomy
    (hα : Function.Surjective α) (a b : X) (hab : a ≠ b)
    (hpair : ∀ u v, coordinateCover ρ σ α F (Pi.single a u) +
      coordinateCover ρ σ α F (Pi.single b v) = 0 → u = 0 ∧ v = 0)
    (hmin : ∀ P : Submodule k U, (∀ g u, u ∈ P → σ g u ∈ P) → P = ⊥ ∨ P = ⊤) :
    F.ker.toSubmodule = ⊥ ∨
      F.ker.toSubmodule = LinearMap.range (constantTensor (k:=k) (U:=U) (X:=X)) := by
  let e := TensorProduct.piScalarRight k k U X
  let J := LinearMap.ker (F.toLinearMap.comp (constantTensor (k:=k) (U:=U) (X:=X)))
  have hJ (g : K) (u : U) (hu : u ∈ J) : σ g u ∈ J := by
    change coordinateCover ρ σ α F (fun _ => σ g u) = 0
    have hh := coordinateCover_action ρ σ α F g 1 (fun _ => u)
    have hz : coordinateCover ρ σ α F (fun _ => u) = 0 := hu
    simpa only [map_one,Equiv.Perm.one_apply,hz,map_zero] using hh
  have hconst (z : U ⊗[k] (X → k)) (hz : F z = 0) :
      constantTensor (k:=k) (X:=X) (e z a) = z := by
    apply e.injective
    change e (e.symm (fun _ => e z a)) = e z
    rw [e.apply_symm_apply]
    ext x
    exact coordinateCover_kernel_constant ρ σ α F hα a b hab hpair (e z)
      (by change F (e.symm (e z)) = 0; rw [e.symm_apply_apply]; exact hz) a x
  rcases hmin J hJ with hj | hj
  · left
    apply le_antisymm ?_ bot_le
    intro z hz
    have hc := hconst z hz
    have hu : e z a ∈ J := by
      change F (constantTensor (k:=k) (X:=X) (e z a)) = 0
      rw [hc]; exact hz
    rw [hj] at hu
    have hu' : e z a = 0 := hu
    rw [hu',map_zero] at hc
    exact hc.symm
  · right
    apply le_antisymm
    · intro z hz
      exact ⟨e z a,hconst z hz⟩
    · rintro z ⟨u,rfl⟩
      exact (show u ∈ J from hj ▸ Submodule.mem_top)

/-- The original seed and its specified disjoint translate supply pair separation. -/
theorem tensor_kernel_dichotomy_of_disjoint
    (hα : Function.Surjective α) (a : X) (c : I) (hc : a ≠ α c a)
    (f : σ.IntertwiningMap (ρ.comp (MonoidHom.inl K I)))
    (hf : Function.Injective f)
    (hmark : ∀ u, F (u ⊗ₜ[k] Pi.single a 1) = f u)
    (hdis : Disjoint f.range.toSubmodule (f.range.toSubmodule.map (ρ (1,c))))
    (hmin : ∀ P : Submodule k U, (∀ g u, u ∈ P → σ g u ∈ P) → P = ⊥ ∨ P = ⊤) :
    F.ker.toSubmodule = ⊥ ∨
      F.ker.toSubmodule = LinearMap.range (constantTensor (k:=k) (U:=U) (X:=X)) := by
  apply tensor_kernel_dichotomy ρ σ α F hα a (α c a) hc _ hmin
  intro u v h
  rw [coordinateCover_single_action,coordinateCover_single,coordinateCover_single,
    hmark,hmark] at h
  have hfu : f u = 0 := hdis.le_bot ⟨⟨u,rfl⟩,
    ⟨f (-v),⟨-v,rfl⟩,by rw [map_neg,map_neg]; exact (eq_neg_of_add_eq_zero_left h).symm⟩⟩
  have hu : u = 0 := hf (hfu.trans (map_zero f).symm)
  have hfv : f v = 0 := by
    rw [hfu,zero_add] at h
    have hh := congrArg (ρ (1,c⁻¹)) h
    simpa only [←Module.End.mul_apply,←map_mul,Prod.mk_mul_mk,one_mul,
      inv_mul_cancel,←Prod.one_eq_mk,map_one,Module.End.one_apply,map_zero] using hh
  exact ⟨hu,hf (hfv.trans (map_zero f).symm)⟩

end
end Representation.TransitiveSeedCover
