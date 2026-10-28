module
public import Theory.Representation.BinaryFifteenPoint.InvariantLattice
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# The original parabolic seed spans every small fifteen-point quotient

The four marked parabolic actors connect the fourteen non-base cosets.
Their differences, together with the two coset seeds, span the whole module.
Every invariant kernel of dimension at least four contains a specific vector
which eliminates the second seed. The other two kernels force the target
movement space to have dimension at least twelve.
-/
public noncomputable section
namespace BinaryFifteenPoint
open Matrix

private def difference (i : Fin 13) : Fin 15 → ZMod 2 :=
  Pi.single ⟨i.val+2,by omega⟩ 1-Pi.single 1 1

private def edge (a : Fin 4) (i : Fin 15) : Fin 15 → ZMod 2 :=
  Pi.single (BinaryEndpointInduction.transitionIndex ⟨a.val+2,by omega⟩ i) 1-
    Pi.single i 1

private def path (i : Fin 13) : List (Fin 4 × Fin 15) :=
  ![[(0,1)], [(0,1), (1,2), (2,9), (3,14), (1,4)], [(0,1), (1,2), (2,9), (3,14)], [(0,1), (1,2), (0,9), (2,10), (3,13)], [(0,1), (1,2), (0,9), (3,10)], [(0,1), (1,2), (2,9), (1,14), (0,8)], [(0,1), (1,2), (2,9), (1,14)], [(0,1), (1,2)], [(0,1), (1,2), (0,9)], [(0,1), (1,2), (3,9)], [(0,1), (1,2), (3,9), (1,11)], [(0,1), (1,2), (0,9), (2,10)], [(0,1), (1,2), (2,9)]] i

private theorem path_sum : ∀ i : Fin 13,
    ((path i).map fun p => edge p.1 p.2).sum=difference i := by decide +kernel

private theorem edge_eq (a : Fin 4) (i : Fin 15) :
    edge a i=(Pi.single i 1) ᵥ* permutationActor ⟨a.val+2,by omega⟩-Pi.single i 1 := by
  rw [Matrix.single_one_vecMul]
  funext j
  simp [edge,permutationActor_entry,Pi.single_apply,eq_comm]

private theorem differences_mem (S : Submodule (ZMod 2) (Fin 15 → ZMod 2))
    (hS : ∀ (a : Fin 4) x, x ᵥ* permutationActor ⟨a.val+2,by omega⟩-x ∈ S)
    (i : Fin 13) : difference i ∈ S := by
  rw [←path_sum i]
  apply list_sum_mem
  intro x hx
  obtain ⟨p,_,rfl⟩ := List.mem_map.mp hx
  rw [edge_eq]
  exact hS p.1 _

private theorem contains_basis (S : Submodule (ZMod 2) (Fin 15 → ZMod 2))
    (h0 : Pi.single 0 1 ∈ S) (h1 : Pi.single 1 1 ∈ S)
    (hd : ∀ i, difference i ∈ S) : S=⊤ := by
  apply top_unique
  rw [←(Pi.basisFun (ZMod 2) (Fin 15)).span_eq]
  apply Submodule.span_le.mpr
  rintro _ ⟨i,rfl⟩
  simp only [Pi.basisFun_apply]
  change Pi.single i 1 ∈ S
  by_cases hi0 : i=0
  · simpa [hi0] using h0
  by_cases hi1 : i=1
  · simpa [hi1] using h1
  have hi : 2 ≤ (i : Fin 15).val := by
    have h0' : i.val≠0 := by simpa only [Fin.ext_iff,Fin.val_zero] using hi0
    have h1' : i.val≠1 := by simpa only [Fin.ext_iff,Fin.val_one] using hi1
    omega
  let j : Fin 13 := ⟨i.val-2,by omega⟩
  have hj : (⟨j.val+2,by omega⟩ : Fin 15)=i := by apply Fin.ext; dsimp [j]; omega
  have hh := S.add_mem (hd j) h1
  simpa only [difference,hj,sub_add_cancel] using hh

private theorem connector_mem (r : Fin 8) (hr : 2≤r.val) :
    changeMatrix 4 ∈ invariantSubspace r := by
  have hb : (invariantMask r).val.testBit (coordinateBlock 4).val=true :=
    (by decide +kernel : ∀ r : Fin 8, 2≤r.val →
      (invariantMask r).val.testBit (coordinateBlock 4).val=true) r hr
  refine ⟨Pi.single 4 1,?_,?_⟩
  · intro j hj
    by_cases hj4 : j=4
    · subst j
      rw [hb] at hj
      contradiction
    · simp [hj4]
  · exact Matrix.single_one_vecMul 4 changeMatrix

private theorem connector_decomposition :
    changeMatrix 4=Pi.single 0 1+Pi.single 1 1+
      ∑ i : Fin 13, changeMatrix 4 ⟨i.val+2,by omega⟩ • difference i := by decide +kernel

/-- For every exact invariant quotient, a subspace of dimension at most
eleven containing all four marked parabolic displacements spans the target
together with the original base-coset seed. The quotient map is retained. -/
theorem parabolic_seed_span_of_finrank_le
    {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    (r : Fin 8) (f : (Fin 15 → ZMod 2) →ₗ[ZMod 2] W)
    (hf : Function.Surjective f) (hk : f.ker=invariantSubspace r)
    (S : Submodule (ZMod 2) W) (hSdim : Module.finrank (ZMod 2) S≤11)
    (hS : ∀ (a : Fin 4) x,
      f (x ᵥ* permutationActor ⟨a.val+2,by omega⟩)-f x ∈ S) :
    Submodule.span (ZMod 2) {f (Pi.single 0 1)} ⊔ S=⊤ := by
  classical
  let : Module.Finite (ZMod 2) W := Module.Finite.of_surjective f hf
  have hd (i : Fin 13) : f (difference i) ∈ S :=
    differences_mem (S.comap f) (by
      intro a x
      change f (x ᵥ* permutationActor ⟨a.val+2,by omega⟩-x) ∈ S
      rw [map_sub]
      exact hS a x) i
  let A := Submodule.span (ZMod 2) {f (Pi.single 0 1)} ⊔ S
  have h0 : f (Pi.single 0 1) ∈ A :=
    Submodule.mem_sup_left (Submodule.subset_span (by simp))
  have hdA (i : Fin 13) : f (difference i) ∈ A := Submodule.mem_sup_right (hd i)
  have hspan (h1 : f (Pi.single 1 1) ∈ A) : A=⊤ := by
    have hc : A.comap f=⊤ := contains_basis (A.comap f) h0 h1 hdA
    apply top_unique
    intro w _
    obtain ⟨x,rfl⟩ := hf w
    exact (show x ∈ A.comap f from hc.symm ▸ Submodule.mem_top)
  have hr : 2≤r.val := by
    by_contra hr
    have hrank : rowDimension r≤1 := by
      have hlt : r.val<2 := by omega
      fin_cases r <;> norm_num [rowDimension] at *
    let B := A ⊔ Submodule.span (ZMod 2) {f (Pi.single 1 1)}
    have hB : B=⊤ := by
      have hc : B.comap f=⊤ := contains_basis (B.comap f)
        (Submodule.mem_sup_left h0)
        (Submodule.mem_sup_right (Submodule.subset_span (by simp)))
        (fun i => Submodule.mem_sup_left (hdA i))
      apply top_unique
      intro w _
      obtain ⟨x,rfl⟩ := hf w
      exact (show x ∈ B.comap f from hc.symm ▸ Submodule.mem_top)
    have hdim : Module.finrank (ZMod 2) W≤13 := by
      have hBbound := Submodule.finrank_sup_add_finrank_inf_eq A
        (Submodule.span (ZMod 2) {f (Pi.single 1 1)})
      have hAbound := Submodule.finrank_sup_add_finrank_inf_eq
        (Submodule.span (ZMod 2) {f (Pi.single 0 1)}) S
      have hdim0 : Module.finrank (ZMod 2)
          (Submodule.span (ZMod 2) {f (Pi.single 0 1)})≤1 := by
        simpa using (finrank_span_le_card (R := ZMod 2) {f (Pi.single 0 1)})
      have hdim1 : Module.finrank (ZMod 2)
          (Submodule.span (ZMod 2) {f (Pi.single 1 1)})≤1 := by
        simpa using (finrank_span_le_card (R := ZMod 2) {f (Pi.single 1 1)})
      change Module.finrank (ZMod 2) B+_=_ at hBbound
      rw [hB,_root_.finrank_top] at hBbound
      dsimp only [A] at *
      omega
    have hn := f.finrank_range_add_finrank_ker
    rw [LinearMap.range_eq_top.mpr hf,_root_.finrank_top,hk,
      invariantSubspace_finrank,Module.finrank_fin_fun] at hn
    omega
  have hconnector : f (changeMatrix 4)=0 :=
    LinearMap.mem_ker.mp (hk.symm ▸ connector_mem r hr)
  have hsum : f (∑ i : Fin 13,
      changeMatrix 4 ⟨i.val+2,by omega⟩ • difference i) ∈ A := by
    rw [map_sum]
    apply A.sum_mem
    intro i _
    rw [map_smul]
    exact A.smul_mem _ (hdA i)
  have heq := congrArg f connector_decomposition
  rw [hconnector,map_add,map_add] at heq
  apply hspan
  have hh := A.sub_mem (A.sub_mem A.zero_mem hsum) h0
  have heq' : f (Pi.single 1 1)=(0-f (∑ i : Fin 13,
      changeMatrix 4 ⟨i.val+2,by omega⟩ • difference i))-f (Pi.single 0 1) := by
    apply eq_sub_iff_add_eq.mpr
    apply eq_sub_iff_add_eq.mpr
    simpa only [add_comm (f (Pi.single 1 1)) (f (Pi.single 0 1))] using heq.symm
  exact heq'.symm ▸ hh

end BinaryFifteenPoint
