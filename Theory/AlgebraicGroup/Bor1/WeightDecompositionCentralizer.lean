module

public import Theory.AlgebraicGroup.Bor1.WeightBlocks
import Mathlib.Algebra.DirectSum.Module

universe u v

namespace Theory.AlgebraicGroup.Bor1

variable {k : Type u} [Field k]
variable {ι : Type v} {V : Type*} [AddCommGroup V] [Module k V]

noncomputable def blockComponent
    (E : ι → Submodule k V) (hInd : iSupIndep E)
    (hTop : ⨆ i, E i = ⊤) (i : ι) : V →ₗ[k] E i :=
  by
    classical
    exact (DirectSum.component k ι (fun j => E j) i).comp
      (hInd.linearEquiv hTop).symm.toLinearMap

theorem blockComponent_apply_of_mem
    (E : ι → Submodule k V) (hInd : iSupIndep E)
    (hTop : ⨆ i, E i = ⊤) (i : ι) {x : V} (hx : x ∈ E i) :
    blockComponent E hInd hTop i x = ⟨x, hx⟩ := by
  classical
  rw [blockComponent, LinearMap.comp_apply]
  change (DirectSum.component k ι (fun j => E j) i)
    ((hInd.linearEquiv hTop).symm x) = ⟨x, hx⟩
  rw [hInd.linearEquiv_symm_apply hTop hx]
  exact @DFinsupp.single_eq_same ι (fun j => E j) _ (Classical.decEq ι)
    i ⟨x, hx⟩

theorem blockComponent_apply_of_mem_ne
    (E : ι → Submodule k V) (hInd : iSupIndep E)
    (hTop : ⨆ i, E i = ⊤) {i j : ι} (hij : j ≠ i)
    {x : V} (hx : x ∈ E j) :
    blockComponent E hInd hTop i x = 0 := by
  classical
  rw [blockComponent, LinearMap.comp_apply]
  change (DirectSum.component k ι (fun j => E j) i)
    ((hInd.linearEquiv hTop).symm x) = 0
  rw [hInd.linearEquiv_symm_apply hTop hx]
  exact @DFinsupp.single_eq_of_ne ι (fun j => E j) _ (Classical.decEq ι)
    j i ⟨x, hx⟩ hij.symm

noncomputable def extendBlockEnd
    (E : ι → Submodule k V) (hInd : iSupIndep E)
    (hTop : ⨆ i, E i = ⊤) (i : ι) (u : Module.End k (E i)) :
    Module.End k V :=
  (E i).subtype.comp (u.comp (blockComponent E hInd hTop i))

theorem extendBlockEnd_apply_of_mem
    (E : ι → Submodule k V) (hInd : iSupIndep E)
    (hTop : ⨆ i, E i = ⊤) (i : ι) (u : Module.End k (E i))
    {x : V} (hx : x ∈ E i) :
    extendBlockEnd E hInd hTop i u x = u ⟨x, hx⟩ := by
  simp [extendBlockEnd, blockComponent_apply_of_mem E hInd hTop i hx]

theorem extendBlockEnd_apply_of_mem_ne
    (E : ι → Submodule k V) (hInd : iSupIndep E)
    (hTop : ⨆ i, E i = ⊤) {i j : ι} (hij : j ≠ i)
    (u : Module.End k (E i)) {x : V} (hx : x ∈ E j) :
    extendBlockEnd E hInd hTop i u x = 0 := by
  simp [extendBlockEnd,
    blockComponent_apply_of_mem_ne E hInd hTop hij hx]

theorem extendBlockEnd_mem_blockDiagonalEnd
    (E : ι → Submodule k V) (hInd : iSupIndep E)
    (hTop : ⨆ i, E i = ⊤) (i : ι) (u : Module.End k (E i)) :
    extendBlockEnd E hInd hTop i u ∈ blockDiagonalEnd E := by
  intro j x hx
  by_cases hji : j = i
  · subst j
    rw [extendBlockEnd_apply_of_mem E hInd hTop i u hx]
    exact (u ⟨x, hx⟩).2
  · rw [extendBlockEnd_apply_of_mem_ne E hInd hTop hji u hx]
    exact (E j).zero_mem

theorem extendBlockEnd_apply_mem
    (E : ι → Submodule k V) (hInd : iSupIndep E)
    (hTop : ⨆ i, E i = ⊤) (i : ι) (u : Module.End k (E i))
    (x : V) : extendBlockEnd E hInd hTop i u x ∈ E i := by
  change ((E i).subtype (u (blockComponent E hInd hTop i x))) ∈ E i
  exact (u (blockComponent E hInd hTop i x)).2

/-- If independent blocks span a vector space, their block-diagonal
endomorphism algebra has centralizer exactly the blockwise scalar maps.  This
is the linear-algebra calculation used for both kernels in Bor1 §5.6. -/
public theorem blockDiagonalEnd_centralizer_iff_blockwise_scalar
    (E : ι → Submodule k V) (hInd : iSupIndep E)
    (hTop : ⨆ i, E i = ⊤) (A : Module.End k V) :
    (∀ u : blockDiagonalEnd E, Commute A u.1) ↔
      ∀ i, ∃ c : k, ∀ x : V, x ∈ E i → A x = c • x := by
  constructor
  · intro hA i
    let P : Module.End k V :=
      extendBlockEnd E hInd hTop i LinearMap.id
    have hPmem : P ∈ blockDiagonalEnd E :=
      extendBlockEnd_mem_blockDiagonalEnd E hInd hTop i LinearMap.id
    have hpres : ∀ x : V, x ∈ E i → A x ∈ E i := by
      intro x hx
      have hcomm := (hA ⟨P, hPmem⟩).eq
      have hxcomm := LinearMap.congr_fun hcomm x
      have hPx : P x = x := by
        simp [P, extendBlockEnd_apply_of_mem E hInd hTop i LinearMap.id hx]
      have hPAx : P (A x) ∈ E i :=
        extendBlockEnd_apply_mem E hInd hTop i LinearMap.id (A x)
      change A (P x) = P (A x) at hxcomm
      rw [hPx] at hxcomm
      rw [hxcomm]
      exact hPAx
    let Ai : Module.End k (E i) :=
      LinearMap.codRestrict (E i) (A.domRestrict (E i))
        (fun x => hpres x.1 x.2)
    have hAi : ∀ u : Module.End k (E i), Commute Ai u := by
      intro u
      let U : Module.End k V := extendBlockEnd E hInd hTop i u
      have hUmem : U ∈ blockDiagonalEnd E :=
        extendBlockEnd_mem_blockDiagonalEnd E hInd hTop i u
      rw [commute_iff_eq]
      apply LinearMap.ext
      intro x
      apply Subtype.ext
      have hcomm := (hA ⟨U, hUmem⟩).eq
      have hxcomm := LinearMap.congr_fun hcomm x.1
      change A (U x.1) = U (A x.1) at hxcomm
      dsimp only [U] at hxcomm
      rw [extendBlockEnd_apply_of_mem E hInd hTop i u x.2,
        extendBlockEnd_apply_of_mem E hInd hTop i u (hpres x.1 x.2)] at hxcomm
      exact hxcomm
    obtain ⟨c, hc⟩ := eq_smul_id_of_commute_all Ai hAi
    refine ⟨c, ?_⟩
    intro x hx
    have hcx := LinearMap.congr_fun hc ⟨x, hx⟩
    exact congrArg Subtype.val hcx
  · intro hscalar u
    rw [commute_iff_eq]
    apply LinearMap.ext
    intro x
    have hxTop : x ∈ ⨆ i, E i := by
      rw [hTop]
      exact Submodule.mem_top
    exact Submodule.iSup_induction E (motive := fun y => A (u.1 y) = u.1 (A y)) hxTop
      (fun i y hy => by
        obtain ⟨c, hc⟩ := hscalar i
        rw [hc y hy, hc (u.1 y) (u.2 i y hy)]
        exact (u.1.map_smul c y).symm)
      (by simp)
      (fun y z hy hz => by simpa only [map_add] using congrArg₂ (· + ·) hy hz)

/-- The point-kernel calculation of Bor1 §5.6, separated from the geometric
construction of the weight blocks.  Once membership in `N` is exactly
blockwise scalar action, conjugation on block-diagonal endomorphisms has
kernel `N`. -/
public theorem blockDiagonalEnd_conjRepresentation_ker_eq_of_blockwiseScalar_iff
    {Γ : Type*} [Group Γ]
    (E : ι → Submodule k V) (hInd : iSupIndep E)
    (hTop : ⨆ i, E i = ⊤)
    (ρ : Γ →* LinearMap.GeneralLinearGroup k V)
    (σ : Γ →* Equiv.Perm ι)
    (hE : ∀ g i, Submodule.map
      ((ρ g : LinearMap.GeneralLinearGroup k V) : Module.End k V) (E i) =
        E ((σ g : Equiv ι ι) i))
    (N : Subgroup Γ)
    (hN : ∀ g : Γ,
      (∀ i, ∃ c : k, ∀ x : V, x ∈ E i →
        (ρ g : Module.End k V) x = c • x) ↔ g ∈ N) :
    (blockDiagonalEnd_conjRepresentation E ρ σ hE).ker = N := by
  apply blockDiagonalEnd_conjRepresentation_ker_eq E ρ σ hE N
  intro g
  rw [blockDiagonalEnd_centralizer_iff_blockwise_scalar E hInd hTop]
  exact hN g

/-- The point-kernel conclusion of Bor1 §5.6 from its two geometric inputs:
the distinguished subspace lies in one weight block and has stabilizer `N`,
while `N` acts by a scalar on every weight block. -/
public theorem blockDiagonalEnd_conjRepresentation_ker_eq_of_lineStabilizer
    [FiniteDimensional k V]
    {Γ : Type*} [Group Γ]
    (E : ι → Submodule k V) (hInd : iSupIndep E)
    (hTop : ⨆ i, E i = ⊤)
    (ρ : Γ →* LinearMap.GeneralLinearGroup k V)
    (σ : Γ →* Equiv.Perm ι)
    (hE : ∀ g i, Submodule.map
      ((ρ g : LinearMap.GeneralLinearGroup k V) : Module.End k V) (E i) =
        E ((σ g : Equiv ι ι) i))
    (D : Submodule k V) (iD : ι) (hD : D ≤ E iD)
    (N : Subgroup Γ)
    (hStabilizer : ∀ g : Γ,
      Submodule.map (ρ g : Module.End k V) D = D ↔ g ∈ N)
    (hNscalar : ∀ n : N, ∀ i, ∃ c : k, ∀ x : V, x ∈ E i →
      (ρ n.1 : Module.End k V) x = c • x) :
    (blockDiagonalEnd_conjRepresentation E ρ σ hE).ker = N := by
  apply blockDiagonalEnd_conjRepresentation_ker_eq_of_blockwiseScalar_iff
    E hInd hTop ρ σ hE N
  intro g
  constructor
  · intro hscalar
    apply (hStabilizer g).mp
    apply Submodule.eq_of_le_of_finrank_eq
    · rintro _ ⟨x, hx, rfl⟩
      obtain ⟨c, hc⟩ := hscalar iD
      rw [hc x (hD hx)]
      exact D.smul_mem c hx
    · exact LinearEquiv.finrank_map_eq
        (LinearMap.GeneralLinearGroup.toLinearEquiv (ρ g)) D
  · intro hg
    exact hNscalar ⟨g, hg⟩

end Theory.AlgebraicGroup.Bor1
