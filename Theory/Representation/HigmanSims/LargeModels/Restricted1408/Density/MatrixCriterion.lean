module

public import Theory.Representation.HigmanSims.LargeModels.Restricted1408.Density.CyclicKernel

/-!
# Matrix form of the cyclic-kernel criterion

Transport the matrix subalgebra to coordinate endomorphisms. A cyclic
right-kernel vector and a cyclic left annihilator give precisely the kernel,
cyclicity and separation hypotheses of `CyclicKernel.end_top`. This
adapter uses the ordinary column action and the literal row action; it
requires neither a group representation nor an irreducibility premise.
-/

public section
namespace Representation.CyclicKernel
open Matrix
variable {F ι : Type*} [Field F] [Fintype ι] [DecidableEq ι] [Nonempty ι]

theorem matrix_top (P : Subalgebra F (Matrix ι ι F))
    (S : Matrix ι ι F) (v lam : ι → F)
    (hS : S ∈ P) (hSv : S.mulVec v = 0)
    (hker : ∀ w, S.mulVec w = 0 → ∃ c : F, w = c • v)
    (hcol : ∀ w, ∃ M ∈ P, M.mulVec v = w)
    (hrow : ∀ w, ∃ M ∈ P, Matrix.vecMul lam M = w)
    (hlam : Matrix.vecMul lam S = 0) : P = ⊤ := by
  let e : Matrix ι ι F ≃ₐ[F] Module.End F (ι → F) := Matrix.toLinAlgEquiv'
  let Q := P.map e.toAlgHom
  let f : Module.Dual F (ι → F) := dotProductBilin F F lam
  have he (M : Matrix ι ι F) (w : ι → F) : e M w = M.mulVec w :=
    Matrix.toLinAlgEquiv'_apply M w
  have hsv : e S v = 0 := by rw [he]; exact hSv
  have hk : ∀ w : ι → F, e S w = 0 → ∃ c : F, w = c • v := by
    intro w hw
    rw [he] at hw
    exact hker w hw
  have hc : ∀ w : ι → F, ∃ a ∈ Q, a v = w := by
    intro w
    obtain ⟨M, hM, hw⟩ := hcol w
    exact ⟨e M, ⟨M, hM, rfl⟩, (he M v).trans hw⟩
  have hd : ∀ w : ι → F, (∀ a ∈ Q, f (a w) = 0) → w = 0 := by
    intro w hw
    funext i
    obtain ⟨M, hM, hrowM⟩ := hrow (Pi.single i 1)
    have hh := hw (e M) ⟨M, hM, rfl⟩
    change dotProduct lam (e M w) = 0 at hh
    rw [he, dotProduct_mulVec, hrowM, single_dotProduct, one_mul] at hh
    exact hh
  have hf : ∀ w : ι → F, f (e S w) = 0 := by
    intro w
    change dotProduct lam (e S w) = 0
    rw [he, dotProduct_mulVec, hlam, zero_dotProduct]
  have hQ : Q = ⊤ := end_top Q (e S) v f ⟨S, hS, rfl⟩ hsv hk hc hd hf
  apply top_unique
  intro M _
  have hm : e M ∈ Q := by rw [hQ]; trivial
  change ∃ M' ∈ P, e M' = e M at hm
  obtain ⟨M', hM', hMa⟩ := hm
  exact e.injective hMa ▸ hM'
end Representation.CyclicKernel
