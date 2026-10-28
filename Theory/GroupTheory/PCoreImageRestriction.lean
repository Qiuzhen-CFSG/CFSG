module

public import Theory.GroupTheory.PCoreSurjective
public import Theory.GroupTheory.PCoreLocalSetup

/-!
# Prime cores restricted to subgroup images

For a homomorphism with p-group kernel, the part of A mapping into the
p-core of f(A) is exactly O_p(A). Restrict the homomorphism to A, apply
the intrinsic core-preimage theorem, and embed the result in the original
group. No normality of A in the ambient group is assumed.

This keeps the two successive quotient maps in Aschbacher--Smith,
Lemma 12.6.5 (printed p.824), distinct until their core comparison is proved.
-/

public section
namespace Subgroup
variable {G D : Type*} [Group G] [Group D] [Finite G] [Finite D]

/-- Restricting a core preimage to the original subgroup recovers its own core. -/
theorem inf_comap_pCoreIn_eq_of_ker_isPGroup (p : ℕ) [Fact p.Prime] (f : G →* D) (A : Subgroup G)
    (hk : IsPGroup p f.ker) :
    A ⊓ ((A.map f).pCoreIn p).comap f = A.pCoreIn p := by
  let fA := f.subgroupMap A
  have hkA : IsPGroup p fA.ker := by
    have he : fA.ker = f.ker.comap A.subtype := by
      ext a
      simp only [MonoidHom.mem_ker, mem_comap]
      exact Subtype.ext_iff
    rw [he]
    exact hk.comap_of_injective A.subtype A.subtype_injective
  have hcore := fA.comap_pCore_of_ker_isPGroup (f.subgroupMap_surjective A) hkA
  ext a
  constructor
  · rintro ⟨ha, b, hb, he⟩
    refine ⟨⟨a, ha⟩, ?_, rfl⟩
    rw [← hcore]
    change fA ⟨a, ha⟩ ∈ pCore p (A.map f)
    have he' : b = fA ⟨a, ha⟩ := Subtype.ext he
    exact he' ▸ hb
  · rintro ⟨a, ha, rfl⟩
    refine ⟨a.property, fA a, ?_, rfl⟩
    exact hcore.ge ha

end Subgroup
