module

public import Theory.GroupTheory.ElementSubgroupIncidence
public import Theory.GroupTheory.PGroup.NormalizedSylowConjugation

/-!
# Sylow reduction of element/subgroup incidence

For an abelian p-subgroup A containing z, every conjugate containing z is
inside C_G(z). If C_G(z) contains a Sylow p-subgroup P, Sylow conjugacy in
that centralizer reduces incidence transitivity to the conjugates inside P.
The element/subgroup incidence equivalence then gives transitivity of N_G(A)
on the ambient conjugates of z lying in A.

Source application: Aschbacher--Smith F.5.4(4), printed p.301.
-/

public section
open Subgroup
namespace Sylow
variable {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]

/-- Local conjugacy of the abelian subgroup inside the selected Sylow
suffices for the normalizer to fuse its marked elements. -/
theorem normalizer_transitive_of_local_incidence (P : Sylow p G)
    (A : Subgroup G) (z : G) (hA : IsPGroup p A)
    (hcomm : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a)
    (hP : (P : Subgroup G) ≤ centralizer ({z} : Set G))
    (hlocal : ∀ g : G, A.conjBy g ≤ P →
      ∃ c ∈ centralizer ({z} : Set G), A.conjBy c = A.conjBy g) :
    ∀ y ∈ A, IsConj z y →
      ∃ n ∈ normalizer (A : Set G), MulAut.conj n z = y := by
  apply (element_fusion_iff_centralizer_incidence A z).mpr
  intro g hz
  let B := A.conjBy g
  have hBC : B ≤ centralizer ({z} : Set G) := by
    obtain ⟨a,ha,he⟩ := hz
    rintro _ ⟨b,hb,rfl⟩
    apply mem_centralizer_singleton_iff.mpr
    rw [← he]
    exact (map_mul (MulAut.conj g) b a).symm.trans
      ((congrArg (MulAut.conj g) (hcomm b hb a ha)).trans (map_mul (MulAut.conj g) a b))
  obtain ⟨k,hk,hB⟩ := IsPGroup.exists_conj_le_sylow_of_normalized P
    (centralizer ({z} : Set G)) B (hP.trans le_normalizer)
    (hA.map (MulAut.conj g).toMonoidHom) hBC
  have hkg : A.conjBy (k * g) ≤ P := by
    rw [conjBy_mul]
    exact hB
  obtain ⟨c,hc,he⟩ := hlocal (k*g) hkg
  refine ⟨k⁻¹*c,(centralizer ({z} : Set G)).mul_mem
    ((centralizer ({z} : Set G)).inv_mem hk) hc,?_⟩
  rw [conjBy_mul,he,conjBy_mul,conjBy_inv]

end Sylow
