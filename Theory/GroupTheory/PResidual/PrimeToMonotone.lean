module

public import Theory.GroupTheory.PResidual.PrimeTo

/-!
# Functoriality of the prime-to-p residual

An arbitrary homomorphism sends O^{p′}(A) into O^{p′}(B): pull back a
normal subgroup of index prime to p, and use divisibility of the index of
the pullback. In particular, this residual is monotone for embedded
subgroups. Isomorphisms transport the embedded residual exactly.

This is the residual-transfer step used in Aschbacher–Smith, combined
manuscript of 1 March 2004, proof of Lemma 16.4.8, pp.1187–1188.
-/

public section

namespace Subgroup

variable {A B G : Type*} [Group A] [Group B] [Group G] (p : ℕ)

/-- Functoriality does not require the homomorphism to be surjective. -/
theorem map_primeToResidual_le_of_hom (f : A →* B) :
    (primeToResidual p A).map f ≤ primeToResidual p B := by
  apply le_sInf
  rintro N ⟨hN, hc⟩
  let := hN
  rw [map_le_iff_le_comap]
  apply primeToResidual_le
  rw [N.index_comap]
  exact hc.coprime_dvd_right (N.relIndex_dvd_index_of_normal f.range)

/-- The prime-to-p residual is monotone as an actual subgroup of G. -/
theorem embedded_primeToResidual_mono {U V : Subgroup G} (hUV : U ≤ V) :
    (primeToResidual p U).map U.subtype ≤ (primeToResidual p V).map V.subtype := by
  rintro x ⟨u, hu, rfl⟩
  exact ⟨inclusion hUV u, map_primeToResidual_le_of_hom p (inclusion hUV)
    (mem_map_of_mem _ hu), rfl⟩

/-- Transporting an embedded residual retains its embedding, not just its
abstract isomorphism type. -/
theorem map_embedded_primeToResidual (U : Subgroup A) (e : A ≃* B) :
    ((primeToResidual p U).map U.subtype).map e.toMonoidHom =
      (primeToResidual p (U.map e.toMonoidHom)).map (U.map e.toMonoidHom).subtype := by
  let eU : U ≃* U.map e.toMonoidHom := e.subgroupMap U
  have he : e.toMonoidHom.comp U.subtype =
      (U.map e.toMonoidHom).subtype.comp eU.toMonoidHom := rfl
  rw [map_map, he, ← map_map, map_primeToResidual]

end Subgroup
