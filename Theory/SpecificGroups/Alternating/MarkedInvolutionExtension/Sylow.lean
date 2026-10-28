module

public import Theory.SpecificGroups.Alternating.MarkedInvolutionExtension
public import Theory.GroupTheory.SylowNormalizedSupIndex

/-!
# Sylow placement preserving a marked odd involution

Start with the constructed symmetric extension of an alternating subgroup.
The preimage of the actual ambient two-subgroup contains an alternating
Sylow and the odd involution, so it is Sylow in S_n. Its elements commute
with the marked involution. Sylow conjugacy inside that involution's
centralizer then puts any prescribed centralizing symmetric Sylow in the
original two-subgroup without changing the involution.

Source: Aschbacher--Smith, Proposition 2.2.2, pp.519--520, the alternating
rows of the component inspection (combined manuscript, 1 March 2004).
-/

public section
open Subgroup Equiv

namespace Theory.GroupTheory.MarkedAlternatingExtension

/-- Place the prescribed symmetric Sylow in the original two-subgroup while
fixing the original involution. The symmetric extension is constructed. -/
theorem exists_sylow_embedding {G : Type*} [Group G] [Finite G]
    {n : ℕ} (hn : 4 ≤ n) (S : Subgroup G) (hS : IsPGroup 2 S)
    (j : alternatingGroup (Fin n) →* G) (hj : Function.Injective j)
    (P : Sylow 2 (alternatingGroup (Fin n))) (hPS : (P : Subgroup _).map j ≤ S)
    (t : Perm (Fin n)) (ht : t.sign = -1) (ht2 : t ^ 2 = 1)
    (z : G) (hz : z ∈ S) (hz2 : z ^ 2 = 1)
    (hzc : ∀ s ∈ S, Commute z s)
    (haction : ∀ a : alternatingGroup (Fin n),
      j (MulAut.conjNormal t a) = z * j a * z⁻¹)
    (Q : Sylow 2 (Perm (Fin n)))
    (hQc : (Q : Subgroup _) ≤ centralizer ({t} : Set (Perm (Fin n)))) :
    ∃ F : Perm (Fin n) →* G, Function.Injective F ∧
      F t = z ∧ (Q : Subgroup _).map F ≤ S := by
  obtain ⟨F, hF, hFA, hFt, _⟩ := exists_embedding hn j hj t ht ht2 z hz2 haction
  let A := alternatingGroup (Fin n)
  let R := S.comap F
  have hR : IsPGroup 2 R := hS.comap_of_injective F hF
  have htR : t ∈ R := by change F t ∈ S; rwa [hFt]
  have hPR : (P : Subgroup A).map A.subtype ≤ R := by
    rintro _ ⟨a, ha, rfl⟩
    change F a ∈ S
    rw [hFA]
    exact hPS (mem_map_of_mem j ha)
  have hgen : A ⊔ R = ⊤ := by
    apply top_unique
    rw [← alternating_sup_odd_involution t ht]
    exact sup_le le_sup_left ((zpowers_le.mpr htR).trans le_sup_right)
  have hnorm : R ≤ normalizer (A : Set (Perm (Fin n))) := by
    rw [Subgroup.normalizer_eq_top]
    exact le_top
  obtain ⟨V, hV⟩ := IsPGroup.exists_sylow_sup_of_coprime_index A R hR hnorm
    (P : Subgroup A) P.not_dvd_index hPR
  let e : (A ⊔ R : Subgroup (Perm (Fin n))) ≃* Perm (Fin n) :=
    (MulEquiv.subgroupCongr hgen).trans Subgroup.topEquiv
  let V' : Sylow 2 (Perm (Fin n)) := V.mapSurjective (f := e.toMonoidHom) e.surjective
  have hV' : (V' : Subgroup (Perm (Fin n))) = R := by
    change (V : Subgroup _).map e.toMonoidHom = R
    have he : e.toMonoidHom = (A ⊔ R : Subgroup (Perm (Fin n))).subtype := by
      ext x
      rfl
    rw [he, hV]
  have hRc : (V' : Subgroup (Perm (Fin n))) ≤ centralizer ({t} : Set _) := by
    intro s hs
    apply mem_centralizer_singleton_iff.mpr
    apply hF
    rw [map_mul, map_mul, hFt]
    have hsR : s ∈ R := hV' ▸ hs
    exact (hzc (F s) hsR).eq.symm
  let C := centralizer ({t} : Set (Perm (Fin n)))
  obtain ⟨c, hc⟩ := MulAction.exists_smul_eq C (Q.subtype hQc) (V'.subtype hRc)
  have hcQ (x : Perm (Fin n)) (hx : x ∈ (Q : Subgroup _)) :
      (c : Perm (Fin n)) * x * (c : Perm (Fin n))⁻¹ ∈ R := by
    have hxC : x ∈ C := hQc hx
    have hxQ : (⟨x, hxC⟩ : C) ∈ (Q.subtype hQc : Subgroup C) := hx
    have hm : c * (⟨x, hxC⟩ : C) * c⁻¹ ∈ (V'.subtype hRc : Subgroup C) := by
      rw [← hc]
      exact mem_map_of_mem (MulAut.conj c).toMonoidHom hxQ
    exact hV' ▸ hm
  let F' := F.comp (MulAut.conj (c : Perm (Fin n))).toMonoidHom
  have hct : (c : Perm (Fin n)) * t * (c : Perm (Fin n))⁻¹ = t := by
    rw [mem_centralizer_singleton_iff.mp c.property, mul_inv_cancel_right]
  refine ⟨F', hF.comp (MulAut.conj (c : Perm (Fin n))).injective, ?_, ?_⟩
  · change F ((c : Perm (Fin n)) * t * (c : Perm (Fin n))⁻¹) = z
    rw [hct, hFt]
  · rintro _ ⟨x, hx, rfl⟩
    exact hcQ x hx

end Theory.GroupTheory.MarkedAlternatingExtension
