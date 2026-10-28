module

public import Theory.GroupTheory.SylowNormalIntersection

/-!
# Frattini generation from weak closure

Let J lie in both a Sylow p-subgroup S and a normal subgroup N of a
finite group. If every conjugate of J contained in S equals J, then
N_G(J) N is the whole group. Consequently a subgroup normalized by N
and by N_G(J) is normal in the whole group.

The intersection S ∩ N is Sylow in N. An element normalizing that
intersection sends J into S, hence normalizes J by weak closure.
The ordinary Frattini argument for S ∩ N then gives the claimed
generation. The normality corollary follows by bounding this join
by the subgroup's normalizer.

This is the normality transfer needed in Stellmacher (2.2), Journal of
Algebra 190 (1997), p.20. Only standard finite-group and Sylow results
are imported; no campaign-specific assumptions enter the theorem.
-/

public theorem normalizer_sup_eq_top_of_weakly_closed
    {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (S : Sylow p G) (N J : Subgroup G) [N.Normal]
    (hJS : J ≤ (S : Subgroup G)) (hJN : J ≤ N)
    (hweak : ∀ g : G, J.map (MulAut.conj g).toMonoidHom ≤ (S : Subgroup G) →
      J.map (MulAut.conj g).toMonoidHom = J) :
    Subgroup.normalizer (J : Set G) ⊔ N = ⊤ := by
  obtain ⟨T, hT⟩ := S.exists_subgroupOf_eq_of_normal N
  have hTmap : (T : Subgroup N).map N.subtype = (S : Subgroup G) ⊓ N := by
    rw [hT, Subgroup.subgroupOf_map_subtype]
  have hJTin : J ≤ (T : Subgroup N).map N.subtype := by
    rw [hTmap]
    exact le_inf hJS hJN
  have hnorm : Subgroup.normalizer ((T : Subgroup N).map N.subtype : Set G) ≤
      Subgroup.normalizer (J : Set G) := by
    intro g hg
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    apply hweak
    have hm := Subgroup.map_mono (f := (MulAut.conj g).toMonoidHom) hJTin
    have heq : ((T : Subgroup N).map N.subtype).map (MulAut.conj g).toMonoidHom =
        (T : Subgroup N).map N.subtype := Subgroup.mem_normalizer_iff_map_conj_eq.mp hg
    rw [heq, hTmap] at hm
    exact hm.trans inf_le_left
  apply top_unique
  rw [← T.normalizer_sup_eq_top]
  exact sup_le_sup_right hnorm N

public theorem normal_of_normalized_by_normal_and_weakly_closed_normalizer
    {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (S : Sylow p G) (N J E : Subgroup G) [N.Normal]
    (hJS : J ≤ (S : Subgroup G)) (hJN : J ≤ N)
    (hweak : ∀ g : G, J.map (MulAut.conj g).toMonoidHom ≤ (S : Subgroup G) →
      J.map (MulAut.conj g).toMonoidHom = J)
    (hNE : N ≤ Subgroup.normalizer (E : Set G))
    (hJE : Subgroup.normalizer (J : Set G) ≤ Subgroup.normalizer (E : Set G)) :
    E.Normal := by
  apply Subgroup.normalizer_eq_top_iff.mp
  apply top_unique
  rw [← normalizer_sup_eq_top_of_weakly_closed S N J hJS hJN hweak]
  exact sup_le hJE hNE
