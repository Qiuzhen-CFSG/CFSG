module

public import Theory.PGroupCore

/-!
# Restricting the p-core to an overgroup of prime-to-p index

If H has index prime to p in a finite group G, then O_p(G) is contained
in the ambient image of O_p(H). A Sylow subgroup of H is Sylow in G;
normality puts O_p(G) inside it. Restriction to H and maximality of its
p-core finish the proof.

Source application: the deduction O₂(G) ≤ R from (MS2)(a) in
Aschbacher–Smith, *The Classification of Quasithin Groups*, combined
manuscript (1 March 2004), C.1.31–32, printed pp.135–136.
-/

/-- The ambient p-core lies in the p-core of any subgroup of prime-to-p index. -/
public theorem pCore_le_map_pCore_of_prime_not_dvd_index {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (H : Subgroup G) (hindex : ¬ p ∣ H.index) :
    pCore p G ≤ (pCore p H).map H.subtype := by
  classical
  let S : Sylow p H := Classical.choice inferInstance
  have hmap : ¬ p ∣ ((S : Subgroup H).map H.subtype).index := by
    rw [Subgroup.index_map_subtype]
    exact Nat.Prime.not_dvd_mul Fact.out S.not_dvd_index hindex
  let T : Sylow p G := (S.isPGroup'.map H.subtype).toSylow hmap
  have hQH : pCore p G ≤ H :=
    (pCore_isPGroup.le_sylow_of_normal T).trans (Subgroup.map_subtype_le _)
  have hcore : (pCore p G).subgroupOf H ≤ pCore p H :=
    le_sSup ⟨inferInstance,
      pCore_isPGroup.of_equiv (Subgroup.subgroupOfEquivOfLe hQH).symm⟩
  simpa only [Subgroup.map_subgroupOf_eq_of_le hQH] using
    Subgroup.map_mono (f := H.subtype) hcore
