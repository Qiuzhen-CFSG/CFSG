module

public import Theory.GroupTheory.CharacteristicNormalizerClosure
public import Theory.GroupTheory.PCoreLocalSetup
public import Theory.Quasithin

/-!
# Characteristic normalizer control from two-local uniqueness

If `H` normalizes a two-group `Q` and has a unique maximal two-local
overgroup `M`, every nontrivial characteristic subgroup of `Q` has its
ambient normalizer in `M`. Enlarge that normalizer to a maximal two-local;
it contains `H`, so uniqueness identifies it with `M`.

The core comparison for overgroups of a common Sylow subgroup then turns
relative characteristic two in `M` into an ambient centralizer bound.
These are the elementary arguments in Aschbacher–Smith, *The Classification
of Quasithin Groups*, Lemma 1.4.1(1),(3), pp. 514–515 (1 March 2004).
-/

namespace Subgroup

variable {G : Type*} [Group G]

/-- Uniqueness controls normalizers of subgroups characteristic inside `Q`. -/
public theorem characteristicNormalizerClosure_le_of_unique_twoLocal [Finite G]
    {H Q M : Subgroup G} (hQ : IsPGroup 2 Q)
    (hHQ : H ≤ normalizer (Q : Set G))
    (hunique : ∀ N : Subgroup G, IsMaximalTwoLocal N → H ≤ N → N = M) :
    characteristicNormalizerClosure Q ≤ M := by
  apply (characteristicNormalizerClosure_le_iff Q M).mpr
  intro R hR hRne
  let : R.Characteristic := hR
  have hRmap : R.map Q.subtype ≠ ⊥ := fun he =>
    hRne ((R.map_eq_bot_iff_of_injective Q.subtype_injective).mp he)
  have hlocal : IsTwoLocal (normalizer (R.map Q.subtype : Set G)) :=
    ⟨R.map Q.subtype, hRmap, (hQ.to_subgroup R).map Q.subtype, rfl⟩
  obtain ⟨N, hRN, hN⟩ := Finite.exists_le_maximal hlocal
  have hHN : H ≤ N := hHQ.trans
    ((normalizer_le_normalizer_characteristic_image Q R).trans hRN)
  exact (hunique N hN hHN) ▸ hRN

/-- In particular the ambient centralizer is controlled, without ambient
characteristicness of `Q`. -/
public theorem centralizer_le_of_unique_twoLocal [Finite G]
    {H Q M : Subgroup G} (hQ : IsPGroup 2 Q) (hQne : Q ≠ ⊥)
    (hHQ : H ≤ normalizer (Q : Set G))
    (hunique : ∀ N : Subgroup G, IsMaximalTwoLocal N → H ≤ N → N = M) :
    centralizer (Q : Set G) ≤ M :=
  (centralizer_le_normalizer (Q : Set G)).trans
    ((normalizer_le_characteristicNormalizerClosure_self Q hQne).trans
      (characteristicNormalizerClosure_le_of_unique_twoLocal hQ hHQ hunique))

/-- The normalizer of `Q` has the same unique maximal two-local overgroup. -/
public theorem unique_twoLocal_overgroup_normalizer [Finite G]
    {H Q M : Subgroup G} (hQ : IsPGroup 2 Q) (hQne : Q ≠ ⊥)
    (hHQ : H ≤ normalizer (Q : Set G)) (hM : IsMaximalTwoLocal M)
    (hunique : ∀ N : Subgroup G, IsMaximalTwoLocal N → H ≤ N → N = M) :
    {N : Subgroup G | IsMaximalTwoLocal N ∧ normalizer (Q : Set G) ≤ N} = {M} := by
  have hQM : normalizer (Q : Set G) ≤ M :=
    (normalizer_le_characteristicNormalizerClosure_self Q hQne).trans
      (characteristicNormalizerClosure_le_of_unique_twoLocal hQ hHQ hunique)
  ext N
  constructor
  · rintro ⟨hN, hQN⟩
    exact Set.mem_singleton_iff.mpr (hunique N hN (hHQ.trans hQN))
  · intro hN
    rcases Set.mem_singleton_iff.mp hN with rfl
    exact ⟨hM, hQM⟩

/-- The core of an overgroup lies in the core of a subgroup containing a
Sylow subgroup of the ambient group. -/
public theorem pCoreIn_le_pCoreIn_of_sylow {p : ℕ}
    (T : Sylow p G) {H M : Subgroup G}
    (hTH : (T : Subgroup G) ≤ H) (hHM : H ≤ M) :
    M.pCoreIn p ≤ H.pCoreIn p := by
  have hcoreT : M.pCoreIn p ≤ (T : Subgroup G) := by
    have hc := pCoreIn_le_sylow M (T.subtype (hTH.trans hHM))
    simpa only [Sylow.coe_subtype, map_subgroupOf_eq_of_le (hTH.trans hHM)] using hc
  apply le_pCoreIn_of_normalizes (isPGroup_pCoreIn p M) (hcoreT.trans hTH)
  exact hHM.trans (M.le_normalizer.trans
    (normalizer_le_normalizer_characteristic_image M (pCore p M)))

/-- Uniqueness and relative characteristic two suffice for the ambient
centralizer bound. The two-core containment is derived using the Sylow subgroup. -/
public theorem centralizer_pCoreIn_le_of_unique_twoLocal [Finite G]
    (T : Sylow 2 G) {H M : Subgroup G}
    (hTH : (T : Subgroup G) ≤ H) (hHM : H ≤ M)
    (hQne : H.pCoreIn 2 ≠ ⊥)
    (hunique : ∀ N : Subgroup G, IsMaximalTwoLocal N → H ≤ N → N = M)
    (hchar : M ⊓ centralizer (M.pCoreIn 2 : Set G) ≤ M.pCoreIn 2) :
    centralizer (H.pCoreIn 2 : Set G) ≤ M.pCoreIn 2 ∧
      M.pCoreIn 2 ≤ H.pCoreIn 2 := by
  have hcore := pCoreIn_le_pCoreIn_of_sylow T hTH hHM (p := 2)
  have hCM : centralizer (H.pCoreIn 2 : Set G) ≤ M :=
    centralizer_le_of_unique_twoLocal (isPGroup_pCoreIn 2 H) hQne
      (H.le_normalizer.trans
        (normalizer_le_normalizer_characteristic_image H (pCore 2 H))) hunique
  exact ⟨(le_inf hCM (centralizer_le hcore)).trans hchar, hcore⟩

end Subgroup
