module

public import CFSG.Quasithin.Defs
public import CFSG.Quasithin.MainConverse.ExceptionalLocal.G2Even.OddRank
public import Theory.Quasithin.EvenCharacteristic
public import Theory.AtlasPort.LinearGroups.G2.EvenLocal.LongCore
public import Theory.AtlasPort.LinearGroups.G2.EvenLocal.NormalizerCover
public import Theory.AtlasPort.LinearGroups.G2.EvenLocal.ShortCore
public import Theory.AtlasPort.LinearGroups.G2.LieSpecialRadical

/-!
# Even-field G₂ is quasithin and of even characteristic

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, Theorem
0.1.2(1), printed pp.3–4, repeated as Theorem 0.1.1 on pp.481–482.
For G₂(2^f), f ≥ 2, QT bounds odd-prime ranks in every maximal 2-local;
E tests the intrinsic two-core of each maximal 2-local containing a Sylow
subgroup.

The proof combines conjugate-parabolic coverage for normalizers of arbitrary
nonidentity two-subgroups, the odd-prime ranks of both full parabolics, and
their self-centralizing intrinsic two-cores. The coverage comes from the actual
octonion hexagon, the rank bounds from the concrete Levi representations and
torus characters, and self-centralization from root commutator calculations.
Containment in a parabolic becomes equality for maximal two-locals because the
parabolic normalizes a nonidentity two-group. Isomorphism transport then proves
the intrinsic centralizer condition. The conditional reductions are retained;
the final theorems discharge every local input and apply over every finite field
of characteristic two, hence in particular to the source's range f ≥ 2.
-/

namespace CFSG.Quasithin.MainConverse.G2Even
open Subgroup Atlas.G2 Atlas.G2.LieParabolicSetup
variable {F : Type*} [Field F] [Finite F] [CharP F 2]

omit [Finite F] [CharP F 2] in
private theorem fiveRoot_ne_bot (i : Fin 6) (hi : i = 4 ∨ i = 5) :
    fiveRootSubgroup (F := F) i hi ≠ ⊥ := by
  intro h
  have hm : rootA (1 : F) ∈ fiveRootSubgroup (F := F) i hi :=
    ⟨![1,0,0,0,0,0], by rcases hi with rfl | rfl <;> rfl,
      by simp [unipotentProduct]⟩
  have hroot : rootA (1 : F) = rootA 0 := by simpa [h] using hm
  exact one_ne_zero (rootA_injective hroot)

private theorem maximal_eq_of_normalized_radical {G : Type*} [Group G]
    {M P Q : Subgroup G} (hM : IsMaximalTwoLocal M)
    (hQ : Q ≠ ⊥) (hp : IsPGroup 2 Q)
    (hPN : P ≤ normalizer (Q : Set G)) (hMP : M ≤ P) : M = P := by
  have hN : IsTwoLocal (normalizer (Q : Set G)) := ⟨Q, hQ, hp, rfl⟩
  exact le_antisymm hMP (hPN.trans (hM.2 hN (hMP.trans hPN)))

omit [CharP F 2] in
/-- The coverage input ranges over all two-subgroup normalizers, not just the
standard parabolics or normalizers of subgroups characteristic in a Sylow. -/
public theorem quasithin_of_parabolic_cover
    (hcover : ∀ R : Subgroup (Model F), R ≠ ⊥ → IsPGroup 2 R →
      ∃ g : Model F,
        (normalizer (R : Set (Model F))).map (MulAut.conj g).toMonoidHom ≤ parabolic₁ ∨
        (normalizer (R : Set (Model F))).map (MulAut.conj g).toMonoidHom ≤ parabolic₂)
    (hshort : IsStronglyQuasithin (parabolic₁ (F := F)))
    (hlong : IsStronglyQuasithin (parabolic₂ (F := F))) : IsQuasithin (Model F) := by
  apply Theory.GroupTheory.isQuasithin_iff_twoLocal.mpr
  rintro M ⟨R, hR, hpR, rfl⟩ p hp ho
  obtain ⟨g, hg⟩ := hcover R hR hpR
  rw [Theory.GroupTheory.primeRank_equiv p
    ((MulAut.conj g).subgroupMap (normalizer (R : Set (Model F))))]
  rcases hg with h | h
  · exact (Theory.GroupTheory.primeRank_le_of_injective p (inclusion h)
      (inclusion_injective h)).trans (hshort p hp ho)
  · exact (Theory.GroupTheory.primeRank_le_of_injective p (inclusion h)
      (inclusion_injective h)).trans (hlong p hp ho)

/-- Maximality promotes the parabolic containment to equality, so the
centralizer assertion transports with the actual intrinsic two-core. -/
public theorem evenCharacteristic_of_parabolic_cover
    (hcover : ∀ R : Subgroup (Model F), R ≠ ⊥ → IsPGroup 2 R →
      ∃ g : Model F,
        (normalizer (R : Set (Model F))).map (MulAut.conj g).toMonoidHom ≤ parabolic₁ ∨
        (normalizer (R : Set (Model F))).map (MulAut.conj g).toMonoidHom ≤ parabolic₂)
    (hnorm : parabolic₁ (F := F) ≤ normalizer (radical₁ (F := F) : Set (Model F)))
    (hshort : HasCharacteristicTwo (parabolic₁ (F := F))) :
    IsEvenCharacteristic (Model F) := by
  intro T M hM _
  obtain ⟨R, hR, hpR, hMR⟩ := hM.1
  obtain ⟨g, hg⟩ := hcover R hR hpR
  rw [← hMR] at hg
  have hmap := Theory.Quasithin.isMaximalTwoLocal_map (MulAut.conj g) hM
  apply (Theory.Quasithin.centralizer_pCore_map_le_iff 2 (MulAut.conj g) M).mp
  rcases hg with h | h
  · have he := maximal_eq_of_normalized_radical hmap
      (fiveRoot_ne_bot 5 (Or.inr rfl)) radical₁_isTwoGroup hnorm h
    rw [he]
    exact hshort
  · have he := maximal_eq_of_normalized_radical hmap
      (fiveRoot_ne_bot 4 (Or.inl rfl)) radical₂_isTwoGroup
      Atlas.G2.EvenLocal.parabolic₂_le_normalizer_radical₂ h
    rw [he]
    exact Atlas.G2.EvenLocal.parabolic₂_centralizer_pCore

/-- Every two-local subgroup of the concrete even-field G₂ model has odd-prime
rank at most two. The normalizer cover includes arbitrary nonidentity
two-subgroups, with no requirement that they be standard root subgroups. -/
public theorem quasithin : IsQuasithin (Model F) :=
  quasithin_of_parabolic_cover
    Atlas.G2.EvenLocal.NormalizerCover.normalizer_conjugate_le_parabolic
    (fun _ hp ho => short_parabolic_primeRank_le_two hp ho)
    (fun _ hp ho => long_parabolic_primeRank_le_two hp ho)

/-- Every maximal two-local containing a Sylow two-subgroup has a
self-centralizing intrinsic two-core. -/
public theorem evenCharacteristic : IsEvenCharacteristic (Model F) :=
  evenCharacteristic_of_parabolic_cover
    Atlas.G2.EvenLocal.NormalizerCover.normalizer_conjugate_le_parabolic
    Atlas.G2.EvenLocal.parabolic₁_le_normalizer_radical₁
    Atlas.G2.EvenLocal.parabolic₁_centralizer_pCore

/-- The QT and E clauses for the actual octonion model of even-field G₂. -/
public theorem quasithin_evenCharacteristic :
    IsQuasithin (Model F) ∧ IsEvenCharacteristic (Model F) :=
  ⟨quasithin, evenCharacteristic⟩

omit [CharP F 2] in
/-- The concrete G₂(2^f) branch of the converse, in particular for the source's
simple-group range f ≥ 2. No local-rank or core-centralizer premise remains. -/
public theorem quasithin_evenCharacteristic_of_card {f : ℕ}
    (hcard : Nat.card F = 2 ^ f) :
    IsQuasithin (Model F) ∧ IsEvenCharacteristic (Model F) := by
  let : Fintype F := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow (p := 2) (f := f) (by
    simpa only [Nat.card_eq_fintype_card] using hcard)
  exact quasithin_evenCharacteristic
end CFSG.Quasithin.MainConverse.G2Even
