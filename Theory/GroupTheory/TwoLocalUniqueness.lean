module

public import Theory.GroupTheory.UniqueMaximalOvergroup
public import Theory.GroupTheory.TwoLocalTransport
public import Theory.GroupTheory.NonsolvableTwoLocal
public import Theory.PGroupCore
public import Theory.GroupTheory.CharacteristicCentralizerFusion

/-!
# Uniqueness among maximal two-local subgroups

Maximal two-local subgroups are self-normalizing: a normalizer preserves the
nontrivial characteristic two-core, whose normalizer is itself two-local.
Consequently an elementary abelian subgroup centralizing a uniqueness subgroup
has trivial intersection with its conjugates outside the unique maximal
two-local overgroup. Nonidentity elements have order two, so their centralizers
are two-local and the general uniqueness argument applies.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, combined
1 March 2004 manuscript, Theorem 1.2.7(4), printed p. 506.
-/

namespace Theory.GroupTheory

variable {G : Type*} [Group G]

/-- A maximal two-local subgroup is self-normalizing. -/
public theorem normalizer_eq_of_isMaximalTwoLocal {M : Subgroup G}
    (hM : IsMaximalTwoLocal M) : Subgroup.normalizer (M : Set G) = M := by
  obtain ⟨Q, hQ, hpQ, hMQ⟩ := hM.1
  have hQM : Q ≤ M := hMQ ▸ Q.le_normalizer
  have hQnorm : (Q.subgroupOf M).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hQM).mpr hMQ.le
  have hQcore : Q.subgroupOf M ≤ pCore 2 M :=
    le_sSup ⟨hQnorm, hpQ.comap_subtype⟩
  let A := (pCore 2 M).map M.subtype
  have hQA : Q ≤ A := by
    have h := Subgroup.map_mono (f := M.subtype) hQcore
    simpa only [Subgroup.map_subgroupOf_eq_of_le hQM] using h
  have hA : A ≠ ⊥ := fun hbot => hQ (le_bot_iff.mp (hbot ▸ hQA))
  have hNA : Subgroup.normalizer (M : Set G) ≤ Subgroup.normalizer (A : Set G) :=
    Subgroup.normalizer_le_normalizer_characteristic_image M (pCore 2 M)
  have hlocal : IsTwoLocal (Subgroup.normalizer (A : Set G)) :=
    ⟨A, hA, pCore_isPGroup.map M.subtype, rfl⟩
  exact le_antisymm (hNA.trans (hM.2 hlocal (M.le_normalizer.trans hNA))) M.le_normalizer

/-- The elementary-abelian centralizer consequence of uniqueness among maximal
2-local subgroups. -/
public theorem inf_conjugate_eq_bot_of_unique_maximalTwoLocal
    {G : Type*} [Group G] [Finite G] {H M Z : Subgroup G}
    (hM : IsMaximalTwoLocal M)
    (hunique : ∀ K : Subgroup G, IsMaximalTwoLocal K → H ≤ K → K = M)
    (hHZ : H ≤ Subgroup.centralizer (Z : Set G))
    (hZ : ∀ z ∈ Z, z ^ 2 = 1) {g : G} (hg : g ∉ M) :
    Z ⊓ Z.map (MulAut.conj g).toMonoidHom = ⊥ := by
  apply inf_conjugate_eq_bot_of_unique_maximal
    (F := {K | IsTwoLocal K}) (H := H)
    (fun e _ hK => isTwoLocal_map_aut hK e) hM hunique
    (normalizer_eq_of_isMaximalTwoLocal hM).le hHZ ?_ hg
  intro z hz hz1
  exact ⟨Subgroup.centralizer ({z} : Set G),
    isTwoLocal_involution_centralizer (orderOf_eq_prime (hZ z hz) hz1), le_rfl⟩

end Theory.GroupTheory
