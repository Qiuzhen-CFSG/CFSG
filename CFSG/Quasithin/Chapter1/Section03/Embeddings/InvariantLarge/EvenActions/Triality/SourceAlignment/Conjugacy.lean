module

public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantLarge.EvenActions.Triality.Transport
public import Theory.GroupTheory.NormalizedSupCard
public import Theory.GroupTheory.SylowNormalIntersection

/-!
# Simultaneous Sylow and torus coordinates

After mapping a Sylow two-subgroup to the standard positive subgroup, an odd
p-subgroup of its normalizer can be conjugated into the standard torus without
moving that positive subgroup. Indeed, the torus has index a power of two in
the normalizer, so the p-group has a fixed point on its cosets. This constructs
an actual common equivalence; it does not assume a Cartan alignment witness.

The only triality geometry used is the four clauses of `BorelGeometry` and a
Sylow witness for `unipotent`. In the ambient application, restriction of the
Sylow subgroup to the normal component uses normality in the ambient group.

Source: Aschbacher–Smith, `refs/quasithin.pdf`, A.3.15(5), printed pp.50–51,
and the proof of Proposition 1.3.4, p.511. The coset fixed-point argument is
the usual Sylow conjugacy argument inside the Borel normalizer.
-/

@[expose] public section
noncomputable section
open Subgroup
open scoped Pointwise
open Triality.Standard Triality.Standard.Parabolics Triality.Standard.CartanAction

namespace CFSG.Quasithin.Chapter1.XiEmbedding.InvariantLarge.EvenActions.Triality.SourceAlignment

private theorem conjugate_le_of_index {G : Type*} [Group G]
    {p : ℕ} [Fact p.Prime] (A C : Subgroup G)
    (hA : IsPGroup p A) (hC : ¬ p ∣ C.index) :
    ∃ g : G, A.map (MulAut.conj g).toMonoidHom ≤ C := by
  obtain ⟨x, hx⟩ := hA.nonempty_fixed_point_of_prime_not_dvd_card (G ⧸ C) hC
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
  refine ⟨g⁻¹, ?_⟩
  rintro _ ⟨a, ha, rfl⟩
  have he : (g : G ⧸ C) = (a * g : G) := (hx (⟨a, ha⟩ : A)).symm
  change g⁻¹ * a * (g⁻¹)⁻¹ ∈ C
  simpa only [inv_inv, mul_assoc] using QuotientGroup.eq.mp he

/-- An odd p-subgroup of the positive normalizer has torus coordinates there. -/
theorem torus_conjugacy_in_normalizer (P : Parameters) (hG : BorelGeometry P)
    (hU : IsPGroup 2 (unipotent P))
    {p : ℕ} [Fact p.Prime] (hp : p ≠ 2)
    (B : Subgroup (Carrier P)) (hB : IsPGroup p B)
    (hBN : B ≤ normalizer (unipotent P)) :
    ∃ g ∈ normalizer (unipotent P), B.map (MulAut.conj g).toMonoidHom ≤ torus P := by
  let N : Subgroup (Carrier P) := normalizer (unipotent P : Set (Carrier P))
  let C := (torus P).subgroupOf N
  let A := B.subgroupOf N
  have hsup : unipotent P ⊔ torus P = N := by
    apply le_antisymm (sup_le (unipotent P).le_normalizer hG.normalizes)
    intro x hx
    obtain ⟨u, hu, t, ht, rfl⟩ := hG.product x (hG.normalizer_eq ▸ hx)
    exact mul_mem_sup hu ht
  have hcard : Nat.card N = Nat.card (unipotent P) * Nat.card (torus P) := by
    rw [← hsup]
    exact card_sup_eq_mul_of_normalizes_of_disjoint _ _ hG.normalizes hG.disjoint
  have hCcard : Nat.card C = Nat.card (torus P) :=
    Nat.card_congr (subgroupOfEquivOfLe hG.normalizes).toEquiv
  have hindex : C.index = Nat.card (unipotent P) := by
    have hh := C.card_mul_index
    rw [hCcard, hcard, mul_comm (Nat.card (unipotent P))] at hh
    exact Nat.eq_of_mul_eq_mul_left Nat.card_pos hh
  have hnot : ¬ p ∣ C.index := by
    obtain ⟨a, ha⟩ := hU.exists_card_eq
    rw [hindex, ha]
    intro hd
    exact hp ((Nat.prime_dvd_prime_iff_eq Fact.out Nat.prime_two).mp
      ((Fact.out : p.Prime).dvd_of_dvd_pow hd))
  obtain ⟨g, hg⟩ := conjugate_le_of_index A C hB.comap_subtype hnot
  refine ⟨g, g.property, ?_⟩
  rintro _ ⟨b, hb, rfl⟩
  exact hg ⟨⟨b, hBN hb⟩, hb, rfl⟩

/-- Conjugate the Sylow subgroup and its normalizing p-subgroup simultaneously. -/
theorem simultaneous_sylow_torus_conjugacy {G : Type*} [Group G] [Finite G]
    (P : Parameters) (hG : BorelGeometry P)
    (U : Sylow 2 (Carrier P)) (hU : (U : Subgroup (Carrier P)) = unipotent P)
    (e : G ≃* Carrier P) (T : Sylow 2 G)
    {p : ℕ} [Fact p.Prime] (hp : p ≠ 2)
    (B : Subgroup G) (hB : IsPGroup p B)
    (hBN : B ≤ normalizer (T : Subgroup G)) :
    ∃ e' : G ≃* Carrier P,
      B.map e'.toMonoidHom ≤ torus P ∧
      (T : Subgroup G).map e'.toMonoidHom = unipotent P := by
  let T' := T.mapSurjective (f := e.toMonoidHom) e.surjective
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (Carrier P) T' U
  let e₁ := e.trans (MulAut.conj g)
  have hT : (T : Subgroup G).map e₁.toMonoidHom = unipotent P := by
    rw [show e₁.toMonoidHom = (MulAut.conj g).toMonoidHom.comp e.toMonoidHom from rfl,
      ← map_map]
    exact (congrArg Sylow.toSubgroup hg).trans hU
  have hBN₁ : B.map e₁.toMonoidHom ≤ normalizer (unipotent P) := by
    rw [← hT, ← map_normalizer_eq_of_bijective _ e₁.bijective]
    exact map_mono hBN
  have hB₁ : IsPGroup p (B.map e₁.toMonoidHom) := hB.map _
  have hU₂ : IsPGroup 2 (unipotent P) := hU ▸ U.isPGroup'
  obtain ⟨h, hh, hBT⟩ := torus_conjugacy_in_normalizer P hG hU₂ hp
    (B.map e₁.toMonoidHom) hB₁ hBN₁
  refine ⟨e₁.trans (MulAut.conj h), ?_, ?_⟩
  · change B.map ((MulAut.conj h).toMonoidHom.comp e₁.toMonoidHom) ≤ torus P
    rwa [← map_map]
  · change (T : Subgroup G).map ((MulAut.conj h).toMonoidHom.comp e₁.toMonoidHom) = _
    rw [← map_map, hT]
    exact mem_normalizer_iff_map_conj_eq.mp hh

/-- Ambient alignment once intrinsic normalization of the Sylow intersection is proved. -/
theorem hasCartanAlignment_of_normalizes {J : Type*} [Group J] [Finite J]
    (D : Subgroup J) [D.Normal] (B : Subgroup J) (S : Sylow 2 J)
    (P : Parameters) (hG : BorelGeometry P)
    (U : Sylow 2 (Carrier P)) (hU : (U : Subgroup (Carrier P)) = unipotent P)
    (e : D ≃* Carrier P) {p : ℕ} [Fact p.Prime] (hp : p ≠ 2)
    (hB : IsPGroup p B)
    (hBN : B.subgroupOf D ≤ normalizer ((S : Subgroup J).subgroupOf D)) :
    HasCartanAlignment D B S P := by
  obtain ⟨T, hT⟩ := S.exists_subgroupOf_eq_of_normal D
  obtain ⟨e', hBT, hTU⟩ := simultaneous_sylow_torus_conjugacy P hG U hU e T hp
    (B.subgroupOf D) hB.comap_subtype (hT.symm ▸ hBN)
  exact ⟨e', hBT, hT ▸ hTU⟩

end CFSG.Quasithin.Chapter1.XiEmbedding.InvariantLarge.EvenActions.Triality.SourceAlignment
