module

public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.EvenRankTwo.Reduction
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.Classification.Models
public import Theory.SpecificGroups.ReeF4.ParabolicAmalgam.Geometry.CorootRealization
public import Theory.SpecificGroups.ReeF4.ParabolicAmalgam.ThreeSylowContainment
public import Theory.SpecificGroups.ReeF4.ParabolicAmalgam.ThreePrimeBorel

/-!
# The three-complement obstruction in a Ree Borel

For the general Ree family the field degree is odd. Consequently its Borel
has order prime to three, once the coroot words have been identified with
diagonal matrices. A three-complement whose image lies in that Borel would
have trivial image. This contradicts the given commutator equality in the
nontrivial central quotient. Thus this particular prime does not require an
outer-automorphism calculation or any multiplier hypothesis.

The assembly below unpacks the actual `LocalBlockInput` witness and uses its
matrix-preserving equivalence to `ReeF4.Model m`. It transports the Sylow
subgroup and proves that the image of RS is solvable, proper, and has no
prime divisors other than two and three. The two geometric inputs are supplied
by the Ree parabolic modules: coroot-to-diagonal containment and containment of
these proper solvable Sylow overgroups in a conjugate Borel. The latter is used
for `m ≥ 1`, as in the source application. The final theorem below assembles
them into the unconditional exclusion.

Source: Aschbacher–Smith, proof of Proposition 1.3.4, printed p.511
(PDF p.528 of `refs/quasithin.pdf`).
-/

public section

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.EvenRankTwo.Ree
universe u v
variable {Q : Type u} [Group Q] [Finite Q]
variable {S : Sylow 2 Q} {R : Subgroup Q}

omit [Finite Q] in
/-- A nontrivial quotient cannot send the complement into a three-free subgroup:
its image would be trivial, contradicting the image commutator equality. -/
theorem complement_not_map_le_three_coprime (h : PairInput S R)
    {G : Type v} [Group G] [Finite G] [Nontrivial G]
    (f : Q →* G) (hf : Function.Surjective f) {K : Subgroup G}
    (hK : Nat.Coprime 3 (Nat.card K)) : ¬ R.map f ≤ K := by
  intro hRK
  have hc : Nat.Coprime 3 (Nat.card (R.map f)) :=
    hK.of_dvd_right (card_dvd_of_le hRK)
  let _ : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨n, hn⟩ := (h.oddComplement.isPGroup.map f).exists_card_eq
  have hn0 : n = 0 := by
    by_contra hn0
    have hd : 3 ∣ Nat.card (R.map f) := by
      rw [hn]
      exact dvd_pow_self 3 hn0
    exact Nat.prime_three.coprime_iff_not_dvd.mp hc hd
  have hRb : R.map f = ⊥ := card_eq_one.mp (by simpa [hn0] using hn)
  have ht : (⊤ : Subgroup Q).map f = ⊤ := map_top_of_surjective f hf
  have hcomm : ⁅(⊤ : Subgroup G), R.map f⁆ = ⊤ := by
    rw [← ht, ← map_commutator, h.commutator]
  rw [hRb, commutator_bot_right] at hcomm
  exact bot_ne_top hcomm

/-- The actual product RS remains solvable under any homomorphism. -/
theorem mapped_product_solvable (h : PairInput S R)
    {G : Type v} [Group G] (f : Q →* G) :
    Group.IsSolvable ((R ⊔ (S : Subgroup Q)).map f) := by
  let _ := product_solvable h
  exact Group.isSolvable_of_surjective (f.subgroupMap_surjective _)

/-- The quotient product retains the two-prime restriction supplied by the pair. -/
theorem mapped_product_prime_divisors (h : PairInput S R)
    {G : Type v} [Group G] (f : Q →* G) {p : ℕ}
    (hp : p.Prime) (hd : p ∣ Nat.card ((R ⊔ (S : Subgroup Q)).map f)) :
    p = 2 ∨ p = 3 :=
  product_prime_divisors h hp (hd.trans (card_map_dvd _ f))

/-- In a nontrivial quotient of the perfect group, the solvable image is proper. -/
theorem mapped_product_ne_top (h : PairInput S R)
    {G : Type v} [Group G] [Nontrivial G]
    (f : Q →* G) (hf : Function.Surjective f) :
    (R ⊔ (S : Subgroup Q)).map f ≠ ⊤ := by
  let _ := h.quasisimple
  let _ : Group.IsPerfect G := Group.IsPerfect.ofSurjective hf
  intro he
  let _ : Group.IsSolvable (⊤ : Subgroup G) := he ▸ mapped_product_solvable h f
  exact Group.IsPerfect.not_isSolvable G (Group.isSolvable_of_surjective
    (f := (topEquiv : (⊤ : Subgroup G) ≃* G).toMonoidHom) topEquiv.surjective)

/-- Conditional assembly using the genuine fixed-group isomorphism.
The Borel-containment hypothesis and coroot calculation must still be supplied. -/
theorem pairReducible_of_borel_geometry {m : ℕ} (h : PairInput S R)
    (hmodel : Section02.LocalModels.IsReeF4At (Q ⧸ center Q) m)
    (hT : ReeF4.Parabolics.splitTorus m ≤ ReeF4.Parabolics.diagonalTorus m)
    (hB : IsSimpleGroup (ReeF4.Model m) →
      ∀ (U : Sylow 2 (ReeF4.Model m)) (K : Subgroup (ReeF4.Model m)),
        Group.IsSolvable K → K ≠ ⊤ →
        (∀ p : ℕ, p.Prime → p ∣ Nat.card K → p = 2 ∨ p = 3) →
        (U : Subgroup (ReeF4.Model m)) ≤ K →
        ∃ g : ReeF4.Model m,
          K.map (MulAut.conj g).toMonoidHom ≤ ReeF4.Parabolics.borel m) :
    PairReducible (S : Subgroup Q) R := by
  obtain ⟨d, ⟨e⟩⟩ := hmodel
  let e' := e.trans d.modelEquiv
  let f := e'.toMonoidHom.comp (QuotientGroup.mk' (center Q))
  have hf : Function.Surjective f := e'.surjective.comp (QuotientGroup.mk'_surjective _)
  let _ := h.quasisimple
  let _ : IsSimpleGroup (Q ⧸ center Q) := IsQuasisimple.simple
  let _ : IsSimpleGroup (ReeF4.Model m) := e'.isSimpleGroup_congr.mp inferInstance
  let U : Sylow 2 (ReeF4.Model m) := S.mapSurjective hf
  let K := (R ⊔ (S : Subgroup Q)).map f
  have hUK : (U : Subgroup (ReeF4.Model m)) ≤ K := map_mono le_sup_right
  obtain ⟨g, hg⟩ := hB inferInstance U K (mapped_product_solvable h f)
    (mapped_product_ne_top h f hf) (fun _ hp hd => mapped_product_prime_divisors h f hp hd) hUK
  let f' := (MulAut.conj g).toMonoidHom.comp f
  have hf' : Function.Surjective f' := (MulAut.conj g).surjective.comp hf
  apply False.elim
  apply complement_not_map_le_three_coprime h f' hf'
    (ReeF4.Parabolics.ThreePrimeBorel.borel_coprime_three_of_torus m hT)
  rw [show R.map f' = (R.map f).map (MulAut.conj g).toMonoidHom from (map_map _ _ _).symm]
  exact (map_mono (map_mono le_sup_left)).trans hg

/-- The general Ree model excludes a nonreducible three-complement.

The fixed-group witness supplies the actual central-quotient isomorphism.  The
coroot realization identifies the root-defined split torus with its diagonal
realization, while the Sylow-overgroup theorem places the transported solvable
product in a conjugate Borel.  The Borel order is prime to three, contradicting
the nontrivial three-complement image.
-/
theorem pairReducible_of_equiv {m : ℕ} (hm : 1 ≤ m) (h : PairInput S R)
    (hmodel : Section02.LocalModels.IsReeF4At (Q ⧸ center Q) m) :
    PairReducible (S : Subgroup Q) R := by
  apply pairReducible_of_borel_geometry h hmodel
  · rw [ReeF4.Parabolics.splitTorus_eq_diagonalTorus]
  · intro hsimple U K hK hproper hprimes hUK
    let _ : IsSimpleGroup (ReeF4.Model m) := hsimple
    exact ReeF4.Parabolics.ThreeSylowContainment.exists_conjugate_le_borel_of_two_three_primes
      hm U K hK hproper hprimes hUK

end CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.EvenRankTwo.Ree
