module

public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.LocalPair
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.EvenRankTwo.Reduction
public import Theory.SpecificGroups.SymplecticFour.Sylow
public import Theory.SpecificGroups.SymplecticFour.Sylow.SolvableParabolic
public import Theory.SpecificGroups.SymplecticFour.LocalStructure.TwoLocalCover
public import Theory.GroupTheory.SolvableSmallThreeCore

/-!
# Borel placement of the symplectic Sylow pair

For the actual product H = RS, permutability and the pair hypotheses give
solvability, three-part at most 27, and two-part q⁴. Thus 64 divides |H|
when q = 2ⁿ and n ≥ 2. The solvable small-three-core theorem gives a
nontrivial intrinsic two-core. Its image in the full symplectic matrix group
is normalized by H, so genuine two-local coverage puts H in a conjugate of
one of the two full, proper flag parabolics.

Within either full parabolic, the rank-one quotient of its determinant-one
local factor shows that a solvable Sylow overgroup normalizes that Sylow
subgroup. Since q > 2, this applies to the conjugated product H; transporting
back gives R ≤ N(S). The final theorem discharges all premises from the actual
pair and matrix isomorphism. The concrete carrier remains the full
Matrix.symplecticGroup (Fin 2) F throughout.

Source: Aschbacher–Smith, combined 1 March 2004 manuscript, the
characteristic-two paragraph in the proof of Proposition 1.3.4, printed
p.511 (PDF p.528 of refs/quasithin.pdf).
-/

@[expose] public section

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.EvenRankTwo
open Theory.SpecificGroups.SymplecticFour
universe u v
variable {Q : Type u} [Group Q] [Finite Q]
variable {S : Sylow 2 Q} {R : Subgroup Q}
variable {F : Type v} [Field F] [Finite F] {n : ℕ}

/-- The actual matrix isomorphism determines the full Sylow two-order. -/
theorem symplectic_sylow_card (hF : Nat.card F = 2^n) (hn : 1 ≤ n)
    (e : Q ≃* Sp F) (S : Sylow 2 Q) : Nat.card S = 2^(4*n) := by
  let T := S.mapSurjective (f := e.toMonoidHom) e.surjective
  have hc : Nat.card S = Nat.card T := Nat.card_congr (e.subgroupMap S).toEquiv
  rw [hc, Nat.card_congr (T.equiv (unipotentSylow hF hn)).toEquiv]
  change Nat.card (unipotent (F := F)) = _
  rw [card_unipotent, hF, ← pow_mul, Nat.mul_comm n 4]

/-- The permuting pair has the product order, with three-part at most 27. -/
theorem symplectic_product_order (hF : Nat.card F = 2^n) (hn : 1 ≤ n)
    (e : Q ≃* Sp F) (h : PairInput S R) :
    ∃ b : ℕ, b ≤ 3 ∧
      Nat.card (R ⊔ (S : Subgroup Q) : Subgroup Q) = 2^(4*n) * 3^b := by
  rw [product_card h, symplectic_sylow_card hF hn e S]
  rcases h.oddComplement with ⟨_, hc⟩ | ⟨_, hc, _⟩
  · exact ⟨2, by decide, by rw [hc, mul_comm]⟩
  · exact ⟨3, le_rfl, by rw [hc, mul_comm]⟩

/-- The solvable product RS has a nontrivial intrinsic two-core. -/
theorem symplectic_product_twoCore_ne_bot (hF : Nat.card F = 2^n) (hn : 2 ≤ n)
    (e : Q ≃* Sp F) (h : PairInput S R) :
    pCore 2 (R ⊔ (S : Subgroup Q) : Subgroup Q) ≠ ⊥ := by
  let H := R ⊔ (S : Subgroup Q)
  have hthree : Nat.card (pCore 3 H) ≤ 27 := by
    have hd := (pCore 3 H).card_subgroup_dvd_card
    change Nat.card (pCore 3 H) ∣ Nat.card (R ⊔ (S : Subgroup Q) : Subgroup Q) at hd
    rw [product_card h] at hd
    have hcop := IsPGroup.coprime_card_of_ne 3 2 (by decide)
      (pCore 3 H) (S : Subgroup Q) pCore_isPGroup S.isPGroup'
    have hdiv := hcop.dvd_of_dvd_mul_right hd
    have hR : Nat.card R ≤ 27 := by
      rcases h.oddComplement with ⟨_, hc⟩ | ⟨_, hc, _⟩ <;> rw [hc] <;> decide
    exact (Nat.le_of_dvd Nat.card_pos hdiv).trans hR
  have h64 : 64 ∣ Nat.card H := by
    change 64 ∣ Nat.card (R ⊔ (S : Subgroup Q) : Subgroup Q)
    rw [product_card h, symplectic_sylow_card hF (by omega) e S]
    exact dvd_mul_of_dvd_right (pow_dvd_pow 2 (by omega : 6 ≤ 4*n)) _
  exact twoCore_ne_bot_of_solvable_small_three_core (product_solvable h)
    (fun p hp hd => product_prime_divisors h hp hd) hthree h64

omit [Finite Q] in
/-- Normalize the embedded intrinsic two-core before applying genuine two-local coverage. -/
theorem symplectic_parabolic_cover_of_twoCore_ne_bot (hF : Nat.card F = 2^n)
    (hn : 2 ≤ n) (e : Q ≃* Sp F) (H : Subgroup Q) (hcore : pCore 2 H ≠ ⊥) :
    ∃ g : Sp F, H.map (e.trans (MulAut.conj g)).toMonoidHom ≤ pointParabolic ∨
      H.map (e.trans (MulAut.conj g)).toMonoidHom ≤ planeParabolic := by
  let f := e.toMonoidHom.comp H.subtype
  let A := (pCore 2 H).map f
  have hi : Function.Injective f := e.injective.comp H.subtype_injective
  have hA : A ≠ ⊥ := fun hh =>
    hcore (((pCore 2 H).map_eq_bot_iff_of_injective hi).mp hh)
  have htwo : IsPGroup 2 A := pCore_isPGroup.map f
  have hHN : H.map e.toMonoidHom ≤ normalizer (A : Set (Sp F)) := by
    have hh := (pCore 2 H).le_normalizer_map f
    simpa only [normalizer_eq_top, ← MonoidHom.range_eq_map, f,
      MonoidHom.range_comp, range_subtype] using hh
  obtain ⟨g, hg⟩ := twoLocal_parabolic_cover hF hn (normalizer (A : Set (Sp F)))
    ⟨A, hA, htwo, rfl⟩
  have hmap : H.map (e.trans (MulAut.conj g)).toMonoidHom ≤
      (normalizer (A : Set (Sp F))).map (MulAut.conj g).toMonoidHom := by
    change H.map ((MulAut.conj g).toMonoidHom.comp e.toMonoidHom) ≤ _
    rw [← map_map]
    exact map_mono hHN
  exact ⟨g, hg.imp (hmap.trans ·) (hmap.trans ·)⟩

/-- Both factors lie in the same conjugate of an actual proper parabolic. -/
theorem symplectic_product_proper_parabolic
    (hF : Nat.card F = 2^n) (hn : 2 ≤ n) (e : Q ≃* Sp F) (h : PairInput S R) :
    ∃ (e' : Q ≃* Sp F) (P : Subgroup (Sp F)),
      (P = pointParabolic ∨ P = planeParabolic) ∧ P ≠ ⊤ ∧
      (R ⊔ (S : Subgroup Q)).map e'.toMonoidHom ≤ P := by
  obtain ⟨g, hg | hg⟩ := symplectic_parabolic_cover_of_twoCore_ne_bot hF hn e _
    (symplectic_product_twoCore_ne_bot hF hn e h)
  · exact ⟨e.trans (MulAut.conj g), pointParabolic, Or.inl rfl,
      pointParabolic_ne_top, hg⟩
  · exact ⟨e.trans (MulAut.conj g), planeParabolic, Or.inr rfl,
      planeParabolic_ne_top, hg⟩

/-- Assemble placement using a parabolic normalization theorem.
`symplectic_normalizes` below discharges this premise for the given field. -/
theorem symplectic_normalizes_of_parabolic_normalization
    (hF : Nat.card F = 2^n) (hn : 2 ≤ n) (e : Q ≃* Sp F)
    (h : PairInput S R)
    (hpar : ∀ (T : Sylow 2 (Sp F)) (H : Subgroup (Sp F)),
      Group.IsSolvable H → (T : Subgroup (Sp F)) ≤ H →
      (H ≤ pointParabolic ∨ H ≤ planeParabolic) → H ≤ normalizer (T : Set (Sp F))) :
    R ≤ normalizer (S : Set Q) := by
  let H := R ⊔ (S : Subgroup Q)
  obtain ⟨g, hg⟩ := symplectic_parabolic_cover_of_twoCore_ne_bot hF hn e H
    (symplectic_product_twoCore_ne_bot hF hn e h)
  let a := e.trans (MulAut.conj g)
  let T := S.mapSurjective (f := a.toMonoidHom) a.surjective
  let K := H.map a.toMonoidHom
  let _ : Group.IsSolvable H := product_solvable h
  have hK : Group.IsSolvable K :=
    Group.isSolvable_of_surjective (f := (a.subgroupMap H).toMonoidHom)
      (a.subgroupMap H).surjective
  have hTK : (T : Subgroup (Sp F)) ≤ K := map_mono le_sup_right
  have hKN := hpar T K hK hTK hg
  apply (map_le_map_iff_of_injective (f := a.toMonoidHom) a.injective).mp
  change R.map a.toMonoidHom ≤ (normalizer ((S : Subgroup Q) : Set Q)).map a.toMonoidHom
  rw [map_equiv_normalizer_eq (S : Subgroup Q) a]
  exact (map_mono (show R ≤ H from le_sup_left)).trans hKN

/-- The permuting three-complement lies in the Sylow normalizer in the full
symplectic carrier over a field of order 2ⁿ, n ≥ 2. -/
theorem symplectic_normalizes
    (hF : Nat.card F = 2^n) (hn : 2 ≤ n) (e : Q ≃* Sp F)
    (h : PairInput S R) : R ≤ normalizer (S : Set Q) := by
  let _ : CharP F 2 := EvenProjective.charTwo_of_card hF
  have hcard : 2 < Nat.card F := by
    rw [hF]
    have hh := Nat.pow_le_pow_right (by decide : 0 < 2) hn
    omega
  exact symplectic_normalizes_of_parabolic_normalization hF hn e h
    (solvable_parabolic_le_normalizer hcard)

end CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.EvenRankTwo
