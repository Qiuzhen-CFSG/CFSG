module

public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.EvenRankTwo.Reduction
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.OddClassical.Reduction

/-!
# Central covers in the binary exceptional pair obstruction

If the pair is not reducible, its intersection with the ambient center lies
in the complement's Frattini subgroup. An elementary complement therefore
embeds in the central quotient. For an extraspecial complement we use the
proved central-kernel bound instead: its image has order nine or 27. No
injectivity of an extraspecial complement is assumed.

The image of RS is a proper solvable subgroup containing the image Sylow
subgroup, and only two and three divide its order. Sylow conjugacy reduces
the remaining obstruction to overgroups of one marked Sylow subgroup of
the actual model. The containment and numerical overgroup hypotheses in
the last three lemmas are explicit obligations, not established geometry.

Source: Aschbacher–Smith, combined 1 March 2004 manuscript, proof of
Proposition 1.3.4, printed p.511 (PDF p.528 of `refs/quasithin.pdf`).
-/

@[expose] public section

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.EvenRankTwo.SmallDerived
universe u v
variable {Q : Type u} [Group Q] [Finite Q]
variable {G : Type v} [Group G] [Finite G]
variable {S : Sylow 2 Q} {R : Subgroup Q}

/-- The actual map through the ambient central quotient and a model isomorphism. -/
def quotientModelMap (e : Q ⧸ center Q ≃* G) : Q →* G :=
  e.toMonoidHom.comp (QuotientGroup.mk' (center Q))

omit [Finite Q] [Finite G] in
theorem quotientModelMap_surjective (e : Q ⧸ center Q ≃* G) :
    Function.Surjective (quotientModelMap e) :=
  e.surjective.comp (QuotientGroup.mk'_surjective _)

omit [Finite G] in
/-- Injectivity is proved before transporting an elementary complement. -/
theorem elementary_complement_injective (h : PairInput S R)
    (hn : ¬ PairReducible (S : Subgroup Q) R) (he : IsElementaryAbelian 3 R)
    (e : Q ⧸ center Q ≃* G) :
    Function.Injective ((quotientModelMap e).comp R.subtype) := by
  let _ := he
  let _ : Fact (IsPGroup 3 R) := ⟨h.oddComplement.isPGroup⟩
  have hk : ((QuotientGroup.mk' (center Q)).subgroupMap R).ker = ⊥ := by
    rw [Subgroup.ker_subgroupMap, QuotientGroup.ker_mk']
    apply bot_unique
    simpa only [frattini_eq_bot_of_isElementaryAbelian (R := R) (p := 3)] using
      OddClassical.center_intersection_le_frattini h hn
  have hi := (MonoidHom.ker_eq_bot_iff _).mp hk
  intro a b hab
  apply hi
  apply Subtype.ext
  exact e.injective hab

omit [Finite G] in
/-- Central kernels cannot shrink a nonreducible complement below order nine. -/
theorem model_complement_card (h : PairInput S R)
    (hn : ¬ PairReducible (S : Subgroup Q) R) (e : Q ⧸ center Q ≃* G) :
    Nat.card (R.map (quotientModelMap e)) = 9 ∨
      Nat.card (R.map (quotientModelMap e)) = 27 := by
  simpa only [quotientModelMap, ← map_map, card_map_of_injective (f := e.toMonoidHom) e.injective] using
    OddClassical.central_image_card h hn

omit [Finite G] in
theorem model_complement_not_le_of_nine_not_dvd (h : PairInput S R)
    (hn : ¬ PairReducible (S : Subgroup Q) R) (e : Q ⧸ center Q ≃* G)
    {P : Subgroup G} (hP : ¬ 9 ∣ Nat.card P) :
    ¬ R.map (quotientModelMap e) ≤ P := by
  intro hRP
  have hd : 9 ∣ Nat.card (R.map (quotientModelMap e)) := by
    rcases model_complement_card h hn e with hc | hc
    · rw [hc]
    · rw [hc]; decide
  exact hP (hd.trans (card_dvd_of_le hRP))

omit [Finite G] in
theorem model_product_solvable (h : PairInput S R) (e : Q ⧸ center Q ≃* G) :
    Group.IsSolvable ((R ⊔ (S : Subgroup Q)).map (quotientModelMap e)) := by
  let _ := product_solvable h
  exact Group.isSolvable_of_surjective ((quotientModelMap e).subgroupMap_surjective _)

omit [Finite G] in
theorem model_product_prime_divisors (h : PairInput S R)
    (e : Q ⧸ center Q ≃* G) {p : ℕ} (hp : p.Prime)
    (hd : p ∣ Nat.card ((R ⊔ (S : Subgroup Q)).map (quotientModelMap e))) :
    p = 2 ∨ p = 3 :=
  product_prime_divisors h hp (hd.trans (card_map_dvd _ _))

omit [Finite G] in
/-- Perfectness excludes a solvable image equal to the whole central quotient. -/
theorem model_product_ne_top (h : PairInput S R) (e : Q ⧸ center Q ≃* G) :
    (R ⊔ (S : Subgroup Q)).map (quotientModelMap e) ≠ ⊤ := by
  let _ := h.quasisimple
  let _ := h.quasisimple.simple
  let _ : Nontrivial G := e.symm.surjective.nontrivial
  let _ : Group.IsPerfect G := Group.IsPerfect.ofSurjective (quotientModelMap_surjective e)
  intro ht
  have hs := model_product_solvable h e
  rw [ht] at hs
  let _ := hs
  exact Group.IsPerfect.not_isSolvable G (Group.isSolvable_of_surjective
    (f := (topEquiv : (⊤ : Subgroup G) ≃* G).toMonoidHom) topEquiv.surjective)

omit [Finite G] in
theorem reducible_of_solvable_sylow_overgroups (h : PairInput S R)
    (e : Q ⧸ center Q ≃* G)
    (hloc : ∀ (U : Sylow 2 G) (H : Subgroup G), H ≠ ⊤ → Group.IsSolvable H →
      (U : Subgroup G) ≤ H →
      (∀ p : ℕ, p.Prime → p ∣ Nat.card H → p = 2 ∨ p = 3) →
      ¬ 9 ∣ Nat.card H) :
    PairReducible (S : Subgroup Q) R := by
  by_contra hn
  let f := quotientModelMap e
  let U := S.mapSurjective (quotientModelMap_surjective e)
  let H := (R ⊔ (S : Subgroup Q)).map f
  have hUH : (U : Subgroup G) ≤ H := map_mono le_sup_right
  have hRH : R.map f ≤ H := map_mono le_sup_left
  have hd : 9 ∣ Nat.card (R.map f) := by
    change 9 ∣ Nat.card (R.map (quotientModelMap e))
    rcases model_complement_card h hn e with hc | hc
    · rw [hc]
    · rw [hc]; decide
  exact hloc U H (model_product_ne_top h e) (model_product_solvable h e) hUH
    (fun _ hp hd => model_product_prime_divisors h e hp hd)
    (hd.trans (card_dvd_of_le hRH))

omit [Finite G] in
theorem reducible_of_two_parabolic_containment (h : PairInput S R)
    (e : Q ⧸ center Q ≃* G) (P₁ P₂ : Subgroup G)
    (h₁ : ¬ 9 ∣ Nat.card P₁) (h₂ : ¬ 9 ∣ Nat.card P₂)
    (hcont : ∀ (U : Sylow 2 G) (H : Subgroup G), H ≠ ⊤ → Group.IsSolvable H →
      (U : Subgroup G) ≤ H →
      (∀ p : ℕ, p.Prime → p ∣ Nat.card H → p = 2 ∨ p = 3) → ∃ g : G,
        H ≤ P₁.map (MulAut.conj g).toMonoidHom ∨
        H ≤ P₂.map (MulAut.conj g).toMonoidHom) :
    PairReducible (S : Subgroup Q) R := by
  apply reducible_of_solvable_sylow_overgroups h e
  intro U H hH hs hU hprimes hd
  obtain ⟨g, hg | hg⟩ := hcont U H hH hs hU hprimes
  · apply h₁
    have hh := hd.trans (card_dvd_of_le hg)
    rwa [card_map_of_injective (MulAut.conj g).injective] at hh
  · apply h₂
    have hh := hd.trans (card_dvd_of_le hg)
    rwa [card_map_of_injective (MulAut.conj g).injective] at hh

/-- Conjugating the image Sylow subgroup reduces the model obligation to a fixed marking. -/
theorem reducible_of_marked_sylow_overgroups (h : PairInput S R)
    (e : Q ⧸ center Q ≃* G) (U₀ : Sylow 2 G)
    (hloc : ∀ H : Subgroup G, H ≠ ⊤ → Group.IsSolvable H →
      (U₀ : Subgroup G) ≤ H →
      (∀ p : ℕ, p.Prime → p ∣ Nat.card H → p = 2 ∨ p = 3) →
      ¬ 9 ∣ Nat.card H) :
    PairReducible (S : Subgroup Q) R := by
  apply reducible_of_solvable_sylow_overgroups h e
  intro U H hH hs hU hprimes hd
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G U U₀
  let a := (MulAut.conj g).toMonoidHom
  have hmap : (U : Subgroup G).map a = (U₀ : Subgroup G) := by
    have hh := congrArg (fun V : Sylow 2 G => (V : Subgroup G)) hg
    rw [Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def] at hh
    convert hh using 1
    congr 1
  have hproper : H.map a ≠ ⊤ := by
    intro ht
    apply hH
    apply (Subgroup.map_injective (f := a) (MulAut.conj g).injective)
    rw [ht, Subgroup.map_top_of_surjective a (MulAut.conj g).surjective]
  let _ := hs
  have hsolv : Group.IsSolvable (H.map a) :=
    Group.isSolvable_of_surjective (a.subgroupMap_surjective H)
  apply hloc (H.map a) hproper hsolv
    (hmap ▸ map_mono hU) (fun p hp hdiv => hprimes p hp (by
      rwa [card_map_of_injective (MulAut.conj g).injective] at hdiv))
  rwa [card_map_of_injective (MulAut.conj g).injective]

end CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.EvenRankTwo.SmallDerived
