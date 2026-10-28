module

public import Theory.GroupAction.AbelianCoprimeFixedGeneration
public import Theory.GroupTheory.CoprimeCentralizerDecomposition
public import Theory.GroupTheory.CharacteristicCentralizerFusion

/-!
# Generation by commutators of hyperplane centralizers

An elementary abelian two-subgroup A normalizing a finite odd-prime subgroup X
satisfies [X,A] = ⟨[C_X(B),A] : |A:B|=2⟩. In particular, these subgroups generate
X whenever X=[X,A]. No faithfulness or lower bound on the rank of A is needed.

Coprime abelian fixed-point generation supplies the centralizers with cyclic
actor quotient. Coprime decomposition separates each into its commutator and
its A-fixed subgroup. The common fixed subgroup normalizes all the commutator
factors, allowing the commutator identity to pass through their join. An
exponent-two cyclic quotient has order one or two; the order-one case has
trivial commutator and can be discarded.

Source: Aschbacher--Smith, combined manuscript (1 March 2004), E.1.10(6),
printed pp.211--212, the application of Generation by Centralizers of Hyperplanes.
-/

open scoped IsMulCommutative commutatorElement
namespace Subgroup
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
private theorem abelian_normalizes_fixed (X A B : Subgroup G)
    [IsMulCommutative A] (hAX : A ≤ normalizer X) (hBA : B ≤ A) :
    A ≤ normalizer (X ⊓ centralizer (B : Set G) : Subgroup G) := by
  apply (le_inf hAX ?_).trans inf_normalizer_le_normalizer_inf
  apply (le_trans ?_ (centralizer_le_normalizer (B : Set G))).trans
    (normalizer_le_normalizer_centralizer B)
  intro a ha b hb
  exact congrArg Subtype.val (mul_comm (⟨b, hBA hb⟩ : A) ⟨a, ha⟩)

omit [Finite G] in
private theorem commutator_generated_of_fixed_decomposition
    {ι : Type*} (X A : Subgroup G) (C : ι → Subgroup G)
    (hgen : X = ⨆ i, C i) (hC : ∀ i, C i ≤ X)
    (hfixed : ∀ i, X ⊓ centralizer (A : Set G) ≤ C i)
    (hdecomp : ∀ i, C i = ⁅C i, A⁆ ⊔ (C i ⊓ centralizer (A : Set G))) :
    ⁅X, A⁆ = ⨆ i, ⁅C i, A⁆ := by
  let D := ⨆ i, ⁅C i, A⁆
  have hfixedD : X ⊓ centralizer (A : Set G) ≤ normalizer D :=
    (le_iInf fun i => (hfixed i).trans (normalizer_commutator_ge_left _ _)).trans
      (iInf_normalizer_le_normalizer_iSup _)
  have hXD : X ≤ normalizer D := by
    rw [hgen]
    apply iSup_le
    intro i
    rw [hdecomp i]
    exact sup_le ((le_iSup (fun j => ⁅C j, A⁆) i).trans D.le_normalizer)
      ((inf_le_inf_right _ (hC i)).trans hfixedD)
  apply le_antisymm
  · apply commutator_le.mpr
    intro x hx a ha
    rw [hgen] at hx
    have hall : ∀ a ∈ A, ⁅x, a⁆ ∈ D := by
      induction hx using iSup_induction' with
      | hp i y hy =>
          intro a ha
          exact (le_iSup (fun j => ⁅C j, A⁆) i) (commutator_mem_commutator hy ha)
      | h1 => simp
      | hmul y z hy _ ihy ihz =>
          intro a ha
          rw [commutatorElement_mul_left_eq_conj_mul]
          exact D.mul_mem ((mem_normalizer_iff.mp (hXD (hgen ▸ hy)) _).mp (ihz a ha))
            (ihy a ha)
    exact hall a ha
  · exact iSup_le fun i => commutator_mono (hC i) le_rfl

/-- Hyperplane centralizer commutators generate the full action commutator. -/
public theorem iSup_hyperplane_centralizer_commutator
    {p : ℕ} [Fact p.Prime] (hp : p ≠ 2)
    (X A : Subgroup G) (hX : IsPGroup p X) [IsElementaryAbelian 2 A]
    (hAX : A ≤ normalizer X) :
    (⨆ (B : Subgroup A) (_ : B.index = 2),
      ⁅X ⊓ centralizer (B.map A.subtype : Set G), A⁆) = ⁅X, A⁆ := by
  classical
  let _ : Normalizes A X := ⟨hAX⟩
  let _ : Fact (IsPGroup p X) := ⟨hX⟩
  let C (B : Subgroup A) := X ⊓ centralizer (B.map A.subtype : Set G)
  have hcop : Nat.Coprime (Nat.card A) (Nat.card X) :=
    IsPGroup.coprime_card_of_ne 2 p hp.symm A X (IsElementaryAbelian.isPGroup 2 A) hX
  have hAp : Nat.Coprime (Nat.card A) p := by
    obtain ⟨n, hn⟩ := (IsElementaryAbelian.isPGroup 2 A).exists_card_eq
    rw [hn]
    exact (Nat.coprime_primes Nat.prime_two (Fact.out : p.Prime)).mpr hp.symm |>.pow_left n
  have hmap (B : Subgroup A) :
      (FixedPoints.subgroup B X).map X.subtype = C B := by
    ext x
    constructor
    · rintro ⟨x, hx, rfl⟩
      refine ⟨x.property, ?_⟩
      rintro b ⟨b, hb, rfl⟩
      have he := congrArg Subtype.val (hx ⟨b, hb⟩)
      change (b : G) * (x : G) * (b : G)⁻¹ = (x : G) at he
      exact mul_inv_eq_iff_eq_mul.mp he
    · rintro ⟨hx, hc⟩
      refine ⟨⟨x, hx⟩, ?_, rfl⟩
      intro b
      apply Subtype.ext
      change (b : G) * x * (b : G)⁻¹ = x
      have he : (b : G) * x = x * (b : G) := hc _ (mem_map_of_mem _ b.property)
      rw [he, mul_inv_cancel_right]
  let I := {B : Subgroup A // IsCyclic (A ⧸ B)}
  have hgen : X = ⨆ i : I, C i.1 := by
    have hg := congrArg (fun H : Subgroup X => H.map X.subtype)
      (iSup_fixedPoints_cyclicQuot_eq_top_of_coprime_abelian_pGroup
        (G := X) (A := A) (q := p) hAp)
    simpa only [map_iSup, hmap, ← MonoidHom.range_eq_map, X.range_subtype, I, iSup_subtype] using hg.symm
  have hsplit (i : I) : C i.1 = ⁅C i.1, A⁆ ⊔ (C i.1 ⊓ centralizer (A : Set G)) := by
    have hpC : IsPGroup p (C i.1) := hX.of_injective (inclusion inf_le_left)
      (inclusion_injective _)
    exact eq_commutator_sup_centralizer_of_solvable_coprime _ _
      (abelian_normalizes_fixed X A _ hAX (map_subtype_le _))
      (@IsNilpotent.to_isSolvable _ _ hpC.isNilpotent)
      (hcop.of_dvd_right (card_dvd_of_le inf_le_left))
  have hcomm := commutator_generated_of_fixed_decomposition X A (fun i : I => C i.1)
    hgen (fun _ => inf_le_left)
    (fun i => inf_le_inf_left _ (centralizer_le (map_subtype_le i.1))) hsplit
  apply le_antisymm
  · exact iSup₂_le fun B _ => commutator_mono inf_le_left le_rfl
  · rw [hcomm]
    apply iSup_le
    intro i
    have hidx : i.1.index ∣ 2 := by
      rw [index_eq_card, ← i.2.exponent_eq_card]
      exact (Group.exponent_quotient_dvd i.1).trans (IsElementaryAbelian.exponent_dvd_p 2 A)
    rcases (Nat.dvd_prime Nat.prime_two).mp hidx with hi | hi
    · have he : i.1 = ⊤ := index_eq_one.mp hi
      have hc : ⁅C i.1, A⁆ = ⊥ := by
        apply commutator_eq_bot_iff_le_centralizer.mpr
        simpa only [C, he, ← MonoidHom.range_eq_map, A.range_subtype] using
          (inf_le_right : X ⊓ centralizer (A : Set G) ≤ centralizer (A : Set G))
      rw [hc]
      exact bot_le
    · exact le_iSup_of_le i.1 (le_iSup_of_le hi le_rfl)
/-- The generation identity used in E.1.10(6). -/
public theorem eq_iSup_hyperplane_centralizer_commutator
    {p : ℕ} [Fact p.Prime] (hp : p ≠ 2)
    (X A : Subgroup G) (hX : IsPGroup p X) [IsElementaryAbelian 2 A]
    (hAX : A ≤ normalizer X) (hcomm : X = ⁅X, A⁆) :
    X = ⨆ (B : Subgroup A) (_ : B.index = 2),
      ⁅X ⊓ centralizer (B.map A.subtype : Set G), A⁆ :=
  hcomm.trans (iSup_hyperplane_centralizer_commutator hp X A hX hAX).symm

end Subgroup
