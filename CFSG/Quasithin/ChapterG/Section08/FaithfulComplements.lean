module

public import CFSG.Quasithin.ChapterG.Section08.Basic
public import Theory.GroupAction.AbelianCoprimeFullFixedGeneration
public import Theory.GroupAction.SubgroupConjugation
public import Theory.GroupTheory.CharacteristicCentralizerFusion

/-!
# Faithful complements for elementary abelian two-actions

An elementary abelian two-group A acts on an odd-order group X. If B ≤ A
is faithful on X, some complement D to B preserves faithfulness on C_X(D),
and the kernel of A on this fixed subgroup is exactly D.

The proof inducts on |B|. Fixed-point generation for cyclic-quotient actor
subgroups produces a hyperplane E on whose fixed group B acts nontrivially.
Its index two forces C_A(C_X(E)) = E. Apply induction to B ∩ E inside E;
the resulting complement also complements B in A, and its action kernel
is contained in B ∩ E. This uses only the valid generation part of A.1.17;
nilpotence is unnecessary for this complement construction.

For G.8.5, the nilpotent A × B lemma G.8.4 supplies faithfulness on C_X(Y).
This group is A-invariant, so the complement construction applies to it.
All statements allow trivial X, handled by the same induction base case.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, G.8.2
and G.8.5, printed pp.349–350, combined manuscript of 1 March 2004.
-/

namespace CFSG.Quasithin.ChapterG.Section08
open Subgroup
open scoped IsMulCommutative
variable {G : Type*} [Group G]

private theorem elementary_le {A E : Subgroup G} [IsElementaryAbelian 2 A]
    (hEA : E ≤ A) : IsElementaryAbelian 2 E := by
  refine { toIsMulCommutative := ?_, exponent_dvd_p := ?_ }
  · exact le_centralizer_iff_isMulCommutative.mp
      (hEA.trans (A.le_centralizer.trans (centralizer_le hEA)))
  · exact (Monoid.exponent_dvd_of_monoidHom (inclusion hEA)
      (inclusion_injective hEA)).trans (IsElementaryAbelian.exponent_dvd_p 2 A)

private theorem overgroup_of_relIndex_two {E A H : Subgroup G}
    (hEH : E ≤ H) (hHA : H ≤ A) (hi : E.relIndex A = 2) :
    H = E ∨ H = A := by
  have hm := relIndex_mul_relIndex E H A hEH hHA
  rw [hi] at hm
  have hp : (E.relIndex H * H.relIndex A).Prime := hm ▸ Nat.prime_two
  rcases Nat.prime_mul_iff.mp hp with ⟨_, hr⟩ | ⟨_, hl⟩
  · exact Or.inr (le_antisymm hHA (relIndex_eq_one.mp hr))
  · exact Or.inl (le_antisymm (relIndex_eq_one.mp hl) hEH)

private theorem complement_centralizer (A B X D : Subgroup G)
    [IsMulCommutative A] (hsup : B ⊔ D = A)
    (hfaith : B ⊓ centralizer (X ⊓ centralizer (D : Set G) : Set G) = ⊥) :
    A ⊓ centralizer (X ⊓ centralizer (D : Set G) : Set G) = D := by
  let C := centralizer (X ⊓ centralizer (D : Set G) : Set G)
  have hBC : B ⊓ C = ⊥ := hfaith
  have hBA : B ≤ A := hsup ▸ le_sup_left
  have hDA : D ≤ A := hsup ▸ le_sup_right
  have hDC : D ≤ C := le_centralizer_iff.mpr inf_le_right
  have hs : B.subgroupOf A ⊔ D.subgroupOf A = ⊤ := by
    rw [← subgroupOf_sup hBA hDA, hsup, subgroupOf_self]
  apply le_antisymm _ (le_inf hDA hDC)
  intro x hx
  let BA := B.subgroupOf A
  let _ : BA.Normal := normal_of_isMulCommutative BA
  obtain ⟨b, hb, d, hd, he⟩ := mem_sup_of_normal_left.mp
    (show (⟨x, hx.1⟩ : A) ∈ BA ⊔ D.subgroupOf A by rw [hs]; trivial)
  have heG : (b : G) * (d : G) = x := congrArg Subtype.val he
  have hbC : (b : G) ∈ C := by
    have hbEq : (b : G) = x * (d : G)⁻¹ := by rw [← heG]; simp
    rw [hbEq]
    exact C.mul_mem hx.2 (C.inv_mem (hDC hd))
  have hb1 : (b : G) = 1 := hBC.le ⟨hb, hbC⟩
  simpa only [← heG, hb1, one_mul] using (show (d : G) ∈ D from hd)

variable [Finite G]

private theorem detecting_hyperplane (A B X : Subgroup G)
    [IsElementaryAbelian 2 A] (hodd : Odd (Nat.card X))
    (hnorm : A ≤ normalizer (X : Set G)) (hBA : B ≤ A)
    (hfaith : B ⊓ centralizer (X : Set G) = ⊥) (hB : B ≠ ⊥) :
    ∃ E : Subgroup G, E ≤ A ∧ B ⊔ E = A ∧ B ⊓ E < B ∧
      A ⊓ centralizer (X ⊓ centralizer (E : Set G) : Set G) = E := by
  classical
  obtain ⟨b, hb⟩ := ne_bot_iff_exists_ne_one.mp hB
  have hbne : (b : G) ≠ 1 := fun he => hb (Subtype.ext he)
  have hbnot : (b : G) ∉ centralizer (X : Set G) :=
    fun hc => hbne (hfaith.le ⟨b.property, hc⟩)
  let _ : Fact (IsPGroup 2 A) := ⟨IsElementaryAbelian.isPGroup 2 A⟩
  let _ : MulDistribMulAction A X := conjMulDistribMulActionOfLeNormalizer A X hnorm
  have hgen := iSup_fixedPoints_cyclicQuot_eq_top_of_coprime_abelian_pGroup_action
    (G := X) (A := A) 2 hodd.coprime_two_left
  have hex : ∃ Y : Subgroup A, IsCyclic (A ⧸ Y) ∧
      (b : G) ∉ centralizer (X ⊓ centralizer (Y.map A.subtype : Set G) : Set G) := by
    by_contra! hn
    apply hbnot
    intro x hx
    have htop : (⊤ : Subgroup X) ≤ (centralizer ({(b : G)} : Set G)).subgroupOf X := by
      rw [← hgen]
      refine iSup₂_le fun Y hY => ?_
      intro z hz
      have hzE : (z : G) ∈ X ⊓ centralizer (Y.map A.subtype : Set G) := by
        refine ⟨z.property, ?_⟩
        rintro y ⟨y, hy, rfl⟩
        have hf := congrArg Subtype.val (hz (⟨y, hy⟩ : Y))
        change (y : G) * (z : G) * (y : G)⁻¹ = (z : G) at hf
        exact mul_inv_eq_iff_eq_mul.mp hf
      exact mem_centralizer_singleton_iff.mpr ((hn Y hY) z hzE)
    have hz := htop (mem_top (⟨x, hx⟩ : X))
    exact (mem_centralizer_singleton_iff.mp hz)
  obtain ⟨Y, hY, hbY⟩ := hex
  let E := Y.map A.subtype
  let C := A ⊓ centralizer (X ⊓ centralizer (E : Set G) : Set G)
  have hEA : E ≤ A := map_subtype_le Y
  have hEC : E ≤ C := le_inf hEA (le_centralizer_iff.mpr inf_le_right)
  have hbE : (b : G) ∉ E := fun he => hbY (hEC he).2
  have hi : E.relIndex A = 2 := by
    have hd : E.relIndex A ∣ 2 := by
      have hd' : Y.index ∣ 2 := by
        rw [index_eq_card, ← hY.exponent_eq_card]
        exact (Group.exponent_quotient_dvd Y).trans
          (IsElementaryAbelian.exponent_dvd_p 2 A)
      simpa only [E, relIndex, subgroupOf, comap_map_eq, A.ker_subtype, sup_bot_eq] using hd'
    apply ((Nat.dvd_prime Nat.prime_two).mp hd).resolve_left
    intro h1
    exact hbE ((relIndex_eq_one.mp h1) (hBA b.property))
  have hCE : C = E := by
    rcases overgroup_of_relIndex_two hEC inf_le_left hi with h | h
    · exact h
    · exact (hbY (show (b : G) ∈ C by rw [h]; exact hBA b.property).2).elim
  have hBE : B ⊔ E = A := by
    rcases overgroup_of_relIndex_two le_sup_right (sup_le hBA hEA) hi with h | h
    · exact (hbE (h ▸ (mem_sup_left b.property : (b : G) ∈ B ⊔ E))).elim
    · exact h
  refine ⟨E, hEA, hBE, lt_of_le_of_ne inf_le_left ?_, hCE⟩
  intro he
  have hbBE : (b : G) ∈ B ⊓ E := by rw [he]; exact b.property
  exact hbE hbBE.2

private theorem exists_faithfulComplement (A B X : Subgroup G)
    (hA : IsElementaryAbelian 2 A) (hodd : Odd (Nat.card X))
    (hnorm : A ≤ normalizer (X : Set G)) (hBA : B ≤ A)
    (hfaith : B ⊓ centralizer (X : Set G) = ⊥) :
    ∃ D : Subgroup G, FaithfulComplement A B X D := by
  classical
  induction hc : Nat.card B using Nat.strong_induction_on generalizing A B with
  | h n ih =>
    let _ := hA
    by_cases hB : B = ⊥
    · refine ⟨A, ?_⟩
      simp only [FaithfulComplement, hB, bot_inf_eq, bot_sup_eq, true_and]
      exact le_antisymm inf_le_left (le_inf le_rfl (le_centralizer_iff.mpr inf_le_right))
    obtain ⟨E, hEA, hBE, hlt, hCE⟩ :=
      detecting_hyperplane A B X hodd hnorm hBA hfaith hB
    have hsmall : Nat.card (B ⊓ E : Subgroup G) < n := by
      rw [← hc]
      exact lt_of_le_of_ne (card_le_of_le hlt.le)
        (fun he => hlt.ne (eq_of_le_of_card_ge hlt.le he.ge))
    have hsubfaith : (B ⊓ E) ⊓ centralizer (X : Set G) = ⊥ :=
      bot_unique ((inf_le_inf_right _ inf_le_left).trans hfaith.le)
    obtain ⟨D, hD⟩ := ih (Nat.card (B ⊓ E : Subgroup G)) hsmall E (B ⊓ E)
      (elementary_le hEA) (hEA.trans hnorm) inf_le_right hsubfaith rfl
    rcases hD with ⟨hdis, hsup, hDf, _⟩
    have hDE : D ≤ E := hsup ▸ le_sup_right
    have hDA : D ≤ A := hDE.trans hEA
    have hBD : B ⊓ D = ⊥ := by
      apply bot_unique
      intro x hx
      exact hdis.le ⟨⟨hx.1, hDE hx.2⟩, hx.2⟩
    have hsupA : B ⊔ D = A := by
      apply le_antisymm (sup_le hBA hDA)
      rw [← hBE, ← hsup]
      exact sup_le le_sup_left (sup_le (inf_le_left.trans le_sup_left) le_sup_right)
    have hf : B ⊓ centralizer (X ⊓ centralizer (D : Set G) : Set G) = ⊥ := by
      apply bot_unique
      intro x hx
      have hxE : x ∈ E := hCE.le ⟨hBA hx.1,
        centralizer_le (inf_le_inf_left X (centralizer_le hDE)) hx.2⟩
      exact hDf.le ⟨⟨hx.1, hxE⟩, hx.2⟩
    exact ⟨D, hBD, hsupA, hf, complement_centralizer A B X D hsupA hf⟩

/-- G.8.2, with faithfulness and both complement clauses in the ambient group. -/
public theorem lemma_G_8_2 (A B X : Subgroup G)
    (hA : IsElementaryAbelian 2 A) (_hX : Group.IsNilpotent X)
    (hodd : Odd (Nat.card X)) (hnorm : A ≤ normalizer (X : Set G))
    (hBA : B ≤ A) (hfaith : B ⊓ centralizer (X : Set G) = ⊥) :
    ∃ D : Subgroup G, FaithfulComplement A B X D :=
  exists_faithfulComplement A B X hA hodd hnorm hBA hfaith

/-- The universal faithful-complement input, discharged for every finite ambient group. -/
public theorem faithfulComplementTheorem (G : Type*) [Group G] : FaithfulComplementTheorem G := by
  intro _ A B X hA hX hodd hnorm hBA hfaith
  exact lemma_G_8_2 A B X hA hX hodd hnorm hBA hfaith

/-- G.8.5. The complement can preserve faithfulness on the joint fixed group
of D and the A-invariant subgroup Y. -/
public theorem lemma_G_8_5 (A B X Y : Subgroup G)
    (hA : IsElementaryAbelian 2 A) (hX : Group.IsNilpotent X)
    (hodd : Odd (Nat.card X)) (hnorm : A ≤ normalizer (X : Set G))
    (hBA : B ≤ A) (hYX : Y ≤ X) (hAY : A ≤ normalizer (Y : Set G))
    (hBY : B ≤ centralizer (Y : Set G))
    (hfaith : B ⊓ centralizer (X : Set G) = ⊥) :
    ∃ D : Subgroup G, B ⊓ D = ⊥ ∧ B ⊔ D = A ∧
      B ⊓ centralizer (X ⊓ centralizer ((D ⊔ Y : Subgroup G) : Set G) : Set G) = ⊥ := by
  let _ := hA
  let _ : IsElementaryAbelian 2 B := elementary_le hBA
  let X' := X ⊓ centralizer (Y : Set G)
  have hfaith' : B ⊓ centralizer (X' : Set G) = ⊥ :=
    lemma_G_8_4 B X Y (IsElementaryAbelian.isPGroup 2 B) hX hodd hYX
      (hBA.trans hnorm) hBY hfaith
  have hnorm' : A ≤ normalizer (X' : Set G) :=
    (le_inf hnorm (hAY.trans (normalizer_le_normalizer_centralizer Y))).trans
      inf_normalizer_le_normalizer_inf
  have hodd' : Odd (Nat.card X') := hodd.of_dvd_nat (card_dvd_of_le inf_le_left)
  obtain ⟨D, hD⟩ := exists_faithfulComplement A B X' hA hodd' hnorm' hBA hfaith'
  refine ⟨D, hD.1, hD.2.1, ?_⟩
  have heq : X ⊓ centralizer ((D ⊔ Y : Subgroup G) : Set G) = X' ⊓ centralizer (D : Set G) := by
    apply le_antisymm
    · exact le_inf
        (le_inf inf_le_left (inf_le_right.trans (centralizer_le (show Y ≤ D ⊔ Y from le_sup_right))))
        (inf_le_right.trans (centralizer_le (show D ≤ D ⊔ Y from le_sup_left)))
    · intro x hx
      refine ⟨hx.1.1, ?_⟩
      have hc : D ⊔ Y ≤ centralizer ({x} : Set G) := by
        apply sup_le
        · intro d hd
          exact mem_centralizer_singleton_iff.mpr (hx.2 d hd)
        · intro y hy
          exact mem_centralizer_singleton_iff.mpr (hx.1.2 y hy)
      intro z hz
      exact mem_centralizer_singleton_iff.mp (hc hz)
  change B ⊓ centralizer
    ((X ⊓ centralizer ((D ⊔ Y : Subgroup G) : Set G) : Subgroup G) : Set G) = ⊥
  rw [heq]
  exact hD.2.2.1

end CFSG.Quasithin.ChapterG.Section08
