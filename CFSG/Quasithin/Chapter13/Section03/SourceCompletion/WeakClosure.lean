module
public import CFSG.Quasithin.ChapterE.Section03.Offenders.Transport
public import CFSG.Quasithin.ChapterE.Section03.Offenders.Core.Lifting
public import Theory.GroupTheory.IntersectingConjugateDisplacement

/-!
# The weak-closure step for the natural unitary six-module

For a noncentralizing conjugate `W=Vᵍ`, commutation of intersecting conjugates
forces `V∩W=1`. Centralizer rigidity below `r` then places its actual induced
normalizer action in the fixed-space family `A_(4-k)`.

The genuine binary `G₂` row B.4.6(3,9) leaves `k=2`, image rank three, and
displacement corank at most three. Since `V` has rank six, the action kernel
in `W` is nontrivial. It makes the `V`-conjugate span of `W` abelian, so `W`
centralizes the displacement. The bound `r>3` forces `W≤N(V)`, contradicting
`k=2`. This proves the original weak-closure conclusion without assuming
that the reverse normalizer contains a specified hyperplane.

The action row remains an explicit earlier model theorem; this module does
not assert that the full source hypotheses already construct it. The earlier
inputs are 13.3.17(2) and 13.3.19(1), the latter supplied by 13.3.18 and fusion.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), Lemma
13.3.19(2), printed pp.895–896; B.4.6(3,9), printed pp.88–89.
-/

public section
namespace CFSG.Quasithin.Chapter13.Section03.SourceCompletion
open Subgroup ChapterE Representation.BinaryOffender
open scoped IsMulCommutative
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
/-- For disjoint subgroups, mutual relative normalizers commute. -/
theorem reverse_normalizer_centralizes
    {V W A : Subgroup G} (hdis : V ⊓ W = ⊥)
    (hAW : A ≤ W) (hAN : A ≤ normalizer (V : Set G)) :
    V ⊓ normalizer (W : Set G) ≤ centralizer (A : Set G) := by
  apply commutator_eq_bot_iff_le_centralizer.mp
  apply bot_unique
  rw [← hdis]
  exact le_inf
    ((commutator_mono inf_le_left le_rfl).trans
      (le_normalizer_iff_commutator_le_left.mp hAN))
    ((commutator_mono le_rfl hAW).trans
      (le_normalizer_iff_commutator_le_right.mp inf_le_right))

omit [Finite G] in
/-- Below `r`, the centralizer of a subgroup of a disjoint conjugate is the
reverse normalizer. This uses the intersection condition, not the parameter `s`. -/
theorem centralizer_eq_reverse_normalizer
    {V : Subgroup G} [IsElementaryAbelian 2 V] (g : G) {A : Subgroup G}
    (hdis : V ⊓ V.map (MulAut.conj g).toMonoidHom = ⊥)
    (hA : A ≤ offenderNormalizer V g)
    (hr : (subgroupCorank (V.map (MulAut.conj g).toMonoidHom) A : ℕ∞) < globalR V) :
    V ⊓ centralizer (A : Set G) =
      V ⊓ normalizer (V.map (MulAut.conj g).toMonoidHom : Set G) := by
  have hAW := hA.trans inf_le_left
  have hAN := hA.trans inf_le_right
  apply le_antisymm
  · apply inf_le_inf_left
    apply centralizer_le_normalizer_of_corank_lt_globalR hAW
    rwa [globalR_map_equiv]
  · exact le_inf inf_le_left (reverse_normalizer_centralizes hdis hAW hAN)

/-- The literal induced action belongs to `A_(n-k)` using `r>n-1` and
commutation of intersecting conjugates. -/
theorem induced_family_of_disjoint_conjugate
    {V : Subgroup G} [IsElementaryAbelian 2 V] (g : G)
    (hdis : V ⊓ V.map (MulAut.conj g).toMonoidHom = ⊥)
    (hAC : ¬ offenderNormalizer V g ≤ centralizer (V : Set G))
    (n : ℕ) (hr : (n : ℕ∞) ≤ globalR V)
    (hk : subgroupCorank (V.map (MulAut.conj g).toMonoidHom)
      (offenderNormalizer V g) < n) :
    inducedAutomizer V (offenderNormalizer V g) ∈
      fixedSpaceFamily (automizerRepresentation V)
        (n - subgroupCorank (V.map (MulAut.conj g).toMonoidHom)
          (offenderNormalizer V g)) := by
  let W := V.map (MulAut.conj g).toMonoidHom
  let A := offenderNormalizer V g
  let _ : IsElementaryAbelian 2 W := IsElementaryAbelian.map _
  have hAW : A ≤ W := inf_le_left
  have hAN : A ≤ normalizer (V : Set G) := inf_le_right
  let _ : IsElementaryAbelian 2 A := offender_elementary_of_le hAW
  change subgroupCorank W A < n at hk
  have hcar : (subgroupCorank W A : ℕ∞) < globalR V :=
    lt_of_lt_of_le (by exact_mod_cast hk) hr
  have heq := centralizer_eq_reverse_normalizer g hdis (le_refl A) hcar
  refine ⟨Nat.sub_pos_of_lt hk,
    ⟨fun hbot => hAC ((inducedAutomizer_eq_bot_iff hAN).mp hbot),
      inducedAutomizer_elementary V A hAN⟩, ?_⟩
  intro D hDA hD
  change Nat.log 2 (D.relIndex (inducedAutomizer V A)) < n - subgroupCorank W A at hD
  obtain ⟨B, hBA, hBI, hcor⟩ := core_lift_image_subgroup hAN D hDA
  have hcorB : subgroupCorank W B < n := by
    rw [offender_corank_add hBA hAW, hcor]
    omega
  have hcent := centralizer_eq_reverse_normalizer g hdis hBA
    (lt_of_lt_of_le (by exact_mod_cast hcorB) hr)
  rw [← hBI]
  ext v
  rw [mem_fixedSpace_inducedAutomizer V A hAN,
    mem_fixedSpace_inducedAutomizer V B (hBA.trans hAN)]
  have he := congrArg (fun K : Subgroup G => (v.toMul : G) ∈ K)
    (heq.trans hcent.symm)
  simpa only [Subgroup.mem_inf, v.toMul.property, true_and] using iff_of_eq he

/-- A six-dimensional module with the binary `G₂` fixed-space-family row has
no noncentralizing normalizer of corank at most two. The row supplied here is
B.4.6(3,9): parameter two, actor rank three and displacement corank at most three. -/
theorem small_corank_normalizer_centralizes
    {V : Subgroup G} [IsElementaryAbelian 2 V]
    (hV : rank V = 6)
    (hinter : ∀ g : G, V ⊓ V.map (MulAut.conj g).toMonoidHom ≠ ⊥ →
      ⁅V, V.map (MulAut.conj g).toMonoidHom⁆ = ⊥)
    (hr : (3 : ℕ∞) < globalR V)
    (hB46 : ∀ (A : Subgroup G), A ≤ normalizer (V : Set G) →
      ∀ k : ℕ, 2 ≤ k → inducedAutomizer V A ∈
        fixedSpaceFamily (automizerRepresentation V) k →
      k = 2 ∧ rank (inducedAutomizer V A) = 3 ∧ subgroupCorank V ⁅V,A⁆ ≤ 3)
    (g : G)
    (hk : subgroupCorank (V.map (MulAut.conj g).toMonoidHom)
      (offenderNormalizer V g) ≤ 2) :
    offenderNormalizer V g ≤ centralizer (V : Set G) := by
  by_contra hAC
  let W := V.map (MulAut.conj g).toMonoidHom
  let A := offenderNormalizer V g
  let _ : IsElementaryAbelian 2 W := IsElementaryAbelian.map _
  have hAW : A ≤ W := inf_le_left
  have hAN : A ≤ normalizer (V : Set G) := inf_le_right
  change subgroupCorank W A ≤ 2 at hk
  have hdis : V ⊓ W = ⊥ := by
    by_contra hn
    exact hAC (hAW.trans
      (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp (hinter g hn))))
  have hr4 : (4 : ℕ∞) ≤ globalR V := ENat.natCast_add_one_le_iff.mpr hr
  have hfam := induced_family_of_disjoint_conjugate g hdis hAC 4 hr4 (by change subgroupCorank W A < 4; omega)
  obtain ⟨hparam, hactor, hdisp⟩ := hB46 A hAN (4 - subgroupCorank W A) (by omega) hfam
  have hk2 : subgroupCorank W A = 2 := by omega
  have hW : rank W = 6 := by
    unfold rank
    rw [show Nat.card W = Nat.card V from Subgroup.card_map_of_injective (MulAut.conj g).injective]
    exact hV
  have hker : W ⊓ centralizer (V : Set G) ≠ ⊥ := by
    intro hbot
    have hAbot : A ⊓ centralizer (V : Set G) = ⊥ :=
      bot_unique ((inf_le_inf_right _ hAW).trans hbot.le)
    have harank := rank_inducedAutomizer V A hAN
    rw [hAbot] at harank
    have hc := offender_corank_add (W := W) (A := A) (B := ⊥) bot_le hAW
    have hbW : subgroupCorank W ⊥ = rank W := by simp [subgroupCorank, rank]
    have hbA : subgroupCorank A ⊥ = rank A := by simp [subgroupCorank, rank]
    rw [hbW, hbA, hW, hk2] at hc
    rw [hbA, hactor] at harank
    omega
  have hWC : W ≤ centralizer ((⁅V,A⁆ : Subgroup G) : Set G) :=
    centralizes_displacement_of_intersecting_conjugates W V A
      (intersecting_conjugates_commute_map_equiv V hinter (MulAut.conj g)) hker hAW
  have hdispV : ⁅V,A⁆ ≤ V := le_normalizer_iff_commutator_le_left.mp hAN
  have hWN : W ≤ normalizer (V : Set G) := hWC.trans
    (centralizer_le_normalizer_of_corank_lt_globalR hdispV
      (lt_of_le_of_lt (by exact_mod_cast hdisp) hr))
  have hAW' : A = W := inf_eq_left.mpr hWN
  have hk0 : subgroupCorank W A = 0 := by rw [hAW']; simp [subgroupCorank]
  omega

/-- The actual weak closure `W₂(T,V)` centralizes `V`. No chosen offender,
reverse-normalizer hyperplane, or weak-closure conclusion is an input. -/
theorem weakClosure_two_centralizes_of_unitary_action
    {V : Subgroup G} [IsElementaryAbelian 2 V] {T : Subgroup G}
    (hTN : T ≤ normalizer (V : Set G))
    (hV : rank V = 6)
    (hinter : ∀ g : G, V ⊓ V.map (MulAut.conj g).toMonoidHom ≠ ⊥ →
      ⁅V, V.map (MulAut.conj g).toMonoidHom⁆ = ⊥)
    (hr : (3 : ℕ∞) < globalR V)
    (hB46 : ∀ (A : Subgroup G), A ≤ normalizer (V : Set G) →
      ∀ k : ℕ, 2 ≤ k → inducedAutomizer V A ∈
        fixedSpaceFamily (automizerRepresentation V) k →
      k = 2 ∧ rank (inducedAutomizer V A) = 3 ∧ subgroupCorank V ⁅V,A⁆ ≤ 3) :
    indexedWeakClosure V T 2 ≤ centralizer (V : Set G) := by
  rw [weakClosure_eq_sSup_gamma]
  apply sSup_le
  rintro A ⟨⟨g, hAW, hi⟩, hAT⟩
  let W := V.map (MulAut.conj g).toMonoidHom
  let B := offenderNormalizer V g
  let _ : IsElementaryAbelian 2 W := IsElementaryAbelian.map _
  have hAB : A ≤ B := le_inf hAW (hAT.trans hTN)
  have hcor : subgroupCorank W A = 2 := by
    change Nat.log 2 (A.relIndex (V.map (MulAut.conj g).toMonoidHom)) = 2
    rw [hi, Nat.log_pow (by decide)]
  have hc := offender_corank_add hAB (show B ≤ W from inf_le_left)
  have hB : subgroupCorank W B ≤ 2 := by omega
  exact hAB.trans (small_corank_normalizer_centralizes hV hinter hr hB46 g hB)

end CFSG.Quasithin.Chapter13.Section03.SourceCompletion
