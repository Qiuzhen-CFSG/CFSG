module

public import Theory.GroupTheory.ConjugateSpanOrder
public import Theory.ElementaryAbelian.AbelianNormalClosure
public import Theory.GroupTheory.CentralizerModulo
public import Theory.GroupTheory.CharacteristicCentralizerFusion

/-!
# Centralizers and elementary abelian conjugate spans

A conjugate span is abelian exactly when its seed centralizes the span:
the acting group normalizes the span and hence its centralizer. If the seed
is elementary abelian, commutativity then makes the whole span elementary
abelian, by induction on its conjugate generators.

We also record normality and antitonicity of quotient centralizers. These
are the kernel facts used with a normal-core bound in Aschbacher–Smith,
F.9.2–4, printed p.318.
-/

@[expose] public section
open scoped IsMulCommutative commutatorElement
namespace Subgroup
variable {G : Type*} [Group G]

theorem conjugateSpanBy_commutative_iff (A H : Subgroup G) :
    IsMulCommutative (conjugateSpanBy A H) ↔
      A ≤ centralizer (conjugateSpanBy A H : Set G) := by
  constructor
  · intro hc
    exact (le_conjugateSpanBy A H).trans
      (le_centralizer_iff_isMulCommutative.mpr hc)
  · intro hc
    apply le_centralizer_iff_isMulCommutative.mp
    exact conjugateSpanBy_le hc ((le_normalizer_conjugateSpanBy A H).trans
      (normalizer_le_normalizer_centralizer _))

theorem conjugateSpanBy_elementary_of_commutative {p : ℕ} (A H : Subgroup G)
    [IsElementaryAbelian p A] [hc : IsMulCommutative (conjugateSpanBy A H)] :
    IsElementaryAbelian p (conjugateSpanBy A H) := by
  let : IsMulCommutative (closure {x | ∃ h ∈ H, ∃ a ∈ A, h * a * h⁻¹ = x}) := hc
  apply IsElementaryAbelian.closure_of_isMulCommutative
  rintro x ⟨h, _, a, ha, rfl⟩
  rw [conj_pow, elemPow_eq_one_of_isElementaryAbelian a ha, mul_one, mul_inv_cancel]

theorem centralizerModulo_antitone {A B N T : Subgroup G} [N.Normal]
    (hAB : A ≤ B) : centralizerModulo T B N ≤ centralizerModulo T A N := by
  intro x hx
  obtain ⟨hxT, hc⟩ := mem_centralizerModulo_iff.mp hx
  exact mem_centralizerModulo_iff.mpr ⟨hxT, fun a ha => hc a (hAB ha)⟩

theorem centralizerModulo_top_normal (A N : Subgroup G) [A.Normal] [N.Normal] :
    (centralizerModulo ⊤ A N).Normal := by
  let : (A.map (QuotientGroup.mk' N)).Normal :=
    Normal.map inferInstance _ (QuotientGroup.mk'_surjective N)
  dsimp only [centralizerModulo]
  infer_instance

theorem centralizerModulo_le_normalizer {A N T : Subgroup G} [N.Normal]
    (hNA : N ≤ A) : centralizerModulo T A N ≤ normalizer (A : Set G) := by
  apply le_normalizer_iff_commutator_le_left.mpr
  apply commutator_le.mpr
  intro a ha x hx
  exact hNA ((mem_centralizerModulo_iff.mp hx).2 a ha)

end Subgroup
