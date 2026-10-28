module

public import CFSG.Quasithin.ChapterE.Section02.Structure.OddLinearTwo.QuadraticEmbedding
public import Theory.SpecificGroups.PSL2.SplitSubcentralizerElementaryCard
public import GorensteinWalter.PSL2InvolutionFusion
/-!
# The original quadratic odd-PSL₂ elementary exclusion

The genuine source centralizer theorem identifies the original M with the
centralizer of an involution of K. Involution fusion marks it as the actual
split involution in a faithful projective semilinear image, retaining the
original subgroup and quotient maps. The proved source non-inner-field
witness and the full intermediate-centralizer calculation give |V|≤2
from V≤O₂(M), Sylow normality and elementary abelianness.

Source: Aschbacher–Smith E.2.7, printed pp.218–219. No desired centralizer,
field-triviality, automizer or actor-placement conclusion is an extra premise.
-/

public section
open Subgroup GorensteinWalter
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterE.Structure
/-- The actual quadratic odd source branch has no noncyclic elementary
subgroup in the original maximal's two-core normalized by the original Sylow. -/
theorem quadratic_linear_source_elementary_card_le_two
    {H : Type*} [Group H] [Finite H]
    (T : Sylow 2 H) (hP : ChapterB.IsMinimalParabolicOver T ⊤)
    (K : Subgroup H) [K.Normal] (hgen : K ⊔ (T : Subgroup H) = ⊤)
    (hO : pCore 2 H = ⊥)
    {F : Type*} [Field F] [Finite F] {p : ℕ} [Fact p.Prime]
    (ho : Odd p) (hF : Nat.card F = p ^ 2) (hp : 3 < p)
    (eK : K ≃* PSL2 F)
    (V : Subgroup H) (hV : IsElementaryAbelian 2 V)
    (hVM : V ≤ (pCore 2 (ChapterB.minimalParabolicMax T hP)).map
      (ChapterB.minimalParabolicMax T hP).subtype)
    (hVN : (T : Subgroup H) ≤ normalizer (V : Set H)) : Nat.card V ≤ 2 := by
  obtain ⟨t, ht, _, _, hM, _⟩ := quadratic_linear_source_centralizer T hP K hgen ho hF hp eK
  obtain ⟨s, hs, hsm⟩ := Theory.PSL2.square_field_split_involution_psl ho hF
  have hodd : IsOddPrimePower (Nat.card F) := ⟨p, 2, Fact.out, ho, by decide, hF⟩
  have het : IsInvolution (eK t) :=
    ⟨fun he => ht.1 (eK.injective (by simpa only [map_one] using he)),
     by rw [← map_pow, ht.2, map_one]⟩
  obtain ⟨g, hg⟩ := psl2_involutions_conjugate_of_odd_prime_power F hodd (eK t) s het hs
  let e' : K ≃* PSL2 F := eK.trans (MulAut.conj g)
  have he't : e' t = s := hg
  obtain ⟨q, hq, hqK, hinner, houter⟩ :=
    quadratic_linear_source_semilinear_embedding T hP K hgen hO ho hF hp e'
  let C := centralizer ({(SemidirectProduct.inl (pGammaL2FullSplitTorus F (-1)) : PGammaL2 F)} : Set (PGammaL2 F))
  have hqt : q (t : H) = SemidirectProduct.inl (pGammaL2FullSplitTorus F (-1)) := by
    rw [hqK, he't, hsm]
  have hpre : C.comap q = ChapterB.minimalParabolicMax T hP := by
    rw [hM]
    ext a
    change q a ∈ C ↔ a ∈ centralizer ({(t : H)} : Set H)
    rw [mem_centralizer_singleton_iff, mem_centralizer_singleton_iff]
    change q a * SemidirectProduct.inl (pGammaL2FullSplitTorus F (-1)) =
      SemidirectProduct.inl (pGammaL2FullSplitTorus F (-1)) * q a ↔ a * t = t * a
    rw [← hqt, ← map_mul, ← map_mul, hq.eq_iff]
  exact Theory.GroupTheory.elementary_core_bound_of_faithful_centralizer q hq
    (ChapterB.minimalParabolicMax T hP) C hpre
    (Theory.PSL2.split_subcentralizer_elementary_card_le_two ho hF hp q.range hinner houter)
    T (ChapterB.minimalParabolicMax_spec T hP).2 V hV hVM hVN

/-- The literal noncyclic elementary E.2.7 setup excludes the quadratic odd row. -/
theorem quadratic_linear_source_not_elementary_four
    {H : Type*} [Group H] [Finite H]
    (T : Sylow 2 H) (hP : ChapterB.IsMinimalParabolicOver T ⊤)
    (K : Subgroup H) [K.Normal] (hgen : K ⊔ (T : Subgroup H) = ⊤)
    (hO : pCore 2 H = ⊥)
    {F : Type*} [Field F] [Finite F] {p : ℕ} [Fact p.Prime]
    (ho : Odd p) (hF : Nat.card F = p ^ 2) (hp : 3 < p)
    (eK : K ≃* PSL2 F)
    (V : Subgroup H) (hV : IsElementaryAbelian 2 V)
    (hVM : V ≤ (pCore 2 (ChapterB.minimalParabolicMax T hP)).map
      (ChapterB.minimalParabolicMax T hP).subtype)
    (hVN : (T : Subgroup H) ≤ normalizer (V : Set H))
    (hcard : 4 ≤ Nat.card V) : False := by
  have hh := quadratic_linear_source_elementary_card_le_two T hP K hgen hO ho hF hp eK V hV hVM hVN
  omega
end CFSG.Quasithin.ChapterE.Structure
