module

public import Theory.GroupTheory.ConjugateSpanOrder
public import Theory.GroupTheory.CharacteristicCentralizerFusion
public import Theory.GroupTheory.TwoLocalUniquenessControl

/-!
# The centralizer deduction in the Held branch

An element centralizing Lₜ fixes its normal closure Kₜ once the pointwise
fixer of Lₜ in Aut(Kₜ) is trivial. If C_G(L) were nontrivial, its two-group
structure and LT-invariance would put its full normalizer in the unique
maximal two-local M. That would force Kₜ ≤ M, a contradiction. The Frattini
factorization then gives C_G(Lₜ)=Vₜ and hence C_{C_G(t)}(Kₜ)=Vₜ.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, combined
manuscript of 1 March 2004, Theorem 12.7.7, printed pp.840–841 (PDF 857–858).
The Frattini paragraph drops a Vₜ factor in one equality; its subsequent
conclusion explicitly uses C_G(Lₜ)=Vₜ C_G(LₜX), which is the version here.
The actual local factorization and covering-group fixer are still to be
constructed. The missing transition to P,Y,U,φ and (*) on p.841, and the
recognition theorem Asc94 44.4, are not supplied by these conditional lemmas.
-/

open Subgroup

namespace CFSG.Quasithin.Chapter12.Section07.HeldIdentification
variable {G : Type*} [Group G]

/-- The relative closure defining Kₜ is normalized by C_G(t), so its
embedded center Vₜ is normalized too. This uses 12.7.5's center equality;
it does not assert that Kₜ is normal in the ambient simple group. -/
public theorem normalClosure_center_normalized (Lt : Subgroup G) (t : G)
    (Vt : Subgroup G)
    (hcenter : Vt = (center (conjugateSpanBy Lt (centralizer ({t} : Set G)))).map
      (conjugateSpanBy Lt (centralizer ({t} : Set G))).subtype) :
    centralizer ({t} : Set G) ≤ normalizer (Vt : Set G) := by
  rw [hcenter]
  exact (le_normalizer_conjugateSpanBy Lt _).trans
    (normalizer_le_normalizer_characteristic_image _ _)

/-- An automorphism of K fixing Lₜ pointwise is trivial, so every ambient
element centralizing Lₜ centralizes K. The element t ∈ Lₜ first places the
conjugator in C_G(t), where K is normalized. The pointwise-fixer hypothesis
is a separate local covering-group calculation, not global recognition. -/
public theorem centralizer_seed_eq (Lt K : Subgroup G) (t : G)
    (ht : t ∈ Lt) (hLt : Lt ≤ K)
    (hK : centralizer ({t} : Set G) ≤ normalizer (K : Set G))
    (hfix : ∀ a : MulAut K, (∀ l : K, (l : G) ∈ Lt → a l = l) → a = 1) :
    centralizer (Lt : Set G) = centralizer ({t} : Set G) ⊓ centralizer (K : Set G) := by
  apply le_antisymm
  · intro g hg
    have hgt : g ∈ centralizer ({t} : Set G) :=
      (centralizer_le (Set.singleton_subset_iff.mpr ht)) hg
    refine ⟨hgt, ?_⟩
    let n : normalizer (K : Set G) := ⟨g, hK hgt⟩
    have he : K.normalizerMonoidHom n = 1 := by
      apply hfix
      intro l hl
      apply Subtype.ext
      change g * (l : G) * g⁻¹ = (l : G)
      rw [← mem_centralizer_iff.mp hg l hl, mul_assoc, mul_inv_cancel, mul_one]
    have hn : n ∈ K.normalizerMonoidHom.ker := he
    rw [normalizerMonoidHom_ker] at hn
    exact hn
  · exact inf_le_right.trans (centralizer_le hLt)

/-- The unique maximal two-local overgroup of LT forces C_G(L)=1 when
an escaping K centralizes C_G(Lₜ). The argument applies uniqueness to the
nontrivial two-subgroup C_G(L), which LT normalizes. In particular it needs
no assertion that LT normalizes C_G(Lₜ). -/
public theorem centralizer_eq_bot_of_unique_twoLocal [Finite G] (L T V Lt K M : Subgroup G)
    (hVL : V ≤ L) (hLtL : Lt ≤ L)
    (hT : T ≤ normalizer (L : Set G))
    (hV : IsPGroup 2 (centralizer (V : Set G)))
    (hLK : centralizer (Lt : Set G) ≤ centralizer (K : Set G))
    (hKM : ¬ K ≤ M)
    (hunique : ∀ N : Subgroup G, IsMaximalTwoLocal N → L ⊔ T ≤ N → N = M) :
    centralizer (L : Set G) = ⊥ := by
  by_contra hne
  have htwo : IsPGroup 2 (centralizer (L : Set G)) :=
    hV.of_injective (inclusion (centralizer_le hVL)) (inclusion_injective _)
  have hn : L ⊔ T ≤ normalizer (centralizer (L : Set G) : Set G) :=
    (sup_le L.le_normalizer hT).trans (normalizer_le_normalizer_centralizer L)
  have hKC : K ≤ centralizer (centralizer (L : Set G) : Set G) :=
    le_centralizer_iff.mp ((centralizer_le hLtL).trans hLK)
  exact hKM (hKC.trans ((centralizer_le_normalizer _).trans
    (normalizer_le_of_unique_maximalTwoLocal hunique htwo hne hn)))

/-- The centralizer deduction in the third paragraph of 12.7.7, on the
literal Kₜ = ⟨Lₜ^{C_G(t)}⟩. The local pointwise fixer, scalar centralizer
identity and Frattini factorization remain explicit inputs. The last
conclusion supplies exactly the C_T(L)=1 premise of 12.7.6(2).

The source preliminary geometry and local covering-group calculations must
supply those inputs. This lemma neither assumes nor proves identification
with Held, and it does not supply the missing extraspecial construction. -/
public theorem source_centralizer_consequences [Finite G]
    (L T V Lt Vt X M : Subgroup G) (t : G)
    (ht : t ∈ Lt) (hVL : V ≤ L) (hLtL : Lt ≤ L)
    (hT : T ≤ normalizer (L : Set G))
    (hV : IsPGroup 2 (centralizer (V : Set G)))
    (hfix : ∀ a : MulAut (conjugateSpanBy Lt (centralizer ({t} : Set G))),
      (∀ l : conjugateSpanBy Lt (centralizer ({t} : Set G)),
        (l : G) ∈ Lt → a l = l) → a = 1)
    (hKM : ¬ conjugateSpanBy Lt (centralizer ({t} : Set G)) ≤ M)
    (hunique : ∀ N : Subgroup G, IsMaximalTwoLocal N → L ⊔ T ≤ N → N = M)
    (hscalar : centralizer (Lt ⊔ X : Set G) = centralizer (L : Set G))
    (hfactor : centralizer (Lt : Set G) = Vt ⊔ centralizer (Lt ⊔ X : Set G)) :
    centralizer (L : Set G) = ⊥ ∧
      centralizer (Lt : Set G) = Vt ∧
      centralizer ({t} : Set G) ⊓
        centralizer (conjugateSpanBy Lt (centralizer ({t} : Set G)) : Set G) = Vt ∧
      T ⊓ centralizer (L : Set G) = ⊥ := by
  have he := centralizer_seed_eq Lt
    (conjugateSpanBy Lt (centralizer ({t} : Set G))) t ht
    (le_conjugateSpanBy _ _) (le_normalizer_conjugateSpanBy _ _) hfix
  have hL := centralizer_eq_bot_of_unique_twoLocal L T V Lt
    (conjugateSpanBy Lt (centralizer ({t} : Set G))) M hVL hLtL hT hV
    (le_of_eq he |>.trans inf_le_right) hKM hunique
  have hLt : centralizer (Lt : Set G) = Vt := by
    rw [hfactor, hscalar, hL, sup_bot_eq]
  exact ⟨hL, hLt, he.symm.trans hLt, by rw [hL, inf_bot_eq]⟩

end CFSG.Quasithin.Chapter12.Section07.HeldIdentification
