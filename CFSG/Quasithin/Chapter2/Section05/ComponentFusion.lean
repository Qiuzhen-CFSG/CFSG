module

public import CFSG.Quasithin.Chapter2.Section05.ComponentSetup
public import Theory.GroupTheory.IndexTwoConjugatePair

/-!
# Normalizer and disjointness geometry for Section 2.5

Source: Aschbacher–Smith, combined manuscript (1 March 2004), Lemmas 2.5.5–2.5.6,
printed pp.553–554. The module retains the original H = K₀ S geometry and proves
that a nontrivial S-normal subgroup of S ∩ C(K₀) would force its normalizer into
Γ₀, contradicting the empty Γe₀ hypothesis. It also packages the source
conjugate-disjointness argument with the exact Sylow and normalizer maps.

The model alternatives and later recognition steps remain explicit inputs to the
source assembly; no component classification is encoded here.
-/

@[expose] public section

open Subgroup
namespace CFSG.Quasithin.Chapter2.Section05
variable {G : Type*} [Group G] [Finite G] {M H S T E : Subgroup G} {z : G}

omit [Finite G] in
private theorem pGroup_eq_sylow_image {N Q : Subgroup G}
    (P : Sylow 2 N) (hQ : IsPGroup 2 Q) (hQN : Q ≤ N)
    (hPQ : (P : Subgroup N).map N.subtype ≤ Q) :
    Q = (P : Subgroup N).map N.subtype := by
  have hp : IsPGroup 2 (Q.subgroupOf N) :=
    hQ.comap_of_injective N.subtype N.subtype_injective
  have hle : (P : Subgroup N) ≤ Q.subgroupOf N := by
    intro x hx
    exact hPQ (mem_map_of_mem N.subtype hx)
  rw [← P.is_maximal' hp hle, map_subgroupOf_eq_of_le hQN]

/-- Source 2.3.7 applied to a nontrivial normal two-subgroup of the original H.
Both starred conditions and the literal Sylow image are retained. -/
theorem normalizer_of_normal_subgroup (d : SourceTuple M H S T z)
    (hE : E ≠ ⊥) (hES : E ≤ S) (hHE : H ≤ normalizer (E : Set G)) :
    normalizer (E : Set G) ∈ gammaZero (Chapter1.He G) M ∧
    (∃ P : Sylow 2 (normalizer (E : Set G)),
      (P : Subgroup (normalizer (E : Set G))).map
        (normalizer (E : Set G)).subtype = S) ∧
    (H ∈ gammaStar (Chapter1.He G) M →
      normalizer (E : Set G) ∈ gammaStar (Chapter1.He G) M) ∧
    (H ∈ gammaMax (Chapter1.He G) M →
      normalizer (E : Set G) ∈ gammaMax (Chapter1.He G) M) := by
  obtain ⟨P, hP⟩ := d.sylow_intersection
  have hgam : H ∈ gamma (Chapter1.He G) M :=
    d.gamma_zero.elim (fun h => h.1.1) (fun h => h.1)
  obtain ⟨R, hR⟩ := (intersection_sylow hgam P).2
  have hR' : (R : Subgroup H).map H.subtype = S := hR.trans hP
  have hSp : IsPGroup 2 S := hR' ▸ R.isPGroup'.map H.subtype
  have hEp := hSp.of_injective (inclusion hES) (inclusion_injective hES)
  have hcore : twoCore (normalizer (E : Set G)) ≠ ⊥ := by
    intro he
    have hle := le_pCoreIn_of_normalizes hEp E.le_normalizer le_rfl
    exact hE (bot_unique (he ▸ hle))
  have hn := gammaZero_overgroup d.gamma_zero hHE hcore
  refine ⟨hn.1, ?_, hn.2.2.1, hn.2.2.2⟩
  apply exists_sylow_of_card
  · rw [← hR']
    exact (map_subtype_le _).trans hHE
  · rw [← hR', sylow_image_card, hn.2.1]

/-- The overgroup in the original two-Sylow cannot normalize a nontrivial
normal two-subgroup of H. This is the contradiction used in 2.5.5. -/
theorem normalizer_intersection_eq (d : SourceTuple M H S T z)
    (hE : E ≠ ⊥) (hES : E ≤ S) (hHE : H ≤ normalizer (E : Set G)) :
    T ⊓ normalizer (E : Set G) = S := by
  obtain ⟨P, hP⟩ := (normalizer_of_normal_subgroup d hE hES hHE).2.1
  obtain ⟨R, hR⟩ := d.sylow_maximal
  let _ := ‹Finite G›
  have hTp : IsPGroup 2 T := hR ▸ R.isPGroup'.map M.subtype
  have hp : IsPGroup 2 ↥(T ⊓ normalizer (E : Set G)) :=
    hTp.of_injective (inclusion (show T ⊓ normalizer (E : Set G) ≤ T from inf_le_left))
      (inclusion_injective (show T ⊓ normalizer (E : Set G) ≤ T from inf_le_left))
  have hSH : S ≤ H := by
    obtain ⟨Q, hQ⟩ := d.sylow_intersection
    rw [← hQ]
    exact (map_subtype_le _).trans inf_le_left
  have he := pGroup_eq_sylow_image P hp inf_le_right
    (hP ▸ le_inf d.lt.le (hSH.trans hHE))
  exact he.trans hP

/-- Subgroups of the centralizer factor that are normal in S are normal in
H = K0 S. This constructs the placement input of the normalizer argument. -/
theorem normalizes_centralizer_subgroup {K₀ : Subgroup G}
    (hH : H = K₀ ⊔ S) (hEC : E ≤ S ⊓ centralizer (K₀ : Set G))
    (hSE : S ≤ normalizer (E : Set G)) : H ≤ normalizer (E : Set G) := by
  let _ := ‹Finite G›
  rw [hH]
  exact sup_le ((le_centralizer_iff.mp (hEC.trans inf_le_right)).trans
    (centralizer_le_normalizer _)) hSE

/-- The non-classification part of 2.5.6, for the actual factor C_S(K0). -/
theorem centralizer_subgroup_normalizer {K₀ : Subgroup G}
    (d : SourceTuple M H S T z) (hH : H = K₀ ⊔ S)
    (hE : E ≠ ⊥) (hEC : E ≤ S ⊓ centralizer (K₀ : Set G))
    (hSE : S ≤ normalizer (E : Set G)) :
    normalizer (E : Set G) ∈ gammaZero (Chapter1.He G) M ∧
    (∃ P : Sylow 2 (normalizer (E : Set G)),
      (P : Subgroup (normalizer (E : Set G))).map
        (normalizer (E : Set G)).subtype = S) ∧
    (H ∈ gammaStar (Chapter1.He G) M →
      normalizer (E : Set G) ∈ gammaStar (Chapter1.He G) M) ∧
    (H ∈ gammaMax (Chapter1.He G) M →
      normalizer (E : Set G) ∈ gammaMax (Chapter1.He G) M) :=
  normalizer_of_normal_subgroup d hE (hEC.trans inf_le_left)
    (normalizes_centralizer_subgroup hH hEC hSE)

/-- The disjointness argument of 2.5.5. Conjugation here is explicitly x Q x^-1;
the source's right-conjugation convention is supplied in lemma_2_5_5. -/
theorem centralizer_factor_disjoint {K₀ : Subgroup G} {x : G}
    (d : SourceTuple M H S T z) (hH : H = K₀ ⊔ S)
    (hSK : S ≤ normalizer (K₀ : Set G))
    (hxT : x ∈ T) (hxS : x ∉ S) (hxN : x ∈ normalizer (S : Set G))
    (hx2 : x ^ 2 ∈ S) :
    Disjoint (S ⊓ centralizer (K₀ : Set G))
      ((S ⊓ centralizer (K₀ : Set G)).conjBy x) := by
  let Q := S ⊓ centralizer (K₀ : Set G)
  have hSQ : S ≤ normalizer (Q : Set G) := by
    intro s hs a
    constructor
    · intro ha
      refine ⟨(mem_normalizer_iff.mp (S.le_normalizer hs) a).mp ha.1, ?_⟩
      intro k hk
      have hk' := (mem_normalizer_iff.mp (hSK (S.inv_mem hs)) k).mp hk
      have hc := ha.2 (s⁻¹ * k * s) (by simpa using hk')
      calc
        k * (s * a * s⁻¹) = s * ((s⁻¹ * k * s) * a) * s⁻¹ := by group
        _ = s * (a * (s⁻¹ * k * s)) * s⁻¹ := by rw [hc]
        _ = (s * a * s⁻¹) * k := by group
    · intro ha
      refine ⟨(mem_normalizer_iff.mp (S.le_normalizer hs) a).mpr ha.1, ?_⟩
      intro k hk
      have hk' := (mem_normalizer_iff.mp (hSK hs) k).mp hk
      have hc := ha.2 (s * k * s⁻¹) hk'
      have hh := congrArg (fun b : G => s⁻¹ * b * s) hc
      simpa [mul_assoc] using hh
  have hSQx := normalizes_conjugate_of_normalizes hxN hSQ
  let D := Q ⊓ Q.conjBy x
  have hSD : S ≤ normalizer (D : Set G) := by
    intro s hs a
    exact and_congr (hSQ hs a) (hSQx hs a)
  have hHD : H ≤ normalizer (D : Set G) :=
    normalizes_centralizer_subgroup hH inf_le_left hSD
  have hxx : (Q.conjBy x).conjBy x = Q := by
    rw [conjBy_conjBy, ← pow_two]
    exact mem_normalizer_iff_map_conj_eq.mp (hSQ hx2)
  have hxD : x ∈ normalizer (D : Set G) := by
    apply mem_normalizer_iff_map_conj_eq.mpr
    rw [map_inf _ _ _ (MulAut.conj x).injective]
    change Q.conjBy x ⊓ (Q.conjBy x).conjBy x = Q ⊓ Q.conjBy x
    rw [hxx, inf_comm]
  apply disjoint_iff.mpr
  by_contra hD
  have hn := normalizer_intersection_eq d hD
    (show D ≤ S from inf_le_left.trans inf_le_left) hHD
  exact hxS (hn ▸ (show x ∈ T ⊓ normalizer (D : Set G) from ⟨hxT, hxD⟩))

end CFSG.Quasithin.Chapter2.Section05
