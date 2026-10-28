module
public import CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.BlockCrossing
public import CFSG.Quasithin.ChapterC.Section06.AlternatingCentralVector.Definitions

/-!
# The centralizer endgame for the ordinary A₇ block

Suppose the marked geometry supplies a nonidentity involution z centralizing
L, a conjugate zᵏ in the full module W = [Ω₁Z(O₂(LT)),L], and
K = ⟨L,Lᵏ⟩. Once C.6.4 makes z central in T, uniqueness over LT puts
C_G(z) in N_G(L). Conjugating this inclusion makes O₂(LT) normalize Lᵏ,
because O₂(LT) centralizes W. It already normalizes L. The factorization
T = S O₂(LT) therefore forces T ≤ N_G(K) = H, a contradiction.

The marking and the C.6.4 centrality assertion remain explicit independent
inputs here. This module proves their actual 4.3.7 consumer, not the missing
source constructions. In particular W is not identified with the initially
chosen Chapter 12 module.

Source: Aschbacher--Smith, original 4.3.7, printed p.616.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness
open Chapter12.Section02
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

/-- Geometry to be constructed on the actual seven-letter block. The centrality
of the marked vector in SΛ is deliberately not included. -/
structure BlockAlternatingMarking (c : SourceConfiguration T L) where
  pushingUp : ChapterC.Section06.AlternatingCentralVector.Input
    (c.K.map c.H.subtype) (c.I.pCoreIn 2) ((T : Subgroup G) ⊓ c.H)
    ((L ⊔ (T : Subgroup G)).pCoreIn 2)
  factorization : (T : Subgroup G) =
    ((T : Subgroup G) ⊓ c.H) ⊔ (L ⊔ (T : Subgroup G)).pCoreIn 2
  z : G
  k : G
  z_ne : z ≠ 1
  z_two : z ^ 2 = 1
  z_commutator : z ∈
    ⁅(ChapterC.blockU (c.K.map c.H.subtype)).map (c.K.map c.H.subtype).subtype,
      c.I.pCoreIn 2⁆
  z_centralizes : z ∈ centralizer (L : Set G)
  k_mem : k ∈ c.K.map c.H.subtype
  conjugate_mem : MulAut.conj k⁻¹ z ∈
    Section02.Unitary.fullModule L ((L ⊔ (T : Subgroup G)).pCoreIn 2)
  generation : c.K.map c.H.subtype = L ⊔ L.map (MulAut.conj k⁻¹).toMonoidHom

omit [Finite G] in
private theorem centralizer_conjugate_le_normalizer {z : G}
    (hc : centralizer ({z} : Set G) ≤ normalizer (L : Set G)) (e : G ≃* G) :
    centralizer ({e z} : Set G) ≤ normalizer (L.map e.toMonoidHom : Set G) := by
  intro x hx
  have he : e.symm x ∈ centralizer ({z} : Set G) := by
    apply mem_centralizer_singleton_iff.mpr
    apply e.injective
    simpa only [map_mul, e.apply_symm_apply] using mem_centralizer_singleton_iff.mp hx
  have hm := (L.le_normalizer_map e.toMonoidHom)
    (mem_map_of_mem e.toMonoidHom (hc he))
  simpa only [MulEquiv.coe_toMonoidHom, e.apply_symm_apply] using hm

/-- A central involution of LT has centralizer in the unique maximal two-local
overgroup. This is the actual centralizer assertion used before conjugating. -/
theorem centralizer_le_component_normalizer (D : ChosenModule T L V)
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L) {z : G}
    (hne : z ≠ 1) (hpow : z ^ 2 = 1)
    (hL : z ∈ centralizer (L : Set G))
    (hT : z ∈ centralizer (T : Set G)) :
    centralizer ({z} : Set G) ≤ normalizer (L : Set G) := by
  let Z := zpowers z
  have hp : IsPGroup 2 Z :=
    (IsElementaryAbelian.zpowers_of_pow_eq_one (p := 2) hpow).isPGroup 2 _
  have hZ : Z ≠ ⊥ := fun he => hne (by
    have hz : z ∈ Z := mem_zpowers z
    rw [he] at hz
    exact hz)
  have hcz : centralizer ({z} : Set G) ≤ normalizer (Z : Set G) := by
    intro g hg
    apply mem_normalizer_iff_map_conj_eq.mpr
    rw [MonoidHom.map_zpowers]
    congr 1
    exact mul_inv_eq_iff_eq_mul.mpr (mem_centralizer_singleton_iff.mp hg)
  have hn : L ⊔ (T : Subgroup G) ≤ normalizer (Z : Set G) := by
    apply le_trans _ hcz
    apply sup_le
    · intro l hl
      exact mem_centralizer_singleton_iff.mpr (mem_centralizer_iff.mp hL l hl)
    · intro t ht
      exact mem_centralizer_singleton_iff.mpr (mem_centralizer_iff.mp hT t ht)
  have hNC := normalizer_le_of_unique_maximalTwoLocal
    (unique_sylow_join D h).2.2 hp hZ hn
  exact hcz.trans hNC

/-- The final source contradiction from the two independent marked inputs. -/
theorem SourceConfiguration.false_of_alternating_marking
    (c : SourceConfiguration T L) (D : ChosenModule T L V)
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (d : BlockAlternatingMarking c)
    (hcentral : ∀ {K R S Λ : Subgroup G},
      ChapterC.Section06.AlternatingCentralVector.Input K R S Λ →
        ⁅(ChapterC.blockU K).map K.subtype,R⁆ ≤ centralizer ((S ⊔ Λ : Subgroup G) : Set G)) :
    False := by
  have hzT : d.z ∈ centralizer (T : Set G) := by
    change d.z ∈ centralizer ((T : Subgroup G) : Set G)
    rw [d.factorization]
    exact hcentral d.pushingUp d.z_commutator
  have hc := centralizer_le_component_normalizer D h d.z_ne d.z_two d.z_centralizes hzT
  have hconj := centralizer_conjugate_le_normalizer hc (MulAut.conj d.k⁻¹)
  let Λ := (L ⊔ (T : Subgroup G)).pCoreIn 2
  have hnΛ : L ⊔ (T : Subgroup G) ≤ normalizer (Λ : Set G) :=
    (L ⊔ (T : Subgroup G)).le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image (L ⊔ (T : Subgroup G))
        (pCore 2 (L ⊔ (T : Subgroup G) : Subgroup G)))
  have hnω : L ≤ normalizer (Stellmacher.omegaOneCenterAmbient Λ : Set G) := by
    intro l hl
    apply mem_normalizer_iff_map_conj_eq.mpr
    rw [← Stellmacher.omegaOneCenterAmbient_map_injective _ (MulAut.conj l).injective,
      mem_normalizer_iff_map_conj_eq.mp (hnΛ (mem_sup_left hl))]
  have hv := (le_normalizer_iff_commutator_le_left.mp hnω) d.conjugate_mem
  have hΛconj : Λ ≤ normalizer (L.map (MulAut.conj d.k⁻¹).toMonoidHom : Set G) := by
    apply le_trans _ hconj
    intro q hq
    exact mem_centralizer_singleton_iff.mpr
      (((Stellmacher.mem_omegaOneCenterAmbient_iff _ _).mp hv).2.2 q hq)
  have hΛT : Λ ≤ (T : Subgroup G) := by
    simpa only [Sylow.coe_subtype, map_subgroupOf_eq_of_le le_sup_right] using
      pCoreIn_le_sylow (L ⊔ (T : Subgroup G)) (T.subtype le_sup_right)
  have hΛK : Λ ≤ normalizer (c.K.map c.H.subtype : Set G) := by
    rw [d.generation]
    exact (le_inf (hΛT.trans D.sylow_normalizes_component) hΛconj).trans
      (normalizer_inf_normalizer_le_normalizer_sup _ _)
  have hTH : (T : Subgroup G) ≤ c.H := by
    rw [d.factorization]
    exact sup_le inf_le_right (hΛK.trans c.normalizer_component.ge)
  exact c.sylow_strict.ne (inf_eq_left.mpr hTH)

end CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness
