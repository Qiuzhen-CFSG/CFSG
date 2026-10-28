module
public import CFSG.Quasithin.ChapterC.Section05.ConjugateSource.RankOne.Assembly
public import Theory.GroupAction.SubgroupQuotientFullAction

/-!
# The full block-normalizer action retains the central cover

The characteristic commutator layer and its K-centralizer are preserved by
N_G(K), so literal conjugation descends through U/C_U(K). Three subgroups
then proves that its kernel already centralizes the full U: the K-commutator
of a kernel actor lies in O₂(K), and [U,K]=U. No splitting of the cover and
no vanishing of its central radical is required.

Source: Aschbacher–Smith, C.5.6(7), printed pp.159–160.
-/
@[expose] public section
open Subgroup
open scoped Pointwise commutatorElement
namespace CFSG.Quasithin.ChapterC.Section05.ConjugateSource.RankOne
variable {G W : Type*} [Group G] [Group W] {K : Subgroup G}

/-- Actual conjugation on the original embedded commutator layer. -/
def normalizerConjugate (a : normalizer (K : Set G)) (u : U K) : U K :=
  (U K).normalizerMonoidHom (inclusion
    (normalizer_le_normalizer_characteristic_image K (blockU K)) a) u

/-- Descend the full normalizer action along any literal model of U/C_U(K). -/
theorem exists_normalizer_quotient_action
    (q : U K →* W) (hq : Function.Surjective q)
    (hk : ∀ u : U K, q u = 1 ↔ (u : G) ∈ centralizer (K : Set G)) :
    ∃ ρ : normalizer (K : Set G) →* MulAut W,
      ∀ a u, ρ a (q u) = q (normalizerConjugate a u) := by
  let N := normalizer (K : Set G)
  let Z := centralizer (K : Set G)
  have hNU : N ≤ normalizer (U K : Set G) :=
    normalizer_le_normalizer_characteristic_image K (blockU K)
  have hNZ : N ≤ normalizer (Z : Set G) := (normal_subgroupOf_iff_le_normalizer (Subgroup.centralizer_le_normalizer (K : Set G))).mp inferInstance
  have he : Z.subgroupOf (U K) = q.ker := by ext u; exact (hk u).symm
  have hn : (Z.subgroupOf (U K)).Normal := he ▸ q.normal_ker
  let := hn
  obtain ⟨β,hβ⟩ := exists_quotient_conjugation_action N (U K) Z hNU hNZ hn
  let e : (U K ⧸ Z.subgroupOf (U K)) ≃* W :=
    (QuotientGroup.quotientMulEquivOfEq he).trans
      (QuotientGroup.quotientKerEquivOfSurjective q hq)
  have heq (u : U K) : e (QuotientGroup.mk' _ u) = q u := by
    change (QuotientGroup.quotientKerEquivOfSurjective q hq)
      ((QuotientGroup.quotientMulEquivOfEq he) (QuotientGroup.mk' _ u)) = _
    rfl
  let ρ := (MulAut.congr e).toMonoidHom.comp β
  refine ⟨ρ,?_⟩
  intro a u
  change e (β a (e.symm (q u))) = _
  rw [← heq u,e.symm_apply_apply,hβ,heq]
  rfl

variable [Finite G]

/-- A faithful core-quotient model detects the full-cover centralizer kernel. -/
theorem normalizer_quotient_action_kernel
    (hshort : IsShort K)
    (q : U K →* W) (hq : Function.Surjective q)
    (hk : ∀ u : U K, q u = 1 ↔ (u : G) ∈ centralizer (K : Set G))
    (hcore : ∀ k : K, (∀ u : U K,
      q (normalizerConjugate (inclusion K.le_normalizer k) u) = q u) → k ∈ pCore 2 K)
    (ρ : normalizer (K : Set G) →* MulAut W)
    (hρ : ∀ a u, ρ a (q u) = q (normalizerConjugate a u)) :
    ρ.ker = (centralizer (U K : Set G)).subgroupOf (normalizer (K : Set G)) := by
  let N := normalizer (K : Set G)
  let B := ρ.ker.map N.subtype
  have hBN : B ≤ N := map_subtype_le _
  have hBU : B ≤ normalizer (U K : Set G) :=
    hBN.trans (normalizer_le_normalizer_characteristic_image K (blockU K))
  have hKB : K ≤ normalizer (B : Set G) := by
    have hn := ρ.ker.le_normalizer_map N.subtype
    rw [ρ.ker.normalizer_eq_top,← MonoidHom.range_eq_map,N.range_subtype] at hn
    exact K.le_normalizer.trans hn
  have hKBcore : ⁅K,B⁆ ≤ K.pCoreIn 2 := by
    have hCK : ⁅K,B⁆ ≤ K := le_normalizer_iff_commutator_le_left.mp hBN
    have hCB : ⁅K,B⁆ ≤ B := le_normalizer_iff_commutator_le_right.mp hKB
    intro z hz
    let k : K := ⟨z,hCK hz⟩
    have hzk : k ∈ pCore 2 K := by
      apply hcore k
      intro u
      obtain ⟨b,hb,he⟩ := hCB hz
      have he' : b = inclusion K.le_normalizer k := Subtype.ext he
      have hh := hρ b u
      rw [show ρ b = 1 from hb] at hh
      simpa only [MulAut.one_apply,he'] using hh.symm
    exact mem_map_of_mem K.subtype hzk
  have hUB : ⁅U K,B⁆ ≤ centralizer (K : Set G) := by
    rw [commutator_comm]
    apply commutator_le.mpr
    intro b hb u hu
    obtain ⟨b,hb,rfl⟩ := hb
    let u₀ : U K := ⟨u,hu⟩
    have he : q (normalizerConjugate b u₀ / u₀) = 1 := by
      rw [map_div,← hρ,show ρ b = 1 from hb]
      simp
    have hc := (hk _).mp he
    change (b : G) * u * (b : G)⁻¹ / u ∈ centralizer (K : Set G) at hc
    simpa only [commutatorElement_def,div_eq_mul_inv,subtype_apply] using hc
  have h1 : ⁅⁅U K,B⁆,K⁆ = ⊥ :=
    commutator_eq_bot_iff_le_centralizer.mpr hUB
  have h2 : ⁅⁅B,K⁆,U K⁆ = ⊥ := by
    rw [commutator_comm B K]
    apply commutator_eq_bot_iff_le_centralizer.mpr
    exact hKBcore.trans ((map_mono hshort.core_centralizes_blockU).trans
      (map_centralizer_le_centralizer_image _ K.subtype))
  have h3 := commutator_commutator_eq_bot_of_rotate h1 h2
  have hUK : ⁅U K,K⁆ = U K := by
    have hh := commutator_isPPerfect_idempotent (⊤ : Subgroup K) (pCore 2 K)
      (hshort.twoPerfect.of_surjective (topEquiv (G := K)).symm.toMonoidHom
        (topEquiv (G := K)).symm.surjective) pCore_isPGroup le_normalizer_of_normal
    have hm := congrArg (map K.subtype) hh
    simpa only [U,blockU,map_commutator,← MonoidHom.range_eq_map,range_subtype] using hm
  rw [commutator_comm K (U K),hUK] at h3
  have hBC := le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp h3)
  ext a
  constructor
  · intro ha
    exact hBC (mem_map_of_mem N.subtype ha)
  · intro ha
    apply MulEquiv.ext
    intro w
    obtain ⟨u,rfl⟩ := hq w
    rw [hρ]
    have he : normalizerConjugate a u = u := by
      apply Subtype.ext
      change (a : G) * (u : G) * (a : G)⁻¹ = u
      have hh : (u : G) * (a : G) = (a : G) * (u : G) := ha (u : G) u.property
      rw [← hh,mul_inv_cancel_right]
    rw [he]
    rfl
end CFSG.Quasithin.ChapterC.Section05.ConjugateSource.RankOne
