module
public import Theory.GroupTheory.PPrimeCoreNormalComplement
public import Theory.GroupTheory.NormalizedSupConsequences
public import Theory.GroupTheory.SylowNormalSupplementProduct
public import Theory.GroupTheory.SylowNormalIntersection
public import Theory.GroupTheory.SylowNormalizerFrattini

/-!
# Sylow factorization after a normal complement

A normal p-complement and Frattini's argument show that a prescribed
Sylow q-normalizer has index prime to p, for distinct primes p and q.
Thus it contains a Sylow p-subgroup. If G = K C M with K and C normal,
and M contains a Sylow p-subgroup of C, extend that subgroup through M
to a Sylow B of G. Sylow indices in the two normal products give
B = (B ∩ K)(B ∩ M) and B ∩ C ≤ B ∩ M.

Source application: Aschbacher–Smith 14.7.21(1), printed pp.1049–1050.
The complement is used in C R₁; the final normal factors are K and C
in N_G(K). The proof does not require C R₁ to be normal in N_G(K).
-/

public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Subgroup
namespace Sylow
variable {G : Type*} [Group G] [Finite G] {p q : ℕ} [Fact p.Prime] [Fact q.Prime]

/-- In a group with a normal p-complement, the normalizer of a Sylow q-subgroup
has index prime to p whenever p and q are distinct. -/
theorem not_dvd_normalizer_index_of_normal_complement
    (R : Sylow q G) (hpq : p ≠ q) (hc : HasNormalPComplement p G) :
    ¬ p ∣ (normalizer (R : Set G)).index := by
  obtain ⟨N,hn,hcop,hQ⟩ := hc
  let := hn
  have hRN : (R : Subgroup G) ≤ N := by
    rw [←relIndex_eq_one]
    obtain ⟨a,ha⟩ := hQ.exists_card_eq
    obtain ⟨b,hb⟩ := R.isPGroup'.exists_card_eq
    have hh : Nat.Coprime N.index (Nat.card R) := by
      change Nat.Coprime (Nat.card (G ⧸ N)) (Nat.card R)
      rw [ha,hb]
      exact ((Nat.coprime_primes (Fact.out : p.Prime) (Fact.out : q.Prime)).mpr hpq).pow a b
    exact Nat.eq_one_of_dvd_coprimes hh (N.relIndex_dvd_index_of_normal _)
      (relIndex_dvd_card _ _)
  have hf := (R.subtype hRN).normalizer_sup_eq_top
  rw [Sylow.coe_subtype,map_subgroupOf_eq_of_le hRN] at hf
  change normalizer (R : Set G) ⊔ N = ⊤ at hf
  have hd : (normalizer (R : Set G)).index ∣ Nat.card N := by
    rw [←relIndex_top_right (H := normalizer (R : Set G)),←hf,sup_comm,
      relIndex_sup_of_normalizes N (normalizer (R : Set G)) le_normalizer_of_normal]
    exact relIndex_dvd_card _ _
  exact fun hh => (Fact.out : p.Prime).coprime_iff_not_dvd.mp hcop (hh.trans hd)

/-- A Sylow for the complemented prime can be chosen inside the prescribed
other-prime Sylow normalizer. -/
theorem exists_le_normalizer_of_normal_complement
    (R : Sylow q G) (hpq : p ≠ q) (hc : HasNormalPComplement p G) :
    ∃ S : Sylow p G, (S : Subgroup G) ≤ normalizer (R : Set G) := by
  let M := normalizer (R : Set G)
  obtain ⟨P⟩ := Sylow.nonempty (p := p) (G := M)
  let X := (P : Subgroup M).map M.subtype
  have hi : ¬ p ∣ X.index := by
    rw [index_map_subtype]
    exact (Fact.out : p.Prime).not_dvd_mul P.not_dvd_index
      (R.not_dvd_normalizer_index_of_normal_complement hpq hc)
  exact ⟨(P.isPGroup'.map M.subtype).toSylow hi,map_subtype_le _⟩

/-- Two normal factors and a supplement admit an exact Sylow factorization
when the supplement already contains a Sylow of the second normal factor. -/
theorem exists_factor_of_normal_sylow_containment
    (K C M : Subgroup G) [K.Normal] [C.Normal]
    (hgen : K ⊔ C ⊔ M = ⊤) (S : Sylow p C)
    (hSM : (S : Subgroup C).map C.subtype ≤ M) :
    ∃ B : Sylow p G,
      (B : Subgroup G) = ((B : Subgroup G) ⊓ K) ⊔ ((B : Subgroup G) ⊓ M) ∧
      (B : Subgroup G) ⊓ C ≤ (B : Subgroup G) ⊓ M := by
  let X := (S : Subgroup C).map C.subtype
  have hXp : IsPGroup p (X.subgroupOf M) := (S.isPGroup'.map C.subtype).comap_subtype
  obtain ⟨P,hP⟩ := hXp.exists_le_sylow
  let Y := (P : Subgroup M).map M.subtype
  have hXY : X ≤ Y := by
    exact (map_subgroupOf_eq_of_le (show X ≤ M from hSM)).symm.le.trans (map_mono hP)
  obtain ⟨B,hB⟩ := P.exists_comap_subtype_eq
  have hYB : Y ≤ (B : Subgroup G) := by
    rintro x ⟨y,hy,rfl⟩
    change y ∈ (B : Subgroup G).comap M.subtype
    rwa [hB]
  have hBM : (B : Subgroup G) ⊓ M = Y := by
    rw [←subgroupOf_map_subtype]
    exact congrArg (Subgroup.map M.subtype) hB
  have hBC : (B : Subgroup G) ⊓ C = X := by
    have hs : (B : Subgroup G).subgroupOf C = (S : Subgroup C) :=
      S.is_maximal' B.isPGroup'.comap_subtype (by
        intro x hx
        exact hYB (hXY (mem_map_of_mem C.subtype hx)))
    rw [←subgroupOf_map_subtype,hs]
  obtain ⟨P₀,hP₀⟩ := IsPGroup.exists_sylow_sup_of_normal_sylow_images C M Y
    (P.isPGroup'.map M.subtype) ((map_subtype_le _).trans le_sup_right)
    S P hXY le_rfl
  obtain ⟨Q,hQ⟩ := B.exists_subgroupOf_eq_of_normal K
  let J := ((B : Subgroup G) ⊓ K) ⊔ Y
  have hJB : J ≤ (B : Subgroup G) := sup_le inf_le_left hYB
  have hJp : IsPGroup p J := B.isPGroup'.to_le hJB
  have hJle : J ≤ K ⊔ (C ⊔ M) := sup_le
    (inf_le_right.trans le_sup_left) ((map_subtype_le _).trans (le_sup_right.trans le_sup_right))
  obtain ⟨U,hU⟩ := IsPGroup.exists_sylow_sup_of_normal_sylow_images K (C ⊔ M) J
    hJp hJle Q P₀ (by rw [hQ,subgroupOf_map_subtype]; exact le_sup_left)
    (hP₀.le.trans le_sup_right)
  have hji : ¬ p ∣ J.index := by
    rw [←hU,index_map_subtype]
    have htop : K ⊔ (C ⊔ M) = ⊤ := by rwa [←sup_assoc]
    rw [show (K ⊔ (C ⊔ M)).index = 1 by rw [htop,index_top],mul_one]
    exact U.not_dvd_index
  have heq : (B : Subgroup G) = J := (hJp.toSylow hji).is_maximal' B.isPGroup' hJB
  refine ⟨B,?_,?_⟩
  · rwa [hBM]
  · rw [hBC,hBM]
    exact hXY
end Sylow
