module

public import CFSG.Quasithin.ChapterI.Section04To05.Extraspecial32.NonnormalRecognition.Geometry.Configuration.Middle.LocalData
public import Theory.GroupTheory.ElementSubgroupIncidence

/-!
# Fusion control and faithful normalizer action for the middle sixteen

An elementary sixteen containing z lies inside H = C_G(z). Sylow conjugacy
in H and uniqueness inside a Sylow subgroup therefore identify all conjugates
of A containing z. Element/subgroup incidence then proves that N_G(A) controls
the fusion of z into A. Orbit–stabilizer gives |N_G(A)| = 64 |z^G ∩ A| and
|N_G(A)/A| = 4 |z^G ∩ A|. The quotient is identified with the literal image
of conjugation on A. The characteristic Sylow center also proves that its
normalizer inside N_G(A) is itself.

These conclusions are conditional on the separately constructed local data.
They use no ambient recognition or D-system.
Source: M. Aschbacher, “A 2-local characterization of M12”, Illinois J. Math.
47 (2003), proof of Lemma 3.1, printed pp.36–37.
-/

public section

open Subgroup
namespace CFSG.Quasithin.Extraspecial32.NonnormalRecognition.Configuration
variable {G : Type*} [Group G] [Finite G] {z : G}

namespace MiddleLocalData
variable (m : MiddleLocalData z)

omit [Finite G] in
theorem A_le_centralizer : m.A ≤ Centralizer z :=
  m.A_le_sylow.trans (map_subtype_le _)

omit [Finite G] in
theorem distinguished_mem : z ∈ m.A := by
  rw [← m.relative_centralizer]
  refine ⟨mem_centralizer_singleton_iff.mpr rfl, ?_⟩
  intro a ha
  exact mem_centralizer_singleton_iff.mp (m.A_le_centralizer ha)

omit [Finite G] in
theorem self_centralizing : centralizer (m.A : Set G) = m.A := by
  have hle : centralizer (m.A : Set G) ≤ Centralizer z := by
    intro a ha
    exact mem_centralizer_singleton_iff.mpr (ha z m.distinguished_mem).symm
  exact (inf_eq_right.mpr hle).symm.trans m.relative_centralizer

omit [Finite G] in
theorem sylow_le_normalizer : middleSylowImage m.S ≤ normalizer (m.A : Set G) := by
  rw [← m.normalizer_intersection]
  exact inf_le_right

theorem normalizer_sylow_intersection (h : Hypotheses z) :
    normalizer (m.A : Set G) ⊓ normalizer (middleSylowImage m.S : Set G) =
      middleSylowImage m.S := by
  apply le_antisymm
  · have hn := normalizer_le_centralizer_of_characteristic_involution
      (middleSylowImage m.S) (center (middleSylowImage m.S)) z h.involution m.sylow_center
    exact (le_inf (inf_le_right.trans hn) inf_le_left).trans_eq m.normalizer_intersection
  · exact le_inf m.sylow_le_normalizer (middleSylowImage m.S).le_normalizer

theorem conjugate_sixteen (B : Subgroup G) (hBH : B ≤ Centralizer z)
    (hBe : IsElementaryAbelian 2 B) (hBc : Nat.card B = 16) :
    ∃ c : Centralizer z, B.conjBy (c : G) = m.A := by
  let : IsElementaryAbelian 2 B := hBe
  let BH := B.subgroupOf (Centralizer z)
  have hp : IsPGroup 2 BH := (IsPGroup.of_card (p := 2) (n := 4) hBc).of_equiv
    (subgroupOfEquivOfLe hBH).symm
  obtain ⟨P, hBP⟩ := hp.exists_le_sylow
  obtain ⟨c, hc⟩ := MulAction.exists_smul_eq (Centralizer z) P m.S
  refine ⟨c, m.unique_sixteen (B.conjBy (c : G)) ?_ (IsElementaryAbelian.map _) ?_⟩
  · rintro x ⟨b, hb, rfl⟩
    have hm : (MulAut.conj c) ⟨b, hBH hb⟩ ∈ (m.S : Subgroup (Centralizer z)) := by
      rw [← hc]
      exact mem_map_of_mem (MulAut.conj c).toMonoidHom (hBP hb)
    exact ⟨(MulAut.conj c) ⟨b, hBH hb⟩, hm, rfl⟩
  · exact (card_map_of_injective (MulAut.conj (c : G)).injective).trans hBc

theorem controls_fusion {x : G} (hx : x ∈ m.A) (hc : IsConj z x) :
    ∃ n ∈ normalizer (m.A : Set G), n * z * n⁻¹ = x := by
  apply ((element_fusion_iff_centralizer_incidence m.A z).mpr ?_) x hx hc
  intro r hr
  let B := m.A.conjBy r
  let : IsElementaryAbelian 2 m.A := m.elementary
  have hBe : IsElementaryAbelian 2 B := IsElementaryAbelian.map _
  let : IsElementaryAbelian 2 B := hBe
  have hBH : B ≤ Centralizer z := by
    intro b hb
    exact mem_centralizer_singleton_iff.mpr
      (congrArg (fun a : B => (a : G)) (mul_comm' (⟨b, hb⟩ : B) ⟨z, hr⟩))
  obtain ⟨c, he⟩ := m.conjugate_sixteen B hBH hBe
    ((card_map_of_injective (MulAut.conj r).injective).trans m.card)
  refine ⟨(c : G)⁻¹, (Centralizer z).inv_mem c.property, ?_⟩
  calc
    m.A.conjBy (c : G)⁻¹ = (B.conjBy (c : G)).conjBy (c : G)⁻¹ :=
      congrArg (fun D : Subgroup G => D.conjBy (c : G)⁻¹) he.symm
    _ = B := conjBy_inv B (c : G)

theorem normalizer_card (h : Hypotheses z) :
    Nat.card (normalizer (m.A : Set G)) = Nat.card (MiddleFusion z m.A) * 64 := by
  let N := normalizer (m.A : Set G)
  let : MulDistribMulAction N G :=
    MulDistribMulAction.compHom G (MulAut.conj.comp N.subtype)
  let : MulAction N G := (inferInstance : MulDistribMulAction N G).toMulAction
  have hstab : MulAction.stabilizer N z = (Centralizer z).subgroupOf N := by
    ext n
    change (n : G) * z * (n : G)⁻¹ = z ↔ (n : G) ∈ Centralizer z
    rw [mem_centralizer_singleton_iff, mul_inv_eq_iff_eq_mul]
  have horbit : MulAction.orbit N z = {x : G | x ∈ m.A ∧ IsConj z x} := by
    ext x
    constructor
    · rintro ⟨n, rfl⟩
      exact ⟨(n.property z).mp m.distinguished_mem, isConj_iff.mpr ⟨n, rfl⟩⟩
    · rintro ⟨hx, hzx⟩
      obtain ⟨n, hn, he⟩ := m.controls_fusion hx hzx
      exact ⟨⟨n, hn⟩, he⟩
  have hsub : (Centralizer z).subgroupOf N = (middleSylowImage m.S).subgroupOf N := by
    rw [← m.normalizer_intersection]
    ext n
    exact ⟨fun hn => ⟨hn, n.property⟩, And.left⟩
  have hcard : Nat.card ((Centralizer z).subgroupOf N) = 64 := by
    rw [hsub, Nat.card_congr (subgroupOfEquivOfLe m.sylow_le_normalizer).toEquiv,
      card_map_of_injective (Centralizer z).subtype_injective,
      h.centralizer_sylow_two_card]
  have he := Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup N z)
  rw [Nat.card_prod, hstab, hcard, Nat.card_congr (Equiv.setCongr horbit)] at he
  exact he.symm

theorem normalizer_quotient_card (h : Hypotheses z) :
    Nat.card (normalizer (m.A : Set G) ⧸
      m.A.subgroupOf (normalizer (m.A : Set G))) = Nat.card (MiddleFusion z m.A) * 4 := by
  have hc := card_eq_card_quotient_mul_card_subgroup
    (m.A.subgroupOf (normalizer (m.A : Set G)))
  rw [Nat.card_congr (subgroupOfEquivOfLe m.A.le_normalizer).toEquiv, m.card,
    m.normalizer_card h] at hc
  omega

noncomputable def normalizerActionQuotient :
    (normalizer (m.A : Set G) ⧸ m.A.subgroupOf (normalizer (m.A : Set G))) ≃*
      m.A.normalizerMonoidHom.range := by
  have hk : m.A.normalizerMonoidHom.ker = m.A.subgroupOf (normalizer (m.A : Set G)) := by
    rw [normalizerMonoidHom_ker, m.self_centralizing]
  exact (QuotientGroup.quotientMulEquivOfEq hk.symm).trans
    (QuotientGroup.quotientKerEquivRange m.A.normalizerMonoidHom)

/-- Full fusion of A# would make the faithful normalizer quotient have order sixty. -/
theorem missing_of_quotient_card_ne_sixty (h : Hypotheses z)
    (hsixty : Nat.card (normalizer (m.A : Set G) ⧸
      m.A.subgroupOf (normalizer (m.A : Set G))) ≠ 60) :
    ∃ a ∈ m.A, a ≠ 1 ∧ ¬ IsConj z a := by
  classical
  by_contra! hf
  have he : {x : G | x ∈ m.A ∧ IsConj z x} = (m.A : Set G) \ {1} := by
    ext x
    constructor
    · rintro ⟨hx, hc⟩
      refine ⟨hx, ?_⟩
      intro hx1
      obtain ⟨r, hr⟩ := isConj_iff.mp hc
      have hz : z = 1 := (MulAut.conj r).injective
        ((hr.trans hx1).trans (map_one _).symm)
      have ho := h.involution
      simp [hz] at ho
    · rintro ⟨hx, hx1⟩
      exact ⟨hx, hf x hx hx1⟩
  have hc : Nat.card (MiddleFusion z m.A) = 15 := by
    have hec : Nat.card (MiddleFusion z m.A) = ((m.A : Set G) \ {1}).ncard :=
      Nat.card_congr (Equiv.setCongr he)
    rw [hec]
    rw [Set.ncard_sdiff_singleton_of_mem m.A.one_mem]
    change Nat.card m.A - 1 = 15
    rw [m.card]
  apply hsixty
  rw [m.normalizer_quotient_card h, hc]

end MiddleLocalData
end CFSG.Quasithin.Extraspecial32.NonnormalRecognition.Configuration

end
