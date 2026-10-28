module

public import CFSG.Quasithin.Chapter13.Section09.CentralizerStructure.Pair
public import CFSG.Quasithin.ChapterG.Section02.CentralClosure
public import Theory.GroupTheory.CharacteristicCentralizerFusion
public import Theory.GroupTheory.ReducedNormal.Equiv

/-!
# The actual G.2.2 application in 13.9.8

Take V₁ = ⟨z⟩, V = ⟨t,z⟩, L = 1, H = C_G(z), and the original T.
The marked four-group V is normal in T. Its quotient by the involution
line has no proper nonzero subgroup, which supplies the irreducibility
required by G.2.1. Characteristic two is proved from condition (E).

The normalizer of the involution line equals its centralizer. We exhibit
the resulting equivalence to the literal quotient C_G(z)/⟨z⟩ and retain
the image of every ambient subgroup under that equivalence.

Source: Aschbacher–Smith, proof of Lemma 13.9.8, first paragraph,
printed p.972 (PDF p.989). The later normality and recognition of Q
are separate assertions, not assumptions of this construction.
-/

@[expose] public section
namespace CFSG.Quasithin.Chapter13.Section09.CentralizerStructure
open Subgroup Theory.GroupTheory

variable {G : Type*} [Group G] [Finite G] {d : Configuration G}

namespace PairData
variable (m : PairData d)

/-- The marked four-group facts from the wreath geometry preceding 13.9.2. -/
structure ClosureData : Prop where
  elementary : IsElementaryAbelian 2 m.V
  card_four : Nat.card m.V = 4
  normalized : (d.T : Subgroup G) ≤ normalizer (m.V : Set G)

/-- The literal substitution used in the source's invocation of G.2.2. -/
def closureSetup : ChapterG.Section02.Setup G where
  V := m.V
  V₁ := m.Z
  L := ⊥
  T := d.T
  H := m.C

theorem point_normalizer_eq : m.closureSetup.G₁ = m.C :=
  normalizer_zpowers_eq_centralizer_of_order_two m.z m.z_order

omit [Finite G] in
theorem closureSetup_L₁ : m.closureSetup.L₁ = ⊥ := by
  apply le_bot_iff.mp
  exact (map_subtype_le _).trans inf_le_left

/-- Construction of every G.2.1 premise; irreducibility uses the actual
orders two and four, and the two-residual is that of the trivial L. -/
theorem closure_hypothesis (h : m.ClosureData) (hE : IsEvenCharacteristicAt d.T) :
    m.closureSetup.Hypothesis := by
  have hlocal : m.closureSetup.L₁ ⊔ m.closureSetup.T = (d.T : Subgroup G) := by
    rw [m.closureSetup_L₁, bot_sup_eq]; rfl
  have hVle : m.V ≤ (d.T : Subgroup G) :=
    sup_le (zpowers_le.mpr m.t_mem) (zpowers_le.mpr m.z_mem)
  have hZcard : Nat.card m.Z = 2 := by rw [Nat.card_zpowers, m.z_order]
  have hZne : m.Z ≠ ⊥ := by
    intro he
    rw [he, Nat.card_unique] at hZcard
    omega
  have hZV : m.Z ≠ m.V := by
    intro he
    have hc := h.card_four
    rw [← he, hZcard] at hc
    omega
  have hST : ∃ S : Sylow 2 ((d.T : Subgroup G)),
      (S : Subgroup (d.T : Subgroup G)).map (d.T : Subgroup G).subtype = d.T := by
    refine ⟨d.T.subtype le_rfl, ?_⟩
    exact map_subgroupOf_eq_of_le le_rfl
  refine {
    elementary := h.elementary
    point_ne_bot := hZne
    point_le := le_sup_right
    residual := by
      change pResidual 2 (⊥ : Subgroup G) = ⊤
      apply top_unique
      intro x _
      have hx : x = 1 := Subsingleton.elim _ _
      rw [hx]
      exact one_mem _
    V_le_T := hVle
    T_normalizes_point := by rw [m.point_normalizer_eq]; exact m.z_central
    T_normalizes_V := h.normalized
    T_normalizes_L := by simp only [closureSetup, normalizer_eq_top]; exact le_top
    sylow_LT := by
      have he : m.closureSetup.LT = (d.T : Subgroup G) := bot_sup_eq _
      rw [he]
      exact hST
    H_le := by rw [m.point_normalizer_eq]; exact le_rfl
    local_le := by rw [hlocal]; exact m.z_central
    sylow_H := ⟨d.T.subtype m.z_central, map_subgroupOf_eq_of_le m.z_central⟩
    characteristic_two := (ChapterA.generalizedFitting_eq_pCore_iff 2).mpr
      (m.centralizer_characteristic_two hE)
    local_normalizes_V := by rw [hlocal]; exact h.normalized
    quotient_nonzero := hZV
    irreducible := ?_
  }
  intro A hZA hAV _
  change m.Z ≤ A at hZA
  change A ≤ m.V at hAV
  change A = m.Z ∨ A = m.V
  have hdiv : Nat.card A ∣ 4 := h.card_four ▸ card_dvd_of_le hAV
  have hsmall : 2 ≤ Nat.card A := hZcard ▸ card_le_of_le hZA
  have hcases : Nat.card A = 2 ∨ Nat.card A = 4 := by
    obtain ⟨k, hk, hkcard⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp
      (show Nat.card A ∣ 2 ^ 2 from hdiv)
    interval_cases k
    · have hc : Nat.card A = 1 := hkcard
      omega
    · exact Or.inl hkcard
    · exact Or.inr hkcard
  rcases hcases with hc | hc
  · exact Or.inl (eq_of_le_of_card_ge hZA (by rw [hc, hZcard])).symm
  · exact Or.inr (eq_of_le_of_card_ge hAV (by rw [hc, h.card_four]))

instance line_normal : (m.Z.subgroupOf m.C).Normal := by
  apply (normal_subgroupOf_iff_le_normalizer
    (zpowers_le.mpr (mem_centralizer_singleton_iff.mpr rfl))).mpr
  exact m.point_normalizer_eq.ge

/-- The literal centralizer quotient used throughout 13.9.6–8. -/
abbrev Tilde := m.C ⧸ m.Z.subgroupOf m.C

def tilde (A : Subgroup G) : Subgroup m.Tilde :=
  (A.subgroupOf m.C).map (QuotientGroup.mk' (m.Z.subgroupOf m.C))

instance setupLine_normal : (m.Z.subgroupOf m.closureSetup.G₁).Normal := by
  change (m.Z.subgroupOf (normalizer (m.Z : Set G))).Normal
  infer_instance

/-- This is induced by the identity on the original ambient elements. -/
def tildeEquiv : m.closureSetup.Tilde ≃* m.Tilde :=
  QuotientGroup.equivQuotientSubgroupOfOfEq rfl m.point_normalizer_eq

theorem tildeEquiv_mk (x : m.closureSetup.G₁) :
    m.tildeEquiv (QuotientGroup.mk' (m.Z.subgroupOf m.closureSetup.G₁) x) =
      QuotientGroup.mk' (m.Z.subgroupOf m.C) ⟨x, m.point_normalizer_eq.le x.property⟩ := rfl

/-- The equivalence preserves the literal image of every original subgroup. -/
theorem tilde_map (A : Subgroup G) :
    (m.closureSetup.tilde A).map m.tildeEquiv.toMonoidHom = m.tilde A := by
  ext y
  constructor
  · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    exact ⟨⟨x, m.point_normalizer_eq.le x.property⟩, hx, rfl⟩
  · rintro ⟨x, hx, rfl⟩
    let x' : m.closureSetup.G₁ := ⟨x, m.point_normalizer_eq.ge x.property⟩
    exact ⟨QuotientGroup.mk' (m.Z.subgroupOf m.closureSetup.G₁) x',
      ⟨x', hx, rfl⟩, rfl⟩

theorem tilde_H_top : m.closureSetup.tilde m.closureSetup.H = ⊤ := by
  apply top_unique
  intro y _
  obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective
    (m.Z.subgroupOf m.closureSetup.G₁) y
  exact ⟨x, m.point_normalizer_eq.le x.property, rfl⟩

private def tildeCarrierEquiv : m.closureSetup.tilde m.closureSetup.H ≃* m.Tilde :=
  ((MulEquiv.subgroupCongr m.tilde_H_top).trans Subgroup.topEquiv).trans m.tildeEquiv

/-- The source closure, still a subgroup of the original G. -/
abbrev U : Subgroup G := m.closureSetup.U

private theorem tilde_U_le_H (h : m.ClosureData) (hE : IsEvenCharacteristicAt d.T) :
    m.closureSetup.tilde m.U ≤ m.closureSetup.tilde m.closureSetup.H :=
  map_mono (comap_mono (m.closure_hypothesis h hE).U_le_H)

/-- G.2.2(4) on the literal quotient C_G(z)/⟨z⟩. -/
theorem closure_reduced (h : m.ClosureData) (hE : IsEvenCharacteristicAt d.T) :
    IsPReduced 2 (m.tilde m.U) := by
  have hr := ((m.closure_hypothesis h hE).tilde_U_reduced).map_equiv m.tildeCarrierEquiv
  have hf : m.tildeCarrierEquiv.toMonoidHom = m.tildeEquiv.toMonoidHom.comp
      (m.closureSetup.tilde m.closureSetup.H).subtype := rfl
  rw [hf, ← map_map, map_subgroupOf_eq_of_le (m.tilde_U_le_H h hE), m.tilde_map] at hr
  exact hr

/-- G.2.2(1) on the literal quotient, with the quotient's own two-core. -/
theorem closure_central (h : m.ClosureData) (hE : IsEvenCharacteristicAt d.T) :
    m.tilde m.U ≤ omegaOneAmbient
      ((center (pCore 2 m.Tilde)).map (pCore 2 m.Tilde).subtype) := by
  have hr := m.closure_reduced h hE
  have hc : m.tilde m.U ≤ (center (pCore 2 m.Tilde)).map (pCore 2 m.Tilde).subtype := by
    intro u hu
    refine ⟨⟨u, hr.le_pCore hu⟩, mem_center_iff.mpr ?_, rfl⟩
    intro q
    exact Subtype.ext (hr.le_centralizer_pCore hu q q.property)
  let := hr.elementary
  rw [← omegaOneAmbient_eq_self (m.tilde m.U)]
  exact omegaOneAmbient_mono hc

/-- G.2.2(3): the original closure is a normal two-subgroup of the original T. -/
theorem closure_normal_in_T (h : m.ClosureData) (hE : IsEvenCharacteristicAt d.T) :
    m.U ≤ (d.T : Subgroup G) ∧ (m.U.subgroupOf (d.T : Subgroup G)).Normal ∧
      IsPGroup 2 m.U := by
  have hG := m.closure_hypothesis h hE
  exact ⟨hG.U_normal_in_T.1, hG.U_normal_in_T.2, hG.U_isPGroup⟩

end PairData
end CFSG.Quasithin.Chapter13.Section09.CentralizerStructure
