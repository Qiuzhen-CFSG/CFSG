module

public import CFSG.Quasithin.ChapterG.Section02.AlternatingFive.Block.CoreCollapse.CubicImage
public import Theory.GroupAction.SubgroupQuotientFullAction
public import Theory.GroupAction.CoprimeHall

/-!
# No further central local sections in G.2.4(8)

For any L₁-invariant A between V₁ and U, the literal quotient U/A is
abelian. Its full L₁ commutator action factors through L₁/O₂(L₁), since
G.2.2 and O₂(L₁)≤Q_H put [U,O₂(L₁)] in V₁. The actor therefore has
three-power order. Coprime decomposition makes its fixed subgroup trivial.
Consequently every central L₁-section above V₁ vanishes; in particular
there are no further central chief factors above V₁.

Apply this to A=V and B=U∩Uᵍ. Clause (5) puts [B,L₁] in V_L,
and normalization of U puts it in U, hence in V_L∩U=V.
Thus B≤V and the original second layer V_L(U∩Uᵍ) equals V_L.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
G.2.4(8), printed pp.334–335.
-/

@[expose] public section
open Subgroup
open scoped commutatorElement IsMulCommutative
namespace CFSG.Quasithin.ChapterG.Section02.AlternatingFive
open Setup Block
namespace Hypothesis
variable {G : Type*} [Group G] [Finite G] {D : Setup G} {g : G}

/-- Every L₁-central section of U above its original point V₁ is trivial.
This excludes all additional central chief factors, without choosing a series. -/
theorem terminal_no_central_section (d : Hypothesis D g)
    (c : EarlierStructure D g)
    (hfull : ⁅D.tilde D.U, D.tilde D.L₁⁆ = D.tilde D.U)
    (hcore : D.L₁.pCoreIn 2 ≤ D.QH)
    (A B : Subgroup G) (hpoint : D.V₁ ≤ A) (hAU : A ≤ D.U)
    (hnA : D.L₁ ≤ normalizer (A : Set G)) (hBU : B ≤ D.U)
    (hBA : ⁅B, D.L₁⁆ ≤ A) : B ≤ A := by
  have hcubic := d.terminal_local_core_quotient_card c
  have hLU : D.L₁ ≤ normalizer (D.U : Set G) :=
    (le_sup_left.trans d.setup.local_le).trans (le_normalizer_conjugateSpanBy D.V D.H)
  have hUU : ⁅D.U, D.U⁆ ≤ A :=
    (derived_le_of_frattini_image_le d.setup.U_isPGroup d.setup.frattini_U_le_point).trans hpoint
  have hUA : D.U ≤ normalizer (A : Set G) :=
    le_normalizer_iff_commutator_le_left.mpr ((commutator_mono hAU le_rfl).trans hUU)
  let hN : (A.subgroupOf D.U).Normal :=
    (normal_subgroupOf_iff_le_normalizer hAU).mpr hUA
  let := hN
  have hUC : ⁅D.U, D.L₁.pCoreIn 2⁆ ≤ A := by
    rw [commutator_comm]
    exact ((commutator_mono hcore le_rfl).trans d.local_core_commutator_closure).trans hpoint
  obtain ⟨ρ, hρ, hk, hf⟩ := exists_quotient_conjugation_full_action
    D.L₁ D.U A D.L₁ (D.L₁.pCoreIn 2) hLU hnA hN le_rfl
    (d.terminal_reduction hfull).1.symm hUC
  let W := D.U ⧸ A.subgroupOf D.U
  let q := QuotientGroup.mk' (A.subgroupOf D.U)
  have hker : pCore 2 D.L₁ ≤ ρ.ker := by
    intro x hx
    exact hk (mem_map_of_mem D.L₁.subtype hx)
  let σ : (D.L₁ ⧸ pCore 2 D.L₁) →* MulAut W :=
    QuotientGroup.lift (pCore 2 D.L₁) ρ hker
  have hrange : σ.range = ρ.range := by
    ext a
    constructor
    · rintro ⟨x, rfl⟩
      obtain ⟨l, rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 D.L₁) x
      exact ⟨l, rfl⟩
    · rintro ⟨l, rfl⟩
      exact ⟨QuotientGroup.mk' (pCore 2 D.L₁) l, rfl⟩
  have hthree : IsPGroup 3 ρ.range := by
    rw [← hrange]
    exact (IsPGroup.of_card (n := 1) hcubic).of_surjective σ.rangeRestrict σ.rangeRestrict_surjective
  have htwo : IsPGroup 2 W := d.setup.U_isPGroup.to_quotient (A.subgroupOf D.U)
  have habelian : IsMulCommutative W := by
    apply (_root_.commutator_eq_bot_iff W).mp
    apply bot_unique
    have hm : ⁅(⊤ : Subgroup D.U), ⊤⁆ ≤ A.subgroupOf D.U := by
      intro x hx
      have hh := mem_map_of_mem D.U.subtype hx
      rw [map_commutator, ← MonoidHom.range_eq_map, range_subtype] at hh
      exact hUU hh
    have hh := map_mono (f := q) hm
    rw [map_commutator, map_top_of_surjective q (QuotientGroup.mk'_surjective _),
      QuotientGroup.map_mk'_self] at hh
    exact hh
  let := habelian
  have hcop : Nat.Coprime (Nat.card ρ.range) (Nat.card W) := by
    have hh := IsPGroup.coprime_card_of_ne 3 2 (by decide)
      ρ.range (⊤ : Subgroup W) hthree (htwo.to_subgroup ⊤)
    simpa only [card_top] using hh
  have hcompl := isCompl_fixedPointSubgroup_commutatorAction_of_solvable_coprime_of_isMulCommutative
    (G := W) (A := ρ.range) (Group.isSolvable_of_comm fun a b => mul_comm a b) hcop habelian
  have hfull' : commutatorAction ρ.range W = ⊤ := by
    have he : (D.L₁.subgroupOf D.L₁).map ρ = ρ.range := by
      ext a
      exact ⟨fun ⟨x, _, he⟩ => ⟨x, he⟩, fun ⟨x, he⟩ => ⟨x, x.property, he⟩⟩
    rwa [he] at hf
  have hfixed : FixedPoints.subgroup ρ.range W = ⊥ := by
    have hd := hcompl.disjoint
    rw [hfull'] at hd
    exact disjoint_top.mp hd
  intro b hb
  let bU : D.U := ⟨b, hBU hb⟩
  have hbfix : q bU ∈ FixedPoints.subgroup ρ.range W := by
    rintro ⟨a, l, rfl⟩
    change ρ l (q bU) = q bU
    rw [hρ]
    apply QuotientGroup.eq_iff_div_mem.mpr
    change (l : G) * b * (l : G)⁻¹ / b ∈ A
    have hh : ⁅(l : G), b⁆ ∈ A := by
      rw [commutator_comm] at hBA
      exact hBA (commutator_mem_commutator l.property hb)
    simpa only [commutatorElement_def, div_eq_mul_inv] using hh
  have hbq : q bU = 1 := by simpa only [hfixed, mem_bot] using hbfix
  exact (QuotientGroup.eq_one_iff bU).mp hbq

/-- The chief-factor step gives the exact second layer S₂=V_L. -/
theorem terminal_second_eq_first (d : Hypothesis D g) (c : EarlierStructure D g)
    (hfull : ⁅D.tilde D.U, D.tilde D.L₁⁆ = D.tilde D.U)
    (hcore : D.L₁.pCoreIn 2 ≤ D.QH) : S₂ D g = D.VL := by
  have hloc : D.L₁ ≤ D.L := (map_subtype_le _).trans inf_le_left
  have hLU : D.L₁ ≤ normalizer (D.U : Set G) :=
    (le_sup_left.trans d.setup.local_le).trans (le_normalizer_conjugateSpanBy D.V D.H)
  have hBV : ⁅D.U ⊓ conjugate D.U g, D.L₁⁆ ≤ D.V := by
    rw [← c.orthogonal_intersection]
    exact le_inf
      ((commutator_mono le_sup_right (hloc.trans c.L_le_I)).trans
        (d.second_commutator c.L_le_I))
      ((commutator_mono inf_le_left le_rfl).trans
        (le_normalizer_iff_commutator_le_left.mp hLU))
  have hB := d.terminal_no_central_section c hfull hcore
    D.V (D.U ⊓ conjugate D.U g) d.setup.point_le (le_conjugateSpanBy _ _)
    (le_sup_left.trans d.setup.local_normalizes_V) inf_le_left hBV
  exact sup_eq_left.mpr (hB.trans (c.orthogonal_intersection.ge.trans inf_le_left))

end Hypothesis
end CFSG.Quasithin.ChapterG.Section02.AlternatingFive
