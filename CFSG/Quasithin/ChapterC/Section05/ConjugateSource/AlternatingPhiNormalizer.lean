module
public import CFSG.Quasithin.ChapterC.Section05.ConjugateSource.AlternatingPhiNormalizer.Witness
public import CFSG.Quasithin.ChapterC.Section05.ConjugateSource.AlternatingOrbit

/-!
# The original Frattini stabilizer in the two A₅-block case

The block Sylow Frattini witness prevents an element of R preserving
Φ(C_S(K)) from interchanging K and L. Indeed Φ(S∩L) lies in Φ(C_S(K)),
whereas U_L is disjoint from C_S(L). Characteristic transport gives the
reverse inclusion. The same disjointness identifies the block stabilizer
with the module stabilizer. Their common subgroup is normal in the
actual M₁=N_M(Φ(C_S(K))), as required by the four-family argument.

Source: Aschbacher–Smith C.5.6(5)–(6), printed p.158.
-/

public section
open Subgroup
namespace CFSG.Quasithin.ChapterC.Section05.ConjugateSource
variable {G : Type*} [Group G]

private theorem phi_normalizer_of_block (R K : Subgroup G) :
    let D := ChapterB.baumann R ⊓ centralizer (K : Set G)
    normalizer (R : Set G) ⊓ normalizer (K : Set G) ≤
      normalizer ((frattini D).map D.subtype : Set G) := by
  let D := ChapterB.baumann R ⊓ centralizer (K : Set G)
  have hC : normalizer (K : Set G) ≤ normalizer (centralizer (K : Set G) : Set G) :=
    (normal_subgroupOf_iff_le_normalizer (Subgroup.centralizer_le_normalizer (K : Set G))).mp inferInstance
  have hD : normalizer (R : Set G) ⊓ normalizer (K : Set G) ≤ normalizer (D : Set G) :=
    (le_inf (inf_le_left.trans (Stellmacher.normalizer_le_normalizer_baumann R))
      (inf_le_right.trans hC)).trans inf_normalizer_le_normalizer_inf
  exact hD.trans (normalizer_le_normalizer_characteristic_image D (frattini D))

private theorem centralizer_equiv (K : Subgroup G) (e : G ≃* G) :
    (centralizer (K : Set G)).map e.toMonoidHom = centralizer (K.map e.toMonoidHom : Set G) := by
  apply le_antisymm (map_centralizer_le_centralizer_image _ _)
  intro a ha
  refine ⟨e.symm a, ?_, e.apply_symm_apply a⟩
  intro k hk
  apply e.injective
  simpa only [map_mul, e.apply_symm_apply] using ha (e k) (mem_map_of_mem _ hk)

variable [Finite G] {R K L : Subgroup G}

/-- The literal Φ(C_S(K)) stabilizer in R is exactly the first-block stabilizer. -/
theorem AlternatingPairSetup.phi_normalizer_eq_block_normalizer
    (h₁ : AlternatingPairSetup R K L) (h₂ : AlternatingPairSetup R L K) :
    let D := ChapterB.baumann R ⊓ centralizer (K : Set G)
    R ⊓ normalizer ((frattini D).map D.subtype : Set G) = R ⊓ normalizer (K : Set G) := by
  let S := ChapterB.baumann R
  let D₁ := S ⊓ centralizer (K : Set G)
  let D₂ := S ⊓ centralizer (L : Set G)
  apply le_antisymm
  · intro r hr
    refine ⟨hr.1, ?_⟩
    rcases h₁.permutes r hr.1 with hfix | hswap
    · exact mem_normalizer_iff_map_conj_eq.mpr hfix
    · have hS : S.map (MulAut.conj r).toMonoidHom = S :=
        mem_normalizer_iff_map_conj_eq.mp
          (Stellmacher.normalizer_le_normalizer_baumann R (R.le_normalizer hr.1))
      have hD : D₁.map (MulAut.conj r).toMonoidHom = D₂ := by
        rw [map_inf _ _ _ (MulAut.conj r).injective, hS, centralizer_equiv, hswap]
      have hPhi : (frattini D₂).map D₂.subtype = (frattini D₁).map D₁.subtype := by
        rw [← hD, frattini_image_map _ _ (MulAut.conj r).injective]
        exact mem_normalizer_iff_map_conj_eq.mp hr.2
      have hS₂D₁ : S ⊓ L ≤ D₁ := le_inf inf_le_left (inf_le_right.trans h₁.commute)
      have hp : (frattini (S ⊓ L : Subgroup G)).map (S ⊓ L).subtype ≤ D₂ := by
        have hp' := frattini_image_le_of_le hS₂D₁
          (h₁.twoGroup.to_le (show D₁ ≤ R from inf_le_left.trans inf_le_left))
        rw [← hPhi] at hp'
        exact hp'.trans (map_subtype_le _)
      have hd : Disjoint (sourceModule L) D₂ :=
        alternatingModule_disjoint_of_commuting L D₂ h₂.block inf_le_right
      have hb : sourceModule L ⊓ (frattini (S ⊓ L : Subgroup G)).map (S ⊓ L).subtype ≤ ⊥ :=
        (inf_le_inf_left _ hp).trans hd.le_bot
      exact (h₂.module_inf_block_frattini_ne_bot (le_bot_iff.mp hb)).elim
  · intro r hr
    exact ⟨hr.1, phi_normalizer_of_block R K ⟨R.le_normalizer hr.1, hr.2⟩⟩

omit [Finite G] in
/-- Stabilizing the nontrivial original module is equivalent to stabilizing
its block; the alternative block has disjoint support. -/
theorem AlternatingPairSetup.block_normalizer_eq_module_normalizer
    (h : AlternatingPairSetup R K L) :
    R ⊓ normalizer (K : Set G) = R ⊓ normalizer (sourceModule K : Set G) := by
  apply le_antisymm
  · exact inf_le_inf_left R (normalizer_le_normalizer_characteristic_image K (blockU K))
  · intro r hr
    refine ⟨hr.1, ?_⟩
    rcases h.permutes r hr.1 with hfix | hswap
    · exact mem_normalizer_iff_map_conj_eq.mpr hfix
    · have hU : sourceModule K = sourceModule L := by
        have hm := sourceModule_map_equiv K (MulAut.conj r)
        rw [hswap] at hm
        have hf : (sourceModule K).map (MulAut.conj r).toMonoidHom = sourceModule K :=
          mem_normalizer_iff_map_conj_eq.mp hr.2
        exact hf.symm.trans hm
      have hUL : sourceModule K ≤ L := hU.le.trans (map_subtype_le _)
      have hd := alternatingModule_disjoint_of_commuting K L h.block h.commute
      have hb : sourceModule K = ⊥ :=
        le_bot_iff.mp (fun u hu => hd.le_bot ⟨hu, hUL hu⟩)
      have hc := h.module_card
      rw [hb, card_bot] at hc
      omega

/-- The exact stabilizer identity used in the original S/Φ(D) four-family action. -/
theorem AlternatingPairSetup.source_phi_stabilizers
    (h₁ : AlternatingPairSetup R K L) (h₂ : AlternatingPairSetup R L K) :
    let D := ChapterB.baumann R ⊓ centralizer (K : Set G)
    R ⊓ normalizer ((frattini D).map D.subtype : Set G) = R ⊓ normalizer (K : Set G) ∧
      R ⊓ normalizer (K : Set G) = R ⊓ normalizer (sourceModule K : Set G) :=
  ⟨h₁.phi_normalizer_eq_block_normalizer h₂, h₁.block_normalizer_eq_module_normalizer⟩

/-- Actual source application: N_R(U) is normal in M₁=N_M(Φ(D)),
so M₁ preserves the R-module-stabilizer invariant part of the four-family. -/
theorem AlternatingPairSetup.module_stabilizer_normalized
    (h₁ : AlternatingPairSetup R K L) (h₂ : AlternatingPairSetup R L K)
    (M : Subgroup G) (hMR : M ≤ normalizer (R : Set G)) :
    let D := ChapterB.baumann R ⊓ centralizer (K : Set G)
    M ⊓ normalizer ((frattini D).map D.subtype : Set G) ≤
      normalizer (R ⊓ normalizer (sourceModule K : Set G) : Set G) := by
  let D := ChapterB.baumann R ⊓ centralizer (K : Set G)
  let P := (frattini D).map D.subtype
  have he : R ⊓ normalizer (P : Set G) = R ⊓ normalizer (sourceModule K : Set G) :=
    (h₁.phi_normalizer_eq_block_normalizer h₂).trans h₁.block_normalizer_eq_module_normalizer
  change M ⊓ normalizer (P : Set G) ≤
    normalizer ((R ⊓ normalizer (sourceModule K : Set G) : Subgroup G) : Set G)
  rw [← he]
  exact (le_inf (inf_le_left.trans hMR)
    (inf_le_right.trans (normalizer (P : Set G)).le_normalizer)).trans
      inf_normalizer_le_normalizer_inf

/-- The literal normal subgroup used in C.5.6: if R≤M, then N_R(U) is
normal in N_M(Φ(D)), with containment also supplied by the stabilizer identity. -/
theorem AlternatingPairSetup.module_stabilizer_normal
    (h₁ : AlternatingPairSetup R K L) (h₂ : AlternatingPairSetup R L K)
    (M : Subgroup G) (hRM : R ≤ M) (hMR : M ≤ normalizer (R : Set G)) :
    let D := ChapterB.baumann R ⊓ centralizer (K : Set G)
    ((R ⊓ normalizer (sourceModule K : Set G)).subgroupOf
      (M ⊓ normalizer ((frattini D).map D.subtype : Set G))).Normal := by
  let D := ChapterB.baumann R ⊓ centralizer (K : Set G)
  let P := (frattini D).map D.subtype
  have he : R ⊓ normalizer (P : Set G) = R ⊓ normalizer (sourceModule K : Set G) :=
    (h₁.phi_normalizer_eq_block_normalizer h₂).trans h₁.block_normalizer_eq_module_normalizer
  have hle : R ⊓ normalizer (sourceModule K : Set G) ≤ M ⊓ normalizer (P : Set G) := by
    rw [← he]
    exact inf_le_inf_right _ hRM
  exact (normal_subgroupOf_iff_le_normalizer hle).mpr (h₁.module_stabilizer_normalized h₂ M hMR)
end CFSG.Quasithin.ChapterC.Section05.ConjugateSource
end
