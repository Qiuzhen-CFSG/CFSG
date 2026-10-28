module
public import CFSG.Quasithin.Chapter2.Section04.LinearShadows.Double.SetupSource
public import Theory.GroupTheory.PCoreImage
public import CFSG.Quasithin.ChapterC.Section01.BlockTypes.OddFixedCentralCore
/-!
# Fixed points of the original paired torus

The source identity O₂(L₀)=U₁U₂ puts each factor core inside its natural
module times its center. Thus a nontrivial odd torus fixes only central
elements in the corresponding Sylow group. Applying this to the paired
Thompson decomposition shows that the full torus fixed subgroup centralizes
both blocks, without assuming directness or discarding the central layer.

Source: Aschbacher--Smith, Section 2.4, printed p.540.
-/
public section
open Subgroup Theory.GroupTheory
open scoped Pointwise
namespace CFSG.Quasithin.Chapter2.LinearDouble
open ChapterC.Section05.ConjugateSource
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
private theorem core_le_module_sup_center
    (L J C : Subgroup G) (hLJ : L ≤ J) (hJL : J ≤ normalizer (L : Set G))
    (hcore : J.pCoreIn 2 ≤ sourceModule L ⊔ C)
    (hCL : C ≤ centralizer (L : Set G)) :
    pCore 2 L ≤ ChapterC.blockU L ⊔ center L := by
  have hLN : L.pCoreIn 2 ≤ J.pCoreIn 2 := pCoreIn_mono_of_normalizes hLJ hJL
  have hCU : C ≤ normalizer (sourceModule L : Set G) :=
    (hCL.trans (centralizer_le (map_subtype_le _))).trans (Subgroup.centralizer_le_normalizer _)
  intro x hx
  have hxJ := hcore (hLN (mem_map_of_mem L.subtype hx))
  have hxprod : (x : G) ∈ (sourceModule L : Set G) * (C : Set G) :=
    (coe_mul_of_right_le_normalizer_left _ _ hCU) ▸ hxJ
  obtain ⟨u,⟨u,hu,rfl⟩,c,hc,he⟩ := hxprod
  have hcL : c ∈ L := by
    have hh := L.mul_mem (L.inv_mem u.property) x.property
    rw [←he] at hh
    simpa only [Subtype.coe_eta,subtype_apply,inv_mul_cancel_left] using hh
  have hcz : (⟨c,hcL⟩ : L) ∈ center L := by
    apply mem_center_iff.mpr
    intro y
    apply Subtype.ext
    exact (mem_centralizer_iff.mp (hCL hc)) y y.property
  have hh := mul_mem_sup hu hcz
  exact (show u * (⟨c,hcL⟩ : L) = x from Subtype.ext he) ▸ hh

variable {M : Subgroup G}
/-- The source core identity leaves only a central extra layer in each factor. -/
theorem factor_core_central_bounds
    (d : MinimalBlockSetup M) (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G)
    (hST : (d.S : Subgroup d.H).map d.H.subtype < (T : Subgroup G))
    {M₀ : Subgroup G} {n : ℕ} (c : DoubleLinearSourceSetup d M₀ n) :
    pCore 2 (d.block.map d.H.subtype) ≤
        ChapterC.blockU (d.block.map d.H.subtype) ⊔ center (d.block.map d.H.subtype) ∧
      pCore 2 c.second ≤ ChapterC.blockU c.second ⊔ center c.second := by
  let L := d.block.map d.H.subtype
  let J := d.L0.map d.H.subtype
  have hcore : J.pCoreIn 2 = sourceModule L ⊔ sourceModule c.second := by
    rw [show J = d.L0.map d.H.subtype from rfl,
      ←map_pCoreIn_of_injective 2 d.L0 d.H.subtype d.H.subtype_injective,
      ←(d.core_source hG T hST).1]
    exact (d.two_block_closures c.second c.permutes c.exchange).2
  have hJL : J ≤ normalizer (L : Set G) := by
    rw [show J = d.L0.map d.H.subtype from rfl,←c.join]
    exact sup_le L.le_normalizer (c.commutes.trans (Subgroup.centralizer_le_normalizer _))
  have hJL₂ : J ≤ normalizer (c.second : Set G) := by
    rw [show J = d.L0.map d.H.subtype from rfl,←c.join]
    exact sup_le ((le_centralizer_iff.mp c.commutes).trans (Subgroup.centralizer_le_normalizer _))
      c.second.le_normalizer
  refine ⟨core_le_module_sup_center L J (sourceModule c.second)
    (le_sup_left.trans_eq c.join) hJL hcore.le ((map_subtype_le _).trans c.commutes),?_⟩
  apply core_le_module_sup_center c.second J (sourceModule L)
    (le_sup_right.trans_eq c.join) hJL₂
  · rw [hcore,sup_comm]
  · exact (map_subtype_le _).trans (le_centralizer_iff.mp c.commutes)

omit [Finite G] in
private theorem fixed_centralizes_of_supplement
    (R P C L D : Subgroup G) (hR : R = P ⊔ C) (hPL : P ≤ L)
    (hCL : C ≤ centralizer (L : Set G)) (hDL : D ≤ L)
    (hfix : P ⊓ centralizer (D : Set G) ≤ centralizer (L : Set G)) :
    R ⊓ centralizer (D : Set G) ≤ centralizer (L : Set G) := by
  have hCP : C ≤ normalizer (P : Set G) :=
    (hCL.trans (centralizer_le hPL)).trans (Subgroup.centralizer_le_normalizer _)
  have hCD : C ≤ centralizer (D : Set G) := hCL.trans (centralizer_le hDL)
  rintro r ⟨hr,hDr⟩
  have hp : r ∈ (P : Set G) * (C : Set G) := by
    rw [←coe_mul_of_right_le_normalizer_left _ _ hCP,←hR]
    exact hr
  obtain ⟨p,hp,c,hc,rfl⟩ := hp
  have hpD : p ∈ centralizer (D : Set G) := by
    have hh := (centralizer (D : Set G)).mul_mem hDr
      ((centralizer (D : Set G)).inv_mem (hCD hc))
    simpa only [mul_inv_cancel_right] using hh
  exact (centralizer (L : Set G)).mul_mem (hfix ⟨hp,hpD⟩) (hCL hc)

/-- The paired torus fixes only elements centralizing both original blocks;
the central overlap is retained at this stage. -/
theorem paired_fixed_centralizes
    (R L₁ L₂ C D₁ D₂ : Subgroup G) {n : ℕ}
    (hL₁ : ChapterC.IsL2EvenBlock L₁ n) (hL₂ : ChapterC.IsL2EvenBlock L₂ n)
    (hcore₁ : pCore 2 L₁ ≤ ChapterC.blockU L₁ ⊔ center L₁)
    (hcore₂ : pCore 2 L₂ ≤ ChapterC.blockU L₂ ⊔ center L₂)
    (P₁ : Sylow 2 L₁) (P₂ : Sylow 2 L₂)
    (hP₁ : (P₁ : Subgroup L₁).map L₁.subtype = R ⊓ L₁)
    (hP₂ : (P₂ : Subgroup L₂).map L₂.subtype = R ⊓ L₂)
    (hcomm : L₂ ≤ centralizer (L₁ : Set G))
    (hC : C ≤ centralizer ((L₁ ⊔ L₂ : Subgroup G) : Set G))
    (hR : R = ((R ⊓ L₁) ⊔ (R ⊓ L₂)) ⊔ C)
    (hD₁ : D₁ ≤ L₁) (hD₂ : D₂ ≤ L₂)
    (hodd₁ : Odd (Nat.card D₁)) (hodd₂ : Odd (Nat.card D₂))
    (hne₁ : D₁ ≠ ⊥) (hne₂ : D₂ ≠ ⊥) :
    R ⊓ centralizer ((D₁ ⊔ D₂ : Subgroup G) : Set G) ≤
      centralizer ((L₁ ⊔ L₂ : Subgroup G) : Set G) := by
  have fix₁ : (R ⊓ L₁) ⊓ centralizer (D₁ : Set G) ≤ centralizer (L₁ : Set G) := by
    rw [←hP₁]
    exact (ChapterC.IsL2EvenBlock.ambient_sylow_odd_fixed_le_center_of_core_le L₁ D₁
      hL₁ hcore₁ P₁ hD₁ hodd₁ hne₁).trans (by
        rintro _ ⟨z,hz,rfl⟩ y hy
        exact congrArg Subtype.val (mem_center_iff.mp hz (⟨y,hy⟩ : L₁)))
  have fix₂ : (R ⊓ L₂) ⊓ centralizer (D₂ : Set G) ≤ centralizer (L₂ : Set G) := by
    rw [←hP₂]
    exact (ChapterC.IsL2EvenBlock.ambient_sylow_odd_fixed_le_center_of_core_le L₂ D₂
      hL₂ hcore₂ P₂ hD₂ hodd₂ hne₂).trans (by
        rintro _ ⟨z,hz,rfl⟩ y hy
        exact congrArg Subtype.val (mem_center_iff.mp hz (⟨y,hy⟩ : L₂)))
  have hfix₁ := fixed_centralizes_of_supplement R (R ⊓ L₁) ((R ⊓ L₂) ⊔ C) L₁ D₁
    (hR.trans (sup_assoc _ _ _)) inf_le_right
    (sup_le (inf_le_right.trans hcomm) (hC.trans (centralizer_le (show L₁ ≤ L₁ ⊔ L₂ from le_sup_left)))) hD₁ fix₁
  have hfix₂ := fixed_centralizes_of_supplement R (R ⊓ L₂) ((R ⊓ L₁) ⊔ C) L₂ D₂
    (hR.trans (by rw [sup_comm (R ⊓ L₁) (R ⊓ L₂),sup_assoc])) inf_le_right
    (sup_le (inf_le_right.trans (le_centralizer_iff.mp hcomm))
      (hC.trans (centralizer_le (show L₂ ≤ L₁ ⊔ L₂ from le_sup_right)))) hD₂ fix₂
  apply le_centralizer_iff.mpr
  exact sup_le
    (le_centralizer_iff.mp ((inf_le_inf_left R (centralizer_le (show D₁ ≤ D₁ ⊔ D₂ from le_sup_left))).trans hfix₁))
    (le_centralizer_iff.mp ((inf_le_inf_left R (centralizer_le (show D₂ ≤ D₁ ⊔ D₂ from le_sup_right))).trans hfix₂))
end CFSG.Quasithin.Chapter2.LinearDouble
