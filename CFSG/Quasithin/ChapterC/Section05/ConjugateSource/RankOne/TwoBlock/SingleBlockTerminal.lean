module
public import CFSG.Quasithin.ChapterC.Section05.ConjugateSource.RankOne.TwoBlock.SourceAveraging
public import CFSG.Quasithin.ChapterC.Section05.ConjugateSource.RankOne.TwoBlock.SourceCentralizer
public import CFSG.Quasithin.ChapterC.Section05.ConjugateSource.RankOne.TwoBlock.CentralKernelElimination

/-!
# The single-block full centralizer products

In the genuine single-block case R normalizes K. The original square x²
preserves U, so conjugation gives both full centralizer supplements. Actual
Sylow averaging and central-cover fixed lifting then identify the same
K-centralizer factor in C_R(U) and C_R(Uˣ).

Source: Aschbacher–Smith, C.5.6(7)(i) and C.5.7, printed pp.159–160.
-/
public section
open Subgroup
open scoped Pointwise IsMulCommutative
namespace CFSG.Quasithin.ChapterC.Section05.ConjugateSource.RankOne
variable {G : Type*} [Group G]

private theorem map_centralizer (B : Subgroup G) (e : G ≃* G) :
    (centralizer (B : Set G)).map e.toMonoidHom = centralizer (B.map e.toMonoidHom : Set G) := by
  apply le_antisymm
  · exact map_centralizer_le_centralizer_image _ _
  · intro g hg
    refine ⟨e.symm g,?_,e.apply_symm_apply g⟩
    intro b hb
    apply e.injective
    simpa only [map_mul,e.apply_symm_apply] using hg (e b) (mem_map_of_mem _ hb)

variable [Finite G] {R K : Subgroup G} {F : Type*} [Field F]

theorem Setup.single_block_mutual_centralizers
    (h : Setup R K F) (hR : IsPGroup 2 R)
    (hSylow : (∃ n, IsL2EvenBlock K n) →
      ∃ T : Sylow 2 K, (T : Subgroup K).map K.subtype = S R ⊓ K)
    (hRK : R ≤ normalizer (K : Set G))
    {x : G} (hx : x ∈ normalizer (R : Set G))
    (hnc : ¬ (U K).map (MulAut.conj x⁻¹).toMonoidHom ≤ centralizer (U K : Set G))
    (hsquare : (U K).conjBy (x^2) = U K) :
    let V := (U K).map (MulAut.conj x⁻¹).toMonoidHom
    R ⊓ centralizer (V : Set G) ≤ V ⊔ (R ⊓ centralizer (U K : Set G)) ∧
      R ⊓ centralizer (U K : Set G) ≤ U K ⊔ (R ⊓ centralizer (V : Set G)) := by
  let V := (U K).map (MulAut.conj x⁻¹).toMonoidHom
  have hf := h.source_full_centralizer_le hR hSylow hx hnc (inf_le_left.trans hRK)
  have hUx : (U K).conjBy x = V := by
    change (U K).conjBy x = (U K).conjBy x⁻¹
    calc
      (U K).conjBy x = ((U K).conjBy (x^2)).conjBy x⁻¹ := by
        rw [← Subgroup.conjBy_mul]
        congr 1
        group
      _ = _ := congrArg (fun W : Subgroup G => W.conjBy x⁻¹) hsquare
  have hVx : V.conjBy x = U K := Subgroup.conjBy_inv' _ _
  have hRx : R.map (MulAut.conj x).toMonoidHom = R := mem_normalizer_iff_map_conj_eq.mp hx
  have hC (W : Subgroup G) : (R ⊓ centralizer (W : Set G)).map (MulAut.conj x).toMonoidHom =
      R ⊓ centralizer (W.conjBy x : Set G) := by
    rw [map_inf _ _ _ (MulAut.conj x).injective,map_centralizer,hRx]
    rfl
  have hb := map_mono (f := (MulAut.conj x).toMonoidHom) hf
  rw [Subgroup.map_sup V (R ⊓ centralizer (U K : Set G)),hC,hC] at hb
  change R ⊓ centralizer (V.conjBy x : Set G) ≤ V.conjBy x ⊔
    (R ⊓ centralizer ((U K).conjBy x : Set G)) at hb
  rw [hVx,hUx] at hb
  exact ⟨hf,hb⟩

theorem Setup.single_block_full_centralizer_products
    (h : Setup R K F) (hR : IsPGroup 2 R)
    (hSylow : (∃ n, IsL2EvenBlock K n) →
      ∃ T : Sylow 2 K, (T : Subgroup K).map K.subtype = S R ⊓ K)
    (hRK : R ≤ normalizer (K : Set G))
    {x : G} (hx : x ∈ normalizer (R : Set G))
    (hnc : ¬ (U K).map (MulAut.conj x⁻¹).toMonoidHom ≤ centralizer (U K : Set G))
    (hsquare : (U K).conjBy (x^2) = U K) :
    let V := (U K).map (MulAut.conj x⁻¹).toMonoidHom
    let C := R ⊓ centralizer (K : Set G)
    R ⊓ centralizer (U K : Set G) = U K ⊔ C ∧
      C ≤ centralizer (V : Set G) ∧ R ⊓ centralizer (V : Set G) = V ⊔ C := by
  let V := (U K).map (MulAut.conj x⁻¹).toMonoidHom
  let C := R ⊓ centralizer (K : Set G)
  let P := R ⊓ centralizer (U K : Set G)
  let P' := R ⊓ centralizer (V : Set G)
  have hmut := h.single_block_mutual_centralizers hR hSylow hRK hx hnc hsquare
  have hcommon := h.source_common_centralizer_le hSylow hx hnc (inf_le_left.trans hRK)
  have hRNU : R ≤ normalizer (U K : Set G) :=
    hRK.trans (normalizer_le_normalizer_characteristic_image K (blockU K))
  have hRNv : R ≤ normalizer (V : Set G) := by
    have hs : R.map (MulAut.conj x⁻¹).toMonoidHom = R :=
      mem_normalizer_iff_map_conj_eq.mp ((normalizer (R : Set G)).inv_mem hx)
    rw [← map_equiv_normalizer_eq,← hs]
    exact map_mono hRNU
  have hP'NU : P' ≤ normalizer (U K : Set G) := inf_le_left.trans hRNU
  have hPNv : P ≤ normalizer (V : Set G) := inf_le_left.trans hRNv
  have hCU : C ≤ centralizer (U K : Set G) := inf_le_right.trans (centralizer_le (map_subtype_le _))
  have hCP : C ≤ P := le_inf inf_le_left hCU
  let := h.elementary
  let : IsElementaryAbelian 2 V := IsElementaryAbelian.map (MulAut.conj x⁻¹).toMonoidHom
  have hUP : U K ≤ P := le_inf (h.module_le.trans inf_le_left) (le_centralizer (U K))
  have hprod : P = U K ⊔ C := by
    apply le_antisymm
    · intro p hp
      have hm : p ∈ (U K : Set G) * (P' : Set G) := by
        rw [← coe_mul_of_right_le_normalizer_left _ _ hP'NU]
        exact hmut.2 hp
      obtain ⟨u,hu,a,ha,rfl⟩ := hm
      have haP : a ∈ P := by
        have hh := P.mul_mem (P.inv_mem (hUP hu)) hp
        simpa only [inv_mul_cancel_left] using hh
      exact (U K ⊔ C).mul_mem (mem_sup_left hu) (hcommon ⟨haP,ha.2⟩)
    · exact sup_le hUP hCP
  have hCV : C ≤ centralizer (V : Set G) := h.centralizer_centralizes_of_supplement hx
    ⊥ P' C bot_le bot_le inf_le_right
    (by simpa only [sup_bot_eq] using hP'NU) inf_le_right
    (by simpa only [sup_bot_eq] using hCP.trans hmut.2)
  refine ⟨hprod,hCV,?_⟩
  have hfix : U K ⊓ centralizer (V : Set G) = U K ⊓ V :=
    (h.commutator_eq_fixed hx hnc).1.symm.trans (h.commutator_eq_fixed hx hnc).2
  have hVR : V ≤ R := (h.conjugate_le hx).trans inf_le_left
  apply le_antisymm
  · intro a ha
    have hm : a ∈ (V : Set G) * (P : Set G) := by
      rw [← coe_mul_of_right_le_normalizer_left _ _ hPNv]
      exact hmut.1 ha
    obtain ⟨v,hv,p,hp,hvp⟩ := hm
    have hpV : p ∈ centralizer (V : Set G) := by
      have hh := (centralizer (V : Set G)).mul_mem
        ((centralizer (V : Set G)).inv_mem (le_centralizer V hv)) ha.2
      rw [← hvp] at hh
      simpa only [inv_mul_cancel_left] using hh
    have hm' : p ∈ (U K : Set G) * (C : Set G) := by
      rw [← coe_mul_of_right_le_normalizer_left _ _ (hCU.trans (Subgroup.centralizer_le_normalizer _))]
      exact hprod ▸ hp
    obtain ⟨u,hu,c,hc,huc⟩ := hm'
    have huV : u ∈ centralizer (V : Set G) := by
      have hh := (centralizer (V : Set G)).mul_mem hpV ((centralizer (V : Set G)).inv_mem (hCV hc))
      rw [← huc] at hh
      simpa only [mul_inv_cancel_right] using hh
    have hu' : u ∈ V := (hfix ▸ (show u ∈ U K ⊓ centralizer (V : Set G) from ⟨hu,huV⟩)).2
    rw [← hvp,← huc]
    change v*(u*c) ∈ V ⊔ C
    rw [← mul_assoc]
    exact mul_mem_sup (V.mul_mem hv hu') hc
  · exact sup_le (le_inf hVR (le_centralizer V)) (le_inf inf_le_left hCV)
end CFSG.Quasithin.ChapterC.Section05.ConjugateSource.RankOne
