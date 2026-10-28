module
public import CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.BlockModuleContainment
public import CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.BlockLinearThreeAction
public import CFSG.Quasithin.ChapterC.Section01.BlockTypes.SL3ParabolicModule
public import CFSG.Quasithin.ChapterC.Section01.BlockStructure.Centralizer

/-!
# The SL₃ block contradiction from the original parabolic marking

The intrinsic additive-subgroup calculation is transported through K ≤ H ≤ G
and the original full module W. Perfectness removes the fixed-layer error and
gives [U(K),L] = W. Crossing gives [U(K)ᵗ,L] = W, so each crossed actor fixes the
actual L image in K/O₂(K). Parabolic pointwise rigidity makes its quotient action
trivial. The short-group central-cover lemma then puts [U(K)ᵗ,K] in U(K), contrary
to the proved crossing obstruction.

The model and the placement of the original L image as a standard parabolic
residual remain explicit. Constructing that placement from C.4.1 is still owned
by the rank-one block-exclusion assembly, qt-d-1222-rankone-uniqueness-block.
No equality with the separately chosen Chapter 12 module is used.
Source: Aschbacher--Smith C.4.7 and original 4.3.7, printed pp.153 and 616.
-/

public section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness
open ChapterC
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}

theorem SourceConfiguration.block_commutator_eq_fullModule_of_sl3_parabolic
    (c : SourceConfiguration T L) (hf : generalizedFitting c.K = pCore 2 c.K)
    {F : Type*} [Field F]
    {rho : SL(3,F) →* MulAut (Multiplicative (Fin 3 → F))}
    (m : BlockModuleModel c.K rho)
    (hrho : ∀ g v, (rho g v).toAdd = g.val.mulVec v.toAdd)
    (he : c.componentQuotientL.map m.quotientIso.toMonoidHom =
        Matrix.PSL3.LinearThree.pointLocalSL F ∨
      c.componentQuotientL.map m.quotientIso.toMonoidHom =
        Matrix.PSL3.LinearThree.lineLocalSL F) :
    ⁅c.blockLayer,L⁆ =
      Section02.Unitary.fullModule L ((L ⊔ (T : Subgroup G)).pCoreIn 2) := by
  let W := Section02.Unitary.fullModule L ((L ⊔ (T : Subgroup G)).pCoreIn 2)
  let f : c.K →* G := c.H.subtype.comp c.K.subtype
  have hfi : Function.Injective f := c.H.subtype_injective.comp c.K.subtype_injective
  have hfr : f.range = c.K.map c.H.subtype := by
    rw [MonoidHom.range_comp, range_subtype]
  have hU : (blockU c.K).map f = c.blockLayer := by rw [← map_map]
  let A := L.comap f
  let B := W.comap f
  have hLA : A.map f = L := map_comap_eq_self (by rw [hfr]; exact c.le_component)
  have hWL : W ≤ L := by
    have hs : conjugateSpanBy L (c.H ⊓ normalizer (L : Set G)) = L :=
      le_antisymm (conjugateSpanBy_le le_rfl inf_le_right) (le_conjugateSpanBy _ _)
    simpa only [hs] using c.c28.module_le
  have hWB : B.map f = W := map_comap_eq_self (hWL.trans (by rw [hfr]; exact c.le_component))
  have hBU : B ≤ blockU c.K := by
    intro b hb
    apply (mem_map_iff_mem hfi).mp
    rw [hU]
    exact c.fullModule_le_blockLayer hf hb
  have hBne : B ≠ ⊥ := by
    intro he
    have hWne := c.c28.module_nontrivial
    apply hWne
    change W = ⊥
    rw [← hWB, he, Subgroup.map_bot]
  have hBA : ⁅B,A⁆ = B := by
    apply map_injective hfi
    rw [map_commutator, hWB, hLA]
    have hs : conjugateSpanBy L (c.H ⊓ normalizer (L : Set G)) = L :=
      le_antisymm (conjugateSpanBy_le le_rfl inf_le_right) (le_conjugateSpanBy _ _)
    exact (show W = ⁅W,L⁆ from by simpa only [hs] using c.c28.module_commutator).symm
  have hplace : A.map (m.quotientIso.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 c.K))) =
        Matrix.PSL3.LinearThree.pointLocalSL F ∨
      A.map (m.quotientIso.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 c.K))) =
        Matrix.PSL3.LinearThree.lineLocalSL F := by
    simpa only [SourceConfiguration.componentQuotientL, A, f, subgroupOf, comap_comap, ← map_map] using he
  have hm := map_mono (f := f) (m.sl3_commutator_le_fixed_sup hrho A B hBU hBne hBA hplace)
  rw [map_commutator, hU, hLA, Subgroup.map_sup, hWB] at hm
  apply c.block_commutator_eq_fullModule_of_fixed_layer hf
  apply hm.trans
  apply sup_le_sup_left
  intro z hz
  obtain ⟨u,hu,rfl⟩ := hz
  refine ⟨?_,?_⟩
  · rw [←hU]
    exact mem_map_of_mem f hu.1
  · rintro y ⟨k,hk,rfl⟩
    exact congrArg f (mem_center_iff.mp hu.2 ⟨k,hk⟩)

/-- The SL₃ contradiction once the actual quotient and local image have
been marked. No commutator identity or module placement remains assumed. -/
theorem SourceConfiguration.false_of_sl3_parabolic
    {V : Subgroup G} (c : SourceConfiguration T L)
    (D : Chapter12.Section02.ChosenModule T L V)
    (hf : generalizedFitting c.K = pCore 2 c.K) (hb : IsBlock c.K)
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    {n : ℕ} (hn : 0 < n) (hF : Nat.card F = 2 ^ n)
    {rho : SL(3,F) →* MulAut (Multiplicative (Fin 3 → F))}
    (m : BlockModuleModel c.K rho)
    (hrho : ∀ g v, (rho g v).toAdd = g.val.mulVec v.toAdd)
    (he : c.componentQuotientL.map m.quotientIso.toMonoidHom =
        Matrix.PSL3.LinearThree.pointLocalSL F ∨
      c.componentQuotientL.map m.quotientIso.toMonoidHom =
        Matrix.PSL3.LinearThree.lineLocalSL F) : False := by
  let U' := c.blockLayer.map (MulAut.conj c.t⁻¹).toMonoidHom
  let f : c.K →* G := c.H.subtype.comp c.K.subtype
  have hfi : Function.Injective f := c.H.subtype_injective.comp c.K.subtype_injective
  have hU : (blockU c.K).map f = c.blockLayer := by rw [← map_map]
  have hU'H : U' ≤ c.H := by
    have hs : (((T : Subgroup G) ⊓ c.H).map (MulAut.conj c.t⁻¹).toMonoidHom) =
        (T : Subgroup G) ⊓ c.H := mem_normalizer_iff_map_conj_eq.mp
      ((normalizer (((T : Subgroup G) ⊓ c.H) : Set G)).inv_mem c.crossing_normalizes)
    exact ((map_mono (f := (MulAut.conj c.t⁻¹).toMonoidHom)
      c.blockLayer_le_sylow).trans_eq hs).trans inf_le_right
  have hcomm := c.block_crossing_commutator_fullModule D
    (c.block_commutator_eq_fullModule_of_sl3_parabolic hf m hrho he)
  have hlocal : ⁅U',L⁆ ≤ c.blockLayer := hcomm.le.trans (c.fullModule_le_blockLayer hf)
  let : c.K.Normal := c.component_normal
  apply c.block_crossing_commutator_not_le hb
  rw [commutator_comm]
  apply commutator_le.mpr
  intro u hu k hk
  obtain ⟨k,hk,rfl⟩ := hk
  let z : c.K := ⟨k,hk⟩
  let a : MulAut c.K := MulAut.conjNormal (⟨u,hU'H hu⟩ : c.H)
  have ha : (pCore 2 c.K).quotientAut a = 1 := by
    apply c.quotientAut_eq_one_of_parabolic_image hn hF m.quotientIso he
    rintro x ⟨w,hw,rfl⟩
    rw [quotientAut_apply_mk]
    apply QuotientGroup.eq_iff_div_mem.mpr
    have hd : a w * w⁻¹ ∈ blockU c.K := by
      apply (mem_map_iff_mem hfi).mp
      rw [hU]
      exact hlocal (commutator_mem_commutator hu hw)
    exact blockU_le_core (by simpa only [div_eq_mul_inv] using hd)
  have hacore (w : c.K) : a w * w⁻¹ ∈ pCore 2 c.K := by
    have hh := DFunLike.congr_fun ha (QuotientGroup.mk' (pCore 2 c.K) w)
    rw [quotientAut_apply_mk] at hh
    simpa only [div_eq_mul_inv] using QuotientGroup.eq_iff_div_mem.mp hh
  have hau := DFunLike.congr_fun (hb.short.quotient_blockU_aut_eq_one a hacore)
    (QuotientGroup.mk' (blockU c.K) z)
  rw [quotientAut_apply_mk] at hau
  have hz : a z * z⁻¹ ∈ blockU c.K := by
    simpa only [div_eq_mul_inv] using QuotientGroup.eq_iff_div_mem.mp hau
  rw [←hU]
  exact ⟨a z * z⁻¹,hz,rfl⟩

end CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness
