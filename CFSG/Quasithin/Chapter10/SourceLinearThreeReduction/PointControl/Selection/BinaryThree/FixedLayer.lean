module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.Selection.BinaryThree.Kernel
public import CFSG.Quasithin.Chapter10.SourceNonnormalPairAction
public import CFSG.Quasithin.Chapter10.SourceA5ComponentNormalizer.QuotientStructure
public import Theory.GroupTheory.ConjugateOrbitIndexTwo
public import Theory.GroupTheory.InvolutionCentralizerControl

/-!
# The entire binary-three fixed layer is fixed by the half-Sylow

The original pair and crossed centralization give C_V(L₀)=C_W(L)C_W(L)ᵗ.
The literal half-Sylow normalizes both factors. Each has at most two elements,
so it centralizes their join. The pair and conjugation arguments use the
lower source interfaces directly, avoiding the later A₅ offender argument.
Source: Aschbacher--Smith, 10.1.1 and 10.2.8--9, pp.741,749--750.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative Pointwise
namespace CFSG.Quasithin.Chapter10.PointControl.Selection.BinaryThree
open Chapter3.Section02
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)

omit D in
private theorem normalizer_le_centralizer_of_card_le_two (K : Subgroup G)
    (hK : Nat.card K ≤ 2) : normalizer (K : Set G) ≤ centralizer (K : Set G) := by
  by_cases hz : K = ⊥
  · rw [hz]
    intro x _ y hy
    have hy1 : y = 1 := mem_bot.mp hy
    subst y
    simp
  · exact normalizer_le_centralizer_of_card_two K (by
      have hp := (Subgroup.one_lt_card_iff_ne_bot K).mpr hz
      omega)

/-- Both moved kernels are fixed by the literal half-Sylow. -/
theorem half_sylow_centralizes_moved_kernels
    (hmodel : BinaryThreeNatural D)
    {t : G} (ht : t ∈ (T : Subgroup G)) (htn : t ∉ normalizer (L : Set G)) :
    (T : Subgroup G) ⊓ normalizer (L : Set G) ≤
      centralizer (↑(sourceMovedFixed D ⊔
        (sourceMovedFixed D).map (MulAut.conj t).toMonoidHom : Subgroup G) : Set G) := by
  let S := (T : Subgroup G) ⊓ normalizer (L : Set G)
  let W := ⁅D.fullModule,L⁆
  let B := L.map (MulAut.conj t).toMonoidHom
  let U := W.map (MulAut.conj t).toMonoidHom
  have hSM : S ≤ D.maximalLocal := inf_le_left.trans (le_normalizer_componentOrbit L T)
  have hSW : S ≤ normalizer (W : Set G) :=
    (le_inf hSM inf_le_right).trans (source_moved_normalizer_local_containment D)
  have hSK : S ≤ normalizer (sourceMovedFixed D : Set G) :=
    (le_inf inf_le_right hSW).trans (source_original_moved_fixed_normalizer D)
  have hSB : S ≤ normalizer (B : Set G) :=
    (le_inf inf_le_right hSM).trans (source_nonnormal_component_normalizer_fixes_opposite
      D (fun hn => htn (hn ht)) ht htn)
  have hmap : U = ⁅D.fullModule,B⁆ := by
    dsimp [U,W,B]
    rw [map_commutator,mem_normalizer_iff_map_conj_eq.mp
      (D.maximalLocal_normalizes_fullModule (le_normalizer_componentOrbit L T ht))]
  have hSU : S ≤ normalizer (U : Set G) := by
    rw [hmap]
    intro s hs
    apply mem_normalizer_iff_map_conj_eq.mpr
    rw [map_commutator,mem_normalizer_iff_map_conj_eq.mp
      (D.maximalLocal_normalizes_fullModule (hSM hs)),
      mem_normalizer_iff_map_conj_eq.mp (hSB hs)]
  have hKmap : (sourceMovedFixed D).map (MulAut.conj t).toMonoidHom =
      U ⊓ centralizer (B : Set G) := by
    change (W ⊓ centralizer (L : Set G)).map (MulAut.conj t).toMonoidHom = _
    rw [map_inf _ _ _ (MulAut.conj t).injective,Theory.GroupTheory.map_centralizer_equiv]
    rfl
  have hSK' : S ≤ normalizer
      (((sourceMovedFixed D).map (MulAut.conj t).toMonoidHom) : Set G) := by
    rw [hKmap]
    exact (le_inf hSU (hSB.trans (normalizer_le_normalizer_centralizer B))).trans
      inf_normalizer_le_normalizer_inf
  have hcard := moved_fixed_card_le_two D hmodel
  have hcard' : Nat.card ((sourceMovedFixed D).map (MulAut.conj t).toMonoidHom) ≤ 2 := by
    exact (card_map_of_injective (f := (MulAut.conj t).toMonoidHom)
      (K := sourceMovedFixed D) (MulAut.conj t).injective).le.trans hcard
  apply le_centralizer_iff.mp
  apply sup_le
  · exact le_centralizer_iff.mpr
      (hSK.trans (normalizer_le_centralizer_of_card_le_two _ hcard))
  · exact le_centralizer_iff.mpr
      (hSK'.trans (normalizer_le_centralizer_of_card_le_two _ hcard'))

/-- The full fixed layer is precisely the join of the two original moved kernels. -/
theorem fixed_layer_eq_moved_kernels
    {t : G} (ht : t ∈ (T : Subgroup G)) (htn : t ∉ normalizer (L : Set G))
    (hcross : (⁅D.fullModule,L⁆).map (MulAut.conj t).toMonoidHom ≤ centralizer (L : Set G)) :
    D.fullModule ⊓ centralizer (localOrbit T L : Set G) =
      sourceMovedFixed D ⊔ (sourceMovedFixed D).map (MulAut.conj t).toMonoidHom := by
  let W := ⁅D.fullModule,L⁆
  let B := L.map (MulAut.conj t).toMonoidHom
  let U := W.map (MulAut.conj t).toMonoidHom
  have hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G) := fun h => htn (h ht)
  have hgen : D.fullModule = W ⊔ U := by
    obtain ⟨s,_,_,_,hV,hpair⟩ := source_nonnormal_fullModule_pair D hn
    have hne : U ≠ W := by
      intro he
      have hc : W ≤ centralizer (L : Set G) := he ▸ hcross
      have hz : ⁅W,L⁆ = ⊥ := commutator_eq_bot_iff_le_centralizer.mpr hc
      exact source_full_moved_ne_bot D ((source_full_moved_eq_commutator D).symm.trans hz)
    have he := (hpair t (le_normalizer_componentOrbit L T ht)).resolve_left hne
    exact hV.trans (congrArg (fun X : Subgroup G => W ⊔ X) he.symm)
  have hpair : localOrbit T L = L ⊔ B := componentOrbit_eq_sup_of_index_two L T
    (normalizer (L : Set G))
    (source_nonnormal_sylow_stabilizer_index D.simpleQTKE D.maximal.1 hn) inf_le_right ht htn
  have hsep : W ≤ centralizer (B : Set G) := by
    have hR : (T : Subgroup G) ⊓ normalizer (L : Set G) ≤ normalizer (W : Set G) :=
      (le_inf (inf_le_left.trans (le_normalizer_componentOrbit L T)) inf_le_right).trans
        (source_moved_normalizer_local_containment D)
    have hW := conjugate_twice_eq_of_index_two W (T : Subgroup G)
      (normalizer (L : Set G))
      (source_nonnormal_sylow_stabilizer_index D.simpleQTKE D.maximal.1 hn) hR ht
    have hz := congrArg (map (MulAut.conj t).toMonoidHom)
      (commutator_eq_bot_iff_le_centralizer.mpr hcross)
    rw [map_commutator,hW,Subgroup.map_bot] at hz
    exact commutator_eq_bot_iff_le_centralizer.mp hz
  have hWV : W ≤ D.fullModule := hgen ▸ le_sup_left
  have hUV : U ≤ D.fullModule := hgen ▸ le_sup_right
  have hKmap : (sourceMovedFixed D).map (MulAut.conj t).toMonoidHom =
      U ⊓ centralizer (B : Set G) := by
    change (W ⊓ centralizer (L : Set G)).map (MulAut.conj t).toMonoidHom = _
    rw [map_inf _ _ _ (MulAut.conj t).injective,Theory.GroupTheory.map_centralizer_equiv]
    rfl
  have hc (x : G) : x ∈ centralizer (localOrbit T L : Set G) ↔
      x ∈ centralizer (L : Set G) ∧ x ∈ centralizer (B : Set G) := by
    rw [hpair]
    constructor
    · intro hx
      exact ⟨fun y hy => hx y ((show L ≤ L ⊔ B from le_sup_left) hy),
        fun y hy => hx y ((show B ≤ L ⊔ B from le_sup_right) hy)⟩
    · rintro ⟨hl,hb⟩
      have hh : L ⊔ B ≤ centralizer ({x} : Set G) :=
        sup_le (fun l h => mem_centralizer_singleton_iff.mpr (hl l h))
          (fun b h => mem_centralizer_singleton_iff.mpr (hb b h))
      exact fun y hy => mem_centralizer_singleton_iff.mp (hh hy)
  have hu := Chapter1.Section02.nonsolvable_uniqueness_of_theoremsAC
    (fun X _ _ => ChapterA.Section02.theoremA_knownSimple (G := X))
    (fun X _ _ => ChapterA.Section02.theoremC_knownSimple (G := X))
    D.simpleQTKE T D.maximal
  let := D.fullModule_elementary hu
  have hWU : W ≤ normalizer (U : Set G) :=
    (hWV.trans (D.fullModule.le_centralizer.trans (centralizer_le hUV))).trans
      (Subgroup.centralizer_le_normalizer _)
  apply le_antisymm
  · intro v hv
    have hvprod : v ∈ (W : Set G) * (U : Set G) := by
      rw [← coe_mul_of_left_le_normalizer_right W U hWU]
      exact hgen ▸ hv.1
    obtain ⟨w,hw,u,hu,rfl⟩ := hvprod
    have hvfix := (hc (w*u)).mp hv.2
    have hwfix : w ∈ centralizer (L : Set G) := by
      have hh := (centralizer (L : Set G)).mul_mem hvfix.1
        ((centralizer (L : Set G)).inv_mem (hcross hu))
      simpa only [mul_inv_cancel_right] using hh
    have hufix : u ∈ centralizer (B : Set G) := by
      have hh := (centralizer (B : Set G)).mul_mem
        ((centralizer (B : Set G)).inv_mem (hsep hw)) hvfix.2
      simpa only [inv_mul_cancel_left] using hh
    exact mul_mem_sup (show w ∈ sourceMovedFixed D from ⟨hw,hwfix⟩)
      (hKmap.symm ▸ (show u ∈ U ⊓ centralizer (B : Set G) from ⟨hu,hufix⟩))
  · apply sup_le
    · intro w hw
      exact ⟨hWV hw.1,(hc w).mpr ⟨hw.2,hsep hw.1⟩⟩
    · rw [hKmap]
      intro u hu
      exact ⟨hUV hu.1,(hc u).mpr ⟨hcross hu.1,hu.2⟩⟩

/-- Binary-three natural coordinates fix the entire original L₀-fixed layer under T₁. -/
theorem fixed_layer_centralizes_half_sylow
    (hmodel : BinaryThreeNatural D)
    {t : G} (ht : t ∈ (T : Subgroup G)) (htn : t ∉ normalizer (L : Set G))
    (hcross : (⁅D.fullModule,L⁆).map (MulAut.conj t).toMonoidHom ≤ centralizer (L : Set G)) :
    D.fullModule ⊓ centralizer (localOrbit T L : Set G) ≤
      centralizer (((T : Subgroup G) ⊓ normalizer (L : Set G)) : Set G) := by
  rw [fixed_layer_eq_moved_kernels D ht htn hcross]
  exact le_centralizer_iff.mpr (half_sylow_centralizes_moved_kernels D hmodel ht htn)

end CFSG.Quasithin.Chapter10.PointControl.Selection.BinaryThree
