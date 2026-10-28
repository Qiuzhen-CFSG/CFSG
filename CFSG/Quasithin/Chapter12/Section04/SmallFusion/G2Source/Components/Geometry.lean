module
public import CFSG.Quasithin.Chapter12.Section04.SmallFusion.G2Source.Components.Comparison
public import Theory.GroupTheory.NormalizedSupCard

/-!
# Symmetric comparison for a cubic-normalizing G₂ hyperplane mover

Two distinct hyperplanes of the original binary seven-space generate it and
intersect in dimension five. A cubic normalizing both remains nontrivial on
the intersection, since its local pointwise centralizer centralizes all of V.
The original component and its literal conjugate are therefore both components
of that same intersection centralizer. Cubic-rank uniqueness identifies them,
so the component centralizes both hyperplanes and hence V, a contradiction.

The mover need only normalize the cubic and move the hyperplane. No square
condition on it is used: comparison is applied symmetrically to the two actual
hyperplanes. Source: Aschbacher--Smith, 12.4.8, printed p.815.
-/

public section
open Subgroup Theory.GroupTheory
open CFSG.Quasithin.Chapter12.Section02
open CFSG.Quasithin.ChapterE CFSG.Quasithin.ChapterE.Section06
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section04.SmallFusion.G2Source.Components
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V U : Subgroup G}

omit [Finite G] in
private theorem centralizer_map_equiv (A : Subgroup G) (f : G ≃* G) :
    (centralizer (A : Set G)).map f.toMonoidHom =
      centralizer (A.map f.toMonoidHom : Set G) := by
  apply le_antisymm
  · exact map_centralizer_le_centralizer_image _ _
  · intro x hx
    refine ⟨f.symm x, ?_, f.apply_symm_apply x⟩
    intro y hy
    apply f.injective
    simpa only [map_mul, f.apply_symm_apply] using
      hx (f y) (mem_map_of_mem f.toMonoidHom hy)

private theorem conjugate_geometry [IsElementaryAbelian 2 V]
    (hUV : U ≤ V) (hcardU : Nat.card U = 64) (hcor : subgroupCorank V U = 1)
    (hescape : ¬ centralizer (U : Set G) ≤ normalizer (V : Set G))
    {l : G} (hlV : l ∈ normalizer (V : Set G))
    (hm : l ∉ normalizer (U : Set G)) :
    let W := U.map (MulAut.conj l).toMonoidHom
    W ≤ V ∧ subgroupCorank V W = 1 ∧
      (¬ centralizer (W : Set G) ≤ normalizer (V : Set G)) ∧
      U ⊔ W = V ∧ Nat.card (U ⊓ W : Subgroup G) = 32 ∧
      subgroupCorank U (U ⊓ W) = 1 ∧ subgroupCorank W (U ⊓ W) = 1 := by
  let _ : IsElementaryAbelian 2 U := IsElementaryAbelian.of_le hUV
  let W := U.map (MulAut.conj l).toMonoidHom
  let I := U ⊓ W
  have hVfix := mem_normalizer_iff_map_conj_eq.mp hlV
  have hWV : W ≤ V := (map_mono hUV).trans hVfix.le
  let _ : IsElementaryAbelian 2 W := IsElementaryAbelian.of_le hWV
  have hW : Nat.card W = 64 :=
    (card_map_of_injective (MulAut.conj l).injective).trans hcardU
  have hindex : U.relIndex V = 2 := by
    rw [relIndex_eq_two_pow_quotient_finrank, ←subgroupCorank_eq_quotient_finrank,
      hcor, pow_one]
  have hV : Nat.card V = 128 := by
    have hc := relIndex_mul_relIndex (⊥ : Subgroup G) U V bot_le hUV
    rw [relIndex_bot_left,relIndex_bot_left,hindex,hcardU] at hc
    omega
  have hne : W ≠ U := fun he => hm (mem_normalizer_iff_map_conj_eq.mpr he)
  have hsup : U ⊔ W = V := by
    have hd : Nat.card (U ⊔ W : Subgroup G) ∣ 128 :=
      hV ▸ card_dvd_of_le (sup_le hUV hWV)
    have hlo : 64 ≤ Nat.card (U ⊔ W : Subgroup G) := hcardU ▸ card_le_of_le le_sup_left
    have hneq : Nat.card (U ⊔ W : Subgroup G) ≠ 64 := by
      intro hc
      have he : U = U ⊔ W := eq_of_le_of_card_ge le_sup_left (by omega)
      exact hne (eq_of_le_of_card_ge (he ▸ (le_sup_right : W ≤ U ⊔ W)) (by omega))
    have he : Nat.card (U ⊔ W : Subgroup G) = 128 := by
      have hd' : Nat.card (U ⊔ W : Subgroup G) ∈ Nat.divisors 128 :=
        Nat.mem_divisors.mpr ⟨hd,by decide⟩
      have ht : Nat.divisors 128 = {1,2,4,8,16,32,64,128} := by decide
      rw [ht] at hd'
      simp only [Finset.mem_insert,Finset.mem_singleton] at hd'
      omega
    exact eq_of_le_of_card_ge (sup_le hUV hWV) (by omega)
  have hn : W ≤ normalizer (U : Set G) := by
    apply (show W ≤ centralizer (U : Set G) from ?_).trans
      (Subgroup.centralizer_le_normalizer _)
    intro w hw v hv
    exact setLike_mul_comm (hUV hv) (hWV hw)
  have hc : Nat.card I = 32 := by
    have hh := card_mul_eq_card_inf_mul_card_sup_of_normalizes U W hn
    rw [hcardU,hW,hsup,hV] at hh
    change 64 * 64 = Nat.card I * 128 at hh
    omega
  have hcorU : subgroupCorank U I = 1 := by
    have hi : I.relIndex U = 2 := by
      have hh := relIndex_mul_relIndex (⊥ : Subgroup G) I U bot_le inf_le_left
      simp only [relIndex_bot_left] at hh
      rw [hc,hcardU] at hh
      omega
    rw [relIndex_eq_two_pow_quotient_finrank,←subgroupCorank_eq_quotient_finrank] at hi
    exact Nat.pow_right_injective (by decide : 2 ≤ 2) (by simpa using hi)
  have hcorW : subgroupCorank W I = 1 := by
    have hi : I.relIndex W = 2 := by
      have hh := relIndex_mul_relIndex (⊥ : Subgroup G) I W bot_le inf_le_right
      simp only [relIndex_bot_left] at hh
      rw [hc,hW] at hh
      omega
    rw [relIndex_eq_two_pow_quotient_finrank,←subgroupCorank_eq_quotient_finrank] at hi
    exact Nat.pow_right_injective (by decide : 2 ≤ 2) (by simpa using hi)
  have hWcor : subgroupCorank V W = 1 := by
    change Nat.log 2 (W.relIndex V) = 1
    rw [←hVfix]
    change Nat.log 2 ((U.map (MulAut.conj l).toMonoidHom).relIndex
      (V.map (MulAut.conj l).toMonoidHom)) = 1
    rw [relIndex_map_map_of_injective U V (MulAut.conj l).injective]
    exact hcor
  have hWescape : ¬ centralizer (W : Set G) ≤ normalizer (V : Set G) := by
    intro hC
    apply hescape
    intro a ha
    have hc : MulAut.conj l a ∈ centralizer (W : Set G) := by
      rw [←centralizer_map_equiv U (MulAut.conj l)]
      exact mem_map_of_mem _ ha
    have han := hC hc
    have he : a = l⁻¹ * (MulAut.conj l a) * l := by
      simp only [MulAut.conj_apply]
      group
    rw [he]
    exact (normalizer (V : Set G)).mul_mem
      ((normalizer (V : Set G)).mul_mem
        ((normalizer (V : Set G)).inv_mem hlV) han) hlV
  exact ⟨hWV,hWcor,hWescape,hsup,hc,hcorU,hcorW⟩

/-- The actual symmetric component comparison closes the mover branch.
The same cubic acts on both hyperplanes and their literal intersection. -/
theorem cover_component_false_of_mover
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (D : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (e : ChapterB.QuasisimpleSource.ActionEquiv D.quotientAction
      (Atlas.G2.Natural.OrthogonalCover.action (ZMod 2)))
    (hne : fixedSubgroup L V ≠ ⊥)
    (hUV : U ≤ V) (hcor : subgroupCorank V U = 1)
    (hescape : ¬ centralizer (U : Set G) ≤ normalizer (V : Set G))
    {K : Subgroup G} (hK : IsComponentIn K (centralizer (U : Set G)))
    {x l : G} (hxV : x ∈ normalizer (V : Set G)) (hx : orderOf x = 3)
    (hxU : x ∈ normalizer (U : Set G)) (hxC : x ∉ centralizer (U : Set G))
    (hlV : l ∈ normalizer (V : Set G))
    (hlX : l ∈ normalizer (zpowers x : Set G))
    (hm : l ∉ normalizer (U : Set G)) : False := by
  let _ := D.elementary
  let W := U.map (MulAut.conj l).toMonoidHom
  let I := U ⊓ W
  have hg := escaping_cover_subspaces h D structural e hne hUV hcor hescape
  obtain ⟨hWV,hWcor,hWescape,hsup,hIcard,hIcorU,hIcorW⟩ :=
    conjugate_geometry hUV hg.1 hcor hescape hlV hm
  obtain ⟨c,cs⟩ := cover_localData h D structural e hne hUV hcor hescape
  obtain ⟨d,_⟩ := cover_localData h D structural e hne hWV hWcor hWescape
  have ci : LocalData T V I := cs I inf_le_left hIcorU
  have hS := (cover_escaping_sylow_centralizers h D structural e hne
    hUV hcor hescape).2 I inf_le_left hIcorU
  have hnX : zpowers x ≤ normalizer (U : Set G) := zpowers_le.mpr hxU
  have hnW : zpowers x ≤ normalizer (W : Set G) := by
    have hh := map_mono (f := (MulAut.conj l).toMonoidHom) hnX
    have hX : (zpowers x).map (MulAut.conj l).toMonoidHom = zpowers x :=
      mem_normalizer_iff_map_conj_eq.mp hlX
    rw [hX] at hh
    exact hh.trans (U.le_normalizer_map (MulAut.conj l).toMonoidHom)
  have hxW : x ∈ normalizer (W : Set G) := hnW (mem_zpowers x)
  have hxI : x ∈ normalizer (I : Set G) :=
    inf_normalizer_le_normalizer_inf ⟨hxU,hxW⟩
  have hxCI : x ∉ centralizer (I : Set G) := by
    intro hc
    exact hxC ((centralizer_le hUV) (ci.localCentralizer ⟨hxV,hc⟩))
  have hKI := c.component_in_section_centralizer ci hK inf_le_left hS hx hxI hxCI hxU
  have hKW : IsComponentIn (K.map (MulAut.conj l).toMonoidHom)
      (centralizer (W : Set G)) := by
    rw [←centralizer_map_equiv U (MulAut.conj l)]
    exact hK.map (MulAut.conj l)
  have hKWI := d.component_in_section_centralizer ci hKW inf_le_right hS hx hxI hxCI hxW
  have heK := ci.component_unique hKI hKWI hx hxI hxCI
  have hKCW : K ≤ centralizer (W : Set G) := heK.symm ▸ hKW.1
  have hKCV : K ≤ centralizer (V : Set G) := by
    apply le_centralizer_iff.mpr
    rw [←hsup]
    exact sup_le (le_centralizer_iff.mp hK.1) (le_centralizer_iff.mp hKCW)
  exact (c.component_local hK).1
    (hKCV.trans (Subgroup.centralizer_le_normalizer _))

end CFSG.Quasithin.Chapter12.Section04.SmallFusion.G2Source.Components
