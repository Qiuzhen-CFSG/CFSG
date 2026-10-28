module
public import CFSG.Quasithin.Chapter2.Section04.LinearShadows.Double.SetupSource
public import CFSG.Quasithin.ChapterC.Section06.RankOnePairSource

/-!
# The four maximum elementary subgroups in the double linear source

The two marked natural blocks give the original core, its selected conjugate,
and two mixed module products as the full maximum elementary family of
J(S) = Baum(S). Each mixed product centralizes one original module, whereas
J(S) contains its noncommuting conjugate. Consequently the opposite core is
the unique member which generates J(S) together with the original core.
Simultaneous normalizers of J(S) and the original core therefore normalize
both cores. This is the literal torus step and four-point family used in the
double linear branch.

Source: Aschbacher–Smith, 2.4.7, double-block case, printed pp.539–540,
using C.5.6(7).
-/

@[expose] public section
open Subgroup Theory.GroupTheory Stellmacher
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter2
open ChapterC.Section05.BlockAnalysis ChapterC.Section05.ConjugateSource
variable {G : Type*} [Group G] [Finite G] {M : Subgroup G}
variable {d : MinimalBlockSetup M} {M₀ : Subgroup G} {n : ℕ}

private theorem DoubleLinearSourceSetup.paired_family
    (c : DoubleLinearSourceSetup d M₀ n)
    (hi : ((d.S : Subgroup d.H).map d.H.subtype).relIndex M₀ = 2) :
    let S := (d.S : Subgroup d.H).map d.H.subtype
    let R := elementaryAbelianMaxJ S
    let Q := twoCore d.H
    let Qx := Q.map (MulAut.conj c.x⁻¹).toMonoidHom
    let C := S ⊓ centralizer ((d.block.map d.H.subtype ⊔ c.second : Subgroup G) : Set G)
    let U₁ := sourceModule (d.block.map d.H.subtype)
    let U₂ := sourceModule c.second
    let V₁ := U₁.map (MulAut.conj c.x⁻¹).toMonoidHom
    let V₂ := U₂.map (MulAut.conj c.x⁻¹).toMonoidHom
    ChapterB.baumann S = R ∧ R = Q ⊔ Qx ∧
      elementaryAbelianMaxSubgroups R = {Q,Qx,(U₁ ⊔ V₂) ⊔ C,(V₁ ⊔ U₂) ⊔ C} := by
  let := c.field₁_field
  let := c.field₂_field
  let S := (d.S : Subgroup d.H).map d.H.subtype
  let K := d.block.map d.H.subtype
  have co : OriginalHypotheses d.H M₀ (K ⊔ c.second) S S := by
    rw [show K ⊔ c.second = d.L0.map d.H.subtype from c.join]
    exact c.original
  have ht : ∃ t : M₀, (t : G) ∈ S ∧ K.conjBy (t : G) = c.second := by
    obtain ⟨t,ht,he⟩ := c.exchange
    exact ⟨⟨t,c.original.R_le_M ht⟩,ht,he⟩
  have hfull : S ⊓ centralizer ((sourceModule K ⊔ sourceModule c.second : Subgroup G) : Set G) =
      d.H.pCoreIn 2 := by
    have hh := d.two_block_core_centralizer c.second c.marked₁.short c.marked₂.short
      c.commutes c.permutes c.exchange
    rw [(d.two_block_closures c.second c.permutes c.exchange).2] at hh
    exact hh
  have hf := ChapterC.Section06.rankOne_pair_family_from_original co c.marked₁ c.marked₂
    c.commutes c.permutes ht hfull hi c.x c.x_mem c.noncommuting
  refine ⟨hf.1,hf.1.symm.trans hf.2.2.2.2.1,?_⟩
  rw [←hf.1,baumann_maxFamily]
  exact hf.2.2.2.2.2.2

/-- The full maximum elementary family of the literal Thompson subgroup has
four members: the two cores and the two mixed module products. -/
theorem DoubleLinearSourceSetup.max_family
    (c : DoubleLinearSourceSetup d M₀ n)
    (hi : ((d.S : Subgroup d.H).map d.H.subtype).relIndex M₀ = 2) :
    let S := (d.S : Subgroup d.H).map d.H.subtype
    let R := elementaryAbelianMaxJ S
    let Q := twoCore d.H
    let Qx := Q.map (MulAut.conj c.x⁻¹).toMonoidHom
    let C := S ⊓ centralizer ((d.block.map d.H.subtype ⊔ c.second : Subgroup G) : Set G)
    let U₁ := sourceModule (d.block.map d.H.subtype)
    let U₂ := sourceModule c.second
    let V₁ := U₁.map (MulAut.conj c.x⁻¹).toMonoidHom
    let V₂ := U₂.map (MulAut.conj c.x⁻¹).toMonoidHom
    elementaryAbelianMaxSubgroups R = {Q,Qx,(U₁ ⊔ V₂) ⊔ C,(V₁ ⊔ U₂) ⊔ C} :=
  (c.paired_family hi).2.2

/-- The original core and the selected conjugate generate the exact
Thompson subgroup, which is also the Baumann subgroup. -/
theorem DoubleLinearSourceSetup.core_span
    (c : DoubleLinearSourceSetup d M₀ n)
    (hi : ((d.S : Subgroup d.H).map d.H.subtype).relIndex M₀ = 2) :
    let S := (d.S : Subgroup d.H).map d.H.subtype
    ChapterB.baumann S = elementaryAbelianMaxJ S ∧
      elementaryAbelianMaxJ S = twoCore d.H ⊔
        (twoCore d.H).map (MulAut.conj c.x⁻¹).toMonoidHom :=
  ⟨(c.paired_family hi).1,(c.paired_family hi).2.1⟩

private theorem DoubleLinearSourceSetup.separating_modules
    (c : DoubleLinearSourceSetup d M₀ n)
    (hi : ((d.S : Subgroup d.H).map d.H.subtype).relIndex M₀ = 2) :
    let S := (d.S : Subgroup d.H).map d.H.subtype
    let R := elementaryAbelianMaxJ S
    let Q := twoCore d.H
    let Qx := Q.map (MulAut.conj c.x⁻¹).toMonoidHom
    let C := S ⊓ centralizer ((d.block.map d.H.subtype ⊔ c.second : Subgroup G) : Set G)
    let U₁ := sourceModule (d.block.map d.H.subtype)
    let U₂ := sourceModule c.second
    let V₁ := U₁.map (MulAut.conj c.x⁻¹).toMonoidHom
    let V₂ := U₂.map (MulAut.conj c.x⁻¹).toMonoidHom
    ¬ V₁ ≤ centralizer (U₁ : Set G) ∧
      ¬ V₂ ≤ centralizer (U₂ : Set G) ∧
      Q ≤ centralizer (U₁ : Set G) ∧ Q ≤ centralizer (U₂ : Set G) ∧
      (U₁ ⊔ V₂) ⊔ C ≤ centralizer (U₁ : Set G) ∧
      (V₁ ⊔ U₂) ⊔ C ≤ centralizer (U₂ : Set G) ∧
      V₁ ≤ R ∧ V₂ ≤ R ∧ V₁ ≤ Qx ∧ V₂ ≤ Qx := by
  let := c.field₁_field
  let := c.field₂_field
  let S := (d.S : Subgroup d.H).map d.H.subtype
  let R := elementaryAbelianMaxJ S
  let K := d.block.map d.H.subtype
  let Q := twoCore d.H
  let U₁ := sourceModule K
  let U₂ := sourceModule c.second
  let V₁ := U₁.map (MulAut.conj c.x⁻¹).toMonoidHom
  let V₂ := U₂.map (MulAut.conj c.x⁻¹).toMonoidHom
  let C := S ⊓ centralizer ((K ⊔ c.second : Subgroup G) : Set G)
  have hBR : ChapterB.baumann S = R := (c.core_span hi).1
  have hxS : c.x ∈ normalizer (S : Set G) := c.original.R_normal c.x_mem
  have ht : ∃ t : M₀, (t : G) ∈ S ∧ K.conjBy (t : G) = c.second := by
    obtain ⟨t,ht,he⟩ := c.exchange
    exact ⟨⟨t,c.original.R_le_M ht⟩,ht,he⟩
  have hinputs := c.marked₁.fourModuleSourceInputs c.commutes c.marked₂.module_le
    M₀ S c.x c.x_mem hxS hi c.permutes ht c.noncommuting
  have hnc₂ : ¬ V₂ ≤ centralizer (U₂ : Set G) := RankOne.second_noncommuting hinputs
  have hV₁R : V₁ ≤ R := c.marked₁.conjugate_le hxS |>.trans_eq hBR
  have hV₂R : V₂ ≤ R := c.marked₂.conjugate_le hxS |>.trans_eq hBR
  have hQ : Q ≤ centralizer ((U₁ ⊔ U₂ : Subgroup G) : Set G) := by
    have hh := d.two_block_core_centralizer c.second c.marked₁.short c.marked₂.short
      c.commutes c.permutes c.exchange
    rw [(d.two_block_closures c.second c.permutes c.exchange).2] at hh
    change S ⊓ centralizer ((U₁ ⊔ U₂ : Subgroup G) : Set G) = Q at hh
    rw [←hh]
    exact inf_le_right
  have hQ₁ : Q ≤ centralizer (U₁ : Set G) := hQ.trans (centralizer_le (show U₁ ≤ U₁ ⊔ U₂ from le_sup_left))
  have hQ₂ : Q ≤ centralizer (U₂ : Set G) := hQ.trans (centralizer_le (show U₂ ≤ U₁ ⊔ U₂ from le_sup_right))
  have hC₁ : C ≤ centralizer (U₁ : Set G) := inf_le_right.trans
    (centralizer_le ((map_subtype_le _).trans le_sup_left))
  have hC₂ : C ≤ centralizer (U₂ : Set G) := inf_le_right.trans
    (centralizer_le ((map_subtype_le _).trans le_sup_right))
  have hc : U₁ ⊔ V₁ ≤ centralizer ((U₂ ⊔ V₂ : Subgroup G) : Set G) :=
    commutator_eq_bot_iff_le_centralizer.mp
      (c.marked₁.four_module_geometry c.commutes c.marked₂.module_le M₀ S c.x c.x_mem
        hxS hi c.permutes ht c.noncommuting).2.2.2
  let : IsElementaryAbelian 2 U₁ := c.marked₁.elementary
  let : IsElementaryAbelian 2 U₂ := c.marked₂.elementary
  have hP : (U₁ ⊔ V₂) ⊔ C ≤ centralizer (U₁ : Set G) := sup_le
    (sup_le (le_centralizer U₁) ((le_sup_right.trans (le_centralizer_iff.mp hc)).trans
      (centralizer_le (show U₁ ≤ U₁ ⊔ V₁ from le_sup_left)))) hC₁
  have hP' : (V₁ ⊔ U₂) ⊔ C ≤ centralizer (U₂ : Set G) := sup_le
    (sup_le ((le_sup_right.trans hc).trans (centralizer_le (show U₂ ≤ U₂ ⊔ V₂ from le_sup_left))) (le_centralizer U₂)) hC₂
  have hUQ : U₁ ⊔ U₂ ≤ Q := by
    have hh := map_mono (f := d.H.subtype) d.U0_le_core
    rw [(d.two_block_closures c.second c.permutes c.exchange).2] at hh
    exact hh
  exact ⟨c.noncommuting,hnc₂,hQ₁,hQ₂,hP,hP',hV₁R,hV₂R,
    map_mono (le_sup_left.trans hUQ),map_mono (le_sup_right.trans hUQ)⟩

/-- Among the full maximum family, only the opposite core generates the
Thompson subgroup together with the original core. -/
theorem DoubleLinearSourceSetup.unique_generating_member
    (c : DoubleLinearSourceSetup d M₀ n)
    (hi : ((d.S : Subgroup d.H).map d.H.subtype).relIndex M₀ = 2)
    {A : Subgroup G}
    (hA : A ∈ elementaryAbelianMaxSubgroups
      (elementaryAbelianMaxJ ((d.S : Subgroup d.H).map d.H.subtype)))
    (hQA : twoCore d.H ⊔ A = elementaryAbelianMaxJ ((d.S : Subgroup d.H).map d.H.subtype)) :
    A = (twoCore d.H).map (MulAut.conj c.x⁻¹).toMonoidHom := by
  let S := (d.S : Subgroup d.H).map d.H.subtype
  let R := elementaryAbelianMaxJ S
  let Q := twoCore d.H
  let U₁ := sourceModule (d.block.map d.H.subtype)
  let U₂ := sourceModule c.second
  obtain ⟨hnc₁,hnc₂,hQ₁,hQ₂,hP,hP',hV₁R,hV₂R,_,_⟩ := c.separating_modules hi
  have hf := c.max_family hi
  change A ∈ elementaryAbelianMaxSubgroups R at hA
  rw [hf] at hA
  simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hA
  rcases hA with hA|hA|hA|hA
  · exfalso
    have hh : Q ⊔ A ≤ centralizer (U₁ : Set G) := sup_le hQ₁ (hA ▸ hQ₁)
    exact hnc₁ (hV₁R.trans (hQA ▸ hh))
  · exact hA
  · exfalso
    have hh : Q ⊔ A ≤ centralizer (U₁ : Set G) := sup_le hQ₁ (hA ▸ hP)
    exact hnc₁ (hV₁R.trans (hQA ▸ hh))
  · exfalso
    have hh : Q ⊔ A ≤ centralizer (U₂ : Set G) := sup_le hQ₂ (hA ▸ hP')
    exact hnc₂ (hV₂R.trans (hQA ▸ hh))

/-- All four listed members are distinct, with their source ordering retained. -/
theorem DoubleLinearSourceSetup.family_members_distinct
    (c : DoubleLinearSourceSetup d M₀ n)
    (hi : ((d.S : Subgroup d.H).map d.H.subtype).relIndex M₀ = 2) :
    let S := (d.S : Subgroup d.H).map d.H.subtype
    let Q := twoCore d.H
    let Qx := Q.map (MulAut.conj c.x⁻¹).toMonoidHom
    let C := S ⊓ centralizer ((d.block.map d.H.subtype ⊔ c.second : Subgroup G) : Set G)
    let U₁ := sourceModule (d.block.map d.H.subtype)
    let U₂ := sourceModule c.second
    let V₁ := U₁.map (MulAut.conj c.x⁻¹).toMonoidHom
    let V₂ := U₂.map (MulAut.conj c.x⁻¹).toMonoidHom
    let P := (U₁ ⊔ V₂) ⊔ C
    let P' := (V₁ ⊔ U₂) ⊔ C
    Q ≠ Qx ∧ Q ≠ P ∧ Q ≠ P' ∧ Qx ≠ P ∧ Qx ≠ P' ∧ P ≠ P' := by
  obtain ⟨hnc₁,hnc₂,hQ₁,hQ₂,hP,hP',_,_,hV₁Q,hV₂Q⟩ := c.separating_modules hi
  refine ⟨?_,?_,?_,?_,?_,?_⟩
  · intro he
    exact hnc₁ (hV₁Q.trans (he ▸ hQ₁))
  · intro he
    exact hnc₂ ((le_sup_right.trans le_sup_left).trans (he ▸ hQ₂))
  · intro he
    exact hnc₁ ((le_sup_left.trans le_sup_left).trans (he ▸ hQ₁))
  · intro he
    exact hnc₁ (hV₁Q.trans (he ▸ hP))
  · intro he
    exact hnc₂ (hV₂Q.trans (he ▸ hP'))
  · intro he
    exact hnc₁ ((le_sup_left.trans le_sup_left).trans (he ▸ hP))

/-- The source four-member family as four distinct, explicitly marked labels. -/
theorem DoubleLinearSourceSetup.labelled_max_family
    (c : DoubleLinearSourceSetup d M₀ n)
    (hi : ((d.S : Subgroup d.H).map d.H.subtype).relIndex M₀ = 2) :
    let S := (d.S : Subgroup d.H).map d.H.subtype
    let Q := twoCore d.H
    let Qx := Q.map (MulAut.conj c.x⁻¹).toMonoidHom
    let C := S ⊓ centralizer ((d.block.map d.H.subtype ⊔ c.second : Subgroup G) : Set G)
    let U₁ := sourceModule (d.block.map d.H.subtype)
    let U₂ := sourceModule c.second
    let V₁ := U₁.map (MulAut.conj c.x⁻¹).toMonoidHom
    let V₂ := U₂.map (MulAut.conj c.x⁻¹).toMonoidHom
    ∃ f : Fin 4 → Subgroup G, Function.Injective f ∧
      Set.range f = elementaryAbelianMaxSubgroups (elementaryAbelianMaxJ S) ∧
      f 0 = Q ∧ f 1 = Qx ∧ f 2 = (U₁ ⊔ V₂) ⊔ C ∧ f 3 = (V₁ ⊔ U₂) ⊔ C := by
  dsimp only
  let Q := twoCore d.H
  let Qx := Q.map (MulAut.conj c.x⁻¹).toMonoidHom
  let C := ((d.S : Subgroup d.H).map d.H.subtype) ⊓
    centralizer ((d.block.map d.H.subtype ⊔ c.second : Subgroup G) : Set G)
  let U₁ := sourceModule (d.block.map d.H.subtype)
  let U₂ := sourceModule c.second
  let V₁ := U₁.map (MulAut.conj c.x⁻¹).toMonoidHom
  let V₂ := U₂.map (MulAut.conj c.x⁻¹).toMonoidHom
  let P := (U₁ ⊔ V₂) ⊔ C
  let P' := (V₁ ⊔ U₂) ⊔ C
  obtain ⟨hQW,hQP,hQP',hWP,hWP',hPP⟩ := c.family_members_distinct hi
  let f : Fin 4 → Subgroup G := ![Q,Qx,P,P']
  refine ⟨f,?_,?_,rfl,rfl,rfl,rfl⟩
  · intro i j he
    fin_cases i <;> fin_cases j
    all_goals simp only [f,Matrix.cons_val,Fin.reduceFinMk] at he
    all_goals first
    | rfl
    | exact (hQW he).elim
    | exact (hQW he.symm).elim
    | exact (hQP he).elim
    | exact (hQP he.symm).elim
    | exact (hQP' he).elim
    | exact (hQP' he.symm).elim
    | exact (hWP he).elim
    | exact (hWP he.symm).elim
    | exact (hWP' he).elim
    | exact (hWP' he.symm).elim
    | exact (hPP he).elim
    | exact (hPP he.symm).elim
  · rw [c.max_family hi]
    simp only [f,Matrix.range_cons,Matrix.range_empty,Set.union_empty,Set.singleton_union]
    rfl

/-- The exact maximum family is unchanged on passage from S to J(S). -/
theorem DoubleLinearSourceSetup.max_family_eq_source
    (c : DoubleLinearSourceSetup d M₀ n)
    (hi : ((d.S : Subgroup d.H).map d.H.subtype).relIndex M₀ = 2) :
    elementaryAbelianMaxSubgroups
      (elementaryAbelianMaxJ ((d.S : Subgroup d.H).map d.H.subtype)) =
      elementaryAbelianMaxSubgroups ((d.S : Subgroup d.H).map d.H.subtype) := by
  rw [←(c.core_span hi).1,baumann_maxFamily]

/-- The two joins used by the alternate normalizer construction are
non-elementary: each contains one full noncommuting module pair. -/
theorem DoubleLinearSourceSetup.mixed_joins_not_elementary
    (c : DoubleLinearSourceSetup d M₀ n)
    (hi : ((d.S : Subgroup d.H).map d.H.subtype).relIndex M₀ = 2) :
    let S := (d.S : Subgroup d.H).map d.H.subtype
    let Q := twoCore d.H
    let C := S ⊓ centralizer ((d.block.map d.H.subtype ⊔ c.second : Subgroup G) : Set G)
    let U₁ := sourceModule (d.block.map d.H.subtype)
    let U₂ := sourceModule c.second
    let V₁ := U₁.map (MulAut.conj c.x⁻¹).toMonoidHom
    let V₂ := U₂.map (MulAut.conj c.x⁻¹).toMonoidHom
    ¬ IsElementaryAbelian 2 ↥(Q ⊔ ((U₁ ⊔ V₂) ⊔ C) : Subgroup G) ∧
      ¬ IsElementaryAbelian 2 ↥(Q ⊔ ((V₁ ⊔ U₂) ⊔ C) : Subgroup G) := by
  let S := (d.S : Subgroup d.H).map d.H.subtype
  let Q := twoCore d.H
  let C := S ⊓ centralizer ((d.block.map d.H.subtype ⊔ c.second : Subgroup G) : Set G)
  let U₁ := sourceModule (d.block.map d.H.subtype)
  let U₂ := sourceModule c.second
  let V₁ := U₁.map (MulAut.conj c.x⁻¹).toMonoidHom
  let V₂ := U₂.map (MulAut.conj c.x⁻¹).toMonoidHom
  let W := Q ⊔ ((U₁ ⊔ V₂) ⊔ C)
  let W' := Q ⊔ ((V₁ ⊔ U₂) ⊔ C)
  have hUQ : U₁ ⊔ U₂ ≤ Q := by
    have hh := map_mono (f := d.H.subtype) d.U0_le_core
    rw [(d.two_block_closures c.second c.permutes c.exchange).2] at hh
    exact hh
  obtain ⟨hnc₁,hnc₂,_⟩ := c.separating_modules hi
  change ¬ IsElementaryAbelian 2 W ∧ ¬ IsElementaryAbelian 2 W'
  constructor
  · intro he
    let := he
    have hU : U₂ ≤ W := (le_sup_right.trans hUQ).trans le_sup_left
    have hV : V₂ ≤ W := (le_sup_right.trans le_sup_left).trans le_sup_right
    exact hnc₂ (hV.trans ((le_centralizer W).trans (centralizer_le hU)))
  · intro he
    let := he
    have hU : U₁ ≤ W' := (le_sup_left.trans hUQ).trans le_sup_left
    have hV : V₁ ≤ W' := (le_sup_left.trans le_sup_left).trans le_sup_right
    exact hnc₁ (hV.trans ((le_centralizer W').trans (centralizer_le hU)))

/-- Any simultaneous normalizer of the Thompson subgroup and its original
core normalizes the opposite core. -/
theorem DoubleLinearSourceSetup.normalizes_opposite_core
    (c : DoubleLinearSourceSetup d M₀ n)
    (hi : ((d.S : Subgroup d.H).map d.H.subtype).relIndex M₀ = 2)
    {D : Subgroup G}
    (hDR : D ≤ normalizer
      (elementaryAbelianMaxJ ((d.S : Subgroup d.H).map d.H.subtype) : Set G))
    (hDQ : D ≤ normalizer (twoCore d.H : Set G)) :
    D ≤ normalizer ((twoCore d.H).map (MulAut.conj c.x⁻¹).toMonoidHom : Set G) := by
  let R := elementaryAbelianMaxJ ((d.S : Subgroup d.H).map d.H.subtype)
  let Q := twoCore d.H
  let Qx := Q.map (MulAut.conj c.x⁻¹).toMonoidHom
  have hQx : Qx ∈ elementaryAbelianMaxSubgroups R := by
    rw [c.max_family hi]
    exact Or.inr (Or.inl rfl)
  intro g hg
  apply mem_normalizer_iff_map_conj_eq.mpr
  have hR : R.map (MulAut.conj g).toMonoidHom = R := mem_normalizer_iff_map_conj_eq.mp (hDR hg)
  have hQ : Q.map (MulAut.conj g).toMonoidHom = Q := mem_normalizer_iff_map_conj_eq.mp (hDQ hg)
  have hmax := (maxFamily_map_injective_iff (MulAut.conj g).toMonoidHom
    (MulAut.conj g).injective R Qx).mpr hQx
  rw [hR] at hmax
  apply c.unique_generating_member hi hmax
  have he := congrArg (map (MulAut.conj g).toMonoidHom) (c.core_span hi).2
  rw [Subgroup.map_sup,hR,hQ] at he
  exact he.symm

/-- The literal torus conjugate lies in the original core normalizer.
The hypotheses assert normalization, and require no centralization of Q. -/
theorem DoubleLinearSourceSetup.conjugate_le_core_normalizer
    (c : DoubleLinearSourceSetup d M₀ n)
    (hi : ((d.S : Subgroup d.H).map d.H.subtype).relIndex M₀ = 2)
    {D : Subgroup G}
    (hDR : D ≤ normalizer
      (elementaryAbelianMaxJ ((d.S : Subgroup d.H).map d.H.subtype) : Set G))
    (hDQ : D ≤ normalizer (twoCore d.H : Set G)) :
    D.map (MulAut.conj c.x).toMonoidHom ≤ normalizer (twoCore d.H : Set G) := by
  have hh := (map_mono (f := (MulAut.conj c.x).toMonoidHom)
    (c.normalizes_opposite_core hi hDR hDQ)).trans
      (le_normalizer_map (MulAut.conj c.x).toMonoidHom)
  have he : ((twoCore d.H).map (MulAut.conj c.x⁻¹).toMonoidHom).map
      (MulAut.conj c.x).toMonoidHom = twoCore d.H := by
    rw [map_map]
    have hec : (MulAut.conj c.x).toMonoidHom.comp (MulAut.conj c.x⁻¹).toMonoidHom = MonoidHom.id G := by
      ext z
      simp [MulAut.conj_apply,mul_assoc]
    rw [hec,map_id]
  rwa [he] at hh

/-- The source right-conjugate Dˣ also normalizes Q. The index-two
hypothesis puts x² in S, so both conjugation conventions give the same bound. -/
theorem DoubleLinearSourceSetup.right_conjugate_le_core_normalizer
    (c : DoubleLinearSourceSetup d M₀ n)
    (hi : ((d.S : Subgroup d.H).map d.H.subtype).relIndex M₀ = 2)
    {D : Subgroup G}
    (hDR : D ≤ normalizer
      (elementaryAbelianMaxJ ((d.S : Subgroup d.H).map d.H.subtype) : Set G))
    (hDQ : D ≤ normalizer (twoCore d.H : Set G)) :
    D.map (MulAut.conj c.x⁻¹).toMonoidHom ≤ normalizer (twoCore d.H : Set G) := by
  let S := (d.S : Subgroup d.H).map d.H.subtype
  let N := normalizer (twoCore d.H : Set G)
  have hSN : S ≤ N := (map_subtype_le _).trans (d.H.le_normalizer.trans
    (normalizer_le_normalizer_characteristic_image d.H (pCore 2 d.H)))
  have hxS : c.x ^ 2 ∈ S := sq_mem_of_index_two (H := S.subgroupOf M₀) hi ⟨c.x,c.x_mem⟩
  have hxN : c.x ^ 2 ∈ N := hSN hxS
  have hconj := c.conjugate_le_core_normalizer hi hDR hDQ
  rintro z ⟨a,ha,rfl⟩
  have haN : c.x * a * c.x⁻¹ ∈ N := hconj ⟨a,ha,rfl⟩
  have hh := N.mul_mem (N.mul_mem (N.inv_mem hxN) haN) hxN
  change c.x⁻¹ * a * (c.x⁻¹)⁻¹ ∈ N
  simpa only [pow_two,mul_inv_rev,inv_inv,mul_assoc,inv_mul_cancel_left,mul_inv_cancel_left] using hh

/-- Every element in the outside coset of M₀ sends a simultaneous normalizer
of J(S) and Q into the core normalizer. Thus the torus argument is independent
of the initially selected noncommuting conjugator. -/
theorem DoubleLinearSourceSetup.outside_conjugate_le_core_normalizer
    (c : DoubleLinearSourceSetup d M₀ n)
    (hi : ((d.S : Subgroup d.H).map d.H.subtype).relIndex M₀ = 2)
    {D : Subgroup G}
    (hDR : D ≤ normalizer
      (elementaryAbelianMaxJ ((d.S : Subgroup d.H).map d.H.subtype) : Set G))
    (hDQ : D ≤ normalizer (twoCore d.H : Set G))
    (y : G) (hy : y ∈ M₀) (hyS : y ∉ (d.S : Subgroup d.H).map d.H.subtype) :
    D.map (MulAut.conj y).toMonoidHom ≤ normalizer (twoCore d.H : Set G) := by
  let S := (d.S : Subgroup d.H).map d.H.subtype
  let Q := twoCore d.H
  have hSN : S ≤ normalizer (Q : Set G) := (map_subtype_le _).trans
    (d.H.le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image d.H (pCore 2 d.H)))
  have hxS : c.x ∉ S := by
    intro hx
    exact (c.family_members_distinct hi).1
      (mem_normalizer_iff_map_conj_eq.mp (hSN (S.inv_mem hx))).symm
  have hxiS : c.x⁻¹ ∉ S := by
    intro hx
    exact hxS (by simpa only [inv_inv] using S.inv_mem hx)
  have hyx : y * c.x⁻¹ ∈ S :=
    (mul_mem_iff_of_index_two (H := S.subgroupOf M₀) hi
      (a := (⟨y,hy⟩ : M₀)) (b := (⟨c.x⁻¹,M₀.inv_mem c.x_mem⟩ : M₀))).mpr
      (iff_of_false hyS hxiS)
  have hh := (map_mono (f := (MulAut.conj y).toMonoidHom)
    (c.normalizes_opposite_core hi hDR hDQ)).trans
      (le_normalizer_map (MulAut.conj y).toMonoidHom)
  have he : (Q.map (MulAut.conj c.x⁻¹).toMonoidHom).map
      (MulAut.conj y).toMonoidHom = Q := by
    rw [map_map]
    have hec : (MulAut.conj y).toMonoidHom.comp (MulAut.conj c.x⁻¹).toMonoidHom =
        (MulAut.conj (y * c.x⁻¹)).toMonoidHom := by
      ext z
      simp [MulAut.conj_apply,mul_assoc]
    rw [hec]
    exact mem_normalizer_iff_map_conj_eq.mp (hSN hyx)
  change D.map (MulAut.conj y).toMonoidHom ≤
    normalizer ((Q.map (MulAut.conj c.x⁻¹).toMonoidHom).map
      (MulAut.conj y).toMonoidHom : Set G) at hh
  rwa [he] at hh

/-- The same outside-coset normalizer bound in the source right-conjugation
convention. -/
theorem DoubleLinearSourceSetup.outside_right_conjugate_le_core_normalizer
    (c : DoubleLinearSourceSetup d M₀ n)
    (hi : ((d.S : Subgroup d.H).map d.H.subtype).relIndex M₀ = 2)
    {D : Subgroup G}
    (hDR : D ≤ normalizer
      (elementaryAbelianMaxJ ((d.S : Subgroup d.H).map d.H.subtype) : Set G))
    (hDQ : D ≤ normalizer (twoCore d.H : Set G))
    (y : G) (hy : y ∈ M₀) (hyS : y ∉ (d.S : Subgroup d.H).map d.H.subtype) :
    D.map (MulAut.conj y⁻¹).toMonoidHom ≤ normalizer (twoCore d.H : Set G) := by
  apply c.outside_conjugate_le_core_normalizer hi hDR hDQ y⁻¹ (M₀.inv_mem hy)
  intro hyi
  exact hyS (by simpa only [inv_inv] using ((d.S : Subgroup d.H).map d.H.subtype).inv_mem hyi)

end CFSG.Quasithin.Chapter2
