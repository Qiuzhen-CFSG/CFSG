module
public import CFSG.Quasithin.Chapter15.Section02.SourcePlaneUniqueness.CharacteristicTwo.SmallActionsSource.ChiefCoordinates
public import CFSG.Quasithin.Chapter15.Section02.SourcePlaneUniqueness.CharacteristicTwo.SmallActionsSource.PairedQuotient

/-!
# The distinguished factors in the reducible small action

The image of J(H) contains the two coordinate factors because their
transvections are best offenders on the original noncentral chief module.
The source Thompson-image order then identifies this image with the paired
base. The original KS has the same quotient image and contains the action
kernel, so it is the join of the two plane centralizers from Notation15.2.9.
Every element of T outside S exchanges these factors: otherwise it lies
in KS and forces T into the escaping maximal subgroup. Taking O² retains
the original embeddings and conjugation. Together with the orbit results,
this proves all clauses of15.2.21(1) for the actual marked factors.

Source: Aschbacher--Smith, Notation15.2.9 and15.2.21(1), printed pp.1110,1114;
refs/quasithin.pdf. The genuine preceding source inputs remain in d.
-/

@[expose] public section
open Subgroup Representation Representation.BinaryOffender NoncentralChiefRefinement Stellmacher Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section02.SmallActionsSource
open Section01 Section03 Section03.InitialSource ChapterA.Section05To06 ChapterD ChapterD.UniqueFactor

variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc V H ZS I : Subgroup G}
variable {hsource : ChosenSmallSource T M Mc V}
variable (d : PlaneUniquenessPreceding hsource H ZS)
include d

/-- The original KS is the product of the two marked chief-plane centralizers. -/
theorem chief_marked_join (hI : PlaneEscapes Mc ZS I)
    (hnot : ¬ IsSmallActionIrreducible (smallActionS T ZS) (smallActionK H)) :
    let h := hsource.prepared
    let := h.elementary
    let U := (conjugateSpan H V).subgroupOf H
    let := (h.chief_data hsource.ambient T hsource.empty hsource.maximal hsource.centralizing H d.geometry.outside).1
    let : IsElementaryAbelian 2 U := IsElementaryAbelian.subgroupOf
      (show conjugateSpan H V ≤ H by
        rw [UniqueFactor.conjugateSpan_eq]
        exact conjugateSpanBy_le_self ((h.inside_core H d.geometry.outside).trans (twoCore_le H)))
    ∀ (s : SeriesOn U) (i : Fin s.series.length), ¬ s.Central i →
      ∀ c : ChiefWreathCoordinates (s.factorRepresentation i),
        (TerminalLinear.KS H T ZS).subgroupOf H = c.factor 1 ⊔ c.factor ChiefWreath.flip := by
  let h := hsource.prepared
  let := h.elementary
  let U := (conjugateSpan H V).subgroupOf H
  let := (h.chief_data hsource.ambient T hsource.empty hsource.maximal hsource.centralizing H d.geometry.outside).1
  let : IsElementaryAbelian 2 U := IsElementaryAbelian.subgroupOf
    (show conjugateSpan H V ≤ H by
      rw [UniqueFactor.conjugateSpan_eq]
      exact conjugateSpanBy_le_self ((h.inside_core H d.geometry.outside).trans (twoCore_le H)))
  dsimp only
  intro s i hi c
  let ρ := s.factorRepresentation i
  let J := elementaryAbelianMaxJ (⊤ : Subgroup H)
  let q := QuotientGroup.mk' (pCore 2 H)
  have hk : c.actor.ker = pCore 2 H := c.kernel.trans (chief_action_kernel_eq_core d s i hi)
  let e := QuotientGroup.liftEquiv (pCore 2 H) c.surjective hk.symm
  have he : e.toMonoidHom.comp q = c.actor := by apply MonoidHom.ext; intro g; rfl
  have hm : (J.map q).map e.toMonoidHom = J.map c.actor := by rw [map_map,he]
  have hc : Nat.card (J.map c.actor) = 36 := by
    rw [←hm,card_map_of_injective (f := e.toMonoidHom) e.injective]
    obtain ⟨a⟩ := thompson_core_image_pair d
    rw [Nat.card_congr a.toEquiv]
    norm_num [Nat.card_prod,Nat.card_perm,Nat.card_fin,Nat.card_eq_fintype_card,Fintype.card_perm,Nat.factorial]
  have ht := h.chief_thompson_image_eq hsource.ambient T hsource.empty hsource.maximal
    hsource.centralizing d.geometry.outside s i hi
  have hb : ChiefWreath.base ≤ J.map c.actor := by
    have hh := c.base_le_image_offenders
    rw [←ht,map_map] at hh
    have hh' : c.imageEquiv.toMonoidHom.comp (actionHom ρ) = c.actor := by
      apply MonoidHom.ext
      intro g
      exact c.imageEquiv_actionHom g
    rw [hh'] at hh
    exact hh
  have hJ : J.map c.actor = ChiefWreath.base :=
    (eq_of_le_of_card_ge hb (by rw [hc,ChiefWreath.base_card])).symm
  have hQ := core_le_planeSylow_of_reducible d hI hnot
  have hB := congrArg (Subgroup.map e.toMonoidHom) (residual_plane_image_eq_thompson d hI hQ)
  rw [map_map,map_map,he] at hB
  rw [c.factor_sup_eq_base,←hJ,←hB]
  symm
  apply comap_map_eq_self
  rw [hk]
  intro g hg
  exact (show smallActionS T ZS ≤ TerminalLinear.KS H T ZS from le_sup_right)
    (hQ (mem_map_of_mem H.subtype hg))


/-- An outside Sylow element must exchange the two actual chief planes. -/
theorem outside_chief_permutation {W : Type*} [AddCommGroup W]
    [Module (ZMod 2) W] {ρ : Representation (ZMod 2) H W}
    (c : ChiefWreathCoordinates ρ) (hI : PlaneEscapes Mc ZS I)
    (hjoin : (TerminalLinear.KS H T ZS).subgroupOf H = c.factor 1 ⊔ c.factor ChiefWreath.flip)
    (t : G) (ht : t ∈ (T : Subgroup G)) (htS : t ∉ smallActionS T ZS) :
    (c.actor ⟨t,d.geometry.outside.1.1.2 ht⟩).right = ChiefWreath.flip := by
  rcases ChiefWreath.index_cases (c.actor ⟨t,d.geometry.outside.1.1.2 ht⟩).right with he | he
  · exfalso
    have htI : t ∈ I := by
      have hh : (⟨t,d.geometry.outside.1.1.2 ht⟩ : H) ∈
          (TerminalLinear.KS H T ZS).subgroupOf H := by
        rw [hjoin,c.factor_sup_eq_base]
        exact he
      exact ((d.residual_sup_planeSylow_le hI).trans inf_le_right) hh
    apply d.sylow_not_le_escape hI
    intro x hx
    by_cases hxS : x ∈ smallActionS T ZS
    · exact ((d.residual_sup_planeSylow_le hI).trans inf_le_right) ((show smallActionS T ZS ≤ TerminalLinear.KS H T ZS from le_sup_right) hxS)
    · have hxt : x*t⁻¹ ∈ smallActionS T ZS := by
        apply (((smallActionS T ZS).subgroupOf (T : Subgroup G)).mul_mem_iff_of_index_two
          (d.escape_index hI).2 (a := ⟨x,hx⟩)
          (b := ⟨t⁻¹,(T : Subgroup G).inv_mem ht⟩)).mpr
        change x ∈ smallActionS T ZS ↔ t⁻¹ ∈ smallActionS T ZS
        simp only [hxS,inv_mem_iff,htS]
      have hxI := ((d.residual_sup_planeSylow_le hI).trans inf_le_right) ((show smallActionS T ZS ≤ TerminalLinear.KS H T ZS from le_sup_right) hxt)
      simpa only [inv_mul_cancel_right] using I.mul_mem hxI htI
  · exact he


omit d [Finite G] in
/-- The conjugacy calculation retains the original embedding of H in G. -/
theorem chief_factor_map_conj {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    {ρ : Representation (ZMod 2) H W} (c : ChiefWreathCoordinates ρ)
    (t : H) (i : ChiefWreath.C2) :
    ((c.factor i).map H.subtype).map (MulAut.conj (t : G)).toMonoidHom =
      (c.factor ((c.actor t).right*i)).map H.subtype := by
  calc
    _ = ((c.factor i).map (MulAut.conj t).toMonoidHom).map H.subtype := by
      rw [map_map,map_map]
      congr 1
    _ = _ := by rw [c.factor_conj]

omit d in
/-- Taking O² commutes with the literal conjugation and subgroup embeddings. -/
theorem chief_residual_map_conj {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    {ρ : Representation (ZMod 2) H W} (c : ChiefWreathCoordinates ρ)
    (t : H) (i : ChiefWreath.C2) :
    (smallActionK ((c.factor i).map H.subtype)).map (MulAut.conj (t : G)).toMonoidHom =
      smallActionK ((c.factor ((c.actor t).right*i)).map H.subtype) := by
  unfold smallActionK
  rw [map_embedded_pResidual,chief_factor_map_conj]

/-- Corrected15.2.21(1), with the factors marked by their actual chief planes. -/
theorem source_15_2_21_1_from_preceding
    (horbit : smallActionKc H Mc = smallActionK H ∨
      ∃ L : Subgroup G, L ∈ Chapter1.L G T ∧
        smallActionKc H Mc = componentOrbit L (T : Subgroup G))
    (hI : PlaneEscapes Mc ZS I)
    (hnot : ¬ IsSmallActionIrreducible (smallActionS T ZS) (smallActionK H)) :
    let h := hsource.prepared
    let := h.elementary
    let U := (conjugateSpan H V).subgroupOf H
    let := (h.chief_data hsource.ambient T hsource.empty hsource.maximal hsource.centralizing H d.geometry.outside).1
    let : IsElementaryAbelian 2 U := IsElementaryAbelian.subgroupOf
      (show conjugateSpan H V ≤ H by
        rw [UniqueFactor.conjugateSpan_eq]
        exact conjugateSpanBy_le_self ((h.inside_core H d.geometry.outside).trans (twoCore_le H)))
    ∀ (s : SeriesOn U) (i : Fin s.series.length), ¬ s.Central i →
      ∃ c : ChiefWreathCoordinates (s.factorRepresentation i),
        TerminalLinear.KS H T ZS = (c.factor 1).map H.subtype ⊔
          (c.factor ChiefWreath.flip).map H.subtype ∧
        (∀ (t : G), t ∈ (T : Subgroup G) → t ∉ smallActionS T ZS →
          (smallActionK ((c.factor 1).map H.subtype)).map (MulAut.conj t).toMonoidHom =
            smallActionK ((c.factor ChiefWreath.flip).map H.subtype)) ∧
        smallActionKc H Mc ≤ centralizer (ZS : Set G) ∧
        smallActionKc H Mc = (primeToResidual 3 (Mc ⊓ I : Subgroup G)).map (Mc ⊓ I).subtype := by
  let h := hsource.prepared
  let := h.elementary
  let U := (conjugateSpan H V).subgroupOf H
  let := (h.chief_data hsource.ambient T hsource.empty hsource.maximal hsource.centralizing H d.geometry.outside).1
  let : IsElementaryAbelian 2 U := IsElementaryAbelian.subgroupOf
    (show conjugateSpan H V ≤ H by
      rw [UniqueFactor.conjugateSpan_eq]
      exact conjugateSpanBy_le_self ((h.inside_core H d.geometry.outside).trans (twoCore_le H)))
  dsimp only
  intro s i hi
  obtain ⟨c⟩ := chief_wreath_coordinates d s i hi
  have hjoin := chief_marked_join d hI hnot s i hi c
  refine ⟨c,?_,?_,orbit_centralizes_of_reducible d horbit hI hnot,
    orbit_residual_MI_of_reducible d horbit hI hnot⟩
  · have hh := congrArg (Subgroup.map H.subtype) hjoin
    rw [map_subgroupOf_eq_of_le (show TerminalLinear.KS H T ZS ≤ H from
      sup_le (map_subtype_le _) (inf_le_left.trans d.geometry.outside.1.1.2)),Subgroup.map_sup] at hh
    exact hh
  · intro t ht htS
    have hh := chief_residual_map_conj c (⟨t,d.geometry.outside.1.1.2 ht⟩ : H) 1
    rw [outside_chief_permutation d c hI hjoin t ht htS,mul_one] at hh
    exact hh

end CFSG.Quasithin.Chapter15.Section02.SmallActionsSource
