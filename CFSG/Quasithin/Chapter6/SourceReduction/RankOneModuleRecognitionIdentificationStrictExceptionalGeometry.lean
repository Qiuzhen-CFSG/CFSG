module
public import CFSG.Quasithin.ChapterG.Section11.FullLinearFourModelForm
public import Theory.Representation.BinaryNaturalDual.ModelOrbits.StandardSylow
public import CFSG.Quasithin.ChapterG.Section10.Components.Exchanged
public import Theory.SpecificGroups.SymmetricEight.NormalElementaryOdd

/-!
# Nontriviality of the smaller actor in the exceptional whole action

A point fixed by a Sylow subgroup has nonzero coordinates in both four-space
summands. The full centered transvection condition forces X to exchange those
summands. The half-point and exchanged-axis displacements put a four-space
inside W; isotropy forces equality. The literal quotient X/X₀ therefore has
rank three. An elementary subgroup normal in a Sylow subgroup and containing an odd
permutation of eight points has order at least sixteen, so X₀ is nontrivial.

This uses the original relative Sylow normality and no small-actor bound.
Source: Aschbacher--Smith G.10.10, G.10.15(1), G.11.1, with the exceptional
G.10.15 correction. StrictExceptionalExclusion applies it to the actual
crossed-center image after the ambient central-cover calculation.
-/

public noncomputable section
open Subgroup Module Representation Representation.BinaryOffender Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter6.Source.RankOneRecognition
open ChapterG.Section11.FullLinearFour
open BinaryLinear.OuterCyclic BinaryNaturalDual.ModelOrbits
variable {G V : Type*} [Group G] [Finite G] [AddCommGroup V]
 [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
 {ρ : Representation (ZMod 2) G V} {B : LinearMap.BilinForm (ZMod 2) V}
 {v : V} {W : Submodule (ZMod 2) V} {X : Subgroup G}
 [IsElementaryAbelian 2 X] {X₀ : Subgroup X}
 {H : Subgroup G} {I J : Submodule (ZMod 2) V}

omit [Finite G] [FiniteDimensional (ZMod 2) V] in
private theorem mem_natural_iff (m : WholeActionModel ρ H I J) (u : V) :
    u ∈ I ↔ (m.spaceEquiv u).2 = 0 := by
  constructor
  · intro hu
    exact congrArg Prod.snd (m.natural_coordinates ⟨u,hu⟩)
  · intro hu
    have he : (m.naturalEquiv.symm (m.spaceEquiv u).1 : V) = u := by
      apply m.spaceEquiv.injective
      rw [m.natural_coordinates, m.naturalEquiv.apply_symm_apply]
      exact Prod.ext rfl hu.symm
    exact he ▸ (m.naturalEquiv.symm (m.spaceEquiv u).1).property

omit [Finite G] [FiniteDimensional (ZMod 2) V] in
private theorem mem_dual_iff (m : WholeActionModel ρ H I J) (u : V) :
    u ∈ J ↔ (m.spaceEquiv u).1 = 0 := by
  constructor
  · intro hu
    exact congrArg Prod.fst (m.dual_coordinates ⟨u,hu⟩)
  · intro hu
    have he : (m.dualEquiv.symm (m.spaceEquiv u).2 : V) = u := by
      apply m.spaceEquiv.injective
      rw [m.dual_coordinates, m.dualEquiv.apply_symm_apply]
      exact Prod.ext hu.symm rfl
    exact he ▸ (m.dualEquiv.symm (m.spaceEquiv u).2).property

omit [Finite G] [FiniteDimensional (ZMod 2) V] in
private theorem full_four_pair_complement (m : WholeActionModel ρ H I J) : IsCompl I J := by
  constructor
  · apply Submodule.disjoint_def.mpr
    intro u huI huJ
    apply m.spaceEquiv.injective
    rw [map_zero]
    exact Prod.ext ((mem_dual_iff m u).mp huJ) ((mem_natural_iff m u).mp huI)
  · apply codisjoint_iff.mpr
    apply top_unique
    intro u _
    let a := m.naturalEquiv.symm (m.spaceEquiv u).1
    let b := m.dualEquiv.symm (m.spaceEquiv u).2
    have he : u = (a : V) + (b : V) := by
      apply m.spaceEquiv.injective
      rw [map_add,m.natural_coordinates,m.dual_coordinates]
      simp only [a,b,LinearEquiv.apply_symm_apply,Prod.mk_add_mk,add_zero,zero_add]
    rw [he]
    exact Submodule.add_mem_sup a.property b.property

omit [Finite G] [FiniteDimensional (ZMod 2) V] in
private theorem full_four_dimensions (m : WholeActionModel ρ H I J) :
    finrank (ZMod 2) I = 4 ∧ finrank (ZMod 2) J = 4 ∧ finrank (ZMod 2) V = 8 := by
  refine ⟨?_,?_,?_⟩
  · simpa only [Space,Module.finrank_pi,Fintype.card_fin] using m.naturalEquiv.finrank_eq
  · simpa only [Subspace.dual_finrank_eq,Space,Module.finrank_pi,Fintype.card_fin] using m.dualEquiv.finrank_eq
  · simpa only [BinaryNaturalDual.CoordinateSpace,BinaryNaturalDual.Space,Module.finrank_prod,
      Subspace.dual_finrank_eq,Space,Module.finrank_pi,Fintype.card_fin,Nat.reduceAdd] using m.spaceEquiv.finrank_eq

omit [Finite G] in
private theorem full_four_pair_action (m : WholeActionModel ρ H I J) (a : G) :
    (I.map (ρ a) = I ∧ J.map (ρ a) = J) ∨
      (I.map (ρ a) = J ∧ J.map (ρ a) = I) := by
  let A := AutomorphismModel.coordinateAction (Or.inl (rfl : 4 = 4))
  have hmI : finrank (ZMod 2) (I.map (ρ a)) = 4 :=
    (finrank_map_action ρ I a).trans (full_four_dimensions m).1
  have hmJ : finrank (ZMod 2) (J.map (ρ a)) = 4 :=
    (finrank_map_action ρ J a).trans (full_four_dimensions m).2.1
  obtain ⟨g,hg | hg⟩ := inner_graph (Or.inl (rfl : 4 = 4)) (m.groupEquiv a)
  · left
    constructor
    · apply Submodule.eq_of_le_of_finrank_eq ?_ (hmI.trans (full_four_dimensions m).1.symm)
      rintro _ ⟨u,hu,rfl⟩
      rw [mem_natural_iff m, m.equivariant,hg,A.on_inner,
        BinaryNaturalDual.naturalDualRepresentation_apply,(mem_natural_iff m u).mp hu,map_zero]
    · apply Submodule.eq_of_le_of_finrank_eq ?_ (hmJ.trans (full_four_dimensions m).2.1.symm)
      rintro _ ⟨u,hu,rfl⟩
      rw [mem_dual_iff m, m.equivariant,hg,A.on_inner,
        BinaryNaturalDual.naturalDualRepresentation_apply,(mem_dual_iff m u).mp hu,map_zero]
  · right
    constructor
    · apply Submodule.eq_of_le_of_finrank_eq ?_ (hmI.trans (full_four_dimensions m).2.1.symm)
      rintro _ ⟨u,hu,rfl⟩
      rw [mem_dual_iff m,m.equivariant,hg,map_mul,Module.End.mul_apply,A.on_graph,A.on_inner,
        BinaryNaturalDual.naturalDualRepresentation_apply,BinaryNaturalDual.coordinateSwap_apply,
        (mem_natural_iff m u).mp hu,map_zero,map_zero]
    · apply Submodule.eq_of_le_of_finrank_eq ?_ (hmJ.trans (full_four_dimensions m).1.symm)
      rintro _ ⟨u,hu,rfl⟩
      rw [mem_natural_iff m,m.equivariant,hg,map_mul,Module.End.mul_apply,A.on_graph,A.on_inner,
        BinaryNaturalDual.naturalDualRepresentation_apply,BinaryNaturalDual.coordinateSwap_apply,
        (mem_dual_iff m u).mp hu,map_zero,map_zero]

omit [FiniteDimensional (ZMod 2) V] [IsElementaryAbelian 2 X] in
private theorem full_four_point_avoids_summands (m : WholeActionModel ρ H I J)
    (hv : v ≠ 0) (hS : ChapterG.Section11.NormalSylow ρ v X) : v ∉ I ∧ v ∉ J := by
  obtain ⟨S,hSv,_,_⟩ := hS
  have hd := (BinaryNaturalDual.ModelOrbits.singularDiagonal_iff_exists_sylow_fixed
    (Or.inl (rfl : 4 = 4)) (AutomorphismModel.coordinateAction (Or.inl rfl))
    (fun hh => hv (m.spaceEquiv.map_eq_zero_iff.mp hh))).mpr
    (show ∃ P : Sylow 2 (MulAut (LinearGroup 4)), ∀ a ∈ P,
      (AutomorphismModel.coordinateAction (Or.inl rfl)).representation a (m.spaceEquiv v) = m.spaceEquiv v from
      ⟨S.mapSurjective (f := m.groupEquiv.toMonoidHom) m.groupEquiv.surjective, by
        rintro a ⟨s,hs,rfl⟩
        exact (m.equivariant s v).symm.trans (congrArg m.spaceEquiv (hSv hs))⟩)
  exact ⟨fun hi => hd.2.1 ((mem_natural_iff m v).mp hi),
    fun hj => hd.1 ((mem_dual_iff m v).mp hj)⟩

private theorem full_four_summand_moved (m : WholeActionModel ρ H I J)
    (h : ChapterG.Section10.Hypothesis ρ B v W X X₀)
    (hS : ChapterG.Section11.NormalSylow ρ v X) :
    ∃ x : X, I.map (ρ x) ≠ I := by
  have hd := full_four_dimensions m
  have hcomp := full_four_pair_complement m
  have hne : I ≠ J := by
    intro he
    have hi : I = ⊥ := disjoint_self.mp (by simpa only [← he] using hcomp.disjoint)
    rw [hi,finrank_bot] at hd
    omega
  obtain ⟨hvI,hvJ⟩ := full_four_point_avoids_summands m h.point_ne_zero hS
  by_contra! hstable
  have hs : X ≤ subspaceStabilizer ρ I := fun a ha =>
    (subspace_map_eq_iff ρ I a).mp (hstable ⟨a,ha⟩)
  have hJ : X ≤ subspaceStabilizer ρ J := by
    intro a ha
    apply (subspace_map_eq_iff ρ J a).mp
    rcases full_four_pair_action m a with hh | hh
    · exact hh.2
    · exact (hne ((hstable ⟨a,ha⟩).symm.trans hh.1)).elim
  have hm : ¬ I ≤ fixedSpace ρ X := by
    intro hfix
    have hbot : X = ⊥ := by
      apply le_bot_iff.mp
      intro a ha
      let A := AutomorphismModel.coordinateAction (Or.inl (rfl : 4 = 4))
      obtain ⟨g,hg | hg⟩ := inner_graph (Or.inl (rfl : 4 = 4)) (m.groupEquiv a)
      · have hg1 : g = 1 := by
          apply LinearEquiv.ext
          intro u
          have he := congrArg m.spaceEquiv (hfix (m.naturalEquiv.symm u).property ⟨a,ha⟩)
          change m.spaceEquiv (ρ a (m.naturalEquiv.symm u : V)) = m.spaceEquiv (m.naturalEquiv.symm u : V) at he
          rw [m.equivariant,hg,A.on_inner,m.natural_coordinates,
            BinaryNaturalDual.naturalDualRepresentation_apply,m.naturalEquiv.apply_symm_apply] at he
          exact congrArg Prod.fst he
        exact mem_bot.mpr (m.groupEquiv.map_eq_one_iff.mp (by rw [hg,hg1,map_one]))
      · have he : I.map (ρ a) = J := by
          apply Submodule.eq_of_le_of_finrank_eq ?_
            ((finrank_map_action ρ I a).trans (hd.1.trans hd.2.1.symm))
          rintro _ ⟨u,hu,rfl⟩
          rw [mem_dual_iff m,m.equivariant,hg,map_mul,Module.End.mul_apply,A.on_graph,A.on_inner,
            BinaryNaturalDual.naturalDualRepresentation_apply,BinaryNaturalDual.coordinateSwap_apply,
            (mem_natural_iff m u).mp hu,map_zero,map_zero]
        exact (hne ((hstable ⟨a,ha⟩).symm.trans he)).elim
    have hsmall : Subsingleton X := by rw [hbot]; infer_instance
    let := hsmall
    have hr : Group.rank (X ⧸ X₀) = 0 := Group.rank_eq_zero _
    have hb := h.dimension_bound.1
    omega
  have hiso : ∀ u ∈ I, ∀ w ∈ I, B u w = 0 := by
    intro u hu w hw
    rw [m.form_coordinates B h.alternating h.nondegenerate h.preserves,
      (mem_natural_iff m u).mp hu,(mem_natural_iff m w).mp hw]
    simp
  have horth : B.orthogonal I = I := by
    symm
    have hle : I ≤ B.orthogonal I := fun u hu w hw => hiso w hw u hu
    apply Submodule.eq_of_le_of_finrank_eq hle
    rw [B.finrank_orthogonal h.nondegenerate,hd.1,hd.2.2]
  exact hvJ (h.point_mem_complement_of_large_moved_lagrangian I J hs hvI hm
    (by omega) horth hcomp hJ)

/-- The literal marked actor of an exceptional whole action has nontrivial
smaller actor. This uses the original relative Sylow normality. -/
theorem full_four_smaller_actor_ne_bot
    (m : WholeActionModel ρ H I J)
    (h : ChapterG.Section10.Hypothesis ρ B v W X X₀)
    (hS : ChapterG.Section11.NormalSylow ρ v X) : X₀ ≠ ⊥ := by
  have hd := full_four_dimensions m
  have hcomp := full_four_pair_complement m
  obtain ⟨x,hx⟩ := full_four_summand_moved m h hS
  have hxJ : I.map (ρ x) = J := by
    rcases full_four_pair_action m x with hh | hh
    · exact (hx hh.1).elim
    · exact hh.1
  have hne : I ≠ J := by
    intro he
    have hz : I = ⊥ := disjoint_self.mp (by simpa only [← he] using hcomp.disjoint)
    rw [hz,finrank_bot] at hd
    omega
  have hind : sSupIndep (subspaceOrbit ρ X I) := by
    apply ((sSupIndep_pair hne).mpr hcomp.disjoint).mono
    rintro _ ⟨a,rfl⟩
    rcases full_four_pair_action m a with hh | hh
    · exact Set.mem_insert_iff.mpr (Or.inl hh.1)
    · exact Set.mem_insert_iff.mpr (Or.inr (Set.mem_singleton_iff.mpr hh.1))
  have hspan : Homogeneous.orbitSpan ρ X I = ⊤ := by
    rw [(h.independent_orbit_pair I (by omega) hind x hx).1,hxJ,hcomp.sup_eq_top]
  obtain ⟨i,hiW,hi0,_,_⟩ := h.exchanged_center_geometry I (by omega) hind x hx
    (hspan ▸ Submodule.mem_top)
  have hdis : Disjoint I (I.map (ρ x)) := hxJ.symm ▸ hcomp.disjoint
  let U := I ⊓ (B v).ker
  let F : (ZMod 2 × U) →ₗ[ZMod 2] V :=
    (LinearMap.toSpanSingleton (ZMod 2) V (i : V)).comp (LinearMap.fst _ _ _) +
      ((ρ x - LinearMap.id).comp U.subtype).comp (LinearMap.snd _ _ _)
  have hFW (p : ZMod 2 × U) : F p ∈ W :=
    W.add_mem (W.smul_mem _ hiW) (h.displacement x p.2 p.2.property.2)
  have hFi : Function.Injective F := by
    apply LinearMap.ker_eq_bot.mp
    apply bot_unique
    rintro ⟨a,u⟩ hu
    have he : a • (i : V) + (ρ x u - u) = 0 := hu
    have hxuI : ρ x u ∈ I := by
      have hh : ρ x u = (u : V) - a • (i : V) := by
        have hh := eq_neg_of_add_eq_zero_right he
        exact (sub_eq_iff_eq_add.mp hh).trans (by abel)
      rw [hh]
      exact I.sub_mem u.property.1 (I.smul_mem _ i.property.1)
    have hx0 : ρ x u = 0 := Submodule.disjoint_def.mp hdis _ hxuI ⟨u,u.property.1,rfl⟩
    have hu0 : u = 0 := by
      apply Subtype.ext
      change (u : V) = 0
      have hh := congrArg (ρ (x : G)⁻¹) hx0
      simpa only [map_zero,← Module.End.mul_apply,← map_mul,inv_mul_cancel,
        map_one,Module.End.one_apply] using hh
    have ha0 : a = 0 := by
      subst u
      simp only [Submodule.coe_zero,map_zero,sub_self,add_zero] at he
      exact (smul_eq_zero.mp he).resolve_right hi0
    exact Prod.ext ha0 hu0
  let f := (B v).comp I.subtype
  have hk : f.ker.map I.subtype = U := by
    rw [LinearMap.ker_comp,Submodule.map_comap_subtype]
  have hker : finrank (ZMod 2) f.ker = finrank (ZMod 2) U := by
    rw [← hk]
    exact (Submodule.equivMapOfInjective I.subtype I.subtype_injective f.ker).finrank_eq
  have hrange : finrank (ZMod 2) f.range ≤ 1 := by simpa using f.range.finrank_le
  have hdimf := f.finrank_range_add_finrank_ker
  have hWlow := LinearMap.finrank_le_finrank_of_injective
    (show Function.Injective (F.codRestrict W hFW) from fun _ _ he => hFi (congrArg Subtype.val he))
  rw [Module.finrank_prod,Module.finrank_self] at hWlow
  have hWhigh := B.twice_finrank_le_of_isotropic h.nondegenerate W h.isotropic
  have hdim := h.dimension
  have hr : Group.rank (X ⧸ X₀) = 3 := by omega
  have hqcard : Nat.card (X ⧸ X₀) ≤ 8 := by
    apply Nat.le_of_dvd (by decide)
    have hh := card_dvd_exponent_pow_rank' (X ⧸ X₀)
      (Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
        (IsElementaryAbelian.exponent_dvd_p 2 (X ⧸ X₀)))
    simpa only [hr,Nat.reducePow] using hh
  obtain ⟨S,_,hXS,hSX⟩ := (ChapterG.Section11.normalSylow_iff_normalizer ρ v X).mp hS
  let e := m.symmetricEquiv
  let P := S.mapSurjective (f := e.toMonoidHom) e.surjective
  let C := X.map e.toMonoidHom
  let : IsElementaryAbelian 2 C := IsElementaryAbelian.map _
  have ha : e x ∉ alternatingGroup (Fin 8) := by
    intro hh
    have hi : m.groupEquiv x ∈ MulAut.innerSubgroup (LinearGroup 4) :=
      (BinaryNaturalDual.FourActors.permutationEquiv_mem_alternating _).mp hh
    obtain ⟨g,hg⟩ := hi
    apply hx
    apply Submodule.eq_of_le_of_finrank_eq ?_ (finrank_map_action ρ I x)
    rintro _ ⟨u,hu,rfl⟩
    rw [mem_natural_iff m,m.equivariant,← hg,
      (AutomorphismModel.coordinateAction (Or.inl rfl)).on_inner,
      BinaryNaturalDual.naturalDualRepresentation_apply,(mem_natural_iff m u).mp hu,map_zero]
  have hlarge := Theory.SpecificGroups.SymmetricEight.NormalElementaryOdd.sylow_normal_elementary_card
    P C (map_mono hXS) ((map_mono hSX).trans (le_normalizer_map e.toMonoidHom))
    ⟨e x,mem_map_of_mem _ x.property⟩ ha
  have hlarge' : 16 ≤ Nat.card X := by
    simpa only [C,card_map_of_injective (f := e.toMonoidHom) e.injective] using hlarge
  intro hzero
  have hc := X₀.card_mul_index
  rw [index_eq_card] at hc
  have hcardzero : Nat.card X₀ = 1 := by rw [hzero,card_bot]
  rw [hcardzero,one_mul] at hc
  omega

end CFSG.Quasithin.Chapter6.Source.RankOneRecognition
