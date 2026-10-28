module
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.NaturalContradiction.Parabolics
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.Constrained.Source
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.Constrained.MovingPlane
public import Theory.SpecificGroups.BinaryLinear.InvariantNodeActions.FlagGeometry

/-!
# A common natural flag for the three source parabolics

The recognized natural action of L extends to the literal conjugation action
of LS on UL. Its image is the full binary linear group and its kernel is
O₂(LS). A Sylow flag for the image of S therefore determines actual preimages
of every minimal parabolic in LS, with their original ambient embeddings.

The projected seed is the first flag cut and the moving four-group is the
second. Consequently the first end-node preimage stabilizes the moving plane
and escapes ML S. The same preimages have S as a Sylow subgroup and admit the
embedded O²-residual supplements. These markings are shared by the local
placement and rank-two arguments, so both arguments use one triple.

Source: Aschbacher--Smith, 15.1.28--29, printed pp.1103--1104 of
`refs/quasithin.pdf`.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
open CFSG.Quasithin.ChapterD.UniqueFactor
open CFSG.Quasithin.ChapterA.Section05To06
open CFSG.Quasithin.Chapter15.Section03
open BinaryLinear BinaryLinear.OuterCyclic BinaryLinear.InvariantNodeActions
namespace CFSG.Quasithin.Chapter15.Section01.CaseIComponentData
variable {G : Type*} [Group G]

/-- Conjugation, linearized over the prime field and transported to the chosen coordinates. -/
noncomputable def naturalAction (H U : Subgroup G)
    (hn : H ≤ normalizer (U : Set G)) [IsElementaryAbelian 2 U]
    {n : ℕ} (x : Additive U ≃ₗ[ZMod 2] Space n) : H →* LinearGroup n :=
  (SmallParabolicLevi.linearGroupCongr x).toMonoidHom.comp
    ((LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) (Additive U)).toMonoidHom.comp
      ((imageRepresentation H U hn).asGroupHom.comp (actionHom H U hn).rangeRestrict))

@[simp] theorem naturalAction_apply (H U : Subgroup G)
    (hn : H ≤ normalizer (U : Set G)) [IsElementaryAbelian 2 U]
    {n : ℕ} (x : Additive U ≃ₗ[ZMod 2] Space n) (g : H) (v : Additive U) :
    naturalAction H U hn x g (x v) =
      x (Additive.ofMul (actionHom H U hn g v.toMul)) := by
  change x ((actionHom H U hn g).toMonoidHom.toAdditive.toZModLinearMap 2
    (x.symm (x v))) = _
  rw [x.symm_apply_apply]
  rfl

theorem naturalAction_ker (H U : Subgroup G)
    (hn : H ≤ normalizer (U : Set G)) [IsElementaryAbelian 2 U]
    {n : ℕ} (x : Additive U ≃ₗ[ZMod 2] Space n) :
    (naturalAction H U hn x).ker = (centralizer (U : Set G)).subgroupOf H := by
  rw [← actionHom_ker H U hn]
  ext g
  constructor
  · intro hg
    apply MonoidHom.mem_ker.mpr
    apply MulEquiv.ext
    intro v
    apply x.injective
    have he := congrArg (fun f : LinearGroup n => f (x (Additive.ofMul v)))
      (MonoidHom.mem_ker.mp hg)
    rw [naturalAction_apply] at he
    exact he
  · intro hg
    apply MonoidHom.mem_ker.mpr
    apply LinearEquiv.ext
    intro w
    obtain ⟨v,rfl⟩ := x.surjective w
    rw [naturalAction_apply, MonoidHom.mem_ker.mp hg]
    rfl

variable [Finite G]
variable {T : Sylow 2 G} {M Mc V : Subgroup G}

/-- An actual natural action and common Sylow flag, with no parabolic-placement premise. -/
structure NaturalFlag (d : CaseIComponentData T M Mc V) (t : G) where
  m : ℕ
  dimension : m = 3 ∨ m = 4
  elementary : IsElementaryAbelian 2 (d.UL t)
  normalizes : d.L ⊔ d.S ≤ normalizer (d.UL t : Set G)
  coordinates : letI := elementary; Additive (d.UL t) ≃ₗ[ZMod 2] Space (m + 1)
  component_surjective : letI := elementary;
    Function.Surjective (fun l : d.L =>
      naturalAction (d.L ⊔ d.S) (d.UL t) normalizes coordinates
        ⟨l.val,(show d.L ≤ d.L ⊔ d.S from le_sup_left) l.property⟩)
  surjective : letI := elementary;
    Function.Surjective (naturalAction (d.L ⊔ d.S) (d.UL t) normalizes coordinates)
  kernel : letI := elementary;
    (naturalAction (d.L ⊔ d.S) (d.UL t) normalizes coordinates).ker =
      pCore 2 (d.L ⊔ d.S : Subgroup G)
  basis : Basis m
  sylow : letI := elementary;
    (d.S.subgroupOf (d.L ⊔ d.S)).map
      (naturalAction (d.L ⊔ d.S) (d.UL t) normalizes coordinates) =
        cutStabilizer basis Set.univ

namespace NaturalFlag
variable {d : CaseIComponentData T M Mc V} {t : G}

noncomputable def action (a : NaturalFlag d t) :
    (d.L ⊔ d.S : Subgroup G) →* LinearGroup (a.m + 1) :=
  letI := a.elementary
  naturalAction (d.L ⊔ d.S) (d.UL t) a.normalizes a.coordinates

/-- The full preimage of a minimal flag parabolic, embedded back in G. -/
noncomputable def node (a : NaturalFlag d t) (i : Fin a.m) : Subgroup G :=
  ((minimalParabolic a.basis i).comap a.action).map (d.L ⊔ d.S).subtype

/-- The first end node, its neighbor, and the other end node of the same flag. -/
noncomputable def parabolics (a : NaturalFlag d t) : NaturalParabolics d where
  P0 := a.node ⟨0,by have := a.dimension; omega⟩
  P2 := a.node ⟨1,by have := a.dimension; omega⟩
  P3 := a.node ⟨a.m - 1,by have := a.dimension; omega⟩

theorem node_le (a : NaturalFlag d t) (i : Fin a.m) : a.node i ≤ d.L ⊔ d.S :=
  map_subtype_le _

theorem sylow_le_node (a : NaturalFlag d t) (i : Fin a.m) : d.S ≤ a.node i := by
  intro s hs
  refine ⟨⟨s,(show d.S ≤ d.L ⊔ d.S from le_sup_right) hs⟩,?_,rfl⟩
  change a.action ⟨s,(show d.S ≤ d.L ⊔ d.S from le_sup_right) hs⟩ ∈ minimalParabolic a.basis i
  have hh : a.action ⟨s,(show d.S ≤ d.L ⊔ d.S from le_sup_right) hs⟩ ∈ cutStabilizer a.basis Set.univ := by
    rw [←a.sylow]
    exact mem_map_of_mem _ hs
  exact (cutStabilizer_le_iff a.basis Set.univ {i}ᶜ).mpr (Set.subset_univ _) hh

theorem parabolics_le (a : NaturalFlag d t) :
    a.parabolics.P0 ≤ d.L ⊔ d.S ∧ a.parabolics.P2 ≤ d.L ⊔ d.S ∧
      a.parabolics.P3 ≤ d.L ⊔ d.S :=
  ⟨a.node_le _,a.node_le _,a.node_le _⟩

theorem sylow_le (a : NaturalFlag d t) :
    d.S ≤ a.parabolics.P0 ∧ d.S ≤ a.parabolics.P2 ∧ d.S ≤ a.parabolics.P3 :=
  ⟨a.sylow_le_node _,a.sylow_le_node _,a.sylow_le_node _⟩

theorem node_image (a : NaturalFlag d t) (i : Fin a.m) :
    ((a.node i).subgroupOf (d.L ⊔ d.S)).map a.action = minimalParabolic a.basis i := by
  change ((((minimalParabolic a.basis i).comap a.action).map
    (d.L ⊔ d.S).subtype).comap (d.L ⊔ d.S).subtype).map a.action = _
  rw [comap_map_eq_self_of_injective (d.L ⊔ d.S).subtype_injective]
  exact map_comap_eq_self_of_surjective a.surjective _

theorem node_sylow (a : NaturalFlag d t) (s : d.ExchangedSource) (i : Fin a.m) :
    Chapter1.IsSylowIn 2 d.S (a.node i) :=
  s.centralizer_sylow.restrict (a.sylow_le_node i)
    ((a.node_le i).trans (sup_le d.L_component.1 d.S_le_G1))

theorem node_supplement (a : NaturalFlag d t) (s : d.ExchangedSource) (i : Fin a.m) :
    a.node i = (pResidual 2 (a.node i)).map (a.node i).subtype ⊔ d.S := by
  obtain ⟨P,hP⟩ := a.node_sylow s i
  have hh := congrArg (map (a.node i).subtype) (pResidual_sup_sylow_eq_top P)
  rw [Subgroup.map_sup,hP,←MonoidHom.range_eq_map,range_subtype] at hh
  exact hh.symm

theorem second_supplement (a : NaturalFlag d t) (s : d.ExchangedSource) :
    a.parabolics.P2 = a.parabolics.Y2 ⊔ d.S := a.node_supplement s _

noncomputable def spaceOf (a : NaturalFlag d t) (W : Subgroup G) :
    Submodule (ZMod 2) (Space (a.m + 1)) :=
  letI := a.elementary
  (AddSubgroup.toZModSubmodule 2 (W.subgroupOf (d.UL t)).toAddSubgroup).map
    a.coordinates.toLinearMap

@[simp] theorem mem_spaceOf_coordinates (a : NaturalFlag d t) (W : Subgroup G)
    (v : Additive (d.UL t)) :
    a.coordinates v ∈ a.spaceOf W ↔ v.toMul.val ∈ W := by
  let := a.elementary
  constructor
  · rintro ⟨u,hu,he⟩
    have he' : u = v := a.coordinates.injective he
    exact he' ▸ hu
  · intro hv
    exact ⟨v,hv,rfl⟩

noncomputable def spaceOfEquiv (a : NaturalFlag d t) (W : Subgroup G)
    (hW : W ≤ d.UL t) : W ≃ a.spaceOf W := by
  letI := a.elementary
  exact {
  toFun w := ⟨a.coordinates (Additive.ofMul ⟨w.val,hW w.property⟩),
    (a.mem_spaceOf_coordinates W _).mpr w.property⟩
  invFun v := ⟨(a.coordinates.symm v).toMul.val,by
    apply (a.mem_spaceOf_coordinates W _).mp
    simpa only [a.coordinates.apply_symm_apply] using v.property⟩
  left_inv w := by apply Subtype.ext; simp
  right_inv v := by apply Subtype.ext; simp }

theorem spaceOf_finrank (a : NaturalFlag d t) (W : Subgroup G)
    (hW : W ≤ d.UL t) {r : ℕ} (hc : Nat.card W = 2 ^ r) :
    Module.finrank (ZMod 2) (a.spaceOf W) = r := by
  apply Nat.pow_right_injective (by decide : 2 ≤ 2)
  calc
    2 ^ Module.finrank (ZMod 2) (a.spaceOf W) = Nat.card (a.spaceOf W) := by
      simpa only [Nat.card_zmod] using
        (Module.natCard_eq_pow_finrank (K := ZMod 2) (V := a.spaceOf W)).symm
    _ = Nat.card W := Nat.card_congr (a.spaceOfEquiv W hW).symm
    _ = 2 ^ r := hc

theorem spaceOf_invariant (a : NaturalFlag d t) (W : Subgroup G)
    (hn : d.S ≤ normalizer (W : Set G)) :
    cutStabilizer a.basis Set.univ ≤ parabolic (a.spaceOf W) := by
  let := a.elementary
  intro g hg v
  rw [←a.sylow] at hg
  obtain ⟨s,hs,rfl⟩ := hg
  obtain ⟨v,rfl⟩ := a.coordinates.surjective v
  rw [naturalAction_apply]
  rw [a.mem_spaceOf_coordinates,a.mem_spaceOf_coordinates]
  change s.val * v.toMul.val * s.val⁻¹ ∈ W ↔ v.toMul.val ∈ W
  exact (mem_normalizer_iff.mp (hn hs) _).symm

theorem spaceOf_eq_cut (a : NaturalFlag d t) (W : Subgroup G)
    (hW : W ≤ d.UL t) (hn : d.S ≤ normalizer (W : Set G))
    (i : Fin a.m) (hc : Nat.card W = 2 ^ (i.val + 1)) :
    a.spaceOf W = cutSpace a.basis i := by
  have hr := a.spaceOf_finrank W hW hc
  have h0 : a.spaceOf W ≠ ⊥ := by
    intro he
    rw [he,finrank_bot] at hr
    omega
  have h1 : a.spaceOf W ≠ ⊤ := by
    intro he
    rw [he,finrank_top,Module.finrank_fin_fun] at hr
    have := i.isLt
    omega
  obtain ⟨j,hj⟩ := fullFlag_invariant_subspace a.basis _ h0 h1 (a.spaceOf_invariant W hn)
  have hij : j = i := by
    apply Fin.ext
    rw [hj,cutSpace_finrank] at hr
    omega
  exact hij ▸ hj


theorem node_ne_pointStabilizer (a : NaturalFlag d t) (W : Subgroup G)
    (i : Fin a.m) (hc : a.spaceOf W = cutSpace a.basis i) :
    ¬ a.node i ≤ normalizer (W : Set G) := by
  let := a.elementary
  intro hn
  have hp : minimalParabolic a.basis i ≤ cutStabilizer a.basis {i} := by
    rw [←a.node_image i]
    rintro g ⟨g,hg,rfl⟩
    rw [mem_cutStabilizer]
    intro j hj v
    have hji : j = i := Set.mem_singleton_iff.mp hj
    subst j
    rw [←hc]
    obtain ⟨v,rfl⟩ := a.coordinates.surjective v
    change naturalAction _ _ _ _ g (a.coordinates v) ∈ a.spaceOf W ↔ _
    rw [naturalAction_apply,a.mem_spaceOf_coordinates,a.mem_spaceOf_coordinates]
    exact (mem_normalizer_iff.mp (hn hg) _).symm
  have hh := (cutStabilizer_le_iff a.basis {i}ᶜ {i}).mp hp (Set.mem_singleton i)
  exact hh (Set.mem_singleton i)

theorem node_normalizes_cut (a : NaturalFlag d t) (W : Subgroup G)
    (hW : W ≤ d.UL t) (i j : Fin a.m) (hij : j ≠ i)
    (hcut : a.spaceOf W = cutSpace a.basis j) :
    a.node i ≤ normalizer (W : Set G) := by
  let := a.elementary
  apply le_normalizer_iff.mpr
  intro g hg w hw
  obtain ⟨g,hg,rfl⟩ := hg
  let v : Additive (d.UL t) := Additive.ofMul ⟨w,hW hw⟩
  have hv : a.coordinates v ∈ cutSpace a.basis j := by
    rw [←hcut]
    exact (a.mem_spaceOf_coordinates W v).mpr hw
  have hg' : a.action g ∈ minimalParabolic a.basis i := hg
  have hm := (mem_cutStabilizer a.basis {i}ᶜ _).mp hg' j
    (by simpa using hij) (a.coordinates v)
  have hx : a.action g (a.coordinates v) ∈ a.spaceOf W := hcut ▸ (hm.mpr hv)
  change naturalAction _ _ _ _ g (a.coordinates v) ∈ a.spaceOf W at hx
  rw [naturalAction_apply,a.mem_spaceOf_coordinates] at hx
  exact hx

end NaturalFlag

open Theory.SpecificGroups.BinaryComponentResidual

/-- Recognition and the proved source action-kernel calculation supply the common marking. -/
theorem exists_naturalFlag {d : CaseIComponentData T M Mc V}
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (h : PreparedChosenModule T M V) (hs : d.HasExchangedLinearSource)
    (t : G) (ht : t ∈ (T : Subgroup G)) (htS : t ∉ d.S)
    (hnat : d.HasNaturalMovedModule t) : Nonempty (NaturalFlag d t) := by
  classical
  let s := hs.1.nineSource_of_natural_moved_module hM hu h t ht htS hnat
  obtain ⟨_, hE, hnL, n, hn, e, x, heq, _⟩ := hnat
  let := hE
  let he := small_binary_model_of_marking hn e
  let hf := facts_of_small_binary_model he
  let hi := s.c27Input hG h hf hs.2.1
  have hnLS : d.L ⊔ d.S ≤ normalizer (d.UL t : Set G) := by
    rw [← d.U_commutator_LS s hG hM hu h hi hf t ht]
    exact normalizer_commutator_ge_right _ _
  have hUL : d.UL t ≤ d.L ⊔ d.S :=
    (d.UL_le_U t).trans ((d.U_le_Q1 s hG hM hu h hi hf t ht).trans
      ((d.Q1_le_S s hu).trans le_sup_right))
  have hkernel : (naturalAction (d.L ⊔ d.S) (d.UL t) hnLS x).ker =
      pCore 2 (d.L ⊔ d.S : Subgroup G) := by
    have hk := (d.UL_LS_centralizer_eq s hG hM hu h hi hf t ht).trans
      (d.U_LS_centralizer_eq_pCore s hG hM hu h hi hf t ht htS)
    rw [naturalAction_ker, ← hk]
    ext g
    constructor
    · intro hg v hv
      exact Subtype.ext (hg v.val hv)
    · intro hg v hv
      exact congrArg Subtype.val (hg ⟨v,hUL hv⟩ hv)
  have hsurjL : Function.Surjective (fun l : d.L =>
      naturalAction (d.L ⊔ d.S) (d.UL t) hnLS x
        ⟨l.val,(show d.L ≤ d.L ⊔ d.S from le_sup_left) l.property⟩) := by
    intro a
    obtain ⟨l,hl⟩ := ((e.trans (slEquivLinear n)).surjective) a
    obtain ⟨l,rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 d.L) l
    refine ⟨l,?_⟩
    rw [←hl]
    apply LinearEquiv.ext
    intro w
    obtain ⟨v,rfl⟩ := x.surjective w
    rw [naturalAction_apply, MulEquiv.trans_apply, slEquivLinear_apply]
    exact heq l v
  have hsurj : Function.Surjective (naturalAction (d.L ⊔ d.S) (d.UL t) hnLS x) := by
    intro a
    obtain ⟨l,hl⟩ := hsurjL a
    exact ⟨⟨l.val,(show d.L ≤ d.L ⊔ d.S from le_sup_left) l.property⟩,hl⟩
  obtain ⟨m,hm,rfl⟩ : ∃ m, (m = 3 ∨ m = 4) ∧ n = m + 1 := by
    rcases hn with rfl | rfl
    · exact ⟨3,Or.inl rfl,rfl⟩
    · exact ⟨4,Or.inr rfl,rfl⟩
  have hSyl : Chapter1.IsSylowIn 2 d.S (d.L ⊔ d.S) :=
    s.centralizer_sylow.restrict le_sup_right (sup_le d.L_component.1 d.S_le_G1)
  obtain ⟨P,hP⟩ := hSyl
  have hP' : (P : Subgroup (d.L ⊔ d.S : Subgroup G)) =
      d.S.subgroupOf (d.L ⊔ d.S) := by
    calc
      (P : Subgroup (d.L ⊔ d.S : Subgroup G)) =
          ((P : Subgroup (d.L ⊔ d.S : Subgroup G)).map
            (d.L ⊔ d.S).subtype).comap (d.L ⊔ d.S).subtype :=
        (comap_map_eq_self_of_injective (d.L ⊔ d.S).subtype_injective _).symm
      _ = d.S.subgroupOf (d.L ⊔ d.S) := congrArg
        (fun A : Subgroup G => A.subgroupOf (d.L ⊔ d.S)) hP
  obtain ⟨b,hb⟩ := sylow_eq_cutStabilizer (P.mapSurjective hsurj)
  refine ⟨⟨m,hm,hE,hnLS,x,hsurjL,hsurj,hkernel,b,?_⟩⟩
  simpa only [Sylow.coe_mapSurjective,hP'] using hb

namespace NaturalFlag
variable {d : CaseIComponentData T M Mc V} {t : G}

/-- The literal moving four-group is the two-dimensional cut of every such marking. -/
theorem movingPlane_cut (a : NaturalFlag d t)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (h : PreparedChosenModule T M V) (hs : d.HasExchangedLinearSource)
    (ht : t ∈ (T : Subgroup G)) (htS : t ∉ d.S)
    (hnat : d.HasNaturalMovedModule t) :
    a.spaceOf d.nineMovingPlane =
      cutSpace a.basis ⟨1,by have := a.dimension; omega⟩ := by
  let s := hs.1.nineSource_of_natural_moved_module hM hu h t ht htS hnat
  obtain ⟨n,hn,⟨e⟩⟩ := hs.2.2
  let hf := facts_of_small_binary_model (small_binary_model_of_marking hn e)
  exact a.spaceOf_eq_cut d.nineMovingPlane
    (d.nineMovingPlane_le_UL s hG h hf t ht htS) s.fixes_planes.2 _ s.moving_card

theorem first_normalizes_movingPlane (a : NaturalFlag d t)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (h : PreparedChosenModule T M V) (hs : d.HasExchangedLinearSource)
    (ht : t ∈ (T : Subgroup G)) (htS : t ∉ d.S)
    (hnat : d.HasNaturalMovedModule t) :
    a.parabolics.P0 ≤ normalizer (d.nineMovingPlane : Set G) := by
  let s := hs.1.nineSource_of_natural_moved_module hM hu h t ht htS hnat
  obtain ⟨n,hn,⟨e⟩⟩ := hs.2.2
  let hf := facts_of_small_binary_model (small_binary_model_of_marking hn e)
  exact a.node_normalizes_cut d.nineMovingPlane
    (d.nineMovingPlane_le_UL s hG h hf t ht htS) _ ⟨1,by have := a.dimension; omega⟩
    (by simp) (a.movingPlane_cut hG hM hu h hs ht htS hnat)

theorem exists_markedLine (a : NaturalFlag d t) (hnat : d.HasNaturalMovedModule t) :
    ∃ ZU : Subgroup G, ZU ≤ d.UL t ∧ Nat.card ZU = 2 ∧
      ZU ≤ centralizer (d.S : Set G) ∧ d.L ⊓ centralizer (ZU : Set G) = d.ML ∧
      a.spaceOf ZU = cutSpace a.basis ⟨0,by have := a.dimension; omega⟩ := by
  obtain ⟨_,_,_,_,_,_,_,_,_,_,ZU,hZU,hcard,hS,_,hML⟩ := hnat
  refine ⟨ZU,hZU,hcard,hS,hML,?_⟩
  exact a.spaceOf_eq_cut ZU hZU
    ((le_centralizer_iff.mp hS).trans (Subgroup.centralizer_le_normalizer _)) _ hcard

/-- This end-node preimage is the source parabolic outside the marked point stabilizer. -/
theorem first_not_le_markedParabolic (a : NaturalFlag d t)
    (hnat : d.HasNaturalMovedModule t) : ¬ a.parabolics.P0 ≤ d.ML ⊔ d.S := by
  obtain ⟨ZU,_,_,hS,hML,hcut⟩ := a.exists_markedLine hnat
  have hn : d.ML ⊔ d.S ≤ normalizer (ZU : Set G) := by
    apply le_trans _ (Subgroup.centralizer_le_normalizer _)
    apply sup_le
    · rw [←hML]
      exact inf_le_right
    · exact le_centralizer_iff.mp hS
  exact fun hP => a.node_ne_pointStabilizer ZU _ hcut (hP.trans hn)

end NaturalFlag

end CFSG.Quasithin.Chapter15.Section01.CaseIComponentData
