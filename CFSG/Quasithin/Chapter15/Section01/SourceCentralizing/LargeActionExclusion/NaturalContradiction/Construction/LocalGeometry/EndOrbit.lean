module
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.NaturalContradiction.Construction.LocalGeometry.Geometry
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.NaturalContradiction.Construction.LocalGeometry.EndResidual
public import Theory.SpecificGroups.BinaryLinear.SylowFlagOvergroups.Covers
public import Theory.SpecificGroups.BinaryLinear.FiveFlagGeometry.ResidualExchange

/-!
# The actual end-node orbit and complete natural geometry

Each marked parabolic is a cover of S in the ambient subgroup lattice.
T normalizes S and the source residual extension L₀S, so it permutes the
noninitial nodes, which lie in that extension inside M_L S. In degree four
there are only two such nodes. In degree five their unique solvable pair is
the pair of ends; conjugation preserves solvability and hence this pair.

This proves the orbit of the literal parabolics and their embedded O²-residuals.
The adjacent/remote Sylow distinction then prevents exchanging the ends and
gives T-normalization of Y₂ and Q₂. The same flag now supplies every clause of
NaturalParabolicGeometry. The rank-two MS input remains a separate obligation.

Source: Aschbacher--Smith, 15.1.29, printed pp.1103--1104 of `refs/quasithin.pdf`.
-/

public section
open Subgroup Theory.GroupTheory
open BinaryLinear BinaryLinear.OuterCyclic BinaryLinear.InvariantNodeActions
open CFSG.Quasithin.ChapterA.Section05To06 CFSG.Quasithin.Chapter15.Section03

namespace CFSG.Quasithin.Chapter15.Section01.CaseIComponentData.NaturalFlag
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc V : Subgroup G}
variable {d : CaseIComponentData T M Mc V} {t : G}

private theorem exists_modelSylow (a : NaturalFlag d t) (s : d.ExchangedSource) :
    ∃ P : Sylow 2 (LinearGroup (a.m + 1)),
      (P : Subgroup _) = cutStabilizer a.basis Set.univ := by
  obtain ⟨P,hP⟩ := s.centralizer_sylow.restrict
    (show d.S ≤ d.L ⊔ d.S from le_sup_right)
    (sup_le d.L_component.1 d.S_le_G1)
  refine ⟨P.mapSurjective a.surjective,?_⟩
  change (P : Subgroup _).map a.action = _
  have he : (P : Subgroup _) = d.S.subgroupOf (d.L ⊔ d.S) := by
    apply map_injective (d.L ⊔ d.S).subtype_injective
    rw [hP,map_subgroupOf_eq_of_le le_sup_right]
  rw [he]
  exact a.sylow

private theorem sylow_preimage (a : NaturalFlag d t) (s : d.ExchangedSource) :
    (cutStabilizer a.basis Set.univ).comap a.action = d.S.subgroupOf (d.L ⊔ d.S) := by
  ext g
  exact (a.mem_sylow_iff s g).symm

/-- Every selected node is a literal minimal overgroup of S in G. -/
theorem node_cover (a : NaturalFlag d t) (s : d.ExchangedSource) (i : Fin a.m) :
    d.S ⋖ a.node i := by
  obtain ⟨P,hP⟩ := a.exists_modelSylow s
  have hc := (comap_covBy_iff_of_surjective a.action a.surjective
    (P : Subgroup _) (minimalParabolic a.basis i)).mpr
      (SylowFlagOvergroups.fullFlag_covBy_minimalParabolic P a.basis hP i)
  rw [hP,a.sylow_preimage s] at hc
  have hm := (covBy_map_subtype_iff (d.L ⊔ d.S) _ _).mpr hc
  rwa [map_subgroupOf_eq_of_le (show d.S ≤ d.L ⊔ d.S from le_sup_right)] at hm

/-- Every minimal overgroup of S lying in LS is one of the same flag preimages. -/
theorem eq_node_of_cover (a : NaturalFlag d t) (s : d.ExchangedSource)
    (P : Subgroup G) (hP : P ≤ d.L ⊔ d.S) (hc : d.S ⋖ P) :
    ∃ i : Fin a.m, P = a.node i := by
  obtain ⟨B,hB⟩ := a.exists_modelSylow s
  have hk : a.action.ker ≤ P.subgroupOf (d.L ⊔ d.S) := by
    apply le_trans _ (subgroupOf_mono (d.L ⊔ d.S) hc.le)
    rw [←a.sylow_preimage s]
    exact ker_le_comap _ _
  have hc' : d.S.subgroupOf (d.L ⊔ d.S) ⋖ P.subgroupOf (d.L ⊔ d.S) := by
    apply (covBy_map_subtype_iff (d.L ⊔ d.S) _ _).mp
    rwa [map_subgroupOf_eq_of_le (show d.S ≤ d.L ⊔ d.S from le_sup_right),
      map_subgroupOf_eq_of_le hP]
  have hm : cutStabilizer a.basis Set.univ ⋖ (P.subgroupOf (d.L ⊔ d.S)).map a.action := by
    apply (comap_covBy_iff_of_surjective a.action a.surjective _ _).mp
    rw [a.sylow_preimage s,comap_map_eq_self hk]
    exact hc'
  obtain ⟨i,hi⟩ := (SylowFlagOvergroups.fullFlag_covBy_iff B a.basis hB _).mp (hB.symm ▸ hm)
  refine ⟨i,?_⟩
  have he := congrArg (fun X => (X.comap a.action).map (d.L ⊔ d.S).subtype) hi
  rw [comap_map_eq_self hk,map_subgroupOf_eq_of_le hP] at he
  exact he

/-- Distinct cuts give distinct actual node preimages. -/
theorem node_injective (a : NaturalFlag d t) : Function.Injective a.node := by
  intro i j he
  have hh := congrArg (fun P : Subgroup G => (P.subgroupOf (d.L ⊔ d.S)).map a.action) he
  rw [a.node_image,a.node_image] at hh
  exact minimalParabolic_injective a.basis hh

end CFSG.Quasithin.Chapter15.Section01.CaseIComponentData.NaturalFlag

private theorem solvable_iff_of_equiv {A B : Type*} [Group A] [Group B] (e : A ≃* B) :
    Group.IsSolvable A ↔ Group.IsSolvable B := by
  constructor
  · intro h
    let := h
    exact Group.isSolvable_of_surjective (f := e.toMonoidHom) e.surjective
  · intro h
    let := h
    exact Group.isSolvable_of_surjective (f := e.symm.toMonoidHom) e.symm.surjective

private theorem binary_five_pair_solvable_iff {m : ℕ} (hm : m = 4)
    (b : Basis m) (i j : Fin m) (hij : i ≠ j) :
    Group.IsSolvable (minimalParabolic b i ⊔ minimalParabolic b j : Subgroup _) ↔
      (i.val + 1 < j.val ∨ j.val + 1 < i.val) := by
  subst m
  change Group.IsSolvable (BinaryLinear.FiveFlagGeometry.flagStabilizer b {i}ᶜ ⊔
    BinaryLinear.FiveFlagGeometry.flagStabilizer b {j}ᶜ : Subgroup _) ↔ _
  rw [BinaryLinear.FiveFlagGeometry.rankOne_sup_eq_pair]
  exact BinaryLinear.FiveFlagGeometry.pair_solvable_iff b i j hij

namespace CFSG.Quasithin.Chapter15.Section01.CaseIComponentData.NaturalFlag
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc V : Subgroup G}
variable {d : CaseIComponentData T M Mc V} {t : G}

/-- In degree five, solvability of the actual node join detects nonadjacency. -/
theorem node_pair_solvable_iff (a : NaturalFlag d t) (hm : a.m = 4)
    (i j : Fin a.m) (hij : i ≠ j) :
    Group.IsSolvable (a.node i ⊔ a.node j : Subgroup G) ↔
      (i.val + 1 < j.val ∨ j.val + 1 < i.val) := by
  let P := a.node i ⊔ a.node j
  have hP : P ≤ d.L ⊔ d.S := sup_le (a.node_le i) (a.node_le j)
  have hk : IsPGroup 2 a.action.ker := by
    rw [show a.action.ker = pCore 2 (d.L ⊔ d.S : Subgroup G) from a.kernel]
    exact pCore_isPGroup
  let : Group.IsNilpotent a.action.ker := hk.isNilpotent
  calc
    Group.IsSolvable P ↔ Group.IsSolvable (P.subgroupOf (d.L ⊔ d.S)) :=
      (solvable_iff_of_equiv (subgroupOfEquivOfLe hP)).symm
    _ ↔ Group.IsSolvable ((P.subgroupOf (d.L ⊔ d.S)).map a.action) :=
      (Group.isSolvable_map_iff_of_solvable_ker a.action _).symm
    _ ↔ _ := by
      rw [show P = a.node i ⊔ a.node j from rfl,
        subgroupOf_sup (a.node_le i) (a.node_le j),Subgroup.map_sup,a.node_image,a.node_image]
      exact binary_five_pair_solvable_iff hm a.basis i j hij

/-- Conjugation by T takes every noninitial node to another noninitial
node of the same flag. The proof uses the normalized source residual. -/
theorem conjugate_noninitial_node (a : NaturalFlag d t)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (h : PreparedChosenModule T M V) (hs : d.HasExchangedLinearSource)
    (hu : maximalTwoLocalOvergroups
      (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hnat : d.HasNaturalMovedModule t)
    (x : G) (hx : x ∈ (T : Subgroup G)) (i : Fin a.m) (hi : i.val ≠ 0) :
    ∃ j : Fin a.m, j.val ≠ 0 ∧
      (a.node i).map (MulAut.conj x).toMonoidHom = a.node j := by
  let D := d.naturalEndResidual ⊔ d.S
  have hD : D ≤ d.ML ⊔ d.S := sup_le_sup_right (map_subtype_le _) _
  have hC : d.ML ⊔ d.S ≤ d.L ⊔ d.S := sup_le_sup_right inf_le_right _
  have hnodeD : a.node i ≤ D := by
    rw [a.node_supplement hs.1]
    exact sup_le_sup_right (a.node_residual_le_endResidual hG h hs hu hnat i hi) _
  have hDmap : D.map (MulAut.conj x).toMonoidHom = D :=
    mem_normalizer_iff_map_conj_eq.mp (d.normalizes_naturalEndResidual_sup_sylow hG h hs hx)
  have himageD : (a.node i).map (MulAut.conj x).toMonoidHom ≤ D :=
    (map_mono hnodeD).trans_eq hDmap
  have hSmap : d.S.map (MulAut.conj x).toMonoidHom = d.S :=
    mem_normalizer_iff_map_conj_eq.mp
      ((normal_subgroupOf_iff_le_normalizer d.S_le_T).mp hs.1.sylow_normal hx)
  have hc : d.S.map (MulAut.conj x).toMonoidHom ⋖
      (a.node i).map (MulAut.conj x).toMonoidHom := by
    apply (comap_covBy_iff_of_surjective (MulAut.conj x).toMonoidHom
      (MulAut.conj x).surjective _ _).mp
    rw [comap_map_eq_self_of_injective (MulAut.conj x).injective,
      comap_map_eq_self_of_injective (MulAut.conj x).injective]
    exact a.node_cover hs.1 i
  rw [hSmap] at hc
  obtain ⟨j,hj⟩ := a.eq_node_of_cover hs.1 _ (himageD.trans (hD.trans hC)) hc
  refine ⟨j,?_,hj⟩
  intro hj0
  have he : j = ⟨0,by have := a.dimension; omega⟩ := Fin.ext hj0
  apply a.first_not_le_markedParabolic hnat
  change a.node ⟨0,by have := a.dimension; omega⟩ ≤ _
  rw [←he,←hj]
  exact himageD.trans hD

/-- T permutes the two actual end-node parabolics. In degree five the
unique solvable pair among the three remaining nodes detects the ends. -/
theorem end_parabolic_orbit (a : NaturalFlag d t)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (h : PreparedChosenModule T M V) (hs : d.HasExchangedLinearSource)
    (hu : maximalTwoLocalOvergroups
      (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hnat : d.HasNaturalMovedModule t) (x : G) (hx : x ∈ (T : Subgroup G)) :
    a.parabolics.P2.map (MulAut.conj x).toMonoidHom = a.parabolics.P2 ∨
      a.parabolics.P2.map (MulAut.conj x).toMonoidHom = a.parabolics.P3 := by
  let i : Fin a.m := ⟨1,by have := a.dimension; omega⟩
  let k : Fin a.m := ⟨a.m - 1,by have := a.dimension; omega⟩
  obtain ⟨j,hj0,hj⟩ := a.conjugate_noninitial_node hG h hs hu hnat x hx i (by simp [i])
  have hjend : j = i ∨ j = k := by
    rcases a.dimension with hm | hm
    · have := j.isLt
      have hv : j.val = 1 ∨ j.val = a.m - 1 := by omega
      exact hv.imp Fin.ext Fin.ext
    · obtain ⟨l,hl0,hl⟩ := a.conjugate_noninitial_node hG h hs hu hnat x hx k
        (by simp only [k]; omega)
      have hik : i ≠ k := by
        intro he
        have hv := congrArg Fin.val he
        change 1 = a.m - 1 at hv
        omega
      have hjl : j ≠ l := by
        intro he
        have hnodes : a.node i = a.node k := map_injective (MulAut.conj x).injective
          (hj.trans ((congrArg a.node he).trans hl.symm))
        exact hik (a.node_injective hnodes)
      have hsol : Group.IsSolvable (a.node i ⊔ a.node k : Subgroup G) :=
        (a.node_pair_solvable_iff hm i k hik).mpr (Or.inl (by simp only [i,k]; omega))
      have hsol' : Group.IsSolvable (a.node j ⊔ a.node l : Subgroup G) := by
        have he : (a.node i ⊔ a.node k : Subgroup G).map (MulAut.conj x).toMonoidHom =
            a.node j ⊔ a.node l := by rw [Subgroup.map_sup,hj,hl]
        rw [←he]
        exact (solvable_iff_of_equiv
          ((MulAut.conj x).subgroupMap (a.node i ⊔ a.node k))).mp hsol
      have hn := (a.node_pair_solvable_iff hm j l hjl).mp hsol'
      have := j.isLt
      have := l.isLt
      have hv : j.val = 1 ∨ j.val = a.m - 1 := by omega
      exact hv.imp Fin.ext Fin.ext
  rcases hjend with rfl | rfl
  · exact Or.inl hj
  · exact Or.inr hj

/-- The end-node orbit transports to the literal embedded two-residuals. -/
theorem end_residual_orbit (a : NaturalFlag d t)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (h : PreparedChosenModule T M V) (hs : d.HasExchangedLinearSource)
    (hu : maximalTwoLocalOvergroups
      (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hnat : d.HasNaturalMovedModule t) (x : G) (hx : x ∈ (T : Subgroup G)) :
    a.parabolics.Y2.map (MulAut.conj x).toMonoidHom = a.parabolics.Y2 ∨
      a.parabolics.Y2.map (MulAut.conj x).toMonoidHom = a.parabolics.Y3 := by
  change ((pResidual 2 a.parabolics.P2).map a.parabolics.P2.subtype).map _ = _ ∨ _
  simp only [NaturalParabolics.Y2, NaturalParabolics.Y3, map_embedded_pResidual]
  rcases a.end_parabolic_orbit hG h hs hu hnat x hx with he | he
  · exact Or.inl (congrArg (fun P : Subgroup G => (pResidual 2 P).map P.subtype) he)
  · exact Or.inr (congrArg (fun P : Subgroup G => (pResidual 2 P).map P.subtype) he)

end CFSG.Quasithin.Chapter15.Section01.CaseIComponentData.NaturalFlag

namespace CFSG.Quasithin.Chapter15.Section01.CaseIComponentData
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc V : Subgroup G}

namespace NaturalFlag
variable {d : CaseIComponentData T M Mc V} {t : G}

/-- The marked source action supplies all the natural parabolic geometry,
including the end orbit. No parabolic clause is an extra assumption. -/
theorem geometry (a : NaturalFlag d t)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hM : IsOrderingMaximal T M)
    (hJ : Stellmacher.elementaryAbelianMaxJ (T : Subgroup G) ≤
      centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (h : PreparedChosenModule T M V) (hfull : V = localModule T M)
    (hs : d.HasExchangedLinearSource)
    (ht : t ∈ (T : Subgroup G)) (htS : t ∉ d.S)
    (hnat : d.HasNaturalMovedModule t) : NaturalParabolicGeometry a.parabolics :=
  a.geometry_of_end_orbit hG hM hJ hu h hfull hs ht htS hnat
    (a.end_residual_orbit hG h hs hu hnat)

/-- The actual second residual and its parabolic two-core are normalized
by T, using the proved orbit and the adjacent/remote Sylow distinction. -/
theorem normalizes_second (a : NaturalFlag d t)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hM : IsOrderingMaximal T M)
    (hJ : Stellmacher.elementaryAbelianMaxJ (T : Subgroup G) ≤
      centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (h : PreparedChosenModule T M V) (hfull : V = localModule T M)
    (hs : d.HasExchangedLinearSource)
    (ht : t ∈ (T : Subgroup G)) (htS : t ∉ d.S)
    (hnat : d.HasNaturalMovedModule t) :
    (T : Subgroup G) ≤ normalizer (a.parabolics.Y2 : Set G) ∧
      (T : Subgroup G) ≤ normalizer (a.parabolics.Q2 : Set G) := by
  have hg := a.geometry hG hM hJ hu h hfull hs ht htS hnat
  exact ⟨hg.normalizes_second_residual hM h,hg.normalizes_second_core hs.1 hM h⟩
end NaturalFlag
end CFSG.Quasithin.Chapter15.Section01.CaseIComponentData
