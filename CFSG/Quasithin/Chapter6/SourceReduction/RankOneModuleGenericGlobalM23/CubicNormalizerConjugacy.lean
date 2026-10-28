module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalM23.CubicNormalizer
/-!
# The source cubic-normalizer theorem for every Sylow choice

Sylow conjugacy inside the literal centralizer preimage transports the
constructed scalar cubic and its full ambient normalizer to every permitted
source choice. Both the local and ambient maps use the same conjugating
element. The already proved source cubic fusion then gives ΓL₂(4) as the
ambient normalizer of every cubic in the original left local, the input
used next for the original Cartan subgroup in 5.2.16.

Source: Aschbacher–Smith 5.2.15–16, printed pp.654–655
(`refs/quasithin.pdf`). This does not assert compatible linear completion
or the final ambient M₂₃ isomorphism.
-/
public noncomputable section
open Subgroup Theory.GroupTheory
open Representation.SL2FourNatural.SemilinearNormalizer
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
private theorem map_conjugate_subgroup {X Y : Type*} [Group X] [Group Y]
    (R : Subgroup X) (f : X →* Y) (a : X) :
    (R.map (MulAut.conj a).toMonoidHom).map f =
      (R.map f).map (MulAut.conj (f a)).toMonoidHom := by
  rw [map_map,map_map]
  congr 1
  ext x
  simp only [MonoidHom.comp_apply,MulEquiv.coe_toMonoidHom,MulAut.conj_apply,map_mul,map_inv]

theorem Preparation.linear_nonmaximal_cubic_normalizer
    {G : Type*} [Group G] [Finite G]
    {T : Sylow 2 G} {L W H A B : Subgroup G} {n : ℕ}
    (d : Preparation T L H A B (residual H))
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hp : Group.IsPerfect (residual H))
    (E : Type) [Field E] [Finite E] [CharP E 2]
    {m : ℕ} (hm : 0 < m) (hE : Nat.card E = 2^m)
    (he : Nonempty (RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H))
      (ChapterF.GreenBook.LieModels.LinearThree.amalgam E)) ∨
      Nonempty (RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H))
      (ChapterF.GreenBook.LieModels.LinearThree.amalgam E).reverse))
    (hnonmax : residual H ∉ Chapter1.LStar G (T : Subgroup G))
    (P : Sylow 3 ((centralizer (((L.subgroupOf (normalizer (L : Set G))).map
      (QuotientGroup.mk' (pCore 2 (normalizer (L : Set G))))) :
        Set ((normalizer (L : Set G)) ⧸ pCore 2 (normalizer (L : Set G))))).comap
          (QuotientGroup.mk' (pCore 2 (normalizer (L : Set G)))))) :
    let M := normalizer (L : Set G)
    let π := QuotientGroup.mk' (pCore 2 M)
    let D := (centralizer ((L.subgroupOf M).map π : Set (M ⧸ pCore 2 M))).comap π
    let C := (P : Subgroup D).map D.subtype
    Subgroup.normalizer (C.map M.subtype : Set G) =
      (Subgroup.normalizer (C : Set M)).map M.subtype ∧
      Nonempty (Subgroup.normalizer (C.map M.subtype : Set G) ≃* Gamma) := by
  let M := normalizer (L : Set G)
  let π := QuotientGroup.mk' (pCore 2 M)
  let D := (centralizer ((L.subgroupOf M).map π : Set (M ⧸ pCore 2 M))).comap π
  let C := (P : Subgroup D).map D.subtype
  obtain ⟨_,_,C₀,_,_,⟨P₀,hP₀⟩,_,_,hN₀,eN₀⟩ :=
    d.linear_nonmaximal_scalar_cubic_ambient_normalizer h hH hp E hm hE he hnonmax
  obtain ⟨a,ha⟩ := MulAction.exists_smul_eq D P P₀
  have hP : (P : Subgroup D).map (MulAut.conj a).toMonoidHom = (P₀ : Subgroup D) :=
    congrArg Sylow.toSubgroup ha
  have hC : C.map (MulAut.conj (a : M)).toMonoidHom = C₀ := by
    change ((P : Subgroup D).map D.subtype).map (MulAut.conj (a : M)).toMonoidHom = _
    exact (map_conjugate_subgroup (P : Subgroup D) D.subtype a).symm.trans
      ((congrArg (Subgroup.map D.subtype) hP).trans hP₀)
  have hCG : (C.map M.subtype).map (MulAut.conj ((a : M) : G)).toMonoidHom = C₀.map M.subtype := by
    exact (map_conjugate_subgroup C M.subtype (a : M)).symm.trans
      (congrArg (Subgroup.map M.subtype) hC)
  have hnorm : (Subgroup.normalizer (C.map M.subtype : Set G)).map
      (MulAut.conj ((a : M) : G)).toMonoidHom =
      Subgroup.normalizer (C₀.map M.subtype : Set G) := by
    rw [map_equiv_normalizer_eq,hCG]
  have heq : Subgroup.normalizer (C.map M.subtype : Set G) =
      (Subgroup.normalizer (C : Set M)).map M.subtype := by
    apply map_injective (f := (MulAut.conj ((a : M) : G)).toMonoidHom) (MulAut.conj _).injective
    rw [hnorm,hN₀]
    symm
    calc
      _ = ((Subgroup.normalizer (C : Set M)).map
          (MulAut.conj (a : M)).toMonoidHom).map M.subtype :=
        (map_conjugate_subgroup (Subgroup.normalizer (C : Set M)) M.subtype (a : M)).symm
      _ = (Subgroup.normalizer (C₀ : Set M)).map M.subtype := by
        rw [map_equiv_normalizer_eq,hC]
  exact ⟨heq,⟨((Subgroup.normalizer (C.map M.subtype : Set G)).equivMapOfInjective
    (MulAut.conj ((a : M) : G)).toMonoidHom (MulAut.conj _).injective).trans
      ((MulEquiv.subgroupCongr hnorm).trans eN₀.some)⟩⟩


theorem Preparation.linear_nonmaximal_cubic_normalizer_of_mem_left
    {G : Type*} [Group G] [Finite G]
    {T : Sylow 2 G} {L W H A B : Subgroup G} {n : ℕ}
    (d : Preparation T L H A B (residual H))
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hp : Group.IsPerfect (residual H))
    (E : Type) [Field E] [Finite E] [CharP E 2]
    {m : ℕ} (hm : 0 < m) (hE : Nat.card E = 2^m)
    (he : Nonempty (RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H))
      (ChapterF.GreenBook.LieModels.LinearThree.amalgam E)) ∨
      Nonempty (RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H))
      (ChapterF.GreenBook.LieModels.LinearThree.amalgam E).reverse))
    (hnonmax : residual H ∉ Chapter1.LStar G (T : Subgroup G))
    (c : G) (hc : orderOf c = 3) (hcM : c ∈ normalizer (L : Set G)) :
    Nonempty (Subgroup.normalizer (zpowers c : Set G) ≃* Gamma) := by
  let M := normalizer (L : Set G)
  obtain ⟨_,_,C,_,hC,_,_,_,_,eN⟩ :=
    d.linear_nonmaximal_scalar_cubic_ambient_normalizer h hH hp E hm hE he hnonmax
  obtain ⟨a,ha⟩ := exists_prime_orderOf_dvd_card' (G := C) 3 (by rw [hC])
  have haM : orderOf (a : M) = 3 := (Subgroup.orderOf_coe a).trans ha
  have haG : orderOf ((a : M) : G) = 3 := (Subgroup.orderOf_coe (a : M)).trans haM
  have hcyc : C = zpowers (a : M) := by
    symm
    apply eq_of_le_of_card_ge (zpowers_le.mpr a.property)
    rw [Nat.card_zpowers,haM,hC]
  have hCG : C.map M.subtype = zpowers ((a : M) : G) := by
    exact (congrArg (Subgroup.map M.subtype) hcyc).trans (MonoidHom.map_zpowers M.subtype (a : M))
  obtain ⟨_,halt⟩ := d.linear_maximal_or_exceptional h hH hp E hm hE he
  obtain ⟨_,J,hJ,hKJ,_⟩ := halt.resolve_left hnonmax
  obtain ⟨g,hg⟩ := isConj_iff.mp (d.linear_exceptional_local_cubics_isConj
    h hH hp E hm hE he hJ hKJ c ((a : M) : G) hc haG (.inl hcM) (.inl (a : M).property))
  have hmap : (Subgroup.normalizer (zpowers c : Set G)).map (MulAut.conj g).toMonoidHom =
      Subgroup.normalizer (C.map M.subtype : Set G) := by
    rw [map_equiv_normalizer_eq,MonoidHom.map_zpowers,hCG]
    exact congrArg (fun x : G => Subgroup.normalizer (zpowers x : Set G)) hg
  exact ⟨((Subgroup.normalizer (zpowers c : Set G)).equivMapOfInjective
    (MulAut.conj g).toMonoidHom (MulAut.conj g).injective).trans
      ((MulEquiv.subgroupCongr hmap).trans eN.some)⟩

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
