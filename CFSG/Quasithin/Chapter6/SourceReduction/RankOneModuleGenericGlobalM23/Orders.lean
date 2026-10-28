module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalM23.Triple
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalM23.CubicFusion
public import Theory.SpecificGroups.Alternating.FiveSylowNormalizerCard
public import Theory.GroupTheory.NormalizedSupConsequences
public import Theory.GroupTheory.CyclicHallNormalizerEscape

/-!
# Orders and cubic fusion for both original maximal locals

The triple-stabilizer preimage has order 1152. A Frattini argument identifies
its index in M with the index of a Sylow normalizer in L. The original A₅
quotient gives index five, hence |M| = 5760 and |M/O₂(M)| = 360. This index
also conjugates every cubic of M into M ∩ J, where the exceptional-local
fusion already applies. Thus all cubics in the original union M ∪ J fuse.

Source: Aschbacher–Smith 5.2.11(3) and 5.2.14(2), printed pp.653–654
(`refs/quasithin.pdf`). The order calculation is an input to the ΓL₂(4)
identification; it does not assert that identification on order alone.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
variable {G : Type*} [Group G] [Finite G]

private theorem sylow_normalizer_index_five
    (e : (G ⧸ pCore 2 G) ≃* alternatingGroup (Fin 5)) (P : Sylow 2 G) :
    (normalizer ((P : Subgroup G) : Set G)).index = 5 := by
  let q := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 G))
  have hq : Function.Surjective q := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hk : q.ker = pCore 2 G :=
    (MonoidHom.ker_comp_of_injective _ e.toMonoidHom e.injective).trans (QuotientGroup.ker_mk' _)
  let Q := P.mapSurjective hq
  have hpre : (Q : Subgroup (alternatingGroup (Fin 5))).comap q = (P : Subgroup G) :=
    comap_map_eq_self (hk ▸ (pCore_isPGroup (p := 2)).le_sylow_of_normal P)
  have hN : normalizer ((P : Subgroup G) : Set G) = (normalizer ((Q : Subgroup (alternatingGroup (Fin 5))) : Set (alternatingGroup (Fin 5)))).comap q := by
    rw [comap_normalizer_eq_of_surjective _ hq,hpre]
  rw [hN, (normalizer ((Q : Subgroup (alternatingGroup (Fin 5))) : Set (alternatingGroup (Fin 5)))).index_comap_of_surjective hq]
  have hc := (normalizer ((Q : Subgroup (alternatingGroup (Fin 5))) : Set (alternatingGroup (Fin 5)))).card_mul_index
  have hCQ : Nat.card (normalizer ((Q : Subgroup (alternatingGroup (Fin 5))) : Set (alternatingGroup (Fin 5)))) = 12 :=
    Theory.SpecificGroups.Alternating.FiveBorelOvergroups.sylow_normalizer_card Q
  rw [hCQ] at hc
  have hA : Nat.card (alternatingGroup (Fin 5)) = 60 := by
    rw [nat_card_alternatingGroup,Nat.card_fin]
    norm_num [Nat.factorial]
  rw [hA] at hc
  omega

theorem Preparation.linear_exceptional_left_orders
    {T : Sylow 2 G} {L W H A B : Subgroup G} {n : ℕ}
    (d : Preparation T L H A B (residual H))
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hp : Group.IsPerfect (residual H))
    (F : Type) [Field F] [Finite F] [CharP F 2]
    {m : ℕ} (hm : 0 < m) (hF : Nat.card F = 2^m)
    (he : Nonempty (RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H))
      (ChapterF.GreenBook.LieModels.LinearThree.amalgam F)) ∨
      Nonempty (RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H))
      (ChapterF.GreenBook.LieModels.LinearThree.amalgam F).reverse))
    {J : Subgroup G} (hJ : J ∈ Chapter1.LStar G (T : Subgroup G))
    (hKJ : residual H < J) :
    (normalizer (L : Set G) ⊓ J).relIndex (normalizer (L : Set G)) = 5 ∧
      Nat.card (normalizer (L : Set G)) = 5760 ∧
      Nat.card ((normalizer (L : Set G)) ⧸ pCore 2 (normalizer (L : Set G))) = 360 := by
  have hnonmax : residual H ∉ Chapter1.LStar G (T : Subgroup G) := by
    intro hK
    exact hKJ.ne (hK.2 J hJ.1 hKJ.le).symm
  obtain ⟨_,hn,hF4,hcores,hcore,_,_,_⟩ :=
    d.linear_nonmaximal_core_geometry h hH hp F hm hF he hnonmax
  have hSL : sourceS L H ≤ L := d.linear_sourceS_le_factors h hH.1.1.2 hp F hm hF he 0
  have hs := d.sylow 0
  change ∃ P : Sylow 2 L, (P : Subgroup L).map L.subtype = sourceS L H ⊓ L at hs
  obtain ⟨P,hP⟩ := hs
  rw [inf_eq_left.mpr hSL] at hP
  have hpre : (sourceS L H).subgroupOf L = (P : Subgroup L) := by
    rw [←hP]
    exact comap_map_eq_self_of_injective L.subtype_injective _
  have hplanes := (d.linear_exceptional_sylow_planes h hH hp F hm hF he hJ hKJ).2.2.2.2.2
  have hN : (normalizer (L : Set G) ⊓ J).subgroupOf L = normalizer ((P : Subgroup L) : Set L) := by
    rw [←hpre,←subgroupOf_normalizer_eq hSL]
    ext x
    constructor
    · intro hx
      exact (hplanes.ge ⟨hx.2,hx.1⟩).1
    · intro hx
      exact ⟨L.le_normalizer x.property,(hplanes.le ⟨hx,L.le_normalizer x.property⟩).1⟩
  obtain ⟨E,_,_,hE,⟨e⟩⟩ := h.linear
  have hE4 : Nat.card E = 4 := by simpa only [hn,Nat.reducePow] using hE
  obtain ⟨a⟩ := Matrix.ProjectiveSpecialLinearGroup.equiv_alternatingGroup_of_card_four hE4
  have hindex : (normalizer (L : Set G) ⊓ J).relIndex (normalizer (L : Set G)) = 5 := by
    have hg := relIndex_sup_of_normalizes L (normalizer (L : Set G) ⊓ J) inf_le_left
    rw [d.linear_exceptional_left_generation h hH hp F hm hF he hJ hKJ] at hg
    rw [hg]
    change ((normalizer (L : Set G) ⊓ J).subgroupOf L).index = 5
    rw [hN]
    exact sylow_normalizer_index_five (e.trans a) P
  have hCcard := d.linear_exceptional_intersection_card h hH hp F hm hF he hJ hKJ
  have hMcard : Nat.card (normalizer (L : Set G)) = 5760 := by
    have hc := ((normalizer (L : Set G) ⊓ J).subgroupOf (normalizer (L : Set G))).card_mul_index
    change Nat.card ((normalizer (L : Set G) ⊓ J).subgroupOf (normalizer (L : Set G))) *
      (normalizer (L : Set G) ⊓ J).relIndex (normalizer (L : Set G)) = _ at hc
    rw [Nat.card_congr (subgroupOfEquivOfLe (show normalizer (L : Set G) ⊓ J ≤
      normalizer (L : Set G) from inf_le_left)).toEquiv,hCcard,hindex] at hc
    exact hc.symm
  refine ⟨hindex,hMcard,?_⟩
  have hcorecard : Nat.card (pCore 2 (normalizer (L : Set G))) = 16 := by
    have hc := congrArg (fun X : Subgroup G => Nat.card X) hcore
    change Nat.card ((pCore 2 (normalizer (L : Set G))).map (normalizer (L : Set G)).subtype) =
      Nat.card ((pCore 2 L).map L.subtype) at hc
    rw [card_map_of_injective (normalizer (L : Set G)).subtype_injective,
      card_map_of_injective L.subtype_injective] at hc
    exact hc.trans (hcores 0).2
  have hc := (pCore 2 (normalizer (L : Set G))).card_mul_index
  rw [hcorecard,hMcard,index_eq_card] at hc
  omega

/-- Source 5.2.14(2), for both original maximal locals. -/
theorem Preparation.linear_exceptional_local_cubics_isConj
    {T : Sylow 2 G} {L W H A B : Subgroup G} {n : ℕ}
    (d : Preparation T L H A B (residual H))
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hp : Group.IsPerfect (residual H))
    (F : Type) [Field F] [Finite F] [CharP F 2]
    {m : ℕ} (hm : 0 < m) (hF : Nat.card F = 2^m)
    (he : Nonempty (RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H))
      (ChapterF.GreenBook.LieModels.LinearThree.amalgam F)) ∨
      Nonempty (RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H))
      (ChapterF.GreenBook.LieModels.LinearThree.amalgam F).reverse))
    {J : Subgroup G} (hJ : J ∈ Chapter1.LStar G (T : Subgroup G))
    (hKJ : residual H < J)
    (a b : G) (ha : orderOf a = 3) (hb : orderOf b = 3)
    (haM : a ∈ normalizer (L : Set G) ∨ a ∈ J)
    (hbM : b ∈ normalizer (L : Set G) ∨ b ∈ J) : IsConj a b := by
  have hnonmax : residual H ∉ Chapter1.LStar G (T : Subgroup G) := by
    intro hK
    exact hKJ.ne (hK.2 J hJ.1 hKJ.le).symm
  have hindex := (d.linear_exceptional_left_orders h hH hp F hm hF he hJ hKJ).1
  have place (x : G) (hx : orderOf x = 3)
      (hxM : x ∈ normalizer (L : Set G) ∨ x ∈ J) :
      ∃ y : J, orderOf y = 3 ∧ IsConj x (y : G) := by
    rcases hxM with hxM | hxJ
    · let M := normalizer (L : Set G)
      let c : M := ⟨x,hxM⟩
      have hc : orderOf c = 3 := (Subgroup.orderOf_coe c).symm.trans hx
      have hcp : IsPGroup 3 (zpowers c) := IsPGroup.of_card
        (by rw [Nat.card_zpowers,hc]; decide : Nat.card (zpowers c) = 3^1)
      obtain ⟨g,hg⟩ := exists_conj_le_of_prime_not_dvd_index
        ((M ⊓ J).subgroupOf M) (zpowers c) (by rw [hindex]; decide : ¬3 ∣ (M ⊓ J).relIndex M) hcp
      have hgx : g*c*g⁻¹ ∈ (M ⊓ J).subgroupOf M := hg (mem_map_of_mem _ (mem_zpowers c))
      let y : J := ⟨(g : G)*x*(g : G)⁻¹,hgx.2⟩
      have hxy : IsConj x (y : G) := by
        exact isConj_iff.mpr ⟨(g : G),rfl⟩
      refine ⟨y,?_,hxy⟩
      exact (Subgroup.orderOf_coe y).symm.trans (((MulAut.conj (g : G)).orderOf_eq x).trans hx)
    · exact ⟨⟨x,hxJ⟩,(Subgroup.orderOf_coe ⟨x,hxJ⟩).symm.trans hx,IsConj.refl x⟩
  obtain ⟨a',ha',haa⟩ := place a ha haM
  obtain ⟨b',hb',hbb⟩ := place b hb hbM
  exact haa.trans ((d.linear_nonmaximal_exceptional_cubics_isConj h hH hp F hm hF he
    hnonmax hJ hKJ a' b' ha' hb').trans hbb.symm)

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
