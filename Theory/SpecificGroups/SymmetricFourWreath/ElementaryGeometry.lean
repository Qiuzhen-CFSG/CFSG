module
public import Theory.SpecificGroups.SymmetricFourWreath.Planes
public import Theory.GroupTheory.CentralizerSmallKernelTransport
public import Theory.ElementaryAbelian.Quotient
public import Stellmacher.ElementaryAbelianMaxFamilyMap
public import Stellmacher.ElementaryAbelianMaxJMap

/-!
# The maximum elementary family in the actual dihedral wreath Sylow

An involution outside the wreath base is conjugate to the pure swap. Its
centralizer is D8 × C2, so it cannot belong to an elementary subgroup of
order at least sixteen. Inside the base, each coordinate projection lies
in one of the two dihedral four-groups. This proves that the four displayed
products are precisely the elementary subgroups of maximum order. Their
join is the dihedral base, identifying the actual elementary Thompson group.

Only the eight-element dihedral calculation is finite; no subgroup lattice
or large wreath multiplication table is enumerated.
Source: Aschbacher–Smith 13.9.2(1), printed p.969 (PDF p.986).
-/

public section
namespace SymmetricFourWreath
open Subgroup

private theorem c2_cases (q : C2) : q=1 ∨ q=turn := by
  revert q
  decide +kernel

private theorem dihedral_elementary_plane (E : Subgroup D8) (hE : IsElementaryAbelian 2 E) :
    ∃b, E ≤ plane b := by
  by_cases ht : E ≤ plane true
  · exact ⟨true,ht⟩
  obtain ⟨x,hx,hxt⟩ := Set.not_subset.mp ht
  refine ⟨false,?_⟩
  intro y hy
  have hlocal : ∀x y : D8, x^2=1 → y^2=1 → x*y=y*x → x∉plane true → y∈plane false := by
    decide +kernel
  exact hlocal x y (elemPow_eq_one_of_isElementaryAbelian x hx)
    (elemPow_eq_one_of_isElementaryAbelian y hy)
    (congrArg Subtype.val (hE.is_comm.comm (⟨x,hx⟩ : E) ⟨y,hy⟩)) hxt

variable (D : Type*) [Group D]
private def diagonalPair : D × C2 →* RegularWreathProduct D C2 where
  toFun a := ⟨fun _ => a.1,a.2⟩
  map_one' := rfl
  map_mul' _ _ := rfl

private theorem diagonalPair_injective : Function.Injective (diagonalPair D) := by
  intro a b h
  exact Prod.ext (congrArg (fun w => w.left 1) h) (congrArg RegularWreathProduct.right h)

private theorem diagonalPair_range :
    (diagonalPair D).range = centralizer ({RegularWreathProduct.inl turn} : Set (RegularWreathProduct D C2)) := by
  ext x
  rw [mem_centralizer_singleton_iff]
  constructor
  · rintro ⟨a,rfl⟩
    apply RegularWreathProduct.ext
    · funext q
      simp [diagonalPair]
    · simp [diagonalPair,mul_comm]
  · intro h
    refine ⟨(x.left 1,x.right),?_⟩
    apply RegularWreathProduct.ext
    · funext q
      rcases c2_cases q with rfl | rfl
      · rfl
      · have he := congrArg (fun w => w.left 1) h
        simpa [diagonalPair] using he
    · rfl

private noncomputable def swapCentralizerEquiv :
    centralizer ({RegularWreathProduct.inl turn} : Set (RegularWreathProduct D C2)) ≃* D × C2 :=
  (MulEquiv.subgroupCongr (diagonalPair_range D).symm).trans
    (MonoidHom.ofInjective (diagonalPair_injective D)).symm

variable {D}
private theorem outside_involution_conjugate (x : RegularWreathProduct D C2)
    (hx : x.right ≠ 1) (hxx : x*x=1) : IsConj (RegularWreathProduct.inl turn) x := by
  have hr : x.right=turn := (c2_cases x.right).resolve_left hx
  have he : x.left 1 * x.left turn = 1 := by
    have hh := congrArg (fun w : RegularWreathProduct D C2 => w.left 1) hxx
    simpa [hr] using hh
  have hl : (x.left 1)⁻¹=x.left turn := (inv_eq_iff_mul_eq_one).mpr he
  let a : RegularWreathProduct D C2 := ⟨fun i=>if i=1 then x.left 1 else 1,1⟩
  apply isConj_iff.mpr
  refine ⟨a,?_⟩
  apply RegularWreathProduct.ext
  · funext q
    rcases c2_cases q with rfl | rfl
    · simp [a,turn_ne_one]
    · simp [a,turn_ne_one,hl]
  · simpa [a] using hr.symm

private theorem outsideCentralizerEquiv (x : P) (hx : x.right ≠ 1) (hxx : x*x=1) :
    Nonempty (centralizer ({x} : Set P) ≃* D8 × C2) := by
  obtain ⟨g,hg⟩ := isConj_iff.mp (outside_involution_conjugate x hx hxx)
  have he : (MulAut.conj g) (RegularWreathProduct.inl turn) = x := hg
  exact ⟨(MulEquiv.subgroupCongr (congrArg (fun t : P => centralizer ({t} : Set P)) he.symm)).trans
    ((Theory.GroupTheory.CentralizerSmallKernelTransport.centralizerEquiv
      (MulAut.conj g) (RegularWreathProduct.inl turn)).symm.trans (swapCentralizerEquiv D8))⟩

private theorem large_elementary_base (E : Subgroup P) (hE : IsElementaryAbelian 2 E)
    (hcard : 16 ≤ Nat.card E) : ∀x∈E, x.right=1 := by
  intro x hx
  by_contra hn
  obtain ⟨e⟩ := outsideCentralizerEquiv x hn (by
    simpa only [pow_two] using elemPow_eq_one_of_isElementaryAbelian (p := 2) x hx)
  have hc : Nat.card (centralizer ({x} : Set P)) = 16 := by
    rw [Nat.card_congr e.toEquiv,Nat.card_prod,DihedralGroup.nat_card]
    norm_num [Nat.card_eq_fintype_card,C2]
  have hEC : E ≤ centralizer ({x} : Set P) := by
    intro y hy
    exact mem_centralizer_singleton_iff.mpr
      (congrArg Subtype.val (hE.is_comm.comm (⟨y,hy⟩ : E) ⟨x,hx⟩))
  have heq : E = centralizer ({x} : Set P) := eq_of_le_of_card_ge hEC (hc ▸ hcard)
  have hcom (a b : D8 × C2) : a*b=b*a := by
    have hh := hE.is_comm.comm
      ((MulEquiv.subgroupCongr heq).symm (e.symm a))
      ((MulEquiv.subgroupCongr heq).symm (e.symm b))
    have hh' := congrArg (fun z => e ((MulEquiv.subgroupCongr heq) z)) hh
    simpa only [map_mul,MulEquiv.apply_symm_apply] using hh'
  have hf := hcom (DihedralGroup.r 1,1) (DihedralGroup.sr 0,1)
  exact (by decide : ((DihedralGroup.r 1,1) : D8 × C2)*(DihedralGroup.sr 0,1) ≠
    (DihedralGroup.sr 0,1)*(DihedralGroup.r 1,1)) hf

private theorem pair_range : pair.range = (RegularWreathProduct.rightHom : P →* C2).ker := by
  ext x
  constructor
  · rintro ⟨a,rfl⟩
    rfl
  · intro hx
    refine ⟨(x.left 1,x.left turn),?_⟩
    apply RegularWreathProduct.ext
    · funext q
      rcases c2_cases q with rfl | rfl <;> simp [pair,turn_ne_one]
    · exact hx.symm

private theorem elementary_contained_in_pair (E : Subgroup P) (hE : IsElementaryAbelian 2 E)
    (hcard : 16 ≤ Nat.card E) : ∃b c, E ≤ elementaryInP b c := by
  have hbase : E ≤ pair.range := by
    rw [pair_range]
    exact large_elementary_base E hE hcard
  let E' := E.comap pair
  have hm : E'.map pair = E := map_comap_eq_self hbase
  have hE' : IsElementaryAbelian 2 E' := by
    let e : E' ≃* E := (equivMapOfInjective E' pair pair_injective).trans (MulEquiv.subgroupCongr hm)
    exact IsElementaryAbelian.of_surjective e.symm.toMonoidHom e.symm.surjective
  have h1 : IsElementaryAbelian 2 (E'.map (MonoidHom.fst D8 D8)) := hE'.map _
  have h2 : IsElementaryAbelian 2 (E'.map (MonoidHom.snd D8 D8)) := hE'.map _
  obtain ⟨b,hb⟩ := dihedral_elementary_plane _ h1
  obtain ⟨c,hc⟩ := dihedral_elementary_plane _ h2
  refine ⟨b,c,?_⟩
  rw [←hm]
  apply Subgroup.map_mono
  intro a ha
  exact ⟨hb ⟨a,ha,rfl⟩,hc ⟨a,ha,rfl⟩⟩

theorem card_elementaryInP (b c : Bool) : Nat.card (elementaryInP b c) = 16 := by
  have h := card_elementary b c
  rw [elementary,card_map_of_injective sylowEmbedding_injective] at h
  exact h

theorem elementaryInP_card_bound (E : Subgroup P) (hE : IsElementaryAbelian 2 E) : Nat.card E ≤ 16 := by
  by_cases hc : 16 ≤ Nat.card E
  · obtain ⟨b,c,h⟩ := elementary_contained_in_pair E hE hc
    exact (card_le_of_le h).trans (card_elementaryInP b c).le
  · omega

theorem maximum_elementaryInP (E : Subgroup P) :
    E ∈ Stellmacher.elementaryAbelianMaxSubgroups (⊤ : Subgroup P) ↔
      ∃b c, E = elementaryInP b c := by
  constructor
  · rintro ⟨_,hE,hmax⟩
    have hc : 16 ≤ Nat.card E := by
      simpa only [card_elementaryInP] using hmax (elementaryInP true true) le_top inferInstance
    obtain ⟨b,c,hbc⟩ := elementary_contained_in_pair E hE hc
    exact ⟨b,c,eq_of_le_of_card_ge hbc ((card_elementaryInP b c) ▸ hc)⟩
  · rintro ⟨b,c,rfl⟩
    exact ⟨le_top,inferInstance,fun E _ hE => (elementaryInP_card_bound E hE).trans_eq (card_elementaryInP b c).symm⟩

theorem maximum_elementary (E : Subgroup W) :
    E ∈ Stellmacher.elementaryAbelianMaxSubgroups (standardSylow : Subgroup W) ↔
      ∃b c, E = elementary b c := by
  constructor
  · intro hE
    let D := E.comap sylowEmbedding
    have he : D.map sylowEmbedding = E := map_comap_eq_self hE.1
    have hD : D ∈ Stellmacher.elementaryAbelianMaxSubgroups (⊤ : Subgroup P) := by
      apply (Stellmacher.maxFamily_map_injective_iff sylowEmbedding sylowEmbedding_injective ⊤ D).mp
      simpa only [←MonoidHom.range_eq_map,←standardSylow_coe,he] using hE
    obtain ⟨b,c,hbc⟩ := (maximum_elementaryInP D).mp hD
    exact ⟨b,c,he.symm.trans (congrArg (fun S : Subgroup P => S.map sylowEmbedding) hbc)⟩
  · rintro ⟨b,c,rfl⟩
    have h := (Stellmacher.maxFamily_map_injective_iff sylowEmbedding sylowEmbedding_injective
      ⊤ (elementaryInP b c)).mpr ((maximum_elementaryInP _).mpr ⟨b,c,rfl⟩)
    simpa only [←MonoidHom.range_eq_map,←standardSylow_coe,elementary] using h

private theorem dihedral_plane_product : ∀x : D8, ∃a∈plane true, ∃b∈plane false,x=a*b := by
  decide +kernel

private theorem pair_range_sup : pair.range = elementaryInP true true ⊔ elementaryInP false false := by
  apply le_antisymm
  · rintro _ ⟨x,rfl⟩
    obtain ⟨a,ha,b,hb,he⟩ := dihedral_plane_product x.1
    obtain ⟨c,hc,d,hd,hf⟩ := dihedral_plane_product x.2
    have hx : x=(a,c)*(b,d) := Prod.ext he hf
    rw [hx,map_mul]
    exact (elementaryInP true true ⊔ elementaryInP false false).mul_mem
      (mem_sup_left ⟨(a,c),⟨ha,hc⟩,rfl⟩) (mem_sup_right ⟨(b,d),⟨hb,hd⟩,rfl⟩)
  · exact sup_le (map_le_range _ _) (map_le_range _ _)

theorem J_eq_sup : J = A ⊔ B := by
  simp only [J,pair_range_sup,Subgroup.map_sup,A,B,elementary]

theorem elementary_le_J (b c : Bool) : elementary b c ≤ J :=
  map_mono (map_le_range pair _)

theorem elementary_thompson : Stellmacher.elementaryAbelianMaxJ (standardSylow : Subgroup W) = J := by
  apply le_antisymm
  · apply sSup_le
    intro E hE
    obtain ⟨b,c,rfl⟩ := (maximum_elementary E).mp hE
    exact elementary_le_J b c
  · rw [J_eq_sup]
    exact sup_le (le_sSup ((maximum_elementary A).mpr ⟨true,true,rfl⟩))
      (le_sSup ((maximum_elementary B).mpr ⟨false,false,rfl⟩))

end SymmetricFourWreath
