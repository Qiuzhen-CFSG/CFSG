module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource.BinaryThreeAmbientSourceAction
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource.BinaryThreePointCubicConjugate
public import Theory.GroupTheory.CoprimeQuotientSubgroups

/-!
# The escaping elementary nine in the original point quotient

In the degree-three large-distance setting of [AS, II, §15.3, proof of
Lemma 15.3.23], the original conjugate component supplies a cubic commuting
with a cubic in `Y_L`.  This elementary nine survives the literal quotient
`C_G(z) / O₂(C_G(z))` and escapes the image of `LS`.

The proof uses that `LS/L` is a two-group, so a cubic outside `L` is outside
`LS`, and that `O₂(C_G(z)) ≤ O₂(LS)`, so quotienting preserves this separation.
Coprimality preserves the nine, which forces the point quotient's three-rank
to equal two.  The final theorem retains the original local component and
normal containing component, together with the opposite-core action bound.
These are necessary ambient constraints; they do not yet exclude the branch.
The prescribed earlier MS input remains explicit.
-/

public section
open Subgroup Theory.GroupTheory
open scoped Pointwise MatrixGroups
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource
open LinearThree LinearThree.OriginalSource ChapterC BinaryMS.MS93
universe u
variable {G : Type u} [Group G] [Finite G]

private theorem cubic_mem_component_of_mem_overgroup
    {κ : GroupClass} (L S : Subgroup G)
    (b : BinaryMS.Input κ (L.subgroupOf (L ⊔ S)) (S.subgroupOf (L ⊔ S)))
    (v : G) (hv : orderOf v = 3) (hvJ : v ∈ L ⊔ S) : v ∈ L := by
  let J := L ⊔ S
  let B := L.subgroupOf J
  let : B.Normal := b.component_normal
  let q := QuotientGroup.mk' B
  have hQ : IsPGroup 2 (J ⧸ B) := by
    have hm : (pCore 2 J).map q = ⊤ := by
      have hh := congrArg (Subgroup.map q) b.core_sup_component
      rw [Subgroup.map_sup,map_top_of_surjective q (QuotientGroup.mk'_surjective _)] at hh
      have hz : B.map q = ⊥ := (map_eq_bot_iff B).mpr (QuotientGroup.ker_mk' B).ge
      rwa [hz,sup_bot_eq] at hh
    have hp := (pCore_isPGroup (p := 2) (G := J)).map q
    rw [hm] at hp
    exact hp.of_equiv topEquiv
  let x : J := ⟨v,hvJ⟩
  have hx : (q x)^3 = 1 := by
    rw [←map_pow]
    have hp : x^3 = 1 := Subtype.ext (hv ▸ pow_orderOf_eq_one v)
    rw [hp,map_one]
  have hone : q x = 1 := (hQ.powEquiv (by decide : Nat.Coprime 2 3)).injective (by
    simpa only [IsPGroup.powEquiv_apply,one_pow] using hx)
  exact (QuotientGroup.eq_one_iff x).mp hone

omit [Finite G] in
private theorem quotient_image_separation
    (J C : Subgroup G)
    (hcore : C.pCoreIn 2 ≤ J) (v : C) (hv : (v : G) ∉ J) :
    QuotientGroup.mk' (pCore 2 C) v ∉
      (J.subgroupOf C).map (QuotientGroup.mk' (pCore 2 C)) := by
  intro hm
  have hk : pCore 2 C ≤ J.subgroupOf C := by
    intro x hx
    exact hcore (mem_map_of_mem C.subtype hx)
  have hh : v ∈ ((J.subgroupOf C).map (QuotientGroup.mk' (pCore 2 C))).comap
      (QuotientGroup.mk' (pCore 2 C)) := hm
  rw [comap_map_eq_self (by simpa only [QuotientGroup.ker_mk'] using hk)] at hh
  exact hv hh

private theorem elementary_nine_quotient_card
    (C E : Subgroup G) (hEC : E ≤ C) [IsElementaryAbelian 3 E]
    (hE : Nat.card E = 9) :
    Nat.card ((E.subgroupOf C).map (QuotientGroup.mk' (pCore 2 C))) = 9 := by
  let q := QuotientGroup.mk' (pCore 2 C)
  have hp : IsPGroup 2 q.ker := by rw [QuotientGroup.ker_mk']; exact pCore_isPGroup
  obtain ⟨n,hn⟩ := hp.exists_card_eq
  have hcop : Nat.Coprime 3 (Nat.card q.ker) := by
    rw [hn]
    exact (by decide : Nat.Coprime 3 2).pow_right n
  have hEi : IsPGroup 3 (E.subgroupOf C) := (IsElementaryAbelian.isPGroup 3 E).comap_subtype
  have hinj := injective_comp_subtype_of_coprime_ker q hcop (E.subgroupOf C) hEi
  let f := q.subgroupMap (E.subgroupOf C)
  have hf : Function.Injective f := fun x y h => hinj (congrArg Subtype.val h)
  exact (Nat.card_congr (MulEquiv.ofBijective f ⟨hf,q.subgroupMap_surjective _⟩).toEquiv).symm.trans
    ((Nat.card_congr (subgroupOfEquivOfLe hEC).toEquiv).trans hE)

variable (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (d : LocalData G)
    (hempty : MainForward.faithfulLocalComponents d.T = ∅)
    (hM : ChapterA.Section05To06.IsOrderingMaximal d.T d.M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions d.T : Set G)) = {d.Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (d.T : Subgroup G)).ncard)
    {I : Subgroup G} (hI : I ∈ d.Hplus) (htwo : OutsideStructure.RankTwoCase d I)
    (hf : HasCharacteristicTwo I) (c : ComponentWitness d I)
    (e : (c.L ⧸ pCore 2 c.L) ≃* PSL(3,ZMod 2))
    (b : BinaryMS.Input KnownSimple.IsKnownSimple
      (c.L.subgroupOf (c.L ⊔ d.S)) (d.S.subgroupOf (c.L ⊔ d.S)))
    (t : InputSetup b)
    (common : CommonFacts t.reduction.radical t.source t.geometry)
    (earlier : DistanceEight.CoreFactors.Earlier t.reduction.radical t.geometry)

include hG hempty hM hu hmany hI htwo hf e b t common earlier

/-- The actual outside cubic remains outside the original LS image in the
point quotient. Its elementary nine survives the same two-core quotient. -/
theorem binary_three_source_point_quotient_cubic_escape
    (z : G) (hz : z ∈ intrinsicFour c.L)
    (hLS : c.L ⊔ d.S ≤ centralizer ({z} : Set G))
    (P : Sylow 2 (centralizer ({z} : Set G)))
    (hP : (P : Subgroup _).map (centralizer ({z} : Set G)).subtype = d.S)
    (g : G) (hgT : g ∈ (d.T : Subgroup G)) (hgS : g ∉ d.S) :
    let C := centralizer ({z} : Set G)
    let q := QuotientGroup.mk' (pCore 2 C)
    let Jbar := ((c.L ⊔ d.S).subgroupOf C).map q
    ∃ a v : C, ∃ E : Subgroup C,
      (a : G) ∈ YL d c.L ∧ (v : G) ∈ c.L.conjBy g ∧
      orderOf a = 3 ∧ orderOf v = 3 ∧ a * v = v * a ∧
      (v : G) ∉ c.L ⊔ d.S ∧ a ∈ E ∧ v ∈ E ∧
      IsElementaryAbelian 3 E ∧ Nat.card E = 9 ∧
      q v ∉ Jbar ∧ IsElementaryAbelian 3 (E.map q) ∧ Nat.card (E.map q) = 9 := by
  obtain ⟨a,v,E,haY,hvL,ha,hv,haz,hvz,hav,hvout,hEC,haE,hvE,hE,hcard⟩ :=
    binary_three_source_intrinsic_point_outside_cubic
      hG d hempty hM hu hmany hI htwo hf c e b t common earlier z hz g hgT hgS
  let C := centralizer ({z} : Set G)
  let q := QuotientGroup.mk' (pCore 2 C)
  let aa : C := ⟨a,haz⟩
  let vv : C := ⟨v,hvz⟩
  let EE := E.subgroupOf C
  let := hE
  let : IsElementaryAbelian 3 EE := IsElementaryAbelian.subgroupOf hEC
  have hvJ : v ∉ c.L ⊔ d.S := fun hh =>
    hvout (cubic_mem_component_of_mem_overgroup c.L d.S b v hv hh)
  obtain ⟨hcore,_,_,_⟩ := binary_three_source_point_opposite_core
    hG d hempty hM hu hmany hI htwo hf c e z hLS P hP g hgT hgS
  exact ⟨aa,vv,EE,haY,hvL,(Subgroup.orderOf_coe aa).symm.trans ha,
    (Subgroup.orderOf_coe vv).symm.trans hv,Subtype.ext hav,hvJ,haE,hvE,
    inferInstance,(Nat.card_congr (subgroupOfEquivOfLe hEC).toEquiv).trans hcard,
    quotient_image_separation (c.L ⊔ d.S) C
      (hcore.trans ((c.L ⊔ d.S).pCoreIn_le 2)) vv hvJ,
    IsElementaryAbelian.map q,elementary_nine_quotient_card C E hEC hcard⟩

/-- The original source quotient has three-rank exactly two, with an
elementary nine escaping LS, and still retains the smaller local component,
the opposite-core centralizer bound and the normal containing component. -/
theorem binary_three_source_point_quotient_with_escaping_nine
    (g : G) (hgT : g ∈ (d.T : Subgroup G)) (hgS : g ∉ d.S) :
    ∃ z : G, z ∈ intrinsicFour c.L ∧ orderOf z = 2 ∧
      c.L ⊔ d.S ≤ centralizer ({z} : Set G) ∧
      ¬ centralizer ({z} : Set G) ≤ d.M ∧
      let C := centralizer ({z} : Set G)
      let q := QuotientGroup.mk' (pCore 2 C)
      let B := (c.L.subgroupOf C).map q
      let Jbar := ((c.L ⊔ d.S).subgroupOf C).map q
      let D := (((LinearThree.commutatorCore c.L).conjBy g).subgroupOf C).map q
      IsSQTK KnownSimple.IsKnownSimple (C ⧸ pCore 2 C) ∧
      pCore 2 (C ⧸ pCore 2 C) = ⊥ ∧
      Nat.card (intrinsicFour B) ≤ 2 ∧
      Nonempty ((B ⧸ pCore 2 B) ≃* PSL(3,ZMod 2)) ∧
      C.pCoreIn 2 ≤ (c.L ⊔ d.S).pCoreIn 2 ∧
      D ≠ ⊥ ∧ IsPGroup 2 D ∧ ¬ B ≤ normalizer (D : Set (C ⧸ pCore 2 C)) ∧
      IsPGroup 2 (Jbar ⊓ centralizer (D : Set (C ⧸ pCore 2 C)) : Subgroup _) ∧
      primeRank 3 (C ⧸ pCore 2 C) = 2 ∧ Jbar ≠ ⊤ ∧
      (∃ E : Subgroup C, IsElementaryAbelian 3 E ∧ Nat.card E = 9 ∧
        IsElementaryAbelian 3 (E.map q) ∧ Nat.card (E.map q) = 9 ∧ ¬ E.map q ≤ Jbar) ∧
      ∃ P : Sylow 2 C, (P : Subgroup C).map C.subtype = d.S ∧
        B ∈ ChapterA.Section03.localCComponents
          (P.mapSurjective (QuotientGroup.mk'_surjective (pCore 2 C))) ∧
        ∃ K : Subgroup C, K.IsCComponent ∧ K.Normal ∧ c.L.subgroupOf C ≤ K ∧
          (K.map q).IsCComponent ∧ (K.map q).Normal ∧ B ≤ K.map q := by
  obtain ⟨z,hz,hz2,hLS,hout,hsq,hzero,hfour,he,hcore,hD,hDtwo,hBD,hact,
    P,hP,hB,K,hK,hKn,hLK,hKq,hKnq,hBKq⟩ :=
    binary_three_source_point_quotient_opposite_action
      hG d hempty hM hu hmany hI htwo hf c e b t common earlier g hgT hgS
  obtain ⟨a,v,E,_,_,_,_,_,_,_,hvE,hE,hcard,hvout,hEq,hcardq⟩ :=
    binary_three_source_point_quotient_cubic_escape
      hG d hempty hM hu hmany hI htwo hf c e b t common earlier z hz hLS P hP g hgT hgS
  let q := QuotientGroup.mk' (pCore 2 (centralizer ({z} : Set G)))
  let := hEq
  have hrlo : 2 ≤ primeRank 3 ((centralizer ({z} : Set G)) ⧸ pCore 2 (centralizer ({z} : Set G))) :=
    IsElementaryAbelian.primeRank_ge_of_card (E.map q) hcardq
  have hrhi := hsq.stronglyQuasithin 3 (by decide) (by decide)
  refine ⟨z,hz,hz2,hLS,hout,hsq,hzero,hfour,he,hcore,hD,hDtwo,hBD,hact,
    le_antisymm hrhi hrlo,?_,⟨E,hE,hcard,hEq,hcardq,?_⟩,
    P,hP,hB,K,hK,hKn,hLK,hKq,hKnq,hBKq⟩
  · intro htop
    exact hvout (htop ▸ mem_top _)
  · intro hle
    exact hvout (hle (mem_map_of_mem q hvE))
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource
