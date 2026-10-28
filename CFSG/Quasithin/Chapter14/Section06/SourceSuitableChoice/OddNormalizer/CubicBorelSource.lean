module
public import CFSG.Quasithin.Chapter14.Section06.SourceSuitableChoice.OddNormalizer.Closure.Models.SixteenSource
public import Theory.SpecificGroups.PSL2.SixteenCubicBorel
public import Theory.GroupTheory.SolvableSylowControl.Product
public import Theory.SpecificGroups.PSL2.SixteenWreathComponents
public import CFSG.Quasithin.Chapter14.Section06.SourcePrimitiveOddResidual

/-!
# The actual cubic Borel in the remaining PSL₂(16) square

Take the normalizer of the original Sylow intersection with the marked
normal square in Mc/O₂(Mc), and lift it to Mc. Solvable Sylow control in
the two factors makes the original H normalize this Borel. Its cubic
residual X is two-perfect with elementary two-core quotient of order nine;
14.6.1(4) makes XT an outside subgroup for the unchanged T and M.

Minimal descent inside XT gives a primitive cubic outside subgroup J.
The index-nine bound excludes the quintic alternative. The order-nine
residual conclusion of earlier 14.6.12 then identifies J with XT. Thus
primitivity is constructed by descent, rather than inferred from the
order-nine quotient alone. An actual Sylow three-subgroup P of X is
also elementary of order nine and satisfies PT = XT.

The original 14.6.12 exchanged factors and index remain an explicit input,
produced by qt-e-14612-singleton. Comparing their action with the marked
cubic detector, and final 14.6.14 assembly, remain with this theorem family.
The literal suitable-involution application is in CubicBorelChoice.

Source: Aschbacher--Smith 14.6.12 and 14.6.14, printed pp.1031--1033.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section06.OddNormalizer
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
open Chapter15.Section03.AbelianAmalgam
open Chapter15.Section03.AbelianAmalgam.GenerationOne
local notation "F16" => GaloisField 2 4
local notation "L16" => Matrix.ProjectiveSpecialLinearGroup (Fin 2) F16

private theorem sixteen_solvable_control : SolvableSylowControl 2 L16 := by
  have hc : Nat.card F16 = 16 := GaloisField.card 2 4 (by decide)
  let : IsSimpleGroup L16 := Matrix.ProjectiveSpecialLinearGroup.rank_two_simple (by omega)
  let : Group.IsPerfect L16 := Theory.PSL2.SixteenWreathComponents.perfect
  apply SolvableSylowControl.of_proper_overgroups
  · exact Group.IsPerfect.not_isSolvable L16
  · intro P A hPA hA
    exact (ChapterF.Source.rankOneSylowFacts_psl2 F16 4 (by decide) hc P).unique_maximal A hPA hA

variable {G : Type*} [Group G] [Finite G]

/-- The full preimage of the Borel at the original Sylow intersection
with the marked normal square. Both ambient quotient maps are literal. -/
@[expose] def squareBorelPreimage (T Mc : Subgroup G)
    (K : Subgroup (Mc ⧸ pCore 2 Mc)) : Subgroup G :=
  let q := QuotientGroup.mk' (pCore 2 Mc)
  ((K ⊓ normalizer ((((T.subgroupOf Mc).map q) ⊓ K : Subgroup (Mc ⧸ pCore 2 Mc)) : Set _)).comap q).map Mc.subtype

/-- Construct the Borel at the original Sylow intersection and lift its
actual torus quotient through the ambient two-core. -/
theorem sixteen_borel_lift
    (T : Sylow 2 G) {H Mc : Subgroup G} (hTH : (T : Subgroup G) ≤ H)
    (hHMc : H ≤ Mc) (hs : Group.IsSolvable H)
    (K : Subgroup (Mc ⧸ pCore 2 Mc)) [K.Normal] (k : K ≃* L16 × L16) :
    ∃ B : Subgroup G, B = squareBorelPreimage (T : Subgroup G) Mc K ∧
      B ≤ Mc ∧ H ≤ normalizer (B : Set G) ∧
      Nonempty ((B ⧸ pCore 2 B) ≃* F16ˣ × F16ˣ) := by
  let q := QuotientGroup.mk' (pCore 2 Mc)
  let S := (T.subtype (hTH.trans hHMc)).mapSurjective (QuotientGroup.mk'_surjective (pCore 2 Mc))
  let A := (H.subgroupOf Mc).map q
  let := hs
  let : Group.IsSolvable (H.subgroupOf Mc) := Group.isSolvable_of_isSolvable_injective
    (f := (subgroupOfEquivOfLe hHMc).toMonoidHom) (subgroupOfEquivOfLe hHMc).injective
  let : Group.IsSolvable A := Group.isSolvable_of_surjective (q.subgroupMap_surjective _)
  have hSA : (S : Subgroup (Mc ⧸ pCore 2 Mc)) ≤ A := map_mono (subgroupOf_mono Mc hTH)
  obtain ⟨P,hP⟩ := S.exists_subgroupOf_eq_of_normal K
  let U := (P : Subgroup K).map K.subtype
  have hU : U = (S : Subgroup (Mc ⧸ pCore 2 Mc)) ⊓ K := by
    rw [show U = ((S : Subgroup (Mc ⧸ pCore 2 Mc)).subgroupOf K).map K.subtype by rw [←hP],
      subgroupOf_map_subtype]
  have hUS : U ≤ (S : Subgroup (Mc ⧸ pCore 2 Mc)) := by
    rw [show U = ((S : Subgroup (Mc ⧸ pCore 2 Mc)).subgroupOf K).map K.subtype by rw [←hP],
      subgroupOf_map_subtype]
    exact inf_le_left
  have hctl : SolvableSylowControl 2 K := SolvableSylowControl.of_equiv k
    (sixteen_solvable_control.prod sixteen_solvable_control)
  have hAU : A ≤ normalizer (U : Set (Mc ⧸ pCore 2 Mc)) :=
    hctl.normalizes_sylow K A P le_normalizer_of_normal (hUS.trans hSA)
  let D := (normalizer (P : Set K)).map K.subtype
  have hD : D = K ⊓ normalizer (U : Set (Mc ⧸ pCore 2 Mc)) := by
    have hu : U.subgroupOf K = (P : Subgroup K) :=
      comap_map_eq_self_of_injective K.subtype_injective _
    rw [show D = (normalizer (U.subgroupOf K : Set K)).map K.subtype by rw [hu]; rfl,
      ←subgroupOf_normalizer_eq (map_subtype_le _),subgroupOf_map_subtype,inf_comm]
  have hAD : A ≤ normalizer (D : Set (Mc ⧸ pCore 2 Mc)) := by
    rw [hD]
    exact (le_inf le_normalizer_of_normal (hAU.trans (normalizer _).le_normalizer)).trans
      inf_normalizer_le_normalizer_inf
  let P' := P.mapSurjective (f := k.toMonoidHom) k.surjective
  have hn : (normalizer (P : Set K)).map k.toMonoidHom = normalizer (P' : Set (L16 × L16)) :=
    map_normalizer_eq_of_bijective _ k.bijective
  let d : D ≃* normalizer (P' : Set (L16 × L16)) :=
    (equivMapOfInjective _ K.subtype K.subtype_injective).symm.trans
      ((k.subgroupMap _).trans (MulEquiv.subgroupCongr hn))
  let dt := (QuotientGroup.congr _ _ d (pCore_map_iso 2 d)).trans
    (Theory.PSL2.SixteenCubicBorel.sylowBorelQuotientEquiv F16
      (GaloisField.card 2 4 (by decide)) P')
  let B0 := D.comap q
  let B := B0.map Mc.subtype
  have hBN : H ≤ normalizer (B : Set G) := by
    have hh : H.subgroupOf Mc ≤ normalizer (B0 : Set Mc) := by
      rw [←comap_normalizer_eq_of_surjective D (QuotientGroup.mk'_surjective _)]
      exact map_le_iff_le_comap.mp hAD
    have hm := (map_mono (f := Mc.subtype) hh).trans (le_normalizer_map Mc.subtype)
    rwa [map_subgroupOf_eq_of_le hHMc] at hm
  let f : B0 →* D := (q.comp B0.subtype).codRestrict D (fun x => x.property)
  have hf : Function.Surjective f := by
    intro x
    obtain ⟨b,hb⟩ := QuotientGroup.mk'_surjective (pCore 2 Mc) x.val
    exact ⟨⟨b,show q b ∈ D from hb.symm ▸ x.property⟩,Subtype.ext hb⟩
  have hk : IsPGroup 2 f.ker := by
    have he : f.ker = (pCore 2 Mc).comap B0.subtype := by
      ext x
      exact Subtype.ext_iff.trans (QuotientGroup.eq_one_iff _)
    rw [he]
    exact pCore_isPGroup.comap_subtype
  let b := equivMapOfInjective B0 Mc.subtype Mc.subtype_injective
  have hB : B = squareBorelPreimage (T : Subgroup G) Mc K := by
    dsimp only [B,B0,squareBorelPreimage]
    rw [hD,hU]
    rfl
  exact ⟨B,hB,map_subtype_le _,hBN,⟨(QuotientGroup.congr _ _ b (pCore_map_iso 2 b)).symm.trans
    ((f.pCoreQuotientEquiv hf hk).trans dt)⟩⟩

variable (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (hab : IsMulCommutative (conjugateSpanBy (localModule T M) Mc))
    (H : Subgroup G) (hH : H ∈ Chapter1.HOutside G (T : Set G) (M : Set G))
include hG hempty hM hu hmany hcard e hab hH

/-- The literal cubic Borel residual gives an outside subgroup with the
same T and M; its quotient is elementary nine, with no primitivity assertion. -/
theorem source_sixteen_cubic_outside
    (hs : Group.IsSolvable H)
    (K : Subgroup (Mc ⧸ pCore 2 Mc)) [K.Normal] (k : K ≃* L16 × L16) :
    ∃ B X : Subgroup G, B = squareBorelPreimage (T : Subgroup G) Mc K ∧
      B ≤ Mc ∧ H ≤ normalizer (B : Set G) ∧
      Nonempty ((B ⧸ pCore 2 B) ≃* F16ˣ × F16ˣ) ∧
      X = (primeToResidual 3 B).map B.subtype ∧
      X ≤ B ∧ (T : Subgroup G) ≤ normalizer (X : Set G) ∧ IsPPerfect 2 X ∧
      IsElementaryAbelian 3 (X ⧸ pCore 2 X) ∧ Nat.card (X ⧸ pCore 2 X) = 9 ∧
      X ⊔ (T : Subgroup G) ∈ Chapter1.HOutside G (T : Set G) (M : Set G) := by
  have hHMc : H ≤ Mc :=
    (source_rankTwo_f9_hypothesis hG T hempty hM hu hmany hcard e hab H hH).H_centralizes.trans
      (InitialSource.centralizer_le_partner T hu)
  have hTMc : (T : Subgroup G) ≤ Mc := (show (T : Subgroup G) ≤ H from hH.1.2).trans hHMc
  obtain ⟨B,hBdef,hBMc,hHB,⟨b⟩⟩ := sixteen_borel_lift T hH.1.2 hHMc hs K k
  let X := (primeToResidual 3 B).map B.subtype
  have hXB : X ≤ B := map_subtype_le _
  have hBX : B ≤ normalizer (X : Set G) := B.le_normalizer.trans
    (normalizer_le_normalizer_characteristic_image B (primeToResidual 3 B))
  have hHX : H ≤ normalizer (X : Set G) := hHB.trans
    (normalizer_le_normalizer_characteristic_image B (primeToResidual 3 B))
  have hp : IsPPerfect 2 X := (isPPerfect_primeToResidual 3 2 (by decide)).of_surjective
    (B.subtype.subgroupMap _) (B.subtype.subgroupMap_surjective _)
  let x := equivMapOfInjective (primeToResidual 3 B) B.subtype B.subtype_injective
  let q := (QuotientGroup.congr _ _ x (pCore_map_iso 2 x)).symm.trans
    (Theory.PSL2.SixteenCubicBorel.cubicResidualQuotientEquiv F16
      (GaloisField.card 2 4 (by decide)) b)
  let : IsElementaryAbelian 3 (rootsOfUnity 3 F16 × rootsOfUnity 3 F16) := {
    exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr (fun x =>
      Prod.ext (Subtype.ext x.1.property) (Subtype.ext x.2.property)) }
  have he : IsElementaryAbelian 3 (X ⧸ pCore 2 X) :=
    IsElementaryAbelian.of_surjective q.symm.toMonoidHom q.symm.surjective
  have hc : Nat.card (X ⧸ pCore 2 X) = 9 := by
    rw [Nat.card_congr q.toEquiv,Nat.card_prod,
      FiniteField.CubicSixteen.roots_card F16 (GaloisField.card 2 4 (by decide))]
  have hne : X ≠ ⊥ := by
    intro hz
    rw [hz] at hc
    have hh : Nat.card ((⊥ : Subgroup G) ⧸ pCore 2 (⊥ : Subgroup G)) = 1 :=
      Nat.card_unique
    omega
  let J := B ⊔ H
  have hJMc : J ≤ Mc := sup_le hBMc hHMc
  have hTJ : (T : Subgroup G) ≤ J := (show (T : Subgroup G) ≤ H from hH.1.2).trans le_sup_right
  have hMcMax : IsMaximalTwoLocal Mc :=
    (show Mc ∈ maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) from
      hu ▸ Set.mem_singleton Mc).1
  have hMcH := Chapter1.mem_H_of_isTwoLocal hMcMax.1
  have hQMcT : Mc.pCoreIn 2 ≤ (T : Subgroup G) := by
    simpa only [Sylow.coe_subtype,map_subgroupOf_eq_of_le hTMc] using
      pCoreIn_le_sylow Mc (T.subtype hTMc)
  have hQJ : Mc.pCoreIn 2 ≤ J.pCoreIn 2 := le_pCoreIn_of_normalizes
    (isPGroup_pCoreIn 2 Mc) (hQMcT.trans hTJ)
    (hJMc.trans (Mc.le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image Mc (pCore 2 Mc))))
  have hJ : J ∈ Chapter1.HOutside G (T : Set G) (M : Set G) :=
    ⟨⟨(fun hz => hMcH (bot_unique (hz ▸ hQJ))),hTJ⟩,
      fun hh => hH.2 ((show H ≤ J from le_sup_right).trans hh)⟩
  exact ⟨B,X,hBdef,hBMc,hHB,⟨b⟩,rfl,hXB,hH.1.2.trans hHX,hp,he,hc,
    source_lemma_14_6_1_4 hG T hempty hM hu hmany hcard e hab J hJ X
      (hXB.trans le_sup_left) (sup_le hBX hHX) hp hne⟩

omit hG hempty hM hu hmany hcard e hab hH in
/-- The auxiliary cubic Borel join has the original Sylow at index nine. -/
theorem cubic_borel_join_index
    (X : Subgroup G) (hn : (T : Subgroup G) ≤ normalizer (X : Set G))
    (hc : Nat.card (X ⧸ pCore 2 X) = 9) :
    (T : Subgroup G).relIndex (X ⊔ (T : Subgroup G)) = 9 := by
  have hQT : X.pCoreIn 2 ≤ (T : Subgroup G) := by
    have hnQ := hn.trans (normalizer_le_normalizer_characteristic_image X (pCore 2 X))
    exact sup_eq_left.mp (T.is_maximal'
      (T.isPGroup'.to_sup_of_normal_right' (isPGroup_pCoreIn 2 X) hnQ) le_sup_left)
  have he : (T : Subgroup G).subgroupOf X = pCore 2 X := by
    apply le_antisymm
    · let q := QuotientGroup.mk' (pCore 2 X)
      have hp : IsPGroup 3 (X ⧸ pCore 2 X) := IsPGroup.of_card (n := 2) hc
      have hd := IsPGroup.disjoint_of_coprime
        ((T.isPGroup'.comap_subtype (K := X)).map q) (hp.to_subgroup ⊤)
        (by decide : Nat.Coprime 2 3)
      have hz : ((T : Subgroup G).subgroupOf X).map q = ⊥ := by
        simpa only [disjoint_top, subgroupOf] using hd
      simpa only [q, QuotientGroup.ker_mk'] using
        (map_eq_bot_iff ((T : Subgroup G).subgroupOf X)).mp hz
    · intro x hx
      exact hQT (mem_map_of_mem X.subtype hx)
  rw [relIndex_sup_of_normalizes X (T : Subgroup G) hn]
  change ((T : Subgroup G).subgroupOf X).index = 9
  rw [he]
  exact hc

omit hH in
/-- Minimal descent inside the actual cubic outside subgroup constructs a
primitive cubic residual. This uses no 14.6.15 conclusion or assumed index-two
factor join. Earlier 14.6.12 is applied to this selected subgroup. -/
theorem source_cubic_borel_primitive_subgroup
    (X : Subgroup G) (hn : (T : Subgroup G) ≤ normalizer (X : Set G))
    (he : IsElementaryAbelian 3 (X ⧸ pCore 2 X))
    (hc : Nat.card (X ⧸ pCore 2 X) = 9)
    (hout : X ⊔ (T : Subgroup G) ∈ Chapter1.HOutside G (T : Set G) (M : Set G)) :
    ∃ J : Subgroup G, J ≤ X ⊔ (T : Subgroup G) ∧
      J ∈ Chapter3.HStar (T : Subgroup G) M ∧ Group.IsSolvable J ∧
      PrimitiveResidual J 3 ∧ pResidual 2 (J ⧸ pCore 2 J) ≠ ⊥ := by
  let C := X ⊔ (T : Subgroup G)
  let := he
  let : Group.IsNilpotent (X ⧸ pCore 2 X) :=
    (IsElementaryAbelian.isPGroup 3 _).isNilpotent
  let : Group.IsNilpotent (pCore 2 X) := pCore_isPGroup.isNilpotent
  let : Group.IsSolvable X := (Group.isSolvable_iff_subgroup_quotient (pCore 2 X)).mpr
    ⟨inferInstance,inferInstance⟩
  let : Group.IsNilpotent (T : Subgroup G) := T.isPGroup'.isNilpotent
  let : Group.IsSolvable C := Group.isSolvable_sup_of_normalizes X (T : Subgroup G) hn
  have hi := cubic_borel_join_index T X hn hc
  have hcop : Nat.Coprime 5 (Nat.card C) := by
    have hh := ((T : Subgroup G).subgroupOf C).card_mul_index
    rw [Nat.card_congr (subgroupOfEquivOfLe (show (T : Subgroup G) ≤ C from le_sup_right)).toEquiv] at hh
    change Nat.card (T : Subgroup G) * (T : Subgroup G).relIndex C = Nat.card C at hh
    rw [hi] at hh
    obtain ⟨n,hn⟩ := T.isPGroup'.exists_card_eq
    rw [←hh,hn]
    exact ((by decide : Nat.Coprime 5 2).pow_right n).mul_right (by decide)
  obtain ⟨J,hJ,hJC,hmin⟩ := exists_minimal_subgroup_of_mem_le
    (fun J => J ∈ Chapter1.HOutside G (T : Set G) (M : Set G)) C hout
  have hstar : J ∈ Chapter3.HStar (T : Subgroup G) M :=
    ⟨hJ,fun K hK hKJ => (hmin K hK hKJ).ge⟩
  have hs : Group.IsSolvable J := Group.isSolvable_of_isSolvable_injective (inclusion_injective hJC)
  obtain ⟨p,hp,hE,_hr,hne,hprimitive⟩ := source_solvable_minimal_elementary_residual
    hG T hempty hM hu hmany hcard e hab J hstar hs
  rcases hp with rfl | rfl
  · exact ⟨J,hJC,hstar,hs,⟨hE,hprimitive⟩,hne⟩
  · let := hE
    have hd : 5 ∣ Nat.card (pResidual 2 (J ⧸ pCore 2 J)) :=
      (IsElementaryAbelian.isPGroup 5 _).card_eq_or_dvd.resolve_left
        (fun h => hne ((eq_bot_iff_card _).mpr h))
    have hdJ : 5 ∣ Nat.card J := hd.trans
      ((pResidual 2 (J ⧸ pCore 2 J)).card_subgroup_dvd_card.trans (pCore 2 J).index_dvd_card)
    exact False.elim ((by decide : Nat.Prime 5).coprime_iff_not_dvd.mp hcop
      (hdJ.trans (card_dvd_of_le hJC)))


omit hG hempty hM hu hmany hcard e hab hH in
/-- A Sylow cubic of the constructed residual is an actual elementary nine
subgroup and has the same join with the original T. -/
theorem cubic_borel_sylow_join
    (X : Subgroup G) (hn : (T : Subgroup G) ≤ normalizer (X : Set G))
    (he : IsElementaryAbelian 3 (X ⧸ pCore 2 X))
    (hc : Nat.card (X ⧸ pCore 2 X) = 9) (P : Sylow 3 X) :
    Nat.card P = 9 ∧ IsElementaryAbelian 3 P ∧
      ((P : Subgroup X).map X.subtype) ⊔ (T : Subgroup G) = X ⊔ (T : Subgroup G) := by
  let q := QuotientGroup.mk' (pCore 2 X)
  let := he
  have h3 : IsPGroup 3 (X ⧸ pCore 2 X) := IsElementaryAbelian.isPGroup 3 _
  have hPQ : (P : Subgroup X).map q = ⊤ :=
    ((P.mapSurjective (QuotientGroup.mk'_surjective _)).is_maximal'
      (h3.to_subgroup ⊤) le_top).symm
  let f := q.comp (P : Subgroup X).subtype
  have hf : Function.Surjective f := by
    intro y
    obtain ⟨x,hx,hxy⟩ := (hPQ.symm ▸ mem_top y : y ∈ (P : Subgroup X).map q)
    exact ⟨⟨x,hx⟩,hxy⟩
  have hi : Function.Injective f := by
    apply (MonoidHom.ker_eq_bot_iff _).mp
    apply bot_unique
    intro x hx
    apply Subtype.ext
    exact disjoint_def.mp (IsPGroup.disjoint_of_coprime P.isPGroup' pCore_isPGroup
      (by decide : Nat.Coprime 3 2)) x.property ((QuotientGroup.eq_one_iff _).mp hx)
  let eqP := MulEquiv.ofBijective f ⟨hi,hf⟩
  have hQT : X.pCoreIn 2 ≤ (T : Subgroup G) := by
    have hnQ := hn.trans (normalizer_le_normalizer_characteristic_image X (pCore 2 X))
    exact sup_eq_left.mp (T.is_maximal'
      (T.isPGroup'.to_sup_of_normal_right' (isPGroup_pCoreIn 2 X) hnQ) le_sup_left)
  have hgen : (P : Subgroup X) ⊔ pCore 2 X = ⊤ := by
    have hh := congrArg (comap q) hPQ
    simpa only [comap_map_eq,q,QuotientGroup.ker_mk',comap_top] using hh
  have hX : ((P : Subgroup X).map X.subtype) ⊔ X.pCoreIn 2 = X := by
    simpa only [Subgroup.map_sup,pCoreIn,←MonoidHom.range_eq_map,range_subtype] using congrArg (map X.subtype) hgen
  refine ⟨(Nat.card_congr eqP.toEquiv).trans hc,
    IsElementaryAbelian.of_surjective eqP.symm.toMonoidHom eqP.symm.surjective,?_⟩
  apply le_antisymm (sup_le ((map_subtype_le _).trans le_sup_left) le_sup_right)
  apply sup_le _ le_sup_right
  exact (le_of_eq hX.symm).trans (sup_le le_sup_left (hQT.trans le_sup_right))

omit hG hempty hM hu hmany hcard e hab hH [Finite G] in
/-- A Sylow subgroup of the cubic residual is a Sylow subgroup of the
full Borel: every cubic subgroup of the latter lies in its cubic residual. -/
theorem cubic_borel_sylowIn_borel
    (B X : Subgroup G) (hX : X = (primeToResidual 3 B).map B.subtype)
    (R : Sylow 3 X) :
    Chapter1.IsSylowIn 3 ((R : Subgroup X).map X.subtype) B := by
  have hXB : X ≤ B := hX ▸ map_subtype_le _
  have hPX : Chapter1.IsSylowIn 3 ((R : Subgroup X).map X.subtype) X := ⟨R,rfl⟩
  apply Chapter1.isSylowIn_iff.mpr
  refine ⟨R.isPGroup'.map X.subtype,(map_subtype_le _).trans hXB,?_⟩
  intro Y hY hPY hYB
  have hYX : Y ≤ X := by
    rw [hX]
    calc
      Y = (Y.subgroupOf B).map B.subtype := (map_subgroupOf_eq_of_le hYB).symm
      _ ≤ (primeToResidual 3 B).map B.subtype :=
        map_mono (le_primeToResidual_of_isPGroup hY.comap_subtype)
  exact (Chapter1.isSylowIn_iff.mp hPX).2.2 Y hY hPY hYX

/-- Concrete auxiliary cubic Borel and its primitive outside subgroup.
The original T,M,Mc,H are parameters, and the selected subgroup is contained
in the constructed join, whose Sylow index is exactly nine. -/
@[expose] def CubicBorelOutside (T M Mc H Kz : Subgroup G) : Prop :=
  ∃ B X P J : Subgroup G,
    B = squareBorelPreimage T Mc ((Kz.subgroupOf Mc).map (QuotientGroup.mk' (pCore 2 Mc))) ∧
    B ≤ Mc ∧ H ≤ normalizer (B : Set G) ∧
    Nonempty ((B ⧸ pCore 2 B) ≃* F16ˣ × F16ˣ) ∧
    X = (primeToResidual 3 B).map B.subtype ∧ X ≤ B ∧ X ≤ Kz ∧
    T ≤ normalizer (X : Set G) ∧ IsPPerfect 2 X ∧
    IsElementaryAbelian 3 (X ⧸ pCore 2 X) ∧ Nat.card (X ⧸ pCore 2 X) = 9 ∧
    X ⊔ T ∈ Chapter1.HOutside G (T : Set G) (M : Set G) ∧
    T.relIndex (X ⊔ T) = 9 ∧ P ≤ X ∧ Chapter1.IsSylowIn 3 P B ∧
    Nat.card P = 9 ∧ IsElementaryAbelian 3 P ∧
    P ⊔ T = X ⊔ T ∧ J ≤ X ⊔ T ∧ J ∈ Chapter3.HStar T M ∧ Group.IsSolvable J ∧
    PrimitiveResidual J 3 ∧ pResidual 2 (J ⧸ pCore 2 J) ≠ ⊥

/-- Apply the Borel construction and primitive descent to the actual
remaining marked PSL₂(16) square. No full outer image is assumed. -/
theorem source_small_sixteen_cubic_borel
    (hprim : PrimitiveResidual H 5) (Kz L : Subgroup G) (s : Mc)
    (hr3 : Kz = (primeToResidual 3 Mc).map Mc.subtype)
    (hlayer : StrictClosureLayer Mc Kz) (hsmall : SmallSixteenCubicImage Mc Kz L s) :
    CubicBorelOutside (T : Subgroup G) M Mc H Kz := by
  let K := (Kz.subgroupOf Mc).map (QuotientGroup.mk' (pCore 2 Mc))
  let : K.Normal := by
    change ((Kz.subgroupOf Mc).map (QuotientGroup.mk' (pCore 2 Mc))).Normal
    rw [hlayer.image_eq_generalizedFitting]
    infer_instance
  obtain ⟨_,k,_⟩ := hsmall
  obtain ⟨B,X,hBdef,hB,hHB,hmodel,hX,hXB,hn,hp,he,hc,hout⟩ :=
    source_sixteen_cubic_outside hG T hempty hM hu hmany hcard e hab H hH
      (primitiveResidual_isSolvable H hprim) K k
  obtain ⟨J,hJX,hJ,hs,hprim,hne⟩ := source_cubic_borel_primitive_subgroup
    hG T hempty hM hu hmany hcard e hab X hn he hc hout
  have hXK : X ≤ Kz := by
    rw [hX,hr3]
    exact embedded_primeToResidual_mono 3 hB
  let R : Sylow 3 X := default
  obtain ⟨hRc,hRe,hRT⟩ := cubic_borel_sylow_join T X hn he hc R
  let P := (R : Subgroup X).map X.subtype
  have hPc : Nat.card P = 9 := by rw [card_map_of_injective X.subtype_injective,hRc]
  have hPe : IsElementaryAbelian 3 P := by
    let := hRe
    exact IsElementaryAbelian.of_surjective (X.subtype.subgroupMap _)
      (X.subtype.subgroupMap_surjective _)
  exact ⟨B,X,P,J,hBdef,hB,hHB,hmodel,hX,hXB,hXK,hn,hp,he,hc,hout,
    cubic_borel_join_index T X hn hc,map_subtype_le _,
    cubic_borel_sylowIn_borel B X hX R,hPc,hPe,hRT,hJX,hJ,hs,hprim,hne⟩

omit hG hempty hM hu hmany hcard e hab hH in
/-- The order-nine residual supplied by earlier 14.6.12 makes the selected
outside subgroup the entire cubic Borel join. The proof uses only the original
Sylow index and Lagrange's theorem, not the later prime-three conclusion. -/
theorem cubic_borel_eq_of_residual_card
    (X J : Subgroup G) (hn : (T : Subgroup G) ≤ normalizer (X : Set G))
    (hc : Nat.card (X ⧸ pCore 2 X) = 9)
    (hTJ : (T : Subgroup G) ≤ J) (hJC : J ≤ X ⊔ (T : Subgroup G))
    (hR : Nat.card (pResidual 2 (J ⧸ pCore 2 J)) = 9) :
    J = X ⊔ (T : Subgroup G) := by
  have hi := cubic_borel_join_index T X hn hc
  have hdiv : 9 ∣ Nat.card J := by
    rw [←hR]
    exact (pResidual 2 (J ⧸ pCore 2 J)).card_subgroup_dvd_card.trans
      (pCore 2 J).index_dvd_card
  have hmul := ((T : Subgroup G).subgroupOf J).card_mul_index
  rw [Nat.card_congr (subgroupOfEquivOfLe hTJ).toEquiv] at hmul
  change Nat.card (T : Subgroup G) * (T : Subgroup G).relIndex J = Nat.card J at hmul
  have hcop : Nat.Coprime 9 (Nat.card (T : Subgroup G)) := by
    obtain ⟨n,hn⟩ := T.isPGroup'.exists_card_eq
    rw [hn]
    exact (by decide : Nat.Coprime 9 2).pow_right n
  have hd : 9 ∣ (T : Subgroup G).relIndex J :=
    hcop.dvd_of_dvd_mul_left (hmul.symm ▸ hdiv)
  have he := relIndex_mul_relIndex (T : Subgroup G) J
    (X ⊔ (T : Subgroup G)) hTJ hJC
  rw [hi] at he
  have hij : (T : Subgroup G).relIndex J = 9 :=
    Nat.dvd_antisymm (dvd_of_mul_right_eq _ he) hd
  rw [hij] at he
  exact le_antisymm hJC (relIndex_eq_one.mp (by omega))

omit hG hempty hM hu hmany hcard e hab hH in
/-- Applying the earlier exchanged-factor contract to the primitive subgroup
identifies the very subgroup to which the book applies 14.6.12. -/
theorem cubic_borel_eq_of_exchanged_factors
    (X J U Z : Subgroup G) [IsElementaryAbelian 2 U]
    (a : LocalQuotientAction J U Z) (J0 J1 J2 : Subgroup G)
    (d : ExchangedFactorSetup a (T : Subgroup G) 3 J0 J1 J2)
    (hn : (T : Subgroup G) ≤ normalizer (X : Set G))
    (hc : Nat.card (X ⧸ pCore 2 X) = 9)
    (hJ : J ∈ Chapter3.HStar (T : Subgroup G) M)
    (hJC : J ≤ X ⊔ (T : Subgroup G)) : J = X ⊔ (T : Subgroup G) :=
  cubic_borel_eq_of_residual_card T X J hn hc hJ.1.1.2 hJC d.residual_card

end CFSG.Quasithin.Chapter14.Section06.OddNormalizer
