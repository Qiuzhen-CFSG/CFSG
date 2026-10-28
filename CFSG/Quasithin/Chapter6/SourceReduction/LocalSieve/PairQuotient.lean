module

public import CFSG.Quasithin.Chapter6.SourceReduction.LocalSieve.Pairs
public import Theory.GroupTheory.CComponent.SimplePairQuotient
public import Theory.GroupTheory.NormalSubgroupCoreQuotient
public import Theory.SpecificGroups.SL2.CardFourEquiv

/-!
# The whole quotient of an exchanged A₅ seed

Restrict the original seed and its Sylow mover to H. The two components
generate O²(H), and the quotient by O₂(H) preserves both components and
their exchanger. Their simple images commute and intersect trivially,
so multiplication gives the internal direct product. The normal-subgroup
core formula identifies that product with O²(H)/O₂(O²(H)).

The resulting A₅ × A₅ model concerns the whole residual. It does not
replace this product by the A₅ model of either seed, or exclude the moved
branch. Both actual factor embeddings are retained for that exclusion.

Source: Aschbacher--Smith, 5.1.10(1), 5.1.12(2) and the paired case of
5.1.13, printed pp.634--636.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.LocalSieve
variable {G : Type*} [Group G] [Finite G]

/-- Both source factors survive modulo O₂(H), with their original mover and multiplication map. -/
theorem moved_seed_quotient_pair {T : Sylow 2 G} {K H : Subgroup G}
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hKH : K ≤ H) (hTH : (T : Subgroup G) ≤ H)
    (hH : H ∈ Chapter1.H G) (hK : (K.subgroupOf H).IsCComponent)
    (horbit : componentOrbit K (T : Subgroup G) = residual H)
    (hmoved : K ≠ residual H)
    (hlinear : ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 2 4) :
    ∃ t : H, (t : G) ∈ (T : Subgroup G) ∧
      let q := QuotientGroup.mk' (pCore 2 H)
      let C := (K.subgroupOf H).map q
      IsComponent (H ⧸ pCore 2 H) C ∧
      Nonempty (C ≃* alternatingGroup (Fin 5)) ∧
      (pResidual 2 H).map q = C ⊔ C.conjBy (q t) ∧
      Disjoint C (C.conjBy (q t)) ∧ ⁅C,C.conjBy (q t)⁆ = ⊥ ∧
      q t ∉ normalizer (C : Set (H ⧸ pCore 2 H)) ∧
      ∃ e : C × C.conjBy (q t) ≃* (pResidual 2 H).map q,
        ∀ a b, (e (a,b) : H ⧸ pCore 2 H) = (a : H ⧸ pCore 2 H) * b := by
  obtain ⟨t,ht,hne,hpair,_,_⟩ := moved_seed_pair hG hKH hTH hH hK horbit hmoved
  let A := K.subgroupOf H
  let s : H := ⟨t,hTH ht⟩
  have hA : A.map H.subtype = K := map_subgroupOf_eq_of_le hKH
  have hconj : (A.conjBy s).map H.subtype = K.conjBy t := by
    change (A.map (MulAut.conj s).toMonoidHom).map H.subtype =
      K.map (MulAut.conj t).toMonoidHom
    rw [Subgroup.map_map, ←hA, Subgroup.map_map]
    rfl
  have hpairH : A ⊔ A.conjBy s = pResidual 2 H := by
    apply map_injective H.subtype_injective
    rw [Subgroup.map_sup,hA,hconj]
    exact hpair.symm
  have hneH : A ≠ A.conjBy s := by
    intro he
    have hh := congrArg (map H.subtype) he
    rw [hA,hconj] at hh
    exact hne hh.symm
  let : (A ⊔ A.conjBy s).Normal := by rw [hpairH]; infer_instance
  obtain ⟨F,_,_,hF,⟨eF⟩⟩ := hlinear
  let eK := eF.trans
    (Matrix.ProjectiveSpecialLinearGroup.equiv_alternatingGroup_of_card_four hF).some
  let eA : (A ⧸ pCore 2 A) ≃* alternatingGroup (Fin 5) :=
    (QuotientGroup.congr _ _ (subgroupOfEquivOfLe hKH)
      (pCore_map_iso 2 (subgroupOfEquivOfLe hKH))).trans eK
  let : IsSimpleGroup (A ⧸ pCore 2 A) := eA.isSimpleGroup
  have hdiv : 2 ∣ Nat.card (A ⧸ pCore 2 A) := by
    rw [Nat.card_congr eA.toEquiv,nat_card_alternatingGroup]
    norm_num [Nat.factorial]
  obtain ⟨hc,_,_,_,hec,_,_,hdis,hcomm,_,hout,e,he⟩ :=
    simpleCore_pair_quotient_structure A hK s hneH hdiv
  let q := QuotientGroup.mk' (pCore 2 H)
  let C := A.map q
  have hp : (pResidual 2 H).map q = C ⊔ C.conjBy (q s) := by
    rw [←hpairH,Subgroup.map_sup,hec]
  refine ⟨s,ht,hc,⟨(cComponentTwoCoreQuotientEquiv hK).symm.trans eA⟩,
    hp,hdis,hcomm,hout,e.trans (MulEquiv.subgroupCongr hp.symm),?_⟩
  exact he

/-- In the moved branch the whole residual quotient is A₅ × A₅. -/
theorem moved_seed_residual_quotient {T : Sylow 2 G} {K H : Subgroup G}
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hKH : K ≤ H) (hTH : (T : Subgroup G) ≤ H)
    (hH : H ∈ Chapter1.H G) (hK : (K.subgroupOf H).IsCComponent)
    (horbit : componentOrbit K (T : Subgroup G) = residual H)
    (hmoved : K ≠ residual H)
    (hlinear : ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 2 4) :
    Nonempty (((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) ≃*
      (alternatingGroup (Fin 5) × alternatingGroup (Fin 5))) := by
  obtain ⟨t,_,_,⟨eA⟩,_,_,_,_,e,_⟩ :=
    moved_seed_quotient_pair hG hKH hTH hH hK horbit hmoved hlinear
  let q := QuotientGroup.mk' (pCore 2 H)
  let C := (K.subgroupOf H).map q
  let ec := C.equivMapOfInjective (MulAut.conj (q t)).toMonoidHom
    (MulAut.conj (q t)).injective
  exact ⟨(coreQuotientEquivImage 2 (pResidual 2 H)).trans
    (e.symm.trans (eA.prodCongr (ec.symm.trans eA)))⟩

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.LocalSieve
