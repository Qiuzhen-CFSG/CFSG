module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.CentralHall.Branches
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.CentralHall.LinearThree.Residual
public import Theory.GroupTheory.ConjugateOrbitIndexTwo
public import Theory.GroupTheory.CComponent.SimplePairProduct
public import Theory.GroupTheory.AutomorphismSquareOuterTwo

/-!
# Placement of the literal faithful linear-three Hall actor

The original two C-components identify L₀/O₂(L₀) with SL₃(2)².
The inner and outer automorphism calculations restrict the prime support
of its automorphisms to {2,3,7}. Faithfulness and odd order then restrict B
to {3,7}, whereas the cubic and seven-residual identities make M/L₀ prime
to both. Thus the same Hall subgroup, through its original subtype map,
lies in L₀.

Source: Aschbacher--Smith, 10.1.3 and case (ii) of the proof of10.2.3,
printed pp.742 and745. No normalizer or point-control conclusion is assumed.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter10.CentralHall.LinearThree
open Chapter3.Section02
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)

include D in
/-- The model is an isomorphism of the literal orbit two-core quotient. -/
theorem quotient_equiv
    (e : (L ⧸ pCore 2 L) ≃* Matrix.PSL3Two.SL)
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G)) :
    Nonempty ((localOrbit T L ⧸ pCore 2 (localOrbit T L)) ≃*
      (Matrix.PSL3Two.SL × Matrix.PSL3Two.SL)) := by
  obtain ⟨t,ht,htn⟩ := Set.not_subset.mp hn
  let R := localOrbit T L
  have hLR : L ≤ R := le_componentOrbit L T
  have hRt : R.map (MulAut.conj t).toMonoidHom = R :=
    mem_normalizer_iff_map_conj_eq.mp (le_normalizer_componentOrbit L T ht)
  let τ : MulAut R := ((MulAut.conj t).subgroupMap R).trans (MulEquiv.subgroupCongr hRt)
  let A := L.subgroupOf R
  let B := A.map τ.toMonoidHom
  have hA : A.IsCComponent :=
    D.maximal.1.1.subgroupOf_of_le hLR (componentOrbit_le_sup L T)
  have hB : B.IsCComponent := hA.map_equiv τ
  have hmapA : A.map R.subtype = L := map_subgroupOf_eq_of_le hLR
  have hmapB : B.map R.subtype = L.map (MulAut.conj t).toMonoidHom := by
    rw [show B = A.map τ.toMonoidHom from rfl,map_map,
      show R.subtype.comp τ.toMonoidHom =
        (MulAut.conj t).toMonoidHom.comp R.subtype from rfl,←map_map,hmapA]
  have hne : A ≠ B := by
    intro he
    apply htn
    apply mem_normalizer_iff_map_conj_eq.mpr
    exact hmapB.symm.trans ((congrArg (map R.subtype) he).symm.trans hmapA)
  have hp : L ⊔ L.map (MulAut.conj t).toMonoidHom = R :=
    (componentOrbit_eq_sup_of_index_two L T (normalizer (L : Set G))
      (source_nonnormal_sylow_stabilizer_index D.simpleQTKE D.maximal.1 hn)
      inf_le_right ht htn).symm
  have hgen : A ⊔ B = ⊤ := by
    apply map_injective R.subtype_injective
    rw [Subgroup.map_sup,hmapA,hmapB,←MonoidHom.range_eq_map,range_subtype,hp]
  let a : A ≃* L := subgroupOfEquivOfLe hLR
  let eA := (QuotientGroup.congr _ _ a (pCore_map_iso 2 a)).trans e
  let b : A ≃* B := τ.subgroupMap A
  let eB := (QuotientGroup.congr _ _ b.symm (pCore_map_iso 2 b.symm)).trans eA
  let : IsSimpleGroup Matrix.PSL3Two.PSL := Atlas.Comparisons.Exceptional.psl3Two_simple
  let : IsSimpleGroup Matrix.PSL3Two.SL := Matrix.PSL3Two.equiv.isSimpleGroup
  obtain ⟨q,hq,hk,_,_⟩ :=
    exists_twoCore_product_of_simple_pair A B hA hB hne hgen eA eB
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hk.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective q hq)⟩

private theorem pair_automorphism_isPGroup [IsQuasisimple Matrix.PSL3Two.SL] :
    IsPGroup 42 (MulAut (Matrix.PSL3Two.SL × Matrix.PSL3Two.SL)) := by
  let A := Matrix.PSL3Two.SL × Matrix.PSL3Two.SL
  let : IsSimpleGroup Matrix.PSL3Two.PSL := Atlas.Comparisons.Exceptional.psl3Two_simple
  let : IsSimpleGroup Matrix.PSL3Two.SL := Matrix.PSL3Two.equiv.isSimpleGroup
  have ha : IsPGroup 42 A := IsPGroup.of_card_dvd_pow (n := 6) (by
    dsimp [A]
    rw [Nat.card_prod, Matrix.PSL3Two.card_SL]
    norm_num)
  have hi : IsPGroup 42 (MulAut.innerSubgroup A) :=
    ha.of_surjective MulAut.conj.rangeRestrict MulAut.conj.rangeRestrict_surjective
  have ho : IsPGroup 42 (MulAut.Outer A) :=
    (AutomorphismSquare.outer_isPGroup_two Matrix.PSL3Two.center_eq_bot
      Matrix.PSL3Two.Automorphisms.outer_sl_isTwoGroup).mono (by decide)
  have hk : IsPGroup 42 (QuotientGroup.mk' (MulAut.innerSubgroup A)).ker := by
    rw [QuotientGroup.ker_mk']
    exact hi
  have hh := (ho.to_subgroup ⊤).comap_of_ker_isPGroup
    (QuotientGroup.mk' (MulAut.innerSubgroup A)) hk
  simpa using hh.of_equiv Subgroup.topEquiv

/-- The source Hall assumption supplies odd order on the actual carrier B. -/
theorem hall_odd {H : Subgroup G} {B : Subgroup H} (c : Context D H B) :
    Odd (Nat.card B) := by
  apply Nat.not_even_iff_odd.mp
  intro he
  apply c.hall.p_in_pi_of_p_dvd_card ⟨2,Nat.prime_two⟩ _ rfl
  rw [Nat.card_congr (subgroupOfEquivOfLe c.hall_le).toEquiv]
  exact even_iff_two_dvd.mp he

/-- Case(ii) in10.2.3: the original faithful Hall actor lies in L₀. -/
theorem hall_le_orbit {H : Subgroup G} {B : Subgroup H} (c : Context D H B)
    (e : (L ⧸ pCore 2 L) ≃* Matrix.PSL3Two.SL) :
    B.map H.subtype ≤ localOrbit T L := by
  let R := localOrbit T L
  let M := D.maximalLocal
  let C := B.map H.subtype
  have hCM : C ≤ M := map_le_iff_le_comap.mpr c.hall_le
  obtain ⟨eqR⟩ := quotient_equiv D e c.nonnormal
  let := D.quasisimple
  let : IsQuasisimple Matrix.PSL3Two.SL := IsQuasisimple.of_mulEquiv e
  have hAut : IsPGroup 42 (MulAut (R ⧸ pCore 2 R)) :=
    pair_automorphism_isPGroup.of_equiv (MulAut.congr eqR).symm
  have hB42 : IsPGroup 42 B := hAut.of_injective
    (action D B c.hall_le) (action_injective D B c.hall_le c.faithful)
  obtain ⟨n,hcard⟩ := hB42.exists_card_dvd_pow
  have hcard21 : Nat.card B ∣ 21 ^ n := by
    have hh : Nat.card B ∣ 2 ^ n * 21 ^ n := by
      simpa only [←mul_pow, show 2 * 21 = 42 by decide] using hcard
    exact ((hall_odd D c).coprime_two_right.pow_right n).dvd_of_dvd_mul_left hh
  let N := R.subgroupOf M
  let CM := C.subgroupOf M
  let : N.Normal := normal_subgroupOf_of_le_normalizer
    (show M ≤ normalizer (R : Set G) from le_rfl)
  have hc3 : Nat.Coprime 3 N.index := by
    have he : N = primeToResidual 3 M := by
      apply map_injective M.subtype_injective
      rw [map_subgroupOf_eq_of_le R.le_normalizer,
        source_nonnormal_cubic_residual D c.nonnormal]
      rw [Nat.card_congr e.toEquiv,Matrix.PSL3Two.card_SL]
      norm_num
    rw [he]
    exact primeToResidual_index_coprime 3
  have hc7 : Nat.Coprime 7 N.index :=
    source_linearThree_orbit_index_coprime_seven D e c.nonnormal
  have hc21 : Nat.Coprime 21 N.index := by
    simpa only [show 3 * 7 = 21 by decide] using hc3.mul_left hc7
  have hcCM : Nat.card CM ∣ 21 ^ n := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hCM).toEquiv]
    simpa only [C,card_map_of_injective H.subtype_injective] using hcard21
  have hcop : Nat.Coprime N.index (Nat.card CM) :=
    (hc21.pow_left n).symm.coprime_dvd_right hcCM
  have hle : CM ≤ N := relIndex_eq_one.mp
    (Nat.eq_one_of_dvd_coprimes hcop (N.relIndex_dvd_index_of_normal CM)
      (N.relIndex_dvd_card CM))
  intro b hb
  exact hle (show (⟨b,hCM hb⟩ : M) ∈ CM from hb)

end CFSG.Quasithin.Chapter10.CentralHall.LinearThree
