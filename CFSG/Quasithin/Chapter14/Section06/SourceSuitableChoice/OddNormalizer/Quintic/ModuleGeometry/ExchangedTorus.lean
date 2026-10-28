module
public import CFSG.Quasithin.Chapter14.Section06.SourceSuitableChoice.OddNormalizer.Quintic.ModuleGeometry.ExchangedBorel
public import Theory.SpecificGroups.SL2.SolvableSylowTorus

/-!
# Quintic torus quotients of the actual component intersections

Restrict the binary SL₂ Borel diagonal map to K ∩ H and transport through
its actual two-core quotient. This gives an injective homomorphism to
GF(16)ˣ, so the quotient order divides fifteen. The original H/O₂(H)
has order two hundred and O₂(H) is a two-group. Coprimality then makes
the same quotient order divide five.

These calculations retain the original component and quotient, and remove
the torus-order premise in ExchangedActors. The component-support alignment
and final quintic exclusion remain with qt-e-14615-quintic-exclusion;
the permitted earlier 14.6.12--14 inputs are unchanged.
Source: Aschbacher--Smith 14.6.15, printed pp.1033--1034.
-/

public section
open Subgroup Theory.GroupTheory Representation.BinaryOffender
open scoped IsMulCommutative MatrixGroups
namespace CFSG.Quasithin.Chapter14.Section06.OddNormalizer.Quintic.ModuleGeometry
open Chapter15.Section03.AbelianAmalgam Chapter15.Section03.AbelianAmalgam.GenerationOne
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
open ComponentExclusion
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc H H0 H1 H2 : Subgroup G}
    [IsElementaryAbelian 2 (conjugateSpanBy (localModule T M) H)]
    {a : LocalQuotientAction H (conjugateSpanBy (localModule T M) H) (centralInvolutions T)}
    (s : Context T M Mc H H0 H1 H2 a)

include s in
/-- The actual intersection core quotient has its literal Borel torus embedding. -/
theorem source_exchanged_intersection_torus_embedding {K : Subgroup G}
    (hKM : K ≤ Mc) (hK : (K.subgroupOf Mc).IsCComponent)
    (em : Nonempty ((K ⧸ pCore 2 K) ≃* Theory.PSL2.SixteenWreathComponents.L)) :
    ∃ f : ((K ⊓ H : Subgroup G) ⧸ pCore 2 (K ⊓ H : Subgroup G)) →*
      (GaloisField 2 4)ˣ, Function.Injective f := by
  have hTM : (T : Subgroup G) ≤ Mc := by
    rw [partner_eq_centralizer s]
    exact le_centralizer_iff.mp (centralInvolutions_le_centralizer_sylow T)
  let eK := subgroupOfEquivOfLe hKM
  obtain ⟨R,hR⟩ := (T.subtype hTM).exists_subgroupOf_eq_of_subnormal
    (K.subgroupOf Mc) hK.subnormal
  let P : Sylow 2 K := R.mapSurjective (f := eK.toMonoidHom) eK.surjective
  have hP : (P : Subgroup K) = (T : Subgroup G).subgroupOf K := by
    ext x
    constructor
    · rintro ⟨y,hy,rfl⟩
      rw [hR] at hy
      exact hy
    · intro hx
      refine ⟨eK.symm x,?_,eK.apply_symm_apply x⟩
      rw [hR]
      exact hx
  let e := em.some.trans (Atlas.RankOneFieldAutomorphisms.slEquivPSL
    (F := GaloisField 2 4)).symm
  let q := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 K))
  have hq : Function.Surjective q := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hk : IsPGroup 2 q.ker := by
    rw [MonoidHom.ker_comp_of_injective _ e.toMonoidHom e.injective,QuotientGroup.ker_mk']
    exact pCore_isPGroup
  have hns : ¬ Group.IsSolvable SL(2,GaloisField 2 4) := by
    let := Theory.PSL2.SixteenWreathComponents.perfect
    let := Theory.PSL2.SixteenWreathComponents.simple
    intro hs
    let := hs
    exact Group.IsPerfect.not_isSolvable Theory.PSL2.SixteenWreathComponents.L
      (Group.isSolvable_of_surjective
        (f := (Atlas.RankOneFieldAutomorphisms.slEquivPSL (F := GaloisField 2 4)).toMonoidHom)
        (Atlas.RankOneFieldAutomorphisms.slEquivPSL (F := GaloisField 2 4)).surjective)
  let B := H.subgroupOf K
  let : Group.IsSolvable H := source_quintic_outside_solvable s
  let i : B →* H := (K.subtype.comp B.subtype).codRestrict H (fun x => x.property)
  let : Group.IsSolvable B := Group.isSolvable_of_isSolvable_injective (f := i) (by
    intro x y he
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun z : H => (z : G)) he)
  have hPB : (P : Subgroup K) ≤ B := by
    rw [hP]
    exact fun x hx => s.outside.1.2 hx
  obtain ⟨f,hf⟩ := Matrix.SpecialLinearGroup.solvable_sylow_overgroup_torus_embedding
    q hq hk hns P B hPB
  have hm : B.map K.subtype = K ⊓ H := by
    rw [subgroupOf_map_subtype,inf_comm]
  let eB : B ≃* (K ⊓ H : Subgroup G) :=
    (B.equivMapOfInjective K.subtype K.subtype_injective).trans (MulEquiv.subgroupCongr hm)
  let eQ := QuotientGroup.congr _ _ eB (pCore_map_iso 2 eB)
  exact ⟨f.comp eQ.symm.toMonoidHom,hf.comp eQ.symm.injective⟩

include s in
/-- The original exchanged-factor order removes the cubic torus divisor. -/
theorem source_exchanged_intersection_quotient_card_dvd_five {K : Subgroup G}
    (hKM : K ≤ Mc) (hK : (K.subgroupOf Mc).IsCComponent)
    (em : Nonempty ((K ⧸ pCore 2 K) ≃* Theory.PSL2.SixteenWreathComponents.L)) :
    Nat.card ((K ⊓ H : Subgroup G) ⧸ pCore 2 (K ⊓ H : Subgroup G)) ∣ 5 := by
  let B := K ⊓ H
  let d := Nat.card (B ⧸ pCore 2 B)
  obtain ⟨f,hf⟩ := source_exchanged_intersection_torus_embedding s hKM hK em
  have hd15 : d ∣ 15 := by
    have hd := card_dvd_of_injective f hf
    rwa [Nat.card_units,GaloisField.card 2 4 (by decide)] at hd
  have hdH : d ∣ Nat.card H :=
    (card_quotient_dvd_card (pCore 2 B)).trans (card_dvd_of_le (show B ≤ H from inf_le_right))
  obtain ⟨n,hn⟩ := (pCore_isPGroup (p := 2) (G := H)).exists_card_eq
  have hc : Nat.card H = 2^n * 200 := by
    rw [←(pCore 2 H).card_mul_index,index_eq_card,hn,
      OddCriticalPair.exchanged_actor_card a (T : Subgroup G) 5 H0 H1 H2 s.factors]
    norm_num
  have hd200 : d ∣ 200 := by
    rw [hc] at hdH
    exact (((by decide : Nat.Coprime 15 2).of_dvd_left hd15).pow_right n).dvd_of_dvd_mul_left hdH
  exact Nat.dvd_gcd hd15 hd200

include s in
/-- Apply the order restriction to both of the actual exchanged components. -/
theorem source_exchanged_borel_quotient_orders
    (b : ExchangedFactorData (T : Subgroup G) Mc H (centralInvolutions T)) :
    (Nat.card ((b.K1 ⊓ H : Subgroup G) ⧸ pCore 2 (b.K1 ⊓ H : Subgroup G)) = 1 ∨
      Nat.card ((b.K1 ⊓ H : Subgroup G) ⧸ pCore 2 (b.K1 ⊓ H : Subgroup G)) = 5) ∧
    (Nat.card ((b.K2 ⊓ H : Subgroup G) ⧸ pCore 2 (b.K2 ⊓ H : Subgroup G)) = 1 ∨
      Nat.card ((b.K2 ⊓ H : Subgroup G) ⧸ pCore 2 (b.K2 ⊓ H : Subgroup G)) = 5) := by
  exact ⟨(Nat.dvd_prime (by decide)).mp
      (source_exchanged_intersection_quotient_card_dvd_five s b.first_le b.first_component b.first_model),
    (Nat.dvd_prime (by decide)).mp
      (source_exchanged_intersection_quotient_card_dvd_five s b.second_le b.second_component b.second_model)⟩

end CFSG.Quasithin.Chapter14.Section06.OddNormalizer.Quintic.ModuleGeometry
