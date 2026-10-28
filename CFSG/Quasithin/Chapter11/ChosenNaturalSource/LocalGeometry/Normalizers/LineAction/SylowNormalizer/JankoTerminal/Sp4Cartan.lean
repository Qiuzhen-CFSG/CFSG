module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.LineAction.SylowNormalizer.JankoTerminal.Sp4Radicals
public import Theory.SpecificGroups.PSL2.BinaryAutomorphismOrder
public import Theory.GroupTheory.PResidual.NormalizedSupplement
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.LineAction.SylowNormalizer.FlagNormalizers

/-!
# The odd Cartan and nontrivial displacement in the Sp₄ configuration

The actual intersection A ∩ L is a source Cartan once the inner local
Sylow action removes the outer factor. Its order nine and exponent three
follow from the original torus marking. The local PSL₂(4) automorphism
order excludes a faithful action of this Cartan, so X is nontrivial.
Characteristic two then proves [X,T] is nontrivial.

The companion Sp4Movement module uses these results to show that the
residual moves [X,T] and to complete the terminal argument from shortness.
Source: Aschbacher--Smith 3.3.16, printed p.591.
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Subgroup Representation Matrix
open scoped commutatorElement IsMulCommutative Pointwise
open Theory.SpecificGroups.SymplecticFour DiagramAutomorphisms
open CFSG.Quasithin.Chapter12.Section02 CFSG.Quasithin.ChapterB.QuasisimpleSource
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.SylowNormalizer.Sp4Terminal
open PointCohomology.PointGeometry.Sp4Core
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)
  (m : ActionEquiv D.centralQuotientAction
    (restrictScalars (k := ZMod 2) (symplecticNatural (k := S.field.Carrier) 2)))

omit [Finite G] in
include D in
private theorem odd_intersection_le (A : OddSupplement T) :
    A.subgroup ⊓ (L ⊔ (T : Subgroup G)) ≤ L := by
  let B := A.subgroup ⊓ (L ⊔ (T : Subgroup G))
  have ho : Odd (Nat.card B) := A.odd.of_dvd_nat (card_dvd_of_le inf_le_left)
  have hp : IsPPerfect 2 B := by
    apply (pResidual_eq_top_iff 2 B).mp
    apply top_unique
    intro x _
    exact mem_pResidual_of_orderOf_coprime
      ((Nat.coprime_two_left.mpr ho).of_dvd_right (orderOf_dvd_natCard x))
  exact le_of_isPPerfect_of_le_sup_of_normalizes B L (T : Subgroup G)
    hp T.isPGroup' D.sylow_normalizes_component inf_le_right

/-- The intersection with the original odd Sylow supplement is a full source Cartan. -/
theorem intersection_isCartan {f : InvariantFlag (Coordinates.sp4 m)}
    {A : OddSupplement T} (E : JankoConfiguration S f A) :
    IsCartan T L (A.subgroup ⊓ L) := by
  have ht := sourceTL_eq_sylow D S m E
  let H := cartanNormalizer T L
  let B := (A.subgroup ⊓ L).subgroupOf H
  let P := (T : Subgroup G).subgroupOf H
  have hBH : A.subgroup ⊓ L ≤ H := by
    intro x hx
    refine ⟨hx.2,?_⟩
    change x ∈ normalizer (sourceTL T L : Set G)
    rw [ht]
    exact A.normalizes hx.1
  have hcomp : P.IsComplement' B := by
    apply isComplement'_of_disjoint_and_mul_eq_univ
    · apply disjoint_def.mpr
      intro x hxP hxB
      apply Subtype.ext
      exact mem_bot.mp (A.disjoint.eq_bot ▸ (show x.val ∈ (T : Subgroup G) ⊓ A.subgroup from
        ⟨hxP,hxB.1⟩))
    · apply Set.eq_univ_of_forall
      intro x
      have hxN : x.val ∈ normalizer (T : Set G) := by
        have h := x.property.2
        change x.val ∈ normalizer (sourceTL T L : Set G) at h
        rwa [ht] at h
      have hxprod : x.val ∈ ((T : Subgroup G) : Set G) * (A.subgroup : Set G) := by
        rw [← coe_mul_of_right_le_normalizer_left _ _ A.normalizes,A.generate]
        exact hxN
      obtain ⟨t,htT,b,hbA,he⟩ := hxprod
      have hbJ : b ∈ L ⊔ (T : Subgroup G) := by
        have hh := (L ⊔ (T : Subgroup G)).mul_mem (mem_sup_right (T.inv_mem htT))
          (mem_sup_left x.property.1)
        rw [←he,inv_mul_cancel_left] at hh
        exact hh
      have hbL : b ∈ L := odd_intersection_le D A ⟨hbA,hbJ⟩
      have hbH : b ∈ H := hBH ⟨hbA,hbL⟩
      have htH : t ∈ H := by
        have hh := H.mul_mem x.property (H.inv_mem hbH)
        rw [←he,mul_inv_cancel_right] at hh
        exact hh
      exact ⟨⟨t,htH⟩,htT,⟨b,hbH⟩,⟨hbA,hbL⟩,Subtype.ext he⟩
  refine ⟨hBH,?_,?_⟩
  · intro p hp he
    have ho : Odd (Nat.card B) := by
      rw [Nat.card_congr (subgroupOfEquivOfLe hBH).toEquiv]
      exact A.odd.of_dvd_nat (card_dvd_of_le inf_le_left)
    exact ho.not_two_dvd_nat (by simpa only [he] using hp)
  · intro p hp hpodd
    have hP : IsPGroup 2 P := T.isPGroup'.comap_subtype
    obtain ⟨n,hn⟩ := hP.exists_card_eq
    exact hpodd (Nat.prime_eq_prime_of_dvd_pow p.property Nat.prime_two
      (by rwa [hcomp.index_eq_card,hn] at hp))

/-- The full actual Cartan has exponent three at the exceptional field order. -/
theorem intersection_cube {f : InvariantFlag (Coordinates.sp4 m)}
    {A : OddSupplement T} (E : JankoConfiguration S f A) (x : (A.subgroup ⊓ L : Subgroup G)) :
    x ^ 3 = 1 := by
  let e := (Coordinates.sp4 m).cartanTorusEquiv (intersection_isCartan D S m E)
  have hc : Nat.card S.field.Carrierˣ = 3 := by
    rw [Nat.card_units,S.field.card_eq,E.degree_eq_two]
    rfl
  apply e.injective
  rw [map_pow,map_one]
  apply Prod.ext
  · change (MonoidHom.fst S.field.Carrierˣ S.field.Carrierˣ) (e x ^ 3) = 1
    rw [map_pow]
    simpa only [hc] using pow_card_eq_one' (x := (MonoidHom.fst S.field.Carrierˣ S.field.Carrierˣ) (e x))
  · change (MonoidHom.snd S.field.Carrierˣ S.field.Carrierˣ) (e x ^ 3) = 1
    rw [map_pow]
    simpa only [hc] using pow_card_eq_one' (x := (MonoidHom.snd S.field.Carrierˣ S.field.Carrierˣ) (e x))

/-- Order nine in the actual Cartan forces a nontrivial section centralizer. -/
theorem section_ne_bot {f : InvariantFlag (Coordinates.sp4 m)}
    {A : OddSupplement T} (E : JankoConfiguration S f A) :
    E.oddSectionCentralizer ≠ ⊥ := by
  let B := A.subgroup ⊓ L
  have hodd : Odd (Nat.card B) := A.odd.of_dvd_nat (card_dvd_of_le inf_le_left)
  have hn : B ≤ normalizer (f.Li E.index : Set G) :=
    odd_normalizes_flag_residual f B hodd (inf_le_left.trans A.normalizes)
      (inf_le_right.trans L.le_normalizer) E.index
  let b := (coreQuotientAction (f.Li E.index)).comp (inclusion hn)
  intro hz
  have hb : Function.Injective b := by
    apply (MonoidHom.ker_eq_bot_iff b).mp
    apply _root_.eq_bot_iff.mpr
    intro x hx
    apply Subtype.ext
    apply mem_bot.mp
    rw [←hz]
    exact ⟨x.property,inclusion hn x,hx,rfl⟩
  have hd := Subgroup.card_dvd_of_injective b hb
  have hB : Nat.card B = 9 := by
    rw [(Coordinates.sp4 m).cartan_card (intersection_isCartan D S m E),E.degree_eq_two]
    rfl
  have hs : f.space = (Sp4.flag m S).space := funext fun j =>
    Sp4.flag_unique m S j (f.space j) (f.dimension j) (f.invariant j)
  have hinj : Function.Injective (InvariantFlag.space (c := Coordinates.sp4 m)) := by
    rintro ⟨s,ds,ns,is⟩ ⟨t,dt,nt,it⟩ h
    cases h
    rfl
  have hf : f = Sp4.flag m S := hinj hs
  have hq : Nonempty ((f.Li E.index ⧸ pCore 2 (f.Li E.index)) ≃*
      Matrix.ProjectiveSpecialLinearGroup (Fin 2) S.field.Carrier) := by
    exact hf.symm ▸ (show Nonempty (((Sp4.flag m S).Li E.index ⧸
      pCore 2 ((Sp4.flag m S).Li E.index)) ≃*
        Matrix.ProjectiveSpecialLinearGroup (Fin 2) S.field.Carrier) from
      ⟨Sp4.flag_Li_quotientEquiv m S S.nonbinary E.index⟩)
  have he := MulAut.congr hq.some
  rw [hB,Nat.card_congr he.toEquiv] at hd
  have hF : Nat.card S.field.Carrier = 2 ^ 2 := by rw [S.field.card_eq,E.degree_eq_two]
  have ha := Theory.PSL2.BinaryAutomorphismOrder.aut_card_dvd hF
  have hh := hd.trans ha
  norm_num at hh

/-- The actual odd section centralizer moves T before the stronger residual movement step. -/
theorem displacement_nontrivial {f : InvariantFlag (Coordinates.sp4 m)}
    {A : OddSupplement T} (E : JankoConfiguration S f A) : E.displacement ≠ ⊥ :=
  E.displacement_ne_bot (section_ne_bot D S m E)

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.SylowNormalizer.Sp4Terminal
