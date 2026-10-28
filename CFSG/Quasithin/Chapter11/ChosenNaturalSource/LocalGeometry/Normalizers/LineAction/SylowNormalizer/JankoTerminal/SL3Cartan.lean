module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.LineAction.SylowNormalizer.JankoTerminal.SL3Radicals
public import Theory.GroupTheory.PResidual.NormalizedSupplement
public import Theory.SpecificGroups.PSL2.BinaryAutomorphismOrder
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.LineAction.SylowNormalizer.FlagNormalizers

/-!
# The actual odd Cartan in the SL₃ terminal configuration

The intersection of the original odd Sylow supplement with L is a source
Cartan. At field order four its torus description gives order nine and
exponent three. Its action on the literal Lᵢ/O₂(Lᵢ) quotient cannot be faithful,
since the automorphism group has order dividing 120. Thus the original odd
section centralizer is nontrivial. SL3Terminal uses its cubic scalar action
to construct a nontrivial subgroup normalized by L and the J₁ component.

Source: Aschbacher--Smith 3.3.16, printed p.591.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Subgroup Representation Matrix Matrix.PSL3
open scoped MatrixGroups commutatorElement Pointwise
open CFSG.Quasithin.Chapter12.Section02 CFSG.Quasithin.ChapterB.QuasisimpleSource
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.SylowNormalizer.SL3Terminal
open PointCohomology.PointGeometry.SL3Core
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)
  (m : ActionEquiv D.centralQuotientAction (linearNatural S.field 3))
  (a : SL(3, S.field.Carrier))

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
theorem intersection_isCartan {f : InvariantFlag (Coordinates.sl3 m)}
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
theorem intersection_cube {f : InvariantFlag (Coordinates.sl3 m)}
    {A : OddSupplement T} (E : JankoConfiguration S f A) (x : (A.subgroup ⊓ L : Subgroup G)) :
    x ^ 3 = 1 := by
  let e := (Coordinates.sl3 m).cartanTorusEquiv (intersection_isCartan D S m E)
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
theorem section_ne_bot {f : InvariantFlag (Coordinates.sl3 m)}
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
    rw [(Coordinates.sl3 m).cartan_card (intersection_isCartan D S m E),E.degree_eq_two]
    rfl
  have he := MulAut.congr (SL3.flagLocalCoreEquiv S m f E.index)
  rw [hB,Nat.card_congr he.toEquiv] at hd
  have hF : Nat.card S.field.Carrier = 2 ^ 2 := by rw [S.field.card_eq,E.degree_eq_two]
  have ha := Theory.PSL2.BinaryAutomorphismOrder.aut_card_dvd hF
  have hh := hd.trans ha
  norm_num at hh

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.SylowNormalizer.SL3Terminal
