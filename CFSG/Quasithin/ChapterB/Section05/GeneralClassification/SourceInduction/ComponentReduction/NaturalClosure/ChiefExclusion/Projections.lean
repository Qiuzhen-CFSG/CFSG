module

public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.ComponentReduction.NaturalClosure.Rank

/-!
# The actual offender projections and the equality case of (*)

Multiplication in the two distinct centerless natural components constructs
the two projections of the original offender. The kernel of the first
projection is exactly B=C_A(L). If the offender attains the sum of the two
component ranks, cardinality forces its image to fill the product of its
projections. Consequently B=A_C, A lies in L B, and B attains the second
component rank. In particular rank greater than the first component rank
already implies B is nontrivial.

The final applications use the actual natural markings and the proved
upper bound from `Rank`. They are conditional on the indicated lower rank
bounds; they do not assert the unproved representation estimates (!), (!!),
or the chief-factor contradiction.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, B.5.9,
printed p.108, inequality (*) and its equality consequences.
-/

@[expose] public section

open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
namespace CFSG.Quasithin.ChapterB.SourceInduction.ComponentReduction.NaturalClosure
open QuasisimpleSource
set_option backward.isDefEq.respectTransparency false
variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V)

/-- The actual two coordinate homomorphisms, with multiplication equal to the original inclusion. -/
structure ComponentProjections (A L M : Subgroup G) where
  left : A →* L
  right : A →* M
  multiply : ∀ a, (left a : G) * (right a : G) = (a : G)

private theorem components_disjoint {L M : Subgroup G}
    (hL : IsComponent G L) (hM : IsComponent G M) (hne : L ≠ M)
    (hz : center L = ⊥) : Disjoint L M := by
  have hc := le_centralizer_iff.mp
    (commutator_eq_bot_iff_le_centralizer.mp (hL.commutator_eq_bot_of_ne hM hne))
  apply Subgroup.disjoint_def.mpr
  intro x hx hM
  have hxc : (⟨x, hx⟩ : L) ∈ center L := by
    apply mem_center_iff.mpr
    intro l
    exact Subtype.ext (hc hM l l.property)
  have hxe : (⟨x, hx⟩ : L) = 1 := by simpa only [hz, mem_bot] using hxc
  exact congrArg Subtype.val hxe

theorem SecondComponent.disjoint {A L : Subgroup G}
    (sL : NaturalSeed ρ A L) (hL : IsComponent G L) (d : SecondComponent ρ A L) :
    Disjoint L d.second :=
  components_disjoint hL d.isComponent d.distinct (seed_center_eq_bot ρ sL)

/-- Construct the projections using the product of the two literal components. -/
noncomputable def SecondComponent.projections {A L : Subgroup G}
    (sL : NaturalSeed ρ A L) (hL : IsComponent G L) (d : SecondComponent ρ A L) :
    ComponentProjections A L d.second := by
  have h := exists_mulEquiv_prod_sup_of_disjoint_of_commuting L d.second
    (d.disjoint ρ sL hL)
    (commutator_eq_bot_iff_le_centralizer.mp (hL.commutator_eq_bot_of_ne d.isComponent d.distinct))
  let e := Classical.choose h
  let f := e.symm.toMonoidHom.comp (Subgroup.inclusion d.offender_le)
  refine ⟨(MonoidHom.fst L d.second).comp f, (MonoidHom.snd L d.second).comp f, ?_⟩
  intro a
  change ((f a).1 : G) * ((f a).2 : G) = a
  calc
    _ = (e (f a) : G) := (Classical.choose_spec h (f a).1 (f a).2).symm
    _ = a := congrArg Subtype.val (e.apply_symm_apply _)

namespace ComponentProjections
variable {A L M : Subgroup G} (p : ComponentProjections A L M)

/-- The subgroup A_L in the original ambient group. -/
noncomputable def leftImage : Subgroup G := p.left.range.map L.subtype
/-- The subgroup A_C in the original ambient group. -/
noncomputable def rightImage : Subgroup G := p.right.range.map M.subtype

theorem leftImage_le : p.leftImage ≤ L := map_subtype_le _
theorem rightImage_le : p.rightImage ≤ M := map_subtype_le _

theorem offender_le : A ≤ p.leftImage ⊔ p.rightImage := by
  intro a ha
  change ((⟨a, ha⟩ : A) : G) ∈ p.leftImage ⊔ p.rightImage
  rw [← p.multiply ⟨a, ha⟩]
  exact (p.leftImage ⊔ p.rightImage).mul_mem
    ((show p.leftImage ≤ p.leftImage ⊔ p.rightImage from le_sup_left)
      (Subgroup.mem_map_of_mem _ ⟨⟨a, ha⟩, rfl⟩))
    ((show p.rightImage ≤ p.leftImage ⊔ p.rightImage from le_sup_right)
      (Subgroup.mem_map_of_mem _ ⟨⟨a, ha⟩, rfl⟩))

theorem left_eq_one_iff (hc : L ≤ centralizer (M : Set G)) (hz : center L = ⊥)
    (a : A) : p.left a = 1 ↔ (a : G) ∈ centralizer (L : Set G) := by
  have hr : (p.right a : G) ∈ centralizer (L : Set G) :=
    (le_centralizer_iff.mp hc) (p.right a).property
  constructor
  · intro he
    have ha := p.multiply a
    rw [he, OneMemClass.coe_one, one_mul] at ha
    exact ha ▸ hr
  · intro ha
    have hl : (p.left a : G) ∈ centralizer (L : Set G) := by
      have he : (p.left a : G) = a * (p.right a : G)⁻¹ :=
        eq_mul_inv_iff_mul_eq.mpr (p.multiply a)
      rw [he]
      exact (centralizer (L : Set G)).mul_mem ha ((centralizer (L : Set G)).inv_mem hr)
    have hcenter : p.left a ∈ center L := by
      apply mem_center_iff.mpr
      intro l
      exact Subtype.ext (hl l l.property)
    simpa only [hz, mem_bot] using hcenter

theorem centralizer_eq_ker (hc : L ≤ centralizer (M : Set G)) (hz : center L = ⊥) :
    A ⊓ centralizer (L : Set G) = p.left.ker.map A.subtype := by
  ext a
  constructor
  · rintro ⟨ha, hc'⟩
    exact ⟨⟨a, ha⟩, (p.left_eq_one_iff hc hz ⟨a, ha⟩).mpr hc', rfl⟩
  · rintro ⟨a, ha, rfl⟩
    exact ⟨a.property, (p.left_eq_one_iff hc hz a).mp ha⟩

theorem centralizer_le_rightImage (hc : L ≤ centralizer (M : Set G)) (hz : center L = ⊥) :
    A ⊓ centralizer (L : Set G) ≤ p.rightImage := by
  rintro a ⟨ha, hc'⟩
  have he := p.multiply ⟨a, ha⟩
  rw [(p.left_eq_one_iff hc hz ⟨a, ha⟩).mpr hc', OneMemClass.coe_one, one_mul] at he
  change (p.right ⟨a, ha⟩ : G) = a at he
  rw [← he]
  exact Subgroup.mem_map_of_mem M.subtype ⟨⟨a, ha⟩, rfl⟩

private def intoRanges : A →* p.left.range × p.right.range :=
  p.left.rangeRestrict.prod p.right.rangeRestrict

private theorem intoRanges_injective : Function.Injective p.intoRanges := by
  intro a b hab
  apply Subtype.ext
  rw [← p.multiply a, ← p.multiply b]
  have hl := congrArg (fun x : p.left.range × p.right.range => (x.1 : G)) hab
  have hr := congrArg (fun x : p.left.range × p.right.range => (x.2 : G)) hab
  exact congrArg₂ (· * ·) hl hr

private theorem range_elementary {H K : Type*} [Group H] [Group K]
    [IsElementaryAbelian 2 H] (f : H →* K) : IsElementaryAbelian 2 f.range where
  toIsMulCommutative := inferInstance
  exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr (by
    rintro ⟨_, a, rfl⟩
    apply Subtype.ext
    change (f a) ^ 2 = 1
    rw [← map_pow, Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
      (IsElementaryAbelian.exponent_dvd_p 2 H), map_one])

/-- Maximal rank fills both projections and identifies the centralizer with A_C. -/
theorem split_of_rank_eq [Finite G] (hA : IsElementaryTwo A)
    (hc : L ≤ centralizer (M : Set G)) (hz : center L = ⊥)
    (hmax : rank A = primeRank 2 L + primeRank 2 M) :
    A ⊓ centralizer (L : Set G) = p.rightImage ∧
      A ≤ L ⊔ (A ⊓ centralizer (L : Set G)) ∧
      rank (A ⊓ centralizer (L : Set G)) = primeRank 2 M := by
  let : IsElementaryAbelian 2 A := hA.2
  have hlc : Nat.card p.left.range ≤ 2 ^ primeRank 2 L :=
    (primeRank_le_iff_elementary_card_le L).mp le_rfl p.left.range (range_elementary p.left)
  have hrc : Nat.card p.right.range ≤ 2 ^ primeRank 2 M :=
    (primeRank_le_iff_elementary_card_le M).mp le_rfl p.right.range (range_elementary p.right)
  have hcard : Nat.card (p.left.range × p.right.range) ≤ Nat.card A := by
    rw [Nat.card_prod, hA.card_eq_two_pow_rank, hmax, pow_add]
    exact Nat.mul_le_mul hlc hrc
  have hsurj : Function.Surjective p.intoRanges :=
    ((Nat.bijective_iff_injective_and_card p.intoRanges).mpr
      ⟨p.intoRanges_injective, le_antisymm
        (Nat.card_le_card_of_injective _ p.intoRanges_injective) hcard⟩).2
  have he : A ⊓ centralizer (L : Set G) = p.rightImage := by
    apply le_antisymm (p.centralizer_le_rightImage hc hz)
    rintro x ⟨y, hy, rfl⟩
    obtain ⟨a, ha⟩ := hsurj (1, ⟨y, hy⟩)
    have hl : p.left a = 1 := congrArg (fun z => (z.1 : L)) ha
    have hr : p.right a = y := congrArg (fun z => (z.2 : M)) ha
    have hval := p.multiply a
    rw [hl, OneMemClass.coe_one, one_mul, hr] at hval
    change (y : G) ∈ A ⊓ centralizer (L : Set G)
    rw [hval]
    exact ⟨a.property, (p.left_eq_one_iff hc hz a).mp hl⟩
  have hprod : Nat.card p.left.range * Nat.card p.right.range =
      2 ^ primeRank 2 L * 2 ^ primeRank 2 M := by
    calc
      _ = Nat.card A := by
        rw [← Nat.card_prod]
        exact le_antisymm hcard (Nat.card_le_card_of_injective _ p.intoRanges_injective)
      _ = _ := by rw [hA.card_eq_two_pow_rank, hmax, pow_add]
  have hright : Nat.card p.right.range = 2 ^ primeRank 2 M := by
    apply le_antisymm hrc
    have hpos : 0 < 2 ^ primeRank 2 L := pow_pos (by decide) _
    nlinarith
  refine ⟨he, he ▸ p.offender_le.trans (sup_le_sup p.leftImage_le le_rfl), ?_⟩
  rw [he, rank, rightImage, Subgroup.card_map_of_injective Subtype.val_injective,
    hright, Nat.log_pow (by decide : 1 < 2)]

include p in
theorem centralizer_ne_bot_of_rank_gt [Finite G] (hA : IsElementaryTwo A)
    (hc : L ≤ centralizer (M : Set G)) (hz : center L = ⊥)
    (hgt : primeRank 2 L < rank A) : A ⊓ centralizer (L : Set G) ≠ ⊥ := by
  intro hb
  let : IsElementaryAbelian 2 A := hA.2
  let : CommGroup A := IsMulCommutative.instCommGroup
  have hinj : Function.Injective p.left := by
    apply (MonoidHom.ker_eq_bot_iff p.left).mp
    apply bot_unique
    intro a ha
    apply Subtype.ext
    have hmem : (a : G) ∈ A ⊓ centralizer (L : Set G) :=
      ⟨a.property, (p.left_eq_one_iff hc hz a).mp ha⟩
    simpa only [hb, mem_bot, OneMemClass.coe_one] using hmem
  have hbound := primeRank_ge_of_elementary_embedding (p := 2)
    (fun a => Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
      (IsElementaryAbelian.exponent_dvd_p 2 A) a)
    hA.card_eq_two_pow_rank p.left hinj
  omega

end ComponentProjections

/-- The 4m lower bound, once proved, forces all the group equalities in (*). -/
theorem SecondComponent.split_of_rank_lower [Finite G] {A L : Subgroup G}
    (sL : NaturalSeed ρ A L) (hL : IsComponent G L) (hA : IsElementaryTwo A)
    (d : SecondComponent ρ A L) (horder : d.seed.field.degree ≤ sL.field.degree)
    (hlower : 4 * sL.field.degree ≤ rank A) :
    sL.field.degree = d.seed.field.degree ∧
      A ⊓ centralizer (L : Set G) = (d.projections ρ sL hL).rightImage ∧
      A ≤ L ⊔ (A ⊓ centralizer (L : Set G)) ∧
      rank (A ⊓ centralizer (L : Set G)) = 2 * sL.field.degree := by
  have hu := d.rank_bound ρ sL hL hA
  have he : sL.field.degree = d.seed.field.degree := by omega
  have hrank : rank A = primeRank 2 L + primeRank 2 d.second := by
    rw [seed_two_rank ρ sL, seed_two_rank ρ d.seed]
    omega
  have hsplit := (d.projections ρ sL hL).split_of_rank_eq hA
    (commutator_eq_bot_iff_le_centralizer.mp (hL.commutator_eq_bot_of_ne d.isComponent d.distinct))
    (seed_center_eq_bot ρ sL) hrank
  rw [seed_two_rank ρ d.seed, ← he] at hsplit
  exact ⟨he, hsplit⟩

/-- The rank consequence of (!) with c>2 implies the source B is nontrivial. -/
theorem SecondComponent.centralizer_ne_bot_of_rank_gt [Finite G] {A L : Subgroup G}
    (sL : NaturalSeed ρ A L) (hL : IsComponent G L) (hA : IsElementaryTwo A)
    (d : SecondComponent ρ A L) (hgt : 2 * sL.field.degree < rank A) :
    A ⊓ centralizer (L : Set G) ≠ ⊥ := by
  apply (d.projections ρ sL hL).centralizer_ne_bot_of_rank_gt hA
    (commutator_eq_bot_iff_le_centralizer.mp (hL.commutator_eq_bot_of_ne d.isComponent d.distinct))
    (seed_center_eq_bot ρ sL)
  rwa [seed_two_rank ρ sL]

end CFSG.Quasithin.ChapterB.SourceInduction.ComponentReduction.NaturalClosure
