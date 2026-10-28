module
public import Theory.Representation.InvertedOddSupportRank

/-!
# Inverted odd support on an invariant subgroup

Restricting the action and mapping back along the subgroup inclusion preserves
its displacement exactly. For an inverted odd element, the support order is
the square of the involution displacement on that support. Thus a nontrivial
odd action on a subspace with one involution displacement dimension has
support order four, without a faithfulness hypothesis on the restriction.
An inverted cubic is also trivial on every stable subspace fixed pointwise
by its inverting involution.

These are the restriction steps used in Aschbacher--Smith D.2.25,
*The Classification of Quasithin Groups*, printed p.190.
-/

public section
open scoped IsMulCommutative
namespace ActionSupport
variable {G V : Type*} [Group G] [Group V] [MulDistribMulAction G V]

/-- On a stable support fixed by the involution, an inverted cubic is trivial. -/
theorem inverted_cubic_fixes_fixed_support
    (t x : G) (ht : IsInvolution t) (hx : x^3=1)
    (hinv : t*x*t⁻¹=x⁻¹) (U : Subgroup V)
    (hxU : ∀ v ∈ U, x • v ∈ U)
    (htU : ∀ v ∈ U, t • v = v) :
    ∀ v ∈ U, x • v = v := by
  intro v hv
  have hti : t⁻¹=t := inv_eq_of_mul_eq_one_right (by simpa only [pow_two] using ht.2)
  have he : x⁻¹ • v = x • v := by
    rw [←hinv,mul_smul,mul_smul,hti,htU v hv,htU (x • v) (hxU v hv)]
  have htwo : x • (x • v)=v := by
    rw [←he,smul_inv_smul]
  calc
    x • v = x • (x • (x • v)) := by rw [htwo]
    _ = v := by
      simp only [←mul_smul]
      have hxxx : x*x*x=1 := by simpa only [pow_succ,pow_zero,one_mul] using hx
      rw [←mul_assoc,hxxx,one_smul]

/-- Restriction to an invariant subgroup preserves the literal ambient
commutator and its cardinality. -/
theorem commutator_restriction_map (W : Subgroup V) [IsInvariant G V W]
    (A : Subgroup G) :
    (commutatorAction A W).map W.subtype = commutatorSubgroup A V W := by
  rw [commutatorAction_eq_closure,MonoidHom.map_closure,commutatorSubgroup]
  congr 1
  ext v
  constructor
  · rintro ⟨_,⟨a,w,rfl⟩,rfl⟩
    exact ⟨a,w,w.property,rfl⟩
  · rintro ⟨a,w,hw,rfl⟩
    exact ⟨_,⟨a,(⟨w,hw⟩:W),rfl⟩,rfl⟩

theorem commutator_restriction_card (W : Subgroup V) [IsInvariant G V W]
    (A : Subgroup G) :
    Nat.card (commutatorAction A W) = Nat.card (commutatorSubgroup A V W) := by
  rw [←commutator_restriction_map W A,Subgroup.card_map_of_injective W.subtype_injective]

variable [Finite G] [Finite V] [IsElementaryAbelian 2 V]

/-- On an invariant subspace with one involution displacement dimension,
a nontrivial inverted odd element has support of order four. Faithfulness of
the restricted action is unnecessary. -/
theorem inverted_support_card_four_on_restriction (W : Subgroup V) [IsInvariant G V W]
    (t x : G) (ht : IsInvolution t) (hx : Odd (orderOf x))
    (hinv : t*x*t⁻¹=x⁻¹)
    (hline : Nat.card (commutatorSubgroup (Subgroup.zpowers t) V W)=2)
    (hmove : ∃w∈W,x • w ≠ w) :
    Nat.card (commutatorSubgroup (Subgroup.zpowers x) V W)=4 := by
  let _ : IsElementaryAbelian 2 W := {
    exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr fun w =>
      Subtype.ext (Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
        (IsElementaryAbelian.exponent_dvd_p 2 V) (w:V)) }
  have hline' : Nat.card (commutatorAction (Subgroup.zpowers t) W)=2 :=
    (commutator_restriction_card W _).trans hline
  have hi : ∀ a∈Subgroup.zpowers x,t*a*t⁻¹=a⁻¹ := by
    rintro a ⟨n,rfl⟩
    rw [←conj_zpow,hinv,inv_zpow]
  obtain ⟨hsq,_,hle⟩ := invertedOddSubgroup_support_card_data
    (W:=W) (Subgroup.zpowers x) (by simpa only [Nat.card_zpowers] using hx) t ht hi
  have hb := Subgroup.card_le_of_le hle
  rw [hline'] at hb
  let E := commutatorSubgroup (Subgroup.zpowers t) W (commutatorAction (Subgroup.zpowers x) W)
  have hE : Nat.card E=2 := by
    have hp : 0<Nat.card E := Nat.card_pos
    have hn : Nat.card E≠1 := by
      intro he
      change Nat.card (commutatorAction (Subgroup.zpowers x) W)=Nat.card E^2 at hsq
      rw [he,one_pow] at hsq
      have hbot := Subgroup.card_eq_one.mp hsq
      obtain ⟨w,hw,hm⟩ := hmove
      have hd : (⟨w,hw⟩:W)⁻¹ * (x • (⟨w,hw⟩:W)) ∈
          commutatorAction (Subgroup.zpowers x) W := by
        rw [commutatorAction_eq_closure]
        exact Subgroup.subset_closure ⟨⟨x,Subgroup.mem_zpowers x⟩,(⟨w,hw⟩:W),rfl⟩
      rw [hbot] at hd
      have heq := congrArg Subtype.val (inv_mul_eq_one.mp hd).symm
      exact hm heq
    change Nat.card E≤2 at hb
    omega
  rw [←commutator_restriction_card W,hsq]
  change Nat.card E^2=4
  norm_num [hE]
end ActionSupport
