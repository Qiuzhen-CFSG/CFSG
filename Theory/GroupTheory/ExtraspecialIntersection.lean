module
public import Theory.ElementaryAbelian.ExtraspecialPrimeAbelianBound
public import Theory.ElementaryAbelian.ExtraspecialEquiv
public import Theory.GroupTheory.PGroup.ClassTwoCyclicCenter
public import Theory.GroupTheory.SubgroupCenterImageBound
public import Theory.GroupTheory.NormalizedSupCard

/-!
# Intersections of extraspecial binary subgroups with distinct centers

Squares in each extraspecial subgroup lie in its central line. Disjoint
central lines therefore make the intersection elementary abelian. The
extraspecial commutator pairing bounds its square order by twice the core
order. The same commutator pairing gives index two for the centralizer of
any noncentral core element.

These are the local intersection and centralizer counts used in
Aschbacher--Smith F.4.35, printed p.292, in the triality case.
-/

@[expose] public noncomputable section
open Subgroup
open scoped commutatorElement IsMulCommutative Pointwise
namespace Theory.GroupTheory.ExtraspecialIntersection
variable {G : Type*} [Group G]

/-- Distinct central lines of extraspecial binary subgroups meet trivially. -/
theorem disjoint_centers_of_ne [Finite G] (Q R : Subgroup G)
    [IsExtraspecial 2 Q] [IsExtraspecial 2 R]
    (hne : (center Q).map Q.subtype ≠ (center R).map R.subtype) :
    Disjoint ((center Q).map Q.subtype) ((center R).map R.subtype) := by
  let Z := (center Q).map Q.subtype
  let W := (center R).map R.subtype
  have hZ : Nat.card Z=2 := (card_map_of_injective Q.subtype_injective).trans
    (IsExtraspecial.center_order_p 2 Q)
  have hW : Nat.card W=2 := (card_map_of_injective R.subtype_injective).trans
    (IsExtraspecial.center_order_p 2 R)
  by_contra hd
  have hn : (Z ⊓ W : Subgroup G)≠⊥ := fun he => hd (disjoint_iff_inf_le.mpr he.le)
  have hi := (one_lt_card_iff_ne_bot (H := Z ⊓ W)).mpr hn
  have hIZ : Z ⊓ W=Z := eq_of_le_of_card_ge inf_le_left (by omega)
  have hIW : Z ⊓ W=W := eq_of_le_of_card_ge inf_le_right (by omega)
  exact hne (hIZ.symm.trans hIW)

theorem elementary_inf (Q R : Subgroup G) [IsExtraspecial 2 Q] [IsExtraspecial 2 R]
    (hZ : Disjoint ((center Q).map Q.subtype) ((center R).map R.subtype)) :
    IsElementaryAbelian 2 (Q ⊓ R : Subgroup G) := by
  have hs (x : (Q ⊓ R : Subgroup G)) : x ^ 2 = 1 := by
    apply Subtype.ext
    apply (Subgroup.disjoint_def.mp hZ)
    · exact ⟨(⟨x.val,x.property.1⟩ : Q)^2,
        (IsExtraspecial.quotient_elementary_abelian 2 Q).sq_mem_center_of_central_quotient _,rfl⟩
    · exact ⟨(⟨x.val,x.property.2⟩ : R)^2,
        (IsExtraspecial.quotient_elementary_abelian 2 R).sq_mem_center_of_central_quotient _,rfl⟩
  have hi (x : (Q ⊓ R : Subgroup G)) : x⁻¹=x := inv_eq_of_mul_eq_one_left (by simpa only [pow_two] using hs x)
  exact { toIsMulCommutative := ⟨⟨fun x y => by
            have h := hi (x*y)
            rw [mul_inv_rev,hi x,hi y] at h
            exact h.symm⟩⟩
          exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one hs }

theorem card_inf_sq_le [Finite G] (Q R : Subgroup G)
    [IsExtraspecial 2 Q] [IsExtraspecial 2 R]
    (hZ : Disjoint ((center Q).map Q.subtype) ((center R).map R.subtype)) :
    Nat.card (Q ⊓ R : Subgroup G)^2 ≤ 2 * Nat.card Q := by
  let := elementary_inf Q R hZ
  let := IsElementaryAbelian.subgroupOf (p := 2)
    (show (Q ⊓ R : Subgroup G) ≤ Q from inf_le_left)
  have hb := extraspecial_prime_abelian_card_sq_le_any (p := 2) ((Q ⊓ R).subgroupOf Q)
  rwa [Nat.card_congr (subgroupOfEquivOfLe (show Q ⊓ R ≤ Q from inf_le_left)).toEquiv] at hb

private def commHom {P : Type*} [Group P] [IsExtraspecial 2 P] (v : P) :
    P →* center P where
  toFun x := ⟨⁅v,x⁆,
    (IsExtraspecial.quotient_elementary_abelian 2 P).commutator_le_center_of_central_quotient
      (commutator_mem_commutator (mem_top v) (mem_top x))⟩
  map_one' := by apply Subtype.ext; simp
  map_mul' x y := by
    apply Subtype.ext
    change ⁅v,x*y⁆ = ⁅v,x⁆ * ⁅v,y⁆
    have hc : ⁅v,y⁆ ∈ center P :=
      (IsExtraspecial.quotient_elementary_abelian 2 P).commutator_le_center_of_central_quotient
        (commutator_mem_commutator (mem_top v) (mem_top y))
    rw [commutatorElement_mul_right_eq_mul_conj,mul_assoc ⁅v,x⁆ x ⁅v,y⁆,
      mem_center_iff.mp hc x]
    simp only [←mul_assoc,mul_inv_cancel_right]

/-- The noncentral element centralizer has index two, for any extraspecial size. -/
theorem centralizer_index_two {P : Type*} [Group P] [Finite P] [IsExtraspecial 2 P]
    (u : P) (hu : u ∉ center P) : (centralizer ({u} : Set P)).index=2 := by
  have hk : (commHom u).ker = centralizer ({u} : Set P) := by
    ext x
    change (⟨⁅u,x⁆,_⟩ : center P)=1 ↔ _
    rw [Subtype.ext_iff,OneMemClass.coe_one,commutatorElement_eq_one_iff_mul_comm,
      mem_centralizer_singleton_iff]
    exact eq_comm
  have hi : (centralizer ({u} : Set P)).index ≤ 2 := by
    rw [←hk,index_ker,←IsExtraspecial.center_order_p 2 P]
    exact Nat.card_le_card_of_injective _ (commHom u).range.subtype_injective
  have hn : (centralizer ({u} : Set P)).index≠1 := by
    intro he
    apply hu
    exact mem_center_iff.mpr (fun x => mem_centralizer_singleton_iff.mp
      ((index_eq_one.mp he).symm ▸ mem_top x))
  have hp := (centralizer ({u} : Set P)).index_ne_zero_of_finite
  omega

/-- The literal ambient intersection centralizer has half the core order. -/
theorem card_inf_centralizer_mul_two [Finite G] (R : Subgroup G) [IsExtraspecial 2 R]
    (z : G) (hz : z ∈ R) (hn : z ∉ (center R).map R.subtype) :
    Nat.card (R ⊓ centralizer ({z} : Set G) : Subgroup G)*2=Nat.card R := by
  let u : R := ⟨z,hz⟩
  have hu : u ∉ center R := fun h => hn ⟨u,h,rfl⟩
  have hc : (centralizer ({u} : Set R)).map R.subtype = R ⊓ centralizer ({z} : Set G) := by
    ext x
    constructor
    · rintro ⟨a,ha,rfl⟩
      exact ⟨a.property,mem_centralizer_singleton_iff.mpr
        (congrArg Subtype.val (mem_centralizer_singleton_iff.mp ha))⟩
    · rintro ⟨hx,hxz⟩
      refine ⟨⟨x,hx⟩,mem_centralizer_singleton_iff.mpr ?_,rfl⟩
      exact Subtype.ext (mem_centralizer_singleton_iff.mp hxz)
  have hh := (centralizer ({u} : Set R)).card_mul_index
  rw [centralizer_index_two u hu] at hh
  rwa [←hc,card_map_of_injective R.subtype_injective]

/-- In the triality-sized Sylow subgroup, the other core's centralizer supplies
all eight cosets of the first core. Both the intersection bound and the
centralizer count attain equality. -/
theorem sylow_supplement [Finite G] (Q R S : Subgroup G)
    [IsExtraspecial 2 Q] [IsExtraspecial 2 R]
    (hQ : Nat.card Q=512) (hR : Nat.card R=512) (hS : Nat.card S=4096)
    (hZ : Disjoint ((center Q).map Q.subtype) ((center R).map R.subtype))
    (hQS : Q≤S) (hnQ : S≤normalizer (Q:Set G))
    (z : G) (hz : z∈R) (hzout : z∉(center R).map R.subtype)
    (hcS : R ⊓ centralizer ({z}:Set G) ≤ S) :
    let C := R ⊓ centralizer ({z}:Set G)
    Nat.card C=256 ∧ Nat.card (Q ⊓ C : Subgroup G)=32 ∧ Q ⊔ C=S := by
  let C := R ⊓ centralizer ({z}:Set G)
  have hc : Nat.card C=256 := by
    have hh := card_inf_centralizer_mul_two R z hz hzout
    change Nat.card C*2=Nat.card R at hh
    rw [hR] at hh
    omega
  have hb : Nat.card (Q ⊓ C : Subgroup G)≤32 := by
    have hh := card_inf_sq_le Q R hZ
    rw [hQ] at hh
    have hm := card_le_of_le (show Q ⊓ C ≤ Q ⊓ R from inf_le_inf_left Q inf_le_left)
    nlinarith
  have hnC : C≤normalizer (Q:Set G) := hcS.trans hnQ
  have hp := card_mul_eq_card_inf_mul_card_sup_of_normalizes Q C hnC
  rw [hQ,hc] at hp
  have hle : Q ⊔ C≤S := sup_le hQS hcS
  have hu := card_le_of_le hle
  rw [hS] at hu
  have hprod := Nat.mul_le_mul hb hu
  have he : Nat.card (Q ⊔ C : Subgroup G)=4096 := by nlinarith
  have hi : Nat.card (Q ⊓ C : Subgroup G)=32 := by nlinarith
  change Nat.card C=256 ∧ Nat.card (Q ⊓ C : Subgroup G)=32 ∧ Q ⊔ C=S
  exact ⟨hc,hi,eq_of_le_of_card_ge hle (he.trans hS.symm).ge⟩

/-- The supplement forces its central elements in the first core to be fixed
modulo that core's center by the entire Sylow subgroup. -/
theorem commutator_mem_center_of_supplement (Q C S : Subgroup G)
    [IsExtraspecial 2 Q] (hn : C≤normalizer (Q:Set G)) (hgen : Q ⊔ C=S)
    {t : G} (htQ : t∈Q) (htC : t∈centralizer (C:Set G))
    {x : G} (hx : x∈S) : ⁅x,t⁆ ∈ (center Q).map Q.subtype := by
  have hxprod : x∈(Q:Set G)*(C:Set G) := by
    rw [←coe_mul_of_right_le_normalizer_left Q C hn]
    rwa [hgen]
  obtain ⟨q,hq,c,hc,rfl⟩ := hxprod
  have hct : ⁅c,t⁆=1 := commutatorElement_eq_one_iff_mul_comm.mpr (htC c hc)
  rw [commutatorElement_mul_left_eq_conj_mul,hct]
  simp only [mul_one,mul_inv_cancel,one_mul]
  exact ⟨⁅(⟨q,hq⟩:Q),(⟨t,htQ⟩:Q)⁆,
    (IsExtraspecial.quotient_elementary_abelian 2 Q).commutator_le_center_of_central_quotient
      (commutator_mem_commutator (mem_top _) (mem_top _)),rfl⟩

end Theory.GroupTheory.ExtraspecialIntersection
