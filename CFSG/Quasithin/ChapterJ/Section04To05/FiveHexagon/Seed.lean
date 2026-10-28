module

public import CFSG.Quasithin.ChapterJ.Section01To02.SourceCompletion.Five
public import CFSG.Quasithin.ChapterJ.Section03.Source

/-!
# The first three five-subgroups in the J.4 hexagon

Retain the original B₅, its source extraspecial five-core P, and the actual
z-class element u of H inverting B₅. The completed J.3.2 theorem puts zu
in the same involution class. Brauer–Wielandt and the original order125
calculation force C_P(u) and C_P(zu) to have order five. They give the
literal product P = B₅ C_P(u) C_P(zu). The two new factors generate P,
since B₅ is its Frattini subgroup.

The actual pairs (u,C_P(u)) and (zu,C_P(zu)) are simultaneously conjugate
to (z,B₅). The base subgroup centralizes both new factors; the displayed
intersections are trivial. These establish the first three vertices and
their two edges and extraspecial distance-two join. No six-cycle or
ambient recognition is assumed. The original geometric construction of u
is a separate earlier input to the later hexagon assembly.

Source: Aschbacher–Smith, discussion before J.4.8 and J.4.9(1), printed
pp.442–443, using the complete original-source J.3.1–6.
-/

public section
noncomputable section

open Subgroup
open scoped Pointwise
namespace CFSG.Quasithin.ChapterJ.RuSubgroup.FiveHexagon
open Centralizers Centralizers.Choices
private instance : Fact (Nat.Prime 5) := ⟨by decide⟩
variable {G : Type*} [Group G] [Finite G] {d : LocalSetup G}
  (c : Choices d) (B5 : Sylow 5 d.toTypeRuSetup.H)

/-- The literal five-core centralizer of the given source element. -/
abbrev fixedFive (v : G) : Subgroup G := fiveOddPart B5 ⊓ centralizer ({v} : Set G)

private theorem normalizes_of_inverts (u : G) (h2 : u^2=1)
    (hi : ∀ x ∈ B5Image B5, u*x*u⁻¹=x⁻¹) :
    u ∈ normalizer (fiveOddPart B5 : Set G) := by
  apply normalizer_B5Image_le_normalizer_fiveOddPart B5
  have hf (x:G) (hx:x∈B5Image B5) : u*x*u⁻¹∈B5Image B5 := by
    rw [hi x hx]; exact (B5Image B5).inv_mem hx
  intro x
  refine ⟨hf x, fun hx => ?_⟩
  have hh := hf _ hx
  have he : u*(u*x*u⁻¹)*u⁻¹=x := by
    calc
      _ = (u*u)*x*(u*u)⁻¹ := by group
      _ = x := by rw [← pow_two,h2]; simp
  rwa [he] at hh

private theorem fixed_card_dvd_five (v : G) (hv : IsConj v c.z) :
    Nat.card (fixedFive B5 v) ∣ 5 := by
  obtain ⟨g,hg⟩ := isConj_iff.mp hv
  let A := (fixedFive B5 v).conjBy g
  have hAH : A ≤ d.toTypeRuSetup.H := by
    rintro x ⟨a,ha,rfl⟩
    rw [c.H_eq_centralizer_z,mem_centralizer_singleton_iff]
    change g*v*g⁻¹=c.z at hg
    rw [← hg]
    simpa only [map_mul,MulAut.conj_apply,MulEquiv.coe_toMonoidHom] using
      congrArg (MulAut.conj g) (mem_centralizer_singleton_iff.mp ha.2)
  have he : Nat.card A = Nat.card (fixedFive B5 v) :=
    card_map_of_injective (MulAut.conj g).injective
  have h1 := card_dvd_of_le hAH
  rw [he,d.ru2.card_H d.card_Z] at h1
  have h2 := card_dvd_of_le (show fixedFive B5 v ≤ fiveOddPart B5 from inf_le_left)
  rw [SourceCompletion.five_oddPart_card c B5] at h2
  exact (show Nat.gcd 245760 125 = 5 by decide) ▸ Nat.dvd_gcd h1 h2

private theorem fixed_z : fixedFive B5 c.z = B5Image B5 := by
  obtain ⟨q⟩ := c.fiveQuaternionData_source B5
  exact c.fiveOddPart_inf_centralizer_z d.card_Z B5 q

private theorem common_fixed_bot (u : G)
    (hi : ∀ x ∈ B5Image B5, u*x*u⁻¹=x⁻¹) :
    fixedFive B5 c.z ⊓ centralizer ({u} : Set G) = ⊥ := by
  rw [fixed_z c B5]
  apply eq_bot_iff.mpr
  intro x hx
  have hf : u*x*u⁻¹=x := by
    rw [← mem_centralizer_singleton_iff.mp hx.2,mul_inv_cancel_right]
  have h2 : x^2=1 := by
    calc
      x^2 = x*x := pow_two x
      _ = x⁻¹*x := congrArg (· * x) (hf.symm.trans (hi x hx.1))
      _ = 1 := inv_mul_cancel x
  have h5 : x^5=1 := by
    have h := pow_card_eq_one' (x := (⟨x,hx.1⟩ : B5Image B5))
    rw [B5Image_card d.card_Z B5] at h
    exact congrArg Subtype.val h
  exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp
    (show orderOf x ∣ 1 from Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one h2)
      (orderOf_dvd_of_pow_eq_one h5)))

private theorem actors (u : G) (hu : u∈d.toTypeRuSetup.H) (h2 : u^2=1)
    (hi : ∀ x ∈ B5Image B5, u*x*u⁻¹=x⁻¹) :
    ∃ (a b : normalizer (fiveOddPart B5 : Set G)),
      (a:G)=c.z ∧ (b:G)=u ∧ a^2=1 ∧ b^2=1 ∧ Commute a b := by
  let a : normalizer (fiveOddPart B5 : Set G) :=
    ⟨c.z,G5_normalizes_fiveOddPart B5 (c.z_mem_G5 B5)⟩
  let b : normalizer (fiveOddPart B5 : Set G) := ⟨u,normalizes_of_inverts B5 u h2 hi⟩
  refine ⟨a,b,rfl,rfl,Subtype.ext (c.z_involution_of_card d.card_Z).2,Subtype.ext h2,?_⟩
  apply Subtype.ext
  exact (mem_centralizer_singleton_iff.mp (c.H_eq_centralizer_z ▸ hu)).symm

/-- The ordered product of the three original fixed subgroups equals P. -/
theorem factorization (u : G) (hu : u∈d.toTypeRuSetup.H) (h2 : u^2=1)
    (hi : ∀ x ∈ B5Image B5, u*x*u⁻¹=x⁻¹) (x:G) (hx:x∈fiveOddPart B5) :
    ∃ b∈B5Image B5, ∃ a∈fixedFive B5 u, ∃ w∈fixedFive B5 (c.z*u), x=b*a*w := by
  obtain ⟨a,b,ha,hb,ha2,hb2,hab⟩ := actors c B5 u hu h2 hi
  have h := (fiveOddPart B5).exists_three_odd_centralizers (fiveOddPart_odd B5)
    a b ha2 hb2 hab x hx
  change ∃ r∈fixedFive B5 (a:G), ∃ s∈fixedFive B5 (b:G),
    ∃ t∈fixedFive B5 ((a:G)*(b:G)), x=r*s*t at h
  rwa [ha,hb,fixed_z c B5] at h

/-- The two noncentral fixed subgroups each have order five. -/
theorem fixed_cards (u : G) (hu : u∈d.toTypeRuSetup.H) (h2 : u^2=1)
    (hi : ∀ x ∈ B5Image B5, u*x*u⁻¹=x⁻¹)
    (huz : IsConj u c.z) (hzu : IsConj (c.z*u) c.z) :
    Nat.card (fixedFive B5 u)=5 ∧ Nat.card (fixedFive B5 (c.z*u))=5 := by
  obtain ⟨a,b,ha,hb,ha2,hb2,hab⟩ := actors c B5 u hu h2 hi
  have h := (fiveOddPart B5).card_three_odd_centralizers (fiveOddPart_odd B5)
    a b ha2 hb2 hab
  change Nat.card (fiveOddPart B5) * Nat.card
    (fixedFive B5 (a:G) ⊓ centralizer ({(b:G)} : Set G) : Subgroup G)^2 =
    Nat.card (fixedFive B5 (a:G))*Nat.card (fixedFive B5 (b:G))*
      Nat.card (fixedFive B5 ((a:G)*(b:G))) at h
  rw [ha,hb,common_fixed_bot c B5 u hi,fixed_z c B5,
    SourceCompletion.five_oddPart_card c B5,B5Image_card d.card_Z B5,card_bot] at h
  have h1 := (Nat.dvd_prime (by decide : Nat.Prime 5)).mp (fixed_card_dvd_five c B5 u huz)
  have h2 := (Nat.dvd_prime (by decide : Nat.Prime 5)).mp (fixed_card_dvd_five c B5 (c.z*u) hzu)
  have hnum (a b : ℕ) (ha : a=1 ∨ a=5) (hb : b=1 ∨ b=5)
      (he : 125 * 1^2 = 5*a*b) : a=5 ∧ b=5 := by
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> norm_num at *
  exact hnum _ _ h1 h2 h

/-- A fixed five-subgroup and its z-class involution admit a simultaneous source marking. -/
theorem pair_conjugacy (v : G) (hv : IsConj v c.z)
    (h5 : Nat.card (fixedFive B5 v)=5) :
    ∃ g:G, g*v*g⁻¹=c.z ∧ (fixedFive B5 v).conjBy g=B5Image B5 := by
  obtain ⟨g,hg⟩ := isConj_iff.mp hv
  let A := (fixedFive B5 v).conjBy g
  have hAH : A ≤ d.toTypeRuSetup.H := by
    rintro x ⟨a,ha,rfl⟩
    rw [c.H_eq_centralizer_z,mem_centralizer_singleton_iff]
    change g*v*g⁻¹=c.z at hg
    rw [← hg]
    simpa only [map_mul,MulAut.conj_apply,MulEquiv.coe_toMonoidHom] using
      congrArg (MulAut.conj g) (mem_centralizer_singleton_iff.mp ha.2)
  have hA5 : Nat.card A=5 := by
    change Nat.card ((fixedFive B5 v).map (MulAut.conj g).toMonoidHom)=5
    rw [card_map_of_injective (MulAut.conj g).injective,h5]
  obtain ⟨j,hj⟩ := Section03.five_subgroup_conjugate_into_base B5 A hAH hA5
  refine ⟨(j:G)*g,?_,?_⟩
  · calc
      _ = (j:G)*(g*v*g⁻¹)*(j:G)⁻¹ := by group
      _ = (j:G)*c.z*(j:G)⁻¹ := by rw [hg]
      _ = c.z := mul_inv_eq_iff_eq_mul.mpr
        (mem_centralizer_singleton_iff.mp (c.H_eq_centralizer_z ▸ j.property))
  · rwa [← conjBy_mul] at hj

/-- The original base five-subgroup centralizes each of its fixed factors. -/
theorem central_edge (v : G) : B5Image B5 ≤ centralizer (fixedFive B5 v : Set G) := by
  intro b hb a ha
  exact (fiveOddPart_le_G5 B5 ha.1 b hb).symm

/-- The three source fixed subgroups generate the original odd core. -/
theorem generated_by_three (u : G) (hu : u∈d.toTypeRuSetup.H) (h2 : u^2=1)
    (hi : ∀ x ∈ B5Image B5, u*x*u⁻¹=x⁻¹) :
    (B5Image B5 ⊔ fixedFive B5 u) ⊔ fixedFive B5 (c.z*u) = fiveOddPart B5 := by
  apply le_antisymm
  · exact sup_le (sup_le (B5Image_le_fiveOddPart d.card_Z B5) inf_le_left) inf_le_left
  · intro x hx
    obtain ⟨b,hb,a,ha,w,hw,rfl⟩ := factorization c B5 u hu h2 hi x hx
    have hB : B5Image B5 ≤ (B5Image B5 ⊔ fixedFive B5 u) ⊔ fixedFive B5 (c.z*u) :=
      le_sup_left.trans le_sup_left
    have hA : fixedFive B5 u ≤ (B5Image B5 ⊔ fixedFive B5 u) ⊔ fixedFive B5 (c.z*u) :=
      le_sup_right.trans le_sup_left
    have hW : fixedFive B5 (c.z*u) ≤ (B5Image B5 ⊔ fixedFive B5 u) ⊔ fixedFive B5 (c.z*u) :=
      le_sup_right
    exact mul_mem (mul_mem (hB hb) (hA ha)) (hW hw)

include c in
/-- Inversion makes the base and its new fixed subgroup disjoint. -/
theorem disjoint_base_fixed (u : G)
    (hi : ∀ x ∈ B5Image B5, u*x*u⁻¹=x⁻¹) :
    Disjoint (B5Image B5) (fixedFive B5 u) := by
  apply disjoint_iff.mpr
  apply bot_unique
  intro x hx
  have hm : x ∈ fixedFive B5 c.z ⊓ centralizer ({u} : Set G) :=
    ⟨(fixed_z c B5).symm ▸ hx.1,hx.2.2⟩
  rwa [common_fixed_bot c B5 u hi] at hm

/-- Removing the actual Frattini subgroup leaves the two new factors generating P. -/
theorem generated_by_fixed_pair (u : G) (hu : u∈d.toTypeRuSetup.H) (h2 : u^2=1)
    (hi : ∀ x ∈ B5Image B5, u*x*u⁻¹=x⁻¹) :
    fixedFive B5 u ⊔ fixedFive B5 (c.z*u) = fiveOddPart B5 := by
  have hG := Section03.order_source c
  let P := fiveOddPart B5
  let A := fixedFive B5 u ⊔ fixedFive B5 (c.z*u)
  let : IsExtraspecial 5 P := Section03.five_oddPart_extraspecial c B5 hG
  have hAP : A ≤ P := sup_le inf_le_left inf_le_left
  have hsup : A.subgroupOf P ⊔ frattini P = ⊤ := by
    apply map_injective P.subtype_injective
    rw [Subgroup.map_sup,map_subgroupOf_eq_of_le hAP,← MonoidHom.range_eq_map,P.range_subtype,
      IsExtraspecial.frattini_eq_center (p:=5),Section03.five_oddPart_center c B5 hG]
    calc
      A ⊔ B5Image B5 = (B5Image B5 ⊔ fixedFive B5 u) ⊔ fixedFive B5 (c.z*u) := by
        dsimp [A]; ac_rfl
      _ = P := generated_by_three c B5 u hu h2 hi
  have he := congrArg (Subgroup.map P.subtype) (frattini_nongenerating hsup)
  simpa only [map_subgroupOf_eq_of_le hAP,← MonoidHom.range_eq_map,P.range_subtype] using he

include c in
/-- The two new fixed subgroups have trivial intersection. -/
theorem disjoint_fixed_pair (u : G)
    (hi : ∀ x ∈ B5Image B5, u*x*u⁻¹=x⁻¹) :
    Disjoint (fixedFive B5 u) (fixedFive B5 (c.z*u)) := by
  apply disjoint_iff.mpr
  apply bot_unique
  intro x hx
  have hxu := mem_centralizer_singleton_iff.mp hx.1.2
  have hxzu := mem_centralizer_singleton_iff.mp hx.2.2
  have hxz : x*c.z=c.z*x := by
    apply mul_right_cancel (b:=u)
    calc
      x*c.z*u = x*(c.z*u) := mul_assoc _ _ _
      _ = (c.z*u)*x := hxzu
      _ = c.z*(u*x) := mul_assoc _ _ _
      _ = c.z*(x*u) := by rw [hxu]
      _ = c.z*x*u := (mul_assoc _ _ _).symm
  have hm : x ∈ fixedFive B5 c.z ⊓ centralizer ({u} : Set G) :=
    ⟨⟨hx.1.1,mem_centralizer_singleton_iff.mpr hxz⟩,hx.1.2⟩
  rwa [common_fixed_bot c B5 u hi] at hm

/-- J.3.2 puts the literal product zu in the original z-class. -/
theorem product_class (u : G) (hu : u∈d.toTypeRuSetup.H)
    (huz : IsConj u c.z) (hi : ∀ x ∈ B5Image B5, u*x*u⁻¹=x⁻¹) :
    u^2=1 ∧ IsConj (c.z*u) c.z := by
  have hz2 := (c.z_involution_of_card d.card_Z).2
  have hu2 : u^2=1 := by
    have hp := IsConj.pow 2 huz
    rw [hz2] at hp
    exact isConj_one_left.mp hp
  have hne : u≠c.z := by
    intro he
    have hb := common_fixed_bot c B5 u hi
    rw [he,inf_eq_left.mpr inf_le_right] at hb
    change fixedFive B5 c.z=⊥ at hb
    rw [fixed_z c B5] at hb
    have hc := B5Image_card d.card_Z B5
    rw [hb,card_bot] at hc
    contradiction
  have hp : c.z*u≠1 := by
    intro he
    apply hne
    calc
      u = c.z*(c.z*u) := by rw [← mul_assoc,← pow_two,hz2,one_mul]
      _ = c.z := by rw [he,mul_one]
  obtain ⟨r⟩ := c.suzuki_source
  refine ⟨hu2,?_⟩
  apply IsConj.symm
  apply Section03.class_closed_of_suzuki c r c.two_involution_classes_source
    c.z u (IsConj.refl _) huz.symm ?_ hp
  exact (mem_centralizer_singleton_iff.mp (c.H_eq_centralizer_z ▸ hu)).symm

/-- Multiplication by the original central involution preserves inversion of B₅. -/
theorem inverts_product (u : G) (hi : ∀ x ∈ B5Image B5, u*x*u⁻¹=x⁻¹) :
    ∀ x ∈ B5Image B5, (c.z*u)*x*(c.z*u)⁻¹=x⁻¹ := by
  intro x hx
  calc
    _ = c.z*(u*x*u⁻¹)*c.z⁻¹ := by group
    _ = c.z*x⁻¹*c.z⁻¹ := by rw [hi x hx]
    _ = x⁻¹ := mul_inv_eq_iff_eq_mul.mpr
      ((c.z_mem_G5 B5) x⁻¹ ((B5Image B5).inv_mem hx)).symm

/-- The base also meets the third source five-subgroup trivially. -/
theorem disjoint_base_product (u : G) (hi : ∀ x ∈ B5Image B5, u*x*u⁻¹=x⁻¹) :
    Disjoint (B5Image B5) (fixedFive B5 (c.z*u)) :=
  disjoint_base_fixed c B5 (c.z*u) (inverts_product c B5 u hi)

/-- The first three actual five-subgroups, with their source pair markings and extraspecial join. -/
theorem source_three_fives (u : G) (hu : u∈d.toTypeRuSetup.H)
    (huz : IsConj u c.z) (hi : ∀ x ∈ B5Image B5, u*x*u⁻¹=x⁻¹) :
    Nat.card (fixedFive B5 u)=5 ∧ Nat.card (fixedFive B5 (c.z*u))=5 ∧
      Disjoint (B5Image B5) (fixedFive B5 u) ∧
      Disjoint (fixedFive B5 u) (fixedFive B5 (c.z*u)) ∧
      Disjoint (B5Image B5) (fixedFive B5 (c.z*u)) ∧
      B5Image B5 ≤ centralizer (fixedFive B5 u : Set G) ∧
      B5Image B5 ≤ centralizer (fixedFive B5 (c.z*u) : Set G) ∧
      (∃ g:G, g*u*g⁻¹=c.z ∧ (fixedFive B5 u).conjBy g=B5Image B5) ∧
      (∃ g:G, g*(c.z*u)*g⁻¹=c.z ∧ (fixedFive B5 (c.z*u)).conjBy g=B5Image B5) ∧
      fixedFive B5 u ⊔ fixedFive B5 (c.z*u)=fiveOddPart B5 ∧
      IsExtraspecial 5 (fixedFive B5 u ⊔ fixedFive B5 (c.z*u) : Subgroup G) := by
  obtain ⟨hu2,hzu⟩ := product_class c B5 u hu huz hi
  obtain ⟨h5,h5'⟩ := fixed_cards c B5 u hu hu2 hi huz hzu
  have he := generated_by_fixed_pair c B5 u hu hu2 hi
  exact ⟨h5,h5',disjoint_base_fixed c B5 u hi,disjoint_fixed_pair c B5 u hi,
    disjoint_base_product c B5 u hi,central_edge B5 u,central_edge B5 (c.z*u),pair_conjugacy c B5 u huz h5,
    pair_conjugacy c B5 (c.z*u) hzu h5',he,
    he.symm ▸ (Section03.lemma_J_3_6 c B5).2.1⟩

end CFSG.Quasithin.ChapterJ.RuSubgroup.FiveHexagon
