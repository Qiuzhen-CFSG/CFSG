module
public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.AlternatingFiveSquare
public import Theory.Representation.BinaryOffender.DihedralProductDisplacement
public import Theory.SpecificGroups.SL2.CubicFixedVectors
public import Theory.SpecificGroups.SL2.CardFourEquiv
public import Theory.SpecificGroups.SL2.FieldAutomorphismCore
public import Theory.SpecificGroups.Alternating.FiveLocalGeometry.CubicCentralizer
public import Theory.GroupTheory.ElementaryPairInvolutionUnion

/-!
# Individual diagonal cubics on the natural eight-space

A cubic plane in an actual A₅ square cannot lie in either source factor,
since nine does not divide sixty. The subgroup-union argument selects one
individual cubic with nontrivial projection to both factors. The two natural
intertwiners and the complementary moved spaces show that this cubic fixes
only zero. Its factor centralizers have order three, so its centralizer
contains no nonidentity involution either.

The original tensor point-core application uses these two conclusions on
U/⟨z⟩ and on the literal V-image modulo O₂(C_G(z)), respectively.
Source: Aschbacher--Smith 8.3.12 and H.4.12(1), printed pp.726,385,
refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterB.SourceInduction.AlternatingFiveSquare
open QuasisimpleSource
variable {D V : Type*} [Group D] [Finite D] [AddCommGroup V] [Module (ZMod 2) V]
  {ρ : Representation (ZMod 2) D V}

private theorem natural_five {E W : Type*} [Group E] [AddCommGroup W] [Module (ZMod 2) W]
    {σ : Representation (ZMod 2) E W} {F : BinaryField} (hd : F.degree = 2)
    (h : IsLinearNatural σ F 2) : Nonempty (E ≃* Five) := by
  obtain ⟨e⟩ := h
  obtain ⟨a⟩ := Matrix.ProjectiveSpecialLinearGroup.equiv_alternatingGroup_of_card_four
    (F.card_eq.trans (by rw [hd]; decide))
  exact ⟨e.groupEquiv.trans ((Atlas.RankOneFieldAutomorphisms.slEquivPSL (F := F.Carrier)).trans a)⟩

private theorem natural_cubic_free {E W : Type*} [Group E] [AddCommGroup W] [Module (ZMod 2) W]
    {σ : Representation (ZMod 2) E W} {F : BinaryField}
    (h : IsLinearNatural σ F 2) (a : E) (ha : orderOf a = 3)
    (v : W) (hv : σ a v = v) : v = 0 := by
  obtain ⟨e⟩ := h
  apply e.linearEquiv.injective
  rw [map_zero]
  apply Matrix.SL2.cubic_fixed_eq_zero (e.groupEquiv a) ((e.groupEquiv.orderOf_eq a).trans ha)
  exact (e.intertwines a v).symm.trans (congrArg e.linearEquiv hv)

private theorem five_cubic_no_involution {E : Type*} [Group E] [Finite E]
    (e : E ≃* Five) (a : E) (ha : orderOf a = 3)
    (x : E) (hx : x^2 = 1) (hcomm : Commute a x) : x = 1 := by
  let C := centralizer (zpowers a : Set E)
  have hc : Nat.card C = 3 := alternatingGroup.FiveLocalGeometry.cubic_centralizer_card e
    (zpowers a) (by rw [Nat.card_zpowers,ha])
  have hxC : x ∈ C := by
    change x ∈ centralizer (zpowers a : Set E)
    rw [zpowers_eq_closure,centralizer_closure]
    exact mem_centralizer_singleton_iff.mpr hcomm.eq.symm
  have hx3 : x^3 = 1 := by
    have hh := pow_card_eq_one' (x := (⟨x,hxC⟩ : C))
    rw [hc] at hh
    exact congrArg Subtype.val hh
  have he : orderOf x ∣ 1 := (by decide : Nat.gcd 2 3 = 1) ▸
    Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hx) (orderOf_dvd_of_pow_eq_one hx3)
  exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp he)

omit [Finite D] in
private theorem product_commutes {A B : Subgroup D} (h : InternalProduct A B)
    (a : A) (b : B) : Commute (a:D) (b:D) := by
  have hh : h.equiv ((a,1) * (1,b)) = h.equiv ((1,b) * (a,1)) := by simp
  rw [map_mul,map_mul] at hh
  change (a:D)*(b:D) = (b:D)*(a:D)
  simpa only [h.apply_eq,OneMemClass.coe_one,mul_one,one_mul] using hh

omit [Finite D] in
private theorem cross_fixed (m : NaturalEightDecomposition ρ) :
    (∀ a ∈ m.factors.first, ∀ v ∈ m.factors.secondSpace.toSubmodule, ρ a v = v) ∧
    (∀ a ∈ m.factors.second, ∀ v ∈ m.factors.firstSpace.toSubmodule, ρ a v = v) := by
  have hc := fun a ha b hb => product_commutes m.factors.product ⟨a,ha⟩ ⟨b,hb⟩
  have hd : Disjoint (moved ρ m.factors.first) (moved ρ m.factors.second) := by
    rw [←m.first_moved,←m.second_moved]
    exact m.decomposition.disjoint
  constructor
  · intro a ha v hv
    exact fixes_other_moved_of_disjoint ρ _ _ hc hd ha (show v ∈ moved ρ m.factors.second from m.second_moved ▸ hv)
  · intro a ha v hv
    exact fixes_other_moved_of_disjoint ρ _ _ (fun a ha b hb => (hc b hb a ha).symm)
      hd.symm ha (show v ∈ moved ρ m.factors.first from m.first_moved ▸ hv)

omit [Finite D] in
/-- A cubic nontrivial in both original natural factors fixes only zero. -/
theorem NaturalEightDecomposition.diagonal_cubic_free (m : NaturalEightDecomposition ρ)
    (a : m.factors.first) (b : m.factors.second) (ha : orderOf a = 3) (hb : orderOf b = 3)
    (v : V) (hv : ρ ((a:D)*(b:D)) v = v) : v = 0 := by
  obtain ⟨u,hu,w,hw,rfl⟩ := Submodule.mem_sup.mp (m.decomposition.sup_eq_top.ge (Submodule.mem_top (x := v)))
  have hfix : ρ ((a:D)*(b:D)) u - u = -(ρ ((a:D)*(b:D)) w - w) := by
    rw [map_add] at hv
    apply eq_neg_iff_add_eq_zero.mpr
    calc
      _ = (ρ ((a:D)*(b:D)) u + ρ ((a:D)*(b:D)) w) - (u+w) := by abel
      _ = 0 := sub_eq_zero.mpr hv
  have hzu : ρ ((a:D)*(b:D)) u - u = 0 := by
    apply Submodule.disjoint_def.mp m.decomposition.disjoint
    · exact m.factors.firstSpace.toSubmodule.sub_mem (m.factors.firstSpace.apply_mem_toSubmodule _ hu) hu
    · rw [hfix]
      exact m.factors.secondSpace.toSubmodule.neg_mem
        (m.factors.secondSpace.toSubmodule.sub_mem (m.factors.secondSpace.apply_mem_toSubmodule _ hw) hw)
  have hzw : ρ ((a:D)*(b:D)) w - w = 0 := by
    have hh := hfix
    rw [hzu,eq_comm,neg_eq_zero] at hh
    exact hh
  have hufix : ρ a u = u := by
    simpa only [map_mul,Module.End.mul_apply,(cross_fixed m).2 b b.property u hu] using sub_eq_zero.mp hzu
  have hwfix : ρ b w = w := by
    have hh : ρ ((a:D)*(b:D)) w = ρ b w := by
      rw [(product_commutes m.factors.product a b).eq,map_mul,Module.End.mul_apply,
        (cross_fixed m).1 a a.property w hw]
    rw [hh] at hzw
    exact sub_eq_zero.mp hzw
  have hu0 := natural_cubic_free m.first_natural a ha (⟨u,hu⟩ : m.factors.firstSpace.toSubmodule)
    (Subtype.ext hufix)
  have hw0 := natural_cubic_free m.second_natural b hb (⟨w,hw⟩ : m.factors.secondSpace.toSubmodule)
    (Subtype.ext hwfix)
  have hu' : u = 0 := congrArg Subtype.val hu0
  have hw' : w = 0 := congrArg Subtype.val hw0
  rw [hu',hw',add_zero]

/-- Any actual cubic plane supplies an individual cubic that is fixed-point-free
on the natural pair and has no nonidentity involution in its centralizer. -/
theorem NaturalEightDecomposition.exists_cubic (m : NaturalEightDecomposition ρ)
    (P : Subgroup D) (hc : Nat.card P = 9) (hp : ∀ a ∈ P, a^3 = 1) :
    ∃ a ∈ P, a^3 = 1 ∧ (∀ v, ρ a v = v → v = 0) ∧
      ∀ x : D, x^2 = 1 → Commute a x → x = 1 := by
  obtain ⟨e₁⟩ := natural_five m.first_degree m.first_natural
  obtain ⟨e₂⟩ := natural_five m.second_degree m.second_natural
  have hn₁ : ¬ P ≤ m.factors.first := by
    intro hl
    have hd := card_dvd_of_le hl
    rw [hc,Nat.card_congr e₁.toEquiv,nat_card_alternatingGroup] at hd
    norm_num [Nat.factorial] at hd
  have hn₂ : ¬ P ≤ m.factors.second := by
    intro hl
    have hd := card_dvd_of_le hl
    rw [hc,Nat.card_congr e₂.toEquiv,nat_card_alternatingGroup] at hd
    norm_num [Nat.factorial] at hd
  have hn : ∃ a ∈ P, a ∉ m.factors.first ∧ a ∉ m.factors.second := by
    by_contra hh
    push Not at hh
    have hu := le_one_of_elementwise_union P m.factors.first m.factors.second
      (fun a ha => or_iff_not_imp_left.mpr (hh a ha))
    exact hu.elim hn₁ hn₂
  obtain ⟨g,hg,hg₁,hg₂⟩ := hn
  obtain ⟨a,b,hab⟩ := m.factors.product.exists_mul g
  have ha1 : a ≠ 1 := by
    intro he
    apply hg₂
    simpa only [hab,he,OneMemClass.coe_one,one_mul] using b.property
  have hb1 : b ≠ 1 := by
    intro he
    apply hg₁
    simpa only [hab,he,OneMemClass.coe_one,mul_one] using a.property
  have hpow : (a,b)^3 = (1 : m.factors.first × m.factors.second) := by
    apply m.factors.product.equiv.injective
    rw [map_pow,m.factors.product.apply_eq,←hab,hp g hg,map_one]
  have ha3 : orderOf a = 3 := orderOf_eq_prime (congrArg Prod.fst hpow) ha1
  have hb3 : orderOf b = 3 := orderOf_eq_prime (congrArg Prod.snd hpow) hb1
  refine ⟨g,hg,hp g hg,?_,?_⟩
  · exact hab ▸ m.diagonal_cubic_free a b ha3 hb3
  · intro x hx hcomm
    let y := m.factors.product.equiv.symm x
    have hy2 : y^2 = 1 := by simp only [y,←map_pow,hx,map_one]
    have hcy : Commute (a,b) y := by
      have hh := hcomm.map m.factors.product.equiv.symm.toMonoidHom
      have hg' : m.factors.product.equiv.symm g = (a,b) := by
        apply m.factors.product.equiv.injective
        rw [m.factors.product.equiv.apply_symm_apply,m.factors.product.apply_eq,←hab]
      change Commute (m.factors.product.equiv.symm g) y at hh
      rwa [hg'] at hh
    have hy₁ := five_cubic_no_involution e₁ a ha3 y.1 (congrArg Prod.fst hy2)
      (hcy.map (MonoidHom.fst _ _))
    have hy₂ := five_cubic_no_involution e₂ b hb3 y.2 (congrArg Prod.snd hy2)
      (hcy.map (MonoidHom.snd _ _))
    apply m.factors.product.equiv.symm.injective
    exact (Prod.ext hy₁ hy₂).trans m.factors.product.equiv.symm.map_one.symm
end CFSG.Quasithin.ChapterB.SourceInduction.AlternatingFiveSquare
