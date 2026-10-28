module
public import Mathlib.Algebra.Group.Subgroup.Finite
public import Mathlib.Algebra.Group.Action.Basic
public import Mathlib.Algebra.GroupWithZero.Action.End
public import Mathlib.Tactic.Abel

/-!
# Binary modules with two reflected summands

An abelian group acts regularly on the nonzero vectors of a summand U.
A second summand is obtained by an element that inverts the actor. If the
whole module has a third invariant subgroup of order |U|, every actor has
cube one.

Transitivity first makes both coordinate projections of the third subgroup
injective. Their equal orders give an additive equivalence intertwining the
action with its inverse. Adding a vector to its translate in characteristic
two forces the actor identities b² = a and a² = b.

Source: Delgado--Goldschmidt--Stellmacher, *Groups and Graphs* (1985),
(14.16), printed p.220. The dihedral source application is in
`DGS85/ApartmentExchange/DihedralModule`.
-/

public section
namespace Theory.GroupAction
variable {H U : Type*} [CommGroup H] [AddCommGroup U] [DistribMulAction H U]

private theorem actor_eq {u : U} (hu : u ≠ 0)
    (hfree : ∀ (a : H) (v : U), v ≠ 0 → a • v = v → a = 1)
    {a b : H} (h : a • u = b • u) : a = b := by
  have he : (b⁻¹ * a) • u = u := by rw [mul_smul, h, inv_smul_smul]
  have := hfree (b⁻¹*a) u hu he
  exact (inv_mul_eq_one.mp this).symm

private theorem cubic_of_inverse_intertwiner [Nontrivial U]
    (htwo : ∀ v : U, v + v = 0)
    (hfree : ∀ (a : H) (v : U), v ≠ 0 → a • v = v → a = 1)
    (htrans : ∀ (v w : U), v ≠ 0 → w ≠ 0 → ∃ a : H, a • v = w)
    (f : U ≃+ U) (hf : ∀ (a : H) (v : U), f (a • v) = a⁻¹ • f v) :
    ∀ a : H, a ^ 3 = 1 := by
  obtain ⟨u,hu⟩ := exists_ne (0 : U)
  obtain ⟨c,hc⟩ := htrans u (f u) hu (by simpa using hu)
  have hcomm (a b : H) (v : U) : a • b • v = b • a • v := by
    rw [←mul_smul, mul_comm a b, mul_smul]
  have hsum (a b : H) (hab : u + a • u = b • u) : b*b=a := by
    have hh := congrArg f hab
    rw [map_add, hf, hf, ←hc] at hh
    have hi : u + a⁻¹ • u = b⁻¹ • u := by
      apply (smul_left_cancel_iff c).mp
      simpa only [smul_add, hcomm c a⁻¹ u, hcomm c b⁻¹ u] using hh
    have hi' := congrArg (fun v : U => a • v) hi
    rw [smul_add, smul_inv_smul, ←mul_smul, add_comm (a • u) u, hab] at hi'
    have he : b = a*b⁻¹ := actor_eq hu hfree hi'
    calc
      b*b = (a*b⁻¹)*b := congrArg (· * b) he
      _ = a := by rw [mul_assoc,inv_mul_cancel,mul_one]
  intro a
  by_cases ha : a=1
  · simp [ha]
  have hne : u + a • u ≠ 0 := by
    intro he
    have he' : a • u = u := by
      have hh := congrArg (u + ·) he
      simpa only [←add_assoc, htwo, zero_add, add_zero] using hh
    exact ha (hfree a u hu he')
  obtain ⟨b,hb⟩ := htrans u (u+a•u) hu hne
  have hba : b*b=a := hsum a b hb.symm
  have hab : a*a=b := hsum b a (by
    rw [hb, ←add_assoc, htwo, zero_add])
  have h4 : a^3*a=1*a := by
    calc
      a^3*a = (a*a)*(a*a) := by simp only [pow_succ, pow_zero, one_mul, mul_assoc]
      _ = b*b := by rw [hab]
      _ = a := hba
      _ = 1*a := (one_mul a).symm
  exact mul_right_cancel h4

private theorem axis_card [Finite U] :
    Nat.card ((⊤ : AddSubgroup U).prod (⊥ : AddSubgroup U)) = Nat.card U ∧
      Nat.card ((⊥ : AddSubgroup U).prod (⊤ : AddSubgroup U)) = Nat.card U := by
  constructor <;>
    rw [Nat.card_congr (AddSubgroup.prodEquiv _ _).toEquiv, Nat.card_prod] <;> simp

private theorem cubic_of_third_subgroup [Finite U] [Nontrivial U]
    (htwo : ∀ v : U, v+v=0)
    (hfree : ∀ (a : H) (v : U), v ≠ 0 → a • v=v → a=1)
    (htrans : ∀ (v w : U), v ≠ 0 → w ≠ 0 → ∃ a : H, a • v=w)
    (E : AddSubgroup (U × U)) (hcard : Nat.card E = Nat.card U)
    (hstable : ∀ (a : H) (v : U × U), v ∈ E → (a • v.1, a⁻¹ • v.2) ∈ E)
    (hleft : E ≠ (⊤ : AddSubgroup U).prod (⊥ : AddSubgroup U))
    (hright : E ≠ (⊥ : AddSubgroup U).prod (⊤ : AddSubgroup U)) : ∀ a : H, a^3=1 := by
  have hzeroLeft (v : U) (hv : (v,0) ∈ E) : v=0 := by
    by_contra hn
    apply hleft
    symm
    apply AddSubgroup.eq_of_le_of_card_ge ?_ (by rw [hcard, axis_card.1])
    rintro ⟨w,z⟩ ⟨_,hz⟩
    have hz' : z=0 := hz
    subst z
    by_cases hw : w=0
    · subst w; exact E.zero_mem
    · obtain ⟨a,ha⟩ := htrans v w hn hw
      simpa only [ha, smul_zero] using hstable a (v,0) hv
  have hzeroRight (v : U) (hv : (0,v) ∈ E) : v=0 := by
    by_contra hn
    apply hright
    symm
    apply AddSubgroup.eq_of_le_of_card_ge ?_ (by rw [hcard, axis_card.2])
    rintro ⟨z,w⟩ ⟨hz,_⟩
    have hz' : z=0 := hz
    subst z
    by_cases hw : w=0
    · subst w; exact E.zero_mem
    · obtain ⟨a,ha⟩ := htrans v w hn hw
      simpa only [inv_inv, ha, smul_zero] using hstable a⁻¹ (0,v) hv
  let p : E →+ U := (AddMonoidHom.fst U U).comp E.subtype
  let q : E →+ U := (AddMonoidHom.snd U U).comp E.subtype
  have hp : Function.Injective p := by
    apply (AddMonoidHom.ker_eq_bot_iff p).mp
    apply le_antisymm ?_ bot_le
    intro z hz
    have hz' : z.val.1=0 := hz
    have hh : z.val.2=0 := hzeroRight _ (by simpa only [←hz', Prod.mk.eta] using z.property)
    change z=0
    apply Subtype.ext
    exact Prod.ext hz' hh
  have hq : Function.Injective q := by
    apply (AddMonoidHom.ker_eq_bot_iff q).mp
    apply le_antisymm ?_ bot_le
    intro z hz
    have hz' : z.val.2=0 := hz
    have hh : z.val.1=0 := hzeroLeft _ (by simpa only [←hz', Prod.mk.eta] using z.property)
    change z=0
    apply Subtype.ext
    exact Prod.ext hh hz'
  let ep : E ≃+ U := AddEquiv.ofBijective p
    ((Nat.bijective_iff_injective_and_card p).mpr ⟨hp,hcard⟩)
  let eq : E ≃+ U := AddEquiv.ofBijective q
    ((Nat.bijective_iff_injective_and_card q).mpr ⟨hq,hcard⟩)
  let f : U ≃+ U := ep.symm.trans eq
  apply cubic_of_inverse_intertwiner htwo hfree htrans f
  intro a v
  let z := ep.symm v
  let w : E := ⟨(a • z.val.1,a⁻¹ • z.val.2),hstable a z.val z.property⟩
  have hz : z.val.1=v := ep.apply_symm_apply v
  have hw : ep w=a•v := by change a • z.val.1 = a • v; rw [hz]
  have he : ep.symm (a•v)=w := (ep.symm_apply_eq).mpr hw.symm
  change q (ep.symm (a•v)) = a⁻¹ • q z
  rw [he]
  rfl

/-- A third invariant summand in a binary module with opposite regular actions
forces every element of the abelian actor to have cube one. -/
theorem invariant_summand_eq_or_cubic
    {X V : Type*} [Group X] [AddCommGroup V] [DistribMulAction X V]
    (ι : H →* X) (t : X) (U : AddSubgroup V) [Finite U] [Nontrivial U]
    (htwo : ∀ v : V, v+v=0)
    (hU : ∀ (a : H) (v : V), v∈U → ι a • v∈U)
    (hinv : ∀ a : H, t * ι a * t⁻¹ = ι a⁻¹)
    (hfree : ∀ (a : H) (v : V), v∈U → v≠0 → ι a • v=v → a=1)
    (htrans : ∀ (v w : V), v∈U → w∈U → v≠0 → w≠0 → ∃ a:H, ι a • v=w)
    (hcompl : IsCompl U (U.map (DistribSMul.toAddMonoidHom V t)))
    (E : AddSubgroup V) (hcard : Nat.card E=Nat.card U)
    (hE : ∀ (a:H) (v:V), v∈E → ι a • v∈E) :
    E=U ∨ E=U.map (DistribSMul.toAddMonoidHom V t) ∨ ∀ a:H, a^3=1 := by
  let : DistribMulAction H U := {
    smul a v := ⟨ι a • v.val,hU a v.val v.property⟩
    one_smul v := Subtype.ext (show ι 1 • v.val = v.val by rw [map_one, one_smul])
    mul_smul a b v := Subtype.ext (show ι (a*b) • v.val = ι a • ι b • v.val by rw [map_mul, mul_smul])
    smul_zero a := Subtype.ext (smul_zero (ι a))
    smul_add a v w := Subtype.ext (smul_add (ι a) v.val w.val) }
  let F : U × U →+ V :=
    { toFun := fun v => v.1.val + t • v.2.val
      map_zero' := by simp
      map_add' := by
        intros
        simp only [Prod.fst_add, Prod.snd_add, AddSubgroup.coe_add, smul_add]
        abel }
  have hF : Function.Bijective F := by
    constructor
    · apply (injective_iff_map_eq_zero F).mpr
      rintro ⟨v,w⟩ hvw
      change v.val + t • w.val=0 at hvw
      have he : v.val = -(t • w.val) := eq_neg_of_add_eq_zero_left hvw
      have hz : v.val=0 := AddSubgroup.disjoint_def.mp hcompl.disjoint v.property (by
        rw [he]
        exact AddSubgroup.neg_mem _ ⟨w.val,w.property,rfl⟩)
      have hw : w.val=0 := by
        have hh : t • w.val=0 := by simpa only [hz, zero_add] using hvw
        exact (smul_left_cancel_iff t).mp (hh.trans (smul_zero t).symm)
      exact Prod.ext (Subtype.ext hz) (Subtype.ext hw)
    · intro v
      obtain ⟨u,hu,w,hw,huw⟩ := AddSubgroup.mem_sup.mp
        (show v ∈ U ⊔ U.map (DistribSMul.toAddMonoidHom V t) by rw [hcompl.sup_eq_top]; trivial)
      obtain ⟨w,hw,rfl⟩ := hw
      exact ⟨(⟨u,hu⟩,⟨w,hw⟩),huw⟩
  let D := E.comap F
  have hmap : D.map F=E := AddSubgroup.map_comap_eq_self_of_surjective hF.2 E
  have hDcard : Nat.card D=Nat.card U := by
    rw [←AddSubgroup.card_map_of_injective hF.1, hmap,hcard]
  have hD (a:H) (v:U×U) (hv:v∈D) : (a•v.1,a⁻¹•v.2)∈D := by
    change ι a • v.1.val + t • (ι a⁻¹ • v.2.val) ∈ E
    have he : t*ι a⁻¹=ι a*t := by
      have hh := hinv a⁻¹
      rw [inv_inv] at hh
      exact mul_inv_eq_iff_eq_mul.mp hh
    rw [←mul_smul,he,mul_smul,←smul_add]
    exact hE a (F v) hv
  have hleft : ((⊤:AddSubgroup U).prod (⊥:AddSubgroup U)).map F=U := by
    ext v
    constructor
    · rintro ⟨⟨u,w⟩,⟨_,hw⟩,rfl⟩
      have hw' : w=0 := hw
      simp only [F,AddMonoidHom.coe_mk,ZeroHom.coe_mk,hw',AddSubgroup.coe_zero,smul_zero,add_zero]
      exact u.property
    · intro hv
      exact ⟨(⟨v,hv⟩,0),⟨trivial,rfl⟩,by simp [F]⟩
  have hright : ((⊥:AddSubgroup U).prod (⊤:AddSubgroup U)).map F=
      U.map (DistribSMul.toAddMonoidHom V t) := by
    ext v
    constructor
    · rintro ⟨⟨u,w⟩,⟨hu,_⟩,rfl⟩
      have hu' : u=0 := hu
      exact ⟨w.val,w.property,by simp [F,hu']⟩
    · rintro ⟨w,hw,rfl⟩
      exact ⟨(0,⟨w,hw⟩),⟨rfl,trivial⟩,by simp [F]⟩
  by_cases hl : D=(⊤:AddSubgroup U).prod (⊥:AddSubgroup U)
  · exact Or.inl (hmap.symm.trans ((congrArg (AddSubgroup.map F) hl).trans hleft))
  by_cases hr : D=(⊥:AddSubgroup U).prod (⊤:AddSubgroup U)
  · exact Or.inr (Or.inl (hmap.symm.trans ((congrArg (AddSubgroup.map F) hr).trans hright)))
  right; right
  apply cubic_of_third_subgroup (fun v => Subtype.ext (htwo v)) ?_ ?_ D hDcard hD hl hr
  · intro a v hv he
    exact hfree a v.val v.property (fun hh => hv (Subtype.ext hh)) (congrArg Subtype.val he)
  · intro v w hv hw
    obtain ⟨a,ha⟩ := htrans v.val w.val v.property w.property
      (fun hh => hv (Subtype.ext hh)) (fun hh => hw (Subtype.ext hh))
    exact ⟨a,Subtype.ext ha⟩
end Theory.GroupAction
