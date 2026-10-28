module
public import Theory.GroupTheory.WeakBNPair.RegularTree.NaturalReflection

/-!
# Cartan reflections with a central natural-coordinate kernel

Let a finite local actor map onto SL₂ in characteristic two. Its actual
kernel is a two-group and maps onto the natural plane, with a central kernel.
Hall conjugacy first corrects a lift to normalize an odd diagonal Cartan.
The square of the correction centralizes the Cartan, so its natural image
vanishes. The reflection's fixed vectors are its differences; hence the
correction is a conjugation modulo the central coordinate kernel. Removing
that central discrepancy preserves normalization and the original involution
conjugacy class. No splitting of the actor or triviality of its center is used.

The trivial Cartan case includes the binary field. This normalizes the Cartan
inside the actor; transport to an additional Cartan factor outside the actor
is a separate obligation. In particular this is not the full source (14.2).

Source: DGS, *Groups and Graphs* (1985), (10.5), pp.155--157, and the
reflection lifting argument in (14.2), pp.210--211.
-/

@[expose] public noncomputable section
open Subgroup Matrix Matrix.SpecialLinearGroup
open scoped MatrixGroups Pointwise
namespace Theory.GroupTheory.WeakBNPair.RegularTree.NaturalCubic
variable {F X : Type*} [Field F] [CharP F 2] [Group X]

/-- Natural coordinates on the actual two-kernel, allowing a central kernel of the coordinate map. -/
structure NaturalCentralKernel (π : X →* SL(2,F)) where
  coordinates : π.ker →* Multiplicative (Fin 2 → F)
  onto : Function.Surjective coordinates
  central : ∀ z : π.ker, coordinates z=1 → (z:X)∈center X
  isTwo : IsPGroup 2 π.ker
  equivariant : ∀ (g : X) (z : π.ker),
    coordinates ⟨g*z*g⁻¹,(inferInstance : π.ker.Normal).conj_mem z z.property g⟩ =
      Matrix.SL2.naturalAction F (π g) (coordinates z)

namespace NaturalCentralKernel
variable {π : X →* SL(2,F)} (d : NaturalCentralKernel π)

include d in
omit [CharP F 2] in
/-- A nonidentity diagonal actor kills the natural image of its kernel centralizer. -/
theorem coordinates_eq_one_of_commute_diagonal (z : π.ker) (k : X)
    (b : F) (hb : b≠0) (hb1 : b≠1) (hπk : π k=diag2 b hb)
    (hz : Commute k (z:X)) : d.coordinates z=1 := by
  have hc : (⟨k*z*k⁻¹,(inferInstance : π.ker.Normal).conj_mem z z.property k⟩ : π.ker)=z := by
    apply Subtype.ext
    change k*(z:X)*k⁻¹=(z:X)
    rw [hz.eq,mul_inv_cancel_right]
  have he := d.equivariant k z
  rw [hc,hπk] at he
  exact Multiplicative.toAdd.injective
    (diagonal_fixed b hb hb1 _ (congrArg Multiplicative.toAdd he).symm)

include d in
/-- Hall correction can be replaced by kernel conjugation, despite the central coordinate kernel. -/
theorem exists_conjugate_normalizing [Finite X]
    (K : Subgroup X) [Group.IsSolvable K]
    (hodd : Nat.Coprime 2 (Nat.card K))
    (k : X) (hk : k∈K) (b : F) (hb : b≠0) (hb1 : b≠1) (hπk : π k=diag2 b hb)
    (v : X) (hv : v*v=1) (a : F) (ha : a≠0)
    (hπv : π v=upper a*lower a⁻¹*upper a)
    (hn : π v∈normalizer (K.map π : Set SL(2,F))) :
    ∃ z : π.ker, (z:X)*v*(z:X)⁻¹∈normalizer (K : Set X) := by
  obtain ⟨q,hq,ht⟩ := exists_cartan_normalizer_lift π K d.isTwo hodd v hn
  let t := q*v
  let qQ : π.ker := ⟨q,hq⟩
  have hπt : π t=π v := by simp only [t,map_mul,show π q=1 from hq,one_mul]
  have hdis : K ⊓ π.ker=⊥ := by
    obtain ⟨m,hm⟩ := d.isTwo.exists_card_eq
    exact (disjoint_of_coprime_natCard (by rw [hm]; exact hodd.symm.pow_right m)).eq_bot
  have hs : t*t∈π.ker := by
    change π (t*t)=1
    rw [map_mul,hπt,←map_mul,hv,map_one]
  have hsC : t*t∈centralizer (K : Set X) :=
    kernel_normalizer_centralizes π K hdis hs ((normalizer (K : Set X)).mul_mem ht ht)
  let s : π.ker := ⟨t*t,hs⟩
  have hsφ : d.coordinates s=1 :=
    d.coordinates_eq_one_of_commute_diagonal s k b hb hb1 hπk
      (mem_centralizer_iff.mp hsC k hk)
  have hprod : qQ*(⟨v*qQ*v⁻¹,(inferInstance : π.ker.Normal).conj_mem qQ qQ.property v⟩ : π.ker)=s := by
    apply Subtype.ext
    change q*(v*q*v⁻¹)=(q*v)*(q*v)
    rw [inv_eq_of_mul_eq_one_right hv]
    group
  have hvfix : (upper a*lower a⁻¹*upper a).val *ᵥ (d.coordinates qQ).toAdd =
      (d.coordinates qQ).toAdd := by
    have he := congrArg d.coordinates hprod
    rw [map_mul,d.equivariant,hπv,hsφ] at he
    have he' := congrArg Multiplicative.toAdd he
    change (d.coordinates qQ).toAdd +
      (upper a*lower a⁻¹*upper a).val *ᵥ (d.coordinates qQ).toAdd=0 at he'
    have hh := eq_neg_of_add_eq_zero_right he'
    exact hh.trans (by ext i; exact CharTwo.neg_eq _)
  obtain ⟨w,hw⟩ := braid_fixed_difference a ha (d.coordinates qQ).toAdd hvfix
  obtain ⟨z,hz⟩ := d.onto (Multiplicative.ofAdd w)
  let c : π.ker := z*(⟨v*z*v⁻¹,(inferInstance : π.ker.Normal).conj_mem z z.property v⟩ : π.ker)⁻¹
  have hcφ : d.coordinates c=d.coordinates qQ := by
    change d.coordinates (z*(⟨v*z*v⁻¹,_⟩ : π.ker)⁻¹)=_
    rw [map_mul,map_inv,d.equivariant,hπv,hz]
    apply Multiplicative.toAdd.injective
    simpa only [toAdd_mul,toAdd_inv,Matrix.SL2.naturalAction_apply,
      toAdd_ofAdd,←sub_eq_add_neg] using hw
  have hcentral : ((qQ*c⁻¹ : π.ker):X)∈center X :=
    d.central (qQ*c⁻¹) (by rw [map_mul,map_inv,hcφ,mul_inv_cancel])
  have he : t=(((qQ*c⁻¹ : π.ker):X))*((z:X)*v*(z:X)⁻¹) := by
    change q*v=(q*((z:X)*(v*(z:X)*v⁻¹)⁻¹)⁻¹)*((z:X)*v*(z:X)⁻¹)
    group
  refine ⟨z,?_⟩
  have hnc : (((qQ*c⁻¹ : π.ker):X))∈normalizer (K : Set X) :=
    center_le_normalizer (K : Set X) hcentral
  have hh := (normalizer (K : Set X)).mul_mem
    ((normalizer (K : Set X)).inv_mem hnc) ht
  change (((qQ*c⁻¹ : π.ker):X))⁻¹*t∈normalizer (K : Set X) at hh
  rw [he,inv_mul_cancel_left] at hh
  exact hh
include d in
/-- The selected upper-root involution has a conjugate normalizing the actor Cartan, with its braid matrix retained. -/
theorem exists_diagonal_cartan_reflection [Finite X]
    (honto : Function.Surjective π) (K : Subgroup X)
    [Group.IsSolvable K] (hodd : Nat.Coprime 2 (Nat.card K))
    (hdiag : ∀ k∈K, ∃ b : F, ∃ hb : b≠0, π k=diag2 b hb)
    (x : X) (hx : x*x=1) (a : F) (ha : a≠0) (hπx : π x=upper a) :
    ∃ t : X, t∈normalizer (K : Set X) ∧ t*t=1 ∧ orderOf t=2 ∧
      π t=upper a*lower a⁻¹*upper a ∧ ∃ g : X, g*x*g⁻¹=t := by
  obtain ⟨g,hg⟩ := honto (lower a⁻¹)
  let v := g*x*g⁻¹
  have hv : v*v=1 := by
    calc
      _ = g*(x*x)*g⁻¹ := by dsimp [v]; group
      _ = 1 := by rw [hx,mul_one,mul_inv_cancel]
  have hπv : π v=upper a*lower a⁻¹*upper a := by
    change π (g*x*g⁻¹)=_
    rw [map_mul,map_mul,map_inv,hg,hπx,lower_conjugates_upper a ha]
  have hne : π v≠1 := by
    intro he
    have hh := congrArg (fun z : SL(2,F) => z.val 0 1) he
    rw [hπv,braid_matrix a ha] at hh
    exact ha hh
  have hnorm : π v∈normalizer (K.map π : Set SL(2,F)) := by
    apply mem_normalizer_iff.mpr
    intro y
    have hi : (π v)⁻¹=π v := by
      apply inv_eq_of_mul_eq_one_right
      rw [←map_mul,hv,map_one]
    have hin : ∀ y∈K.map π, π v*y*(π v)⁻¹∈K.map π := by
      rintro y ⟨k,hk,rfl⟩
      obtain ⟨b,hb,hbπ⟩ := hdiag k hk
      have he : π v*π k*(π v)⁻¹=π (k⁻¹) := by
        rw [hπv,hbπ,braid_inverts_diagonal a b ha hb,map_inv,hbπ]
      rw [he]
      exact mem_map_of_mem π (K.inv_mem hk)
    constructor
    · exact hin y
    · intro hy
      have he := hin _ hy
      have heq : π v*(π v*y*(π v)⁻¹)*(π v)⁻¹=y := by
        rw [hi]
        calc
          _ = (π v*π v)*y*(π v*π v) := by group
          _ = y := by rw [←map_mul,hv,map_one,one_mul,mul_one]
      rwa [heq] at he
  have hex : ∃ z : π.ker, (z:X)*v*(z:X)⁻¹∈normalizer (K : Set X) := by
    by_cases hbot : K=⊥
    · refine ⟨1,?_⟩
      rw [hbot,normalizer_eq_top]
      exact mem_top _
    obtain ⟨k,hk,hk1⟩ := K.bot_or_exists_ne_one.resolve_left hbot
    have hdis : K ⊓ π.ker=⊥ := by
      obtain ⟨m,hm⟩ := d.isTwo.exists_card_eq
      exact (disjoint_of_coprime_natCard (by rw [hm]; exact hodd.symm.pow_right m)).eq_bot
    have hkπ : π k≠1 := by
      intro he
      have hm : k∈K ⊓ π.ker := ⟨hk,he⟩
      rw [hdis] at hm
      exact hk1 hm
    obtain ⟨b,hb,hbπ⟩ := hdiag k hk
    have hb1 : b≠1 := by
      intro he
      apply hkπ
      rw [hbπ]
      apply Subtype.ext
      ext i j
      fin_cases i <;> fin_cases j <;> simp [diag2_coe',he]
    exact d.exists_conjugate_normalizing K hodd k hk b hb hb1 hbπ v hv a ha hπv hnorm
  obtain ⟨z,hz⟩ := hex
  let t := (z:X)*v*(z:X)⁻¹
  have ht : t*t=1 := by
    calc
      _ = (z:X)*(v*v)*(z:X)⁻¹ := by dsimp [t]; group
      _ = 1 := by rw [hv,mul_one,mul_inv_cancel]
  have hπt : π t=π v := by
    simp only [t,map_mul,map_inv,show π (z:X)=1 from z.property,one_mul,inv_one,mul_one]
  refine ⟨t,hz,ht,?_,hπt.trans hπv,(z:X)*g,?_⟩
  · apply orderOf_eq_prime (show t^2=1 by simpa only [pow_two] using ht)
    intro he
    exact hne (hπt.symm.trans (he ▸ π.map_one))
  · dsimp [t,v]
    group

/-- Rebase the same quotient by an inner matrix marking, transporting the
natural coordinates by that very matrix. No kernel or actor is changed. -/
def conj (a : SL(2,F)) : NaturalCentralKernel ((MulAut.conj a).toMonoidHom.comp π) := by
  let π' := (MulAut.conj a).toMonoidHom.comp π
  have he : π'.ker=π.ker := by
    ext x
    change a*π x*a⁻¹=1 ↔ π x=1
    simp only [mul_inv_eq_one, mul_eq_left]
  let e : π'.ker ≃* π.ker := MulEquiv.subgroupCongr he
  let A := Matrix.SL2.naturalAction F a
  refine ⟨A.toMonoidHom.comp (d.coordinates.comp e.toMonoidHom),
    A.surjective.comp (d.onto.comp e.surjective),?_,d.isTwo.of_equiv e.symm,?_⟩
  · intro z hz
    exact d.central (e z) (A.injective (hz.trans A.map_one.symm))
  · intro g z
    have heq : e ⟨g*z*g⁻¹,(inferInstance : π'.ker.Normal).conj_mem z z.property g⟩=
        ⟨g*e z*g⁻¹,(inferInstance : π.ker.Normal).conj_mem (e z) (e z).property g⟩ := rfl
    change A (d.coordinates (e ⟨g*z*g⁻¹,_⟩))=
      Matrix.SL2.naturalAction F (a*π g*a⁻¹) (A (d.coordinates (e z)))
    rw [heq,d.equivariant]
    have hr : (Matrix.SL2.naturalAction F (a*π g*a⁻¹))*A=
        A*(Matrix.SL2.naturalAction F (π g)) := by
      change (Matrix.SL2.naturalAction F (a*π g*a⁻¹))*(Matrix.SL2.naturalAction F a)=_
      rw [←map_mul, inv_mul_cancel_right, map_mul]
    exact (congrArg (fun f : MulAut (Multiplicative (Fin 2 → F)) =>
      f (d.coordinates (e z))) hr).symm


/-- Transport the same quotient and central natural coordinates through an actor isomorphism. -/
def ofEquiv {Y : Type*} [Group Y] (e : Y ≃* X) :
    NaturalCentralKernel (π.comp e.toMonoidHom) := by
  let f : (π.comp e.toMonoidHom).ker →* π.ker :=
    { toFun z := ⟨e z,z.property⟩
      map_one' := Subtype.ext e.map_one
      map_mul' x y := Subtype.ext (e.map_mul x y) }
  have hf : Function.Bijective f := by
    constructor
    · intro x y he
      exact Subtype.ext (e.injective (congrArg Subtype.val he))
    · intro z
      refine ⟨⟨e.symm z,?_⟩,Subtype.ext (e.apply_symm_apply z)⟩
      change π (e (e.symm z))=1
      rw [e.apply_symm_apply]
      exact z.property
  refine ⟨d.coordinates.comp f,d.onto.comp hf.2,?_,d.isTwo.of_injective f hf.1,?_⟩
  · intro z hz
    have hc := d.central (f z) hz
    apply Subgroup.mem_center_iff.mpr
    intro y
    apply e.injective
    have he := Subgroup.mem_center_iff.mp hc (e y)
    change e y * e z = e z * e y at he
    simpa only [map_mul] using he
  · intro g z
    change d.coordinates (f ⟨g*z*g⁻¹,_⟩)=
      Matrix.SL2.naturalAction F (π (e g)) (d.coordinates (f z))
    have he : f ⟨g*z*g⁻¹,(inferInstance : (π.comp e.toMonoidHom).ker.Normal).conj_mem z z.property g⟩=
        ⟨e g*f z*(e g)⁻¹,(inferInstance : π.ker.Normal).conj_mem (f z) (f z).property (e g)⟩ := by
      apply Subtype.ext
      exact map_mul e _ _ |>.trans (by rw [map_mul,map_inv]; rfl)
    rw [he,d.equivariant]

end NaturalCentralKernel
end Theory.GroupTheory.WeakBNPair.RegularTree.NaturalCubic
