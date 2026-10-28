module

public import Theory.GroupTheory.SubgroupConjugation
public import Theory.GroupTheory.SolvableOuterQuotient

/-!
# Fiber products of actual conjugation actions

For normal subgroups `N ≤ A`, `M ≤ B` and an isomorphism `d : N ≃* M`,
the fiber product consists of pairs inducing the same automorphism of `N`.
It contains the normal diagonal copy of `N`. Neither projection is presumed
injective: its kernel is the centralizer of the other normal subgroup.

This is the group-theoretic diagram used to compare extensions with the same
outer action while retaining their central kernels. The second Tits parabolic
application is in `ExceptionalParabolics.SecondCoreActionLifting`.
-/

@[expose] public section
noncomputable section
namespace ConjugationFiberProduct
open Subgroup

variable {A B : Type*} [Group A] [Group B]
variable (N : Subgroup A) (M : Subgroup B) [N.Normal] [M.Normal] (d : N ≃* M)

/-- Conjugation in the second group expressed in the first core's coordinates. -/
def action : B →* MulAut N :=
  (MulAut.congr d.symm).toMonoidHom.comp MulAut.conjNormal

omit [N.Normal] in
theorem action_apply (b : B) (n : N) :
    d (action N M d b n) = MulAut.conjNormal b (d n) :=
  d.apply_symm_apply _

/-- Pairs with literally equal actions on the identified normal subgroup. -/
def fiber : Subgroup (A × B) :=
  ((MulAut.conjNormal : A →* MulAut N).comp (MonoidHom.fst A B)).eqLocus
    ((action N M d).comp (MonoidHom.snd A B))

def fst : fiber N M d →* A := (MonoidHom.fst A B).comp (fiber N M d).subtype
def snd : fiber N M d →* B := (MonoidHom.snd A B).comp (fiber N M d).subtype

theorem compatible (x : fiber N M d) (n : N) :
    d (MulAut.conjNormal (fst N M d x) n) =
      MulAut.conjNormal (snd N M d x) (d n) := by
  rw [show MulAut.conjNormal (fst N M d x) = action N M d (snd N M d x)
    from x.property]
  exact action_apply N M d _ _

theorem fst_surjective
    (h : (action N M d).range = (MulAut.conjNormal : A →* MulAut N).range) :
    Function.Surjective (fst N M d) := by
  intro a
  obtain ⟨b,hb⟩ := h.symm ▸ (show MulAut.conjNormal a ∈
    (MulAut.conjNormal : A →* MulAut N).range from ⟨a,rfl⟩)
  exact ⟨⟨(a,b),hb.symm⟩,rfl⟩

theorem snd_surjective
    (h : (action N M d).range = (MulAut.conjNormal : A →* MulAut N).range) :
    Function.Surjective (snd N M d) := by
  intro b
  obtain ⟨a,ha⟩ := h ▸ (show action N M d b ∈ (action N M d).range from ⟨b,rfl⟩)
  exact ⟨⟨(a,b),ha⟩,rfl⟩

/-- The original core embeds diagonally, with its given identification. -/
def diagonalHom : N →* fiber N M d :=
  (N.subtype.prod (M.subtype.comp d.toMonoidHom)).codRestrict _ (by
    intro n
    apply MulEquiv.ext
    intro q
    apply d.injective
    change d (MulAut.conjNormal (n : A) q) = d (action N M d (d n) q)
    rw [action_apply]
    change d (n*q*n⁻¹) = d n * d q * (d n)⁻¹
    simp only [map_mul,map_inv])

def diagonal : Subgroup (fiber N M d) := (diagonalHom N M d).range

theorem diagonalHom_injective : Function.Injective (diagonalHom N M d) := by
  intro x y h
  exact Subtype.ext (congrArg (fst N M d) h)

instance diagonal_normal : (diagonal N M d).Normal := by
  constructor
  rintro _ ⟨n,rfl⟩ x
  refine ⟨MulAut.conjNormal (fst N M d x) n,?_⟩
  apply Subtype.ext
  apply Prod.ext
  · rfl
  · exact congrArg Subtype.val (compatible N M d x n)

theorem disjoint_diagonal_fst_ker : Disjoint (diagonal N M d) (fst N M d).ker := by
  rw [Subgroup.disjoint_def]
  rintro x ⟨n,rfl⟩ hn
  have hn1 : n = 1 := Subtype.ext hn
  rw [hn1,map_one]

theorem disjoint_diagonal_snd_ker : Disjoint (diagonal N M d) (snd N M d).ker := by
  rw [Subgroup.disjoint_def]
  rintro x ⟨n,rfl⟩ hn
  have hd1 : d n = 1 := Subtype.ext (show (d n : B) = 1 from hn)
  have hn1 : n = 1 := d.injective (hd1.trans d.map_one.symm)
  rw [hn1,map_one]

/-- The first projection's kernel is the second core's full centralizer. -/
def fstKerEquiv : (fst N M d).ker ≃* centralizer (M : Set B) := by
  let f : (fst N M d).ker →* centralizer (M : Set B) :=
    ((snd N M d).comp (fst N M d).ker.subtype).codRestrict _ (by
      intro x
      rw [← MulAut.conjNormal_ker_eq_centralizer]
      apply (MulAut.congr d.symm).injective
      rw [map_one]
      change action N M d (snd N M d x.val) = 1
      rw [← show MulAut.conjNormal (fst N M d x.val) =
        action N M d (snd N M d x.val) from x.val.property]
      rw [show fst N M d x.val = 1 from x.property,map_one])
  apply MulEquiv.ofBijective f
  constructor
  · intro x y h
    apply Subtype.ext
    apply Subtype.ext
    exact Prod.ext (x.property.trans y.property.symm) (congrArg Subtype.val h)
  · intro b
    have hb : action N M d b.val = 1 := by
      have h : b.val ∈ (MulAut.conjNormal : B →* MulAut M).ker := by
        simpa only [MulAut.conjNormal_ker_eq_centralizer] using b.property
      change (MulAut.congr d.symm) (MulAut.conjNormal b.val) = 1
      rw [show MulAut.conjNormal b.val = 1 from h,map_one]
    refine ⟨⟨⟨(1,b.val),?_⟩,rfl⟩,rfl⟩
    change MulAut.conjNormal (1 : A) = action N M d b.val
    rw [map_one,hb]

/-- Exact fiber order, before taking the diagonal quotient. -/
theorem card_fiber [Finite A] [Finite B]
    (h : (action N M d).range = (MulAut.conjNormal : A →* MulAut N).range) :
    Nat.card (fiber N M d) = Nat.card (centralizer (M : Set B)) * Nat.card A := by
  have hc := (fst N M d).ker.card_mul_index
  rw [index_ker,MonoidHom.range_eq_top.mpr (fst_surjective N M d h),card_top,
    Nat.card_congr (fstKerEquiv N M d).toEquiv] at hc
  exact hc.symm

theorem card_diagonal : Nat.card (diagonal N M d) = Nat.card N :=
  (Nat.card_congr (MonoidHom.ofInjective (diagonalHom_injective N M d)).toEquiv).symm

/-- The diagonal is killed only here, after forming the full fiber product. -/
abbrev Quotient := fiber N M d ⧸ diagonal N M d

def quotientMap : fiber N M d →* Quotient N M d :=
  QuotientGroup.mk' (diagonal N M d)

def kernelImage : Subgroup (Quotient N M d) :=
  (fst N M d).ker.map (quotientMap N M d)

theorem quotientMap_diagonal (n : N) :
    quotientMap N M d (diagonalHom N M d n) = 1 :=
  (QuotientGroup.eq_one_iff _).mpr ⟨n,rfl⟩

/-- Both central kernels give the same subgroup after quotienting the diagonal.
Self-centralization is needed here, and is not inferred from equality of actions. -/
theorem kernel_images_eq
    (hcN : centralizer (N : Set A) ≤ N) (hcM : centralizer (M : Set B) ≤ M) :
    kernelImage N M d = (snd N M d).ker.map (quotientMap N M d) := by
  apply le_antisymm
  · rintro _ ⟨x,hx,rfl⟩
    have hb : snd N M d x ∈ M := hcM (fstKerEquiv N M d ⟨x,hx⟩).property
    let n := d.symm ⟨snd N M d x,hb⟩
    let y := x * (diagonalHom N M d n)⁻¹
    refine ⟨y,?_,?_⟩
    · change snd N M d (x * (diagonalHom N M d n)⁻¹) = 1
      rw [map_mul,map_inv]
      change snd N M d x * (d (d.symm ⟨snd N M d x,hb⟩)).val⁻¹ = 1
      rw [d.apply_symm_apply,mul_inv_cancel]
    · simp only [y,map_mul,map_inv,quotientMap_diagonal,inv_one,mul_one]
  · rintro _ ⟨x,hx,rfl⟩
    have ha : fst N M d x ∈ N := by
      apply hcN
      rw [← MulAut.conjNormal_ker_eq_centralizer]
      change MulAut.conjNormal (fst N M d x) = 1
      rw [show MulAut.conjNormal (fst N M d x) = action N M d (snd N M d x)
        from x.property,show snd N M d x = 1 from hx,map_one]
    let n : N := ⟨fst N M d x,ha⟩
    let y := x * (diagonalHom N M d n)⁻¹
    refine ⟨y,?_,?_⟩
    · change fst N M d (x * (diagonalHom N M d n)⁻¹) = 1
      rw [map_mul,map_inv]
      exact mul_inv_cancel _
    · simp only [y,map_mul,map_inv,quotientMap_diagonal,inv_one,mul_one]

end ConjugationFiberProduct
