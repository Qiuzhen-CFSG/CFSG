module
public import Theory.GroupTheory.QuotientCommonImage
public import Theory.Representation.SL3.PointConstituents

/-!
# Marked natural common quotients

For two maps p : M → F² and q : M → C with q onto and C abelian,
assume the image of p and the p-image of ker q are invariant under the
same surjective SL₂ action. Irreducibility among additive subgroups makes
C/q(ker p) trivial or the marked natural plane. In the latter case the
isomorphism sends the class of every q(x) to p(x).

The proof applies natural irreducibility to both images, then the actual
two-projection isomorphism theorem. The invariance premises are phrased as
lifts so callers can use their original conjugation maps directly.
Source application: Aschbacher--Smith 11.1.2, printed pp.763--764.
-/

open Subgroup
namespace QuotientGroup.CommonImage
@[expose] public noncomputable section
variable {M C H F : Type*} [Group M] [CommGroup C] [Group H] [Field F]

/-- An irreducible natural image has only a trivial or the same marked natural
common quotient. Both invariance conditions concern the original maps. -/
theorem natural_quotient_dichotomy
    (p : M →* Multiplicative (Fin 2 → F)) (q : M →* C)
    (hq : Function.Surjective q)
    (r : H →* Matrix.SpecialLinearGroup (Fin 2) F) (hr : Function.Surjective r)
    (himage : ∀ h x, ∃ y, p y = Matrix.SL2.naturalAction F (r h) (p x))
    (hkernel : ∀ h x, q x = 1 → ∃ y, q y = 1 ∧
      p y = Matrix.SL2.naturalAction F (r h) (p x)) :
    kernelImage p q = ⊤ ∨
      ∃ e : (C ⧸ kernelImage p q) ≃* Multiplicative (Fin 2 → F),
        ∀ x, e (QuotientGroup.mk' (kernelImage p q) (q x)) = p x := by
  have hi := Representation.SL3PointConstituents.natural_irreducible F r hr p.range
    (by rintro h _ ⟨x,rfl⟩; exact himage h x)
  rcases hi with hi | hi
  · left
    apply top_unique
    intro c _
    obtain ⟨x,rfl⟩ := hq c
    exact mem_map_of_mem q (show x ∈ p.ker from
      mem_bot.mp (hi ▸ (show p x ∈ p.range from ⟨x,rfl⟩)))
  have hk := Representation.SL3PointConstituents.natural_irreducible F r hr (q.ker.map p)
    (by
      rintro h _ ⟨x,hx,rfl⟩
      obtain ⟨y,hy,hpy⟩ := hkernel h x hx
      exact ⟨y,hy,hpy⟩)
  rcases hk with hk | hk
  · right
    have hk' : q.ker.map p.rangeRestrict = ⊥ := by
      apply (map_eq_bot_iff_of_injective _ p.range.subtype_injective).mp
      simpa only [Subgroup.map_map,MonoidHom.subtype_comp_rangeRestrict] using hk
    have hinj : Function.Injective (map p q) := by
      apply (MonoidHom.ker_eq_bot_iff _).mp
      rw [map_ker,hk']
    let e := MulEquiv.ofBijective (map p q) ⟨hinj,map_surjective p q hq⟩
    let j : p.range ≃* Multiplicative (Fin 2 → F) :=
      MulEquiv.ofBijective p.range.subtype ⟨p.range.subtype_injective,
        fun v => ⟨⟨v,hi ▸ mem_top v⟩,rfl⟩⟩
    refine ⟨e.symm.trans j,fun x => ?_⟩
    change j (e.symm (QuotientGroup.mk' (kernelImage p q) (q x))) = p x
    rw [←map_apply p q x]
    change j (e.symm (e (p.rangeRestrict x))) = p x
    rw [e.symm_apply_apply]
    rfl
  · left
    apply top_unique
    intro c _
    obtain ⟨x,rfl⟩ := hq c
    obtain ⟨y,hy,he⟩ := hk.ge (mem_top (p x))
    refine ⟨x*y⁻¹,?_,?_⟩
    · change p (x*y⁻¹) = 1
      rw [map_mul,map_inv,he,mul_inv_cancel]
    · rw [map_mul,map_inv,show q y = 1 from hy,inv_one,mul_one]

end
end QuotientGroup.CommonImage

open Subgroup Matrix
open scoped MatrixGroups
namespace QuotientGroup.CommonImage
@[expose] public noncomputable section
private theorem natural_fixed_eq_one {F H : Type*} [Field F] [Group H]
    (r : H →* SL(2,F)) (hr : Function.Surjective r)
    (v : Multiplicative (Fin 2 → F))
    (hv : ∀ h, Matrix.SL2.naturalAction F (r h) v = v) : v = 1 := by
  have hh (g : SL(2,F)) : Matrix.SL2.naturalAction F g v = v := by
    obtain ⟨h,rfl⟩ := hr g
    exact hv h
  let a : SL(2,F) := ⟨!![1,1;0,1],by simp [Matrix.det_fin_two]⟩
  let b : SL(2,F) := ⟨!![1,0;1,1],by simp [Matrix.det_fin_two]⟩
  have ha := congrArg (fun w => w.toAdd 0) (hh a)
  have hb := congrArg (fun w => w.toAdd 1) (hh b)
  change (!![1,1;0,1] *ᵥ v.toAdd) 0 = v.toAdd 0 at ha
  change (!![1,0;1,1] *ᵥ v.toAdd) 1 = v.toAdd 1 at hb
  have hv1 : v.toAdd 1 = 0 := by
    simpa [a,Matrix.SL2.naturalAction_apply,Matrix.mulVec,dotProduct,Fin.sum_univ_two] using ha
  have hv0 : v.toAdd 0 = 0 := by
    simpa [b,Matrix.SL2.naturalAction_apply,Matrix.mulVec,dotProduct,Fin.sum_univ_two] using hb
  apply Multiplicative.toAdd.injective
  ext i
  fin_cases i <;> assumption

/-- Identify the central kernel as the full fixed subgroup while preserving
an already named original kernel and both representative maps. -/
theorem natural_quotient_fixed_kernel
    {M C H F : Type*} [Group M] [CommGroup C] [Group H] [Field F]
    (p : M →* Multiplicative (Fin 2 → F)) (q : M →* C)
    (hq : Function.Surjective q)
    (r : H →* Matrix.SpecialLinearGroup (Fin 2) F) (hr : Function.Surjective r)
    (Z R : Subgroup C) (hZ : kernelImage p q = Z) (hZR : Z ≤ R)
    (himage : ∀ h x, ∃ y, p y = Matrix.SL2.naturalAction F (r h) (p x))
    (hkernel : ∀ h x, q x = 1 → ∃ y, q y = 1 ∧
      p y = Matrix.SL2.naturalAction F (r h) (p x))
    (hfixed : ∀ h x, q x ∈ R → ∃ y, q y = q x ∧
      p y = Matrix.SL2.naturalAction F (r h) (p x)) :
    Z = R ∧ (Z = ⊤ ∨
      ∃ e : (C ⧸ Z) ≃* Multiplicative (Fin 2 → F),
        ∀ x, e (QuotientGroup.mk' Z (q x)) = p x) := by
  have hquot := natural_quotient_dichotomy p q hq r hr himage hkernel
  rw [hZ] at hquot
  refine ⟨le_antisymm hZR ?_,hquot⟩
  rcases hquot with hz | ⟨e,he⟩
  · rw [hz]; exact le_top
  intro w hw
  apply (QuotientGroup.eq_one_iff _).mp
  apply e.injective
  rw [map_one]
  apply natural_fixed_eq_one r hr
  intro h
  obtain ⟨x,rfl⟩ := hq w
  obtain ⟨y,hy,hp⟩ := hfixed h x hw
  change Matrix.SL2.naturalAction F (r h) (e (QuotientGroup.mk' Z (q x))) =
    e (QuotientGroup.mk' Z (q x))
  rw [he x,←hp,←he y,hy,he x]

end
end QuotientGroup.CommonImage

