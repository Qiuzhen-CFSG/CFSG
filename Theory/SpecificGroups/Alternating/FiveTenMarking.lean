module
public import Theory.SpecificGroups.Alternating.FiveTenAutomorphisms

/-!
# Exact extension and rigidity of the full central-factor overlap

An isomorphism between actual order-ten subgroups extends to their A₅
carriers. Moreover a marking of Z × A₅ is determined by its restriction
to Z × D₁₀ for every abelian central factor Z. This retains the full cubic
factor in the order-180 J₃ overlap, rather than comparing only its A₅ quotient.
-/

public noncomputable section
namespace alternatingGroup.FiveLocalGeometry.TenAutomorphisms
open Subgroup
local notation "A" => alternatingGroup (Fin 5)

/-- Any specified isomorphism between two actual order-ten subgroups
extends to an automorphism of the same A₅ carrier. -/
theorem equiv_extends (D E : Subgroup A) (hD : Nat.card D=10) (hE : Nat.card E=10)
    (f : D ≃* E) : ∃ Φ : MulAut A, ∀ d : D, Φ d = (f d : A) := by
  obtain ⟨g,hg⟩ := ten_subgroups_conjugate (MulEquiv.refl A) D E hD hE
  let k : D ≃* E := ((MulAut.conj g).subgroupMap D).trans (MulEquiv.subgroupCongr hg)
  let α : MulAut E := k.symm.trans f
  obtain ⟨Ψ,hΨ⟩ := automorphism_extends E hE α
  refine ⟨(MulAut.conj g).trans Ψ,?_⟩
  intro d
  change Ψ (k d) = (f d : A)
  rw [hΨ]
  change (f (k.symm (k d)) : A) = _
  rw [k.symm_apply_apply]

/-- The full product automorphism is rigid on an actual order-ten subgroup
and the entire abelian central factor. -/
theorem product_eq_one_of_fixes_ten {Z : Type*} [CommGroup Z]
    (D : Subgroup A) (hD : Nat.card D=10) (φ : MulAut (Z × A))
    (hfix : ∀ (z : Z) (d : D), φ (z,(d : A)) = (z,(d : A))) : φ=1 := by
  let : Group.IsPerfect A := ⟨commutator_alternatingGroup_eq_top (by simp)⟩
  let p : A →* Z := (MonoidHom.fst Z A).comp (φ.toMonoidHom.comp (MonoidHom.inr Z A))
  let : Group.IsPerfect p.range := Group.IsPerfect.range p
  have hp (a : A) : (φ (1,a)).1 = 1 :=
    congrArg Subtype.val (Subsingleton.elim (p.rangeRestrict a) 1)
  let q : A →* A := (MonoidHom.snd Z A).comp (φ.toMonoidHom.comp (MonoidHom.inr Z A))
  have hq : Function.Injective q := by
    intro a b he
    have hh : φ (1,a) = φ (1,b) := Prod.ext ((hp a).trans (hp b).symm) he
    exact congrArg Prod.snd (φ.injective hh)
  let ψ : MulAut A := MulEquiv.ofBijective q ((Nat.bijective_iff_injective_and_card q).mpr ⟨hq,rfl⟩)
  have hψ : ψ=1 := eq_one_of_fixes_ten D hD ψ (by
    intro a ha
    exact congrArg Prod.snd (hfix 1 ⟨a,ha⟩))
  apply MulEquiv.ext
  rintro ⟨z,a⟩
  have hza : (z,a) = (z,(1 : A)) * ((1 : Z),a) := by simp
  have hz : φ (z,(1 : A)) = (z,1) := hfix z 1
  have ha : φ ((1 : Z),a) = (1,a) := by
    apply Prod.ext (hp a)
    exact congrArg (fun α : MulAut A => α a) hψ
  change φ (z,a) = (z,a)
  rw [hza,map_mul,hz,ha]

/-- Two full product markings which agree on the same central-factor and
order-ten overlap agree on every element. -/
theorem product_equiv_ext {Z E : Type*} [CommGroup Z] [Group E]
    (D : Subgroup A) (hD : Nat.card D=10) (f g : Z × A ≃* E)
    (h : ∀ (z : Z) (d : D), f (z,(d : A)) = g (z,(d : A))) : f=g := by
  have he := product_eq_one_of_fixes_ten D hD (f.trans g.symm) (by
    intro z d
    change g.symm (f (z,(d : A))) = (z,(d : A))
    rw [h,g.symm_apply_apply])
  apply MulEquiv.ext
  intro x
  have hx := congrArg (fun α : MulAut (Z × A) => g (α x)) he
  simpa only [MulEquiv.trans_apply,MulEquiv.apply_symm_apply,MulAut.one_apply] using hx
end alternatingGroup.FiveLocalGeometry.TenAutomorphisms
