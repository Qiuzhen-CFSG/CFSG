module

public import Mathlib.GroupTheory.SpecificGroups.Dihedral
public import Mathlib.GroupTheory.Commutator.Basic
public import Mathlib.GroupTheory.NoncommCoprod
public import Mathlib.Logic.Equiv.Prod

/-!
# Extracting a dihedral factor from a product coordinate

If an isomorphism from X × B onto D₈ × Y maps B onto the first coordinate,
then B itself has a direct factor D₈. The inverse coordinate maps supply a
section. The error in their composite is central and kills the center of
D₈, so the composite is invertible; the section commutes with its kernel.

Consequently, the derived subgroup of a remainder without a D₈ factor is
characteristic after adjoining any finite number of D₈ factors. This is the
specialized direct-factor argument needed in Goldschmidt, Automorphisms of
Trivalent Graphs (1980), (2.14), printed p.385.
-/

@[expose] public section

open Subgroup
open scoped commutatorElement

namespace Theory.GroupTheory.DihedralFactorExtraction

private abbrev D := DihedralGroup 4

/-- A direct factor of order eight, with its complement an actual subgroup. -/
def HasFactor (B : Type*) [Group B] : Prop :=
  ∃ K : Subgroup B, Nonempty (B ≃* DihedralGroup 4 × K)

private theorem dihedral_generation : ∀ a b d : D, ⁅a,b⁆ ≠ 1 →
    ∃ i j : Fin 4, d = a ^ i.val * b ^ j.val ∨
      d = a ^ i.val * (a * b) ^ j.val := by
  decide +kernel

private theorem center_commutator : ∀ z : D, (∀ d : D, d * z = z * d) →
    ∃ a b : D, ⁅a,b⁆ = z := by
  decide +kernel

private theorem derived_le_comap {A C : Type*} [Group A] [Group C]
    (f : A →* C) : commutator A ≤ (commutator C).comap f := by
  rw [← map_le_iff_le_comap, map_commutator_eq]
  exact commutator_mono le_top le_top

private theorem surjective_of_derived_movement {B : Type*} [Group B]
    (p : B →* D) {z : B} (hz : z ∈ commutator B) (hne : p z ≠ 1) :
    Function.Surjective p := by
  have hex : ∃ a b : B, ⁅p a,p b⁆ ≠ 1 := by
    by_contra! hh
    have hk : commutator B ≤ p.ker := by
      apply commutator_le.mpr
      intro a _ b _
      change p ⁅a,b⁆ = 1
      rw [map_commutatorElement, hh]
    exact hne (hk hz)
  obtain ⟨a,b,hab⟩ := hex
  intro d
  obtain ⟨i,j,h | h⟩ := dihedral_generation (p a) (p b) d hab
  · exact ⟨a ^ i.val * b ^ j.val, by simpa only [map_mul,map_pow] using h.symm⟩
  · exact ⟨a ^ i.val * (a*b) ^ j.val, by simpa only [map_mul,map_pow] using h.symm⟩

private theorem parts {A B C : Type*} [Group A] [Group B] [Group C]
    (f : A × B →* C) (a : A) (b : B) :
    f (a,b) = f (a,1) * f (1,b) := by
  rw [←map_mul]
  simp

private theorem parts_commute {A B C : Type*} [Group A] [Group B] [Group C]
    (f : A × B →* C) (a : A) (b : B) : Commute (f (a,1)) (f (1,b)) := by
  change f (a,1) * f (1,b) = f (1,b) * f (a,1)
  rw [←map_mul,←map_mul]
  simp

private theorem central_hom_kills_center (c : D →* D)
    (hc : ∀ d, c d ∈ center D) {z : D} (hz : z ∈ center D) : c z = 1 := by
  obtain ⟨a,b,rfl⟩ := center_commutator z (mem_center_iff.mp hz)
  rw [map_commutatorElement]
  exact commutatorElement_eq_one_iff_mul_comm.mpr
    (mem_center_iff.mp (hc b) (c a))

/-- A surjective dihedral coordinate of one source factor extracts a genuine
dihedral direct factor from that source factor. -/
theorem hasFactor_of_surjective_coordinate
    {X B Y : Type*} [Group X] [Group B] [Group Y]
    (e : X × B ≃* DihedralGroup 4 × Y)
    (hp : Function.Surjective (fun b : B => (e (1,b)).1)) : HasFactor B := by
  let a : X →* D := (MonoidHom.fst D Y).comp
    (e.toMonoidHom.comp (MonoidHom.inl X B))
  let p : B →* D := (MonoidHom.fst D Y).comp
    (e.toMonoidHom.comp (MonoidHom.inr X B))
  let u : D →* X := (MonoidHom.fst X B).comp
    (e.symm.toMonoidHom.comp (MonoidHom.inl D Y))
  let j₀ : D →* B := (MonoidHom.snd X B).comp
    (e.symm.toMonoidHom.comp (MonoidHom.inl D Y))
  let c : D →* D := a.comp u
  let t : D →* D := p.comp j₀
  have ha (x : X) : a x ∈ center D := by
    apply mem_center_iff.mpr
    intro d
    obtain ⟨b,rfl⟩ := hp d
    exact (parts_commute ((MonoidHom.fst D Y).comp e.toMonoidHom) x b).eq.symm
  have hc (d : D) : c d ∈ center D := ha (u d)
  have hct (d : D) : c d * t d = d := by
    have hh := parts ((MonoidHom.fst D Y).comp e.toMonoidHom)
      (e.symm (d,1)).1 (e.symm (d,1)).2
    exact hh.symm.trans (congrArg Prod.fst (e.apply_symm_apply (d,1)))
  have hti : Function.Injective t := by
    apply t.ker_eq_bot_iff.mp
    apply bot_unique
    intro d hd
    have he : c d = d := by simpa only [show t d = 1 from hd,mul_one] using hct d
    have hz : d ∈ center D := he ▸ hc d
    have hone := central_hom_kills_center c hc hz
    exact mem_bot.mpr (he.symm.trans hone)
  let τ : D ≃* D := MulEquiv.ofBijective t ⟨hti,Finite.surjective_of_injective hti⟩
  let j : D →* B := j₀.comp τ.symm.toMonoidHom
  have hpj (d : D) : p (j d) = d := τ.apply_symm_apply d
  have hjk (d : D) (k : p.ker) : Commute (j d) (k : B) := by
    have he : (e (1,(k : B))).1 = 1 := k.property
    have hk : (k : B) = (e.symm (1,(e (1,(k : B))).2)).2 := by
      have hh := congrArg Prod.snd (e.symm_apply_apply (1,(k : B)))
      rw [show e (1,(k : B)) = (1,(e (1,(k : B))).2) from Prod.ext he rfl] at hh
      exact hh.symm
    rw [hk]
    exact parts_commute ((MonoidHom.snd X B).comp e.symm.toMonoidHom)
      (τ.symm d) (e (1,(k : B))).2
  let f : D × p.ker →* B := j.noncommCoprod p.ker.subtype hjk
  have hfi : Function.Injective f := by
    intro x y hxy
    have hfirst : x.1 = y.1 := by
      have hh := congrArg p hxy
      change p (j x.1 * x.2) = p (j y.1 * y.2) at hh
      simpa only [map_mul,hpj,show p (x.2 : B) = 1 from x.2.property,
        show p (y.2 : B) = 1 from y.2.property,mul_one] using hh
    have hsecond : x.2 = y.2 := by
      apply Subtype.ext
      change j x.1 * (x.2 : B) = j y.1 * (y.2 : B) at hxy
      rw [hfirst] at hxy
      exact mul_left_cancel hxy
    exact Prod.ext hfirst hsecond
  have hfs : Function.Surjective f := by
    intro b
    let k : p.ker := ⟨(j (p b))⁻¹ * b, by
      change p ((j (p b))⁻¹ * b) = 1
      rw [map_mul,map_inv,hpj,inv_mul_cancel]⟩
    exact ⟨(p b,k),mul_inv_cancel_left (j (p b)) b⟩
  exact ⟨p.ker,⟨(MulEquiv.ofBijective f ⟨hfi,hfs⟩).symm⟩⟩

private def splitAt {ι : Type*} [DecidableEq ι] (i : ι) :
    (ι → D) ≃* D × ({j : ι // j ≠ i} → D) :=
  { Equiv.funSplitAt i D with map_mul' := fun _ _ => rfl }

/-- The derived remainder is characteristic when it has no dihedral direct
factor; the dihedral factors themselves need not be individually preserved. -/
theorem characteristic_derived_remainder (n : ℕ) (B : Type*) [Group B]
    (hB : ¬ HasFactor B) :
    ((⊥ : Subgroup (Fin n → DihedralGroup 4)).prod (commutator B)).Characteristic := by
  classical
  apply characteristic_iff_le_comap.mpr
  intro f
  rintro ⟨x,b⟩ ⟨hx,hb⟩
  have hx' : x = 1 := hx
  subst x
  refine ⟨?_,?_⟩
  · change (f (1,b)).1 = 1
    ext i
    by_contra hne
    let e : ((Fin n → D) × B) ≃* D × (({j : Fin n // j ≠ i} → D) × B) :=
      f.trans ((MulEquiv.prodCongr (splitAt i) (MulEquiv.refl B)).trans
        MulEquiv.prodAssoc)
    let p : B →* D := (MonoidHom.fst D _).comp
      (e.toMonoidHom.comp (MonoidHom.inr (Fin n → D) B))
    exact hB (hasFactor_of_surjective_coordinate e
      (surjective_of_derived_movement p hb (show p b ≠ 1 from hne)))
  · exact derived_le_comap ((MonoidHom.snd (Fin n → D) B).comp
      (f.toMonoidHom.comp (MonoidHom.inr (Fin n → D) B))) hb

end Theory.GroupTheory.DihedralFactorExtraction
