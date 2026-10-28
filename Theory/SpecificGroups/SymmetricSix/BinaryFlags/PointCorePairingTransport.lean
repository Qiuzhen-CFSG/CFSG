module
public import Theory.SpecificGroups.SymmetricSix.BinaryFlags.PointCorePairing
import all Theory.SpecificGroups.SymmetricSix.BinaryFlags.PointCoreGeneration

/-!
# Compatible strict intersections in an arbitrary point-core marking

Transport the paired five-cycle calculation through the literal conjugation
marking u. The prescribed transposition t in the marked point core is retained
in both generation equations. Every vector in either strict intersection is
fixed by the whole symmetric group, including the constant vector in the
five-dimensional augmentation cover.

Source application: Meierfrankenfeld--Stellmacher (1993), (5.5) and
(5.12)(1), printed pp.915,924--925. The full point-core graph selector uses
this theorem without replacing its actor or its central attachment.
-/

public section
open Subgroup BinaryPermutation Representation Representation.BinaryOffender
open Theory.SpecificGroups.SymmetricSix.BinaryFlags
namespace Theory.SpecificGroups.SymmetricSix.BinaryFlags.PointCorePairing

private theorem constants_fixed {x : core (Fin 6)} (hx : x ∈ coreConstants (Ω := Fin 6))
    (k : Equiv.Perm (Fin 6)) : coreRepresentation (Fin 6) k x = x := by
  obtain ⟨c,hc⟩ := (mem_constants_iff x.val).mp hx
  apply Subtype.ext
  funext i
  exact (hc (k.symm i)).trans (hc i).symm

private theorem conj_map (A : Subgroup (Equiv.Perm (Fin 6))) (u k : Equiv.Perm (Fin 6)) :
    (A.map (MulAut.conj k).toMonoidHom).map (MulAut.conj u).toMonoidHom =
      (A.map (MulAut.conj u).toMonoidHom).map (MulAut.conj (u*k*u⁻¹)).toMonoidHom := by
  rw [map_map,map_map]
  congr 1
  apply MonoidHom.ext
  intro x
  change u*(k*x*k⁻¹)*u⁻¹ = (u*k*u⁻¹)*(u*x*u⁻¹)*(u*k*u⁻¹)⁻¹
  group

/-- Paired intersections for the actual conjugate point core and its
actual transposition. The conclusion fixes the full intersection under every
six-letter permutation, retaining the constant attachment. -/
theorem exists_paired_conjugate_card (u t : Equiv.Perm (Fin 6))
    (ht : t.IsSwap) (htR : t ∈ pointCore.map (MulAut.conj u).toMonoidHom)
    (W : Submodule (ZMod 2) (core (Fin 6)))
    (hsmall : Nat.card W < 16)
    (hfixed : fixedSpace (coreRepresentation (Fin 6))
      (pointCore.map (MulAut.conj u).toMonoidHom) ≤ W)
    (hinv : ∀ r ∈ pointCore.map (MulAut.conj u).toMonoidHom,
      ∀ x ∈ W, coreRepresentation (Fin 6) r x ∈ W) :
    ∃ g : alternatingGroup (Fin 6),
      ((pointCore.map (MulAut.conj u).toMonoidHom).map
        (MulAut.conj g.val).toMonoidHom ⊔ zpowers t = ⊤) ∧
      ((pointCore.map (MulAut.conj u).toMonoidHom).map
        (MulAut.conj g.val⁻¹).toMonoidHom ⊔ zpowers t = ⊤) ∧
      (∀ x ∈ W ⊓ W.map (coreRepresentation (Fin 6) g.val),
        ∀ r : Equiv.Perm (Fin 6), coreRepresentation (Fin 6) r x = x) ∧
      (∀ x ∈ W ⊓ W.map (coreRepresentation (Fin 6) g.val⁻¹),
        ∀ r : Equiv.Perm (Fin 6), coreRepresentation (Fin 6) r x = x) := by
  let ρ := coreRepresentation (Fin 6)
  have hleft (x : core (Fin 6)) : ρ u⁻¹ (ρ u x) = x := by
    rw [←Module.End.mul_apply,←map_mul,inv_mul_cancel,map_one,Module.End.one_apply]
  have hright (x : core (Fin 6)) : ρ u (ρ u⁻¹ x) = x := by
    rw [←Module.End.mul_apply,←map_mul,mul_inv_cancel,map_one,Module.End.one_apply]
  have hswap : (MulAut.conj u).toMonoidHom swap45 = t := by
    obtain ⟨s,hs,hst⟩ := htR
    have hsSwap : s.IsSwap := by
      have hc : IsConj s t := isConj_iff.mpr ⟨u,hst⟩
      exact Equiv.Perm.isSwap_iff_cycleType.mpr
        ((Equiv.Perm.isConj_iff_cycleType_eq.mp hc).trans (Equiv.Perm.isSwap_iff_cycleType.mp ht))
    rwa [PointCoreGeneration.swap_in_core hsSwap hs] at hst
  let W₀ := W.comap (ρ u)
  have hcard : Nat.card W₀ < 16 := by
    let f : W₀ → W := fun x => ⟨ρ u x.val,x.property⟩
    have hf : Function.Injective f := by
      intro x y he
      apply Subtype.ext
      have he' := congrArg (fun z : W => ρ u⁻¹ z.val) he
      simpa only [f,hleft] using he'
    exact (Nat.card_le_card_of_injective f hf).trans_lt hsmall
  have hfix₀ : fixedSpace ρ pointCore ≤ W₀ := by
    intro x hx
    change ρ u x ∈ W
    apply hfixed
    rintro ⟨r,hr⟩
    obtain ⟨a,ha,rfl⟩ := hr
    change ρ (u*a*u⁻¹) (ρ u x) = ρ u x
    rw [map_mul,map_mul]
    have haFix : ρ a x = x := hx ⟨a,ha⟩
    simp only [Module.End.mul_apply,hleft,haFix]
  have hinv₀ : ∀ r ∈ pointCore, ∀ x ∈ W₀, ρ r x ∈ W₀ := by
    intro r hr x hx
    have hh := hinv ((MulAut.conj u) r) (mem_map_of_mem (MulAut.conj u).toMonoidHom hr)
      (ρ u x) hx
    change ρ (u*r*u⁻¹) (ρ u x) ∈ W at hh
    rw [map_mul,map_mul] at hh
    change ρ u (ρ r x) ∈ W
    simpa only [Module.End.mul_apply,hleft] using hh
  obtain ⟨k,hk,hki,hW,hWi⟩ := exists_paired_card W₀ hcard hfix₀ hinv₀
  let g : alternatingGroup (Fin 6) := MulAut.conjNormal u k
  have hg : g.val = u*k.val*u⁻¹ := rfl
  have hgi : g.val⁻¹ = u*k.val⁻¹*u⁻¹ := by rw [hg]; group
  have generation (v : Equiv.Perm (Fin 6))
      (hv : pointCore.map (MulAut.conj v).toMonoidHom ⊔ zpowers swap45 = ⊤) :
      (pointCore.map (MulAut.conj u).toMonoidHom).map
        (MulAut.conj (u*v*u⁻¹)).toMonoidHom ⊔ zpowers t = ⊤ := by
    have hh := congrArg (Subgroup.map (MulAut.conj u).toMonoidHom) hv
    rw [Subgroup.map_sup,MonoidHom.map_zpowers,hswap,conj_map,
      map_top_of_surjective (MulAut.conj u).toMonoidHom (MulAut.conj u).surjective] at hh
    exact hh
  have intersection (v : Equiv.Perm (Fin 6))
      (hv : W₀ ⊓ W₀.map (ρ v) ≤ coreConstants (Ω := Fin 6)) :
      ∀ x ∈ W ⊓ W.map (ρ (u*v*u⁻¹)),
        ∀ r : Equiv.Perm (Fin 6), ρ r x = x := by
    intro x hx r
    have hx₀ : ρ u⁻¹ x ∈ W₀ := by change ρ u (ρ u⁻¹ x) ∈ W; rw [hright]; exact hx.1
    have hxmap : ρ u⁻¹ x ∈ W₀.map (ρ v) := by
      obtain ⟨y,hy,he⟩ := hx.2
      refine ⟨ρ u⁻¹ y,?_,?_⟩
      · change ρ u (ρ u⁻¹ y) ∈ W
        rwa [hright]
      · rw [←he,map_mul,map_mul]
        simp only [Module.End.mul_apply,hleft]
    have hconst := hv ⟨hx₀,hxmap⟩
    have hc := constants_fixed hconst (u⁻¹*r*u)
    have hh := congrArg (ρ u) hc
    change ρ u (ρ (u⁻¹*r*u) (ρ u⁻¹ x)) = ρ u (ρ u⁻¹ x) at hh
    rw [map_mul,map_mul] at hh
    simpa only [Module.End.mul_apply,hright] using hh
  refine ⟨g,?_,?_,?_,?_⟩
  · rw [hg]
    exact generation k.val hk
  · rw [hgi]
    exact generation k.val⁻¹ hki
  · rw [hg]
    exact intersection k.val hW
  · rw [hgi]
    exact intersection k.val⁻¹ hWi

end Theory.SpecificGroups.SymmetricSix.BinaryFlags.PointCorePairing
