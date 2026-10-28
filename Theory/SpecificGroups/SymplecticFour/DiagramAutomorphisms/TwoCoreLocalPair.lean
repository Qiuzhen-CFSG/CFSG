module
public import Theory.SpecificGroups.SymplecticFour.EvenBorelTorus.FullTorusFixer
public import Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms.InvariantParabolicPair
public import Theory.GroupTheory.PCoreRestriction

/-!
# The overlap two-core preserves both symplectic local factors

Let a normal subgroup be marked as Sp₄(2ⁿ), n > 1, and let its overlap
with M be the marked flag Borel. Commutators of O₂(M) with that Borel
lie in the Borel two-core, by restriction of prime cores. Thus the
induced automorphisms fix the entire torus quotient. The actual torus
kernel theorem gives inner action, hence preservation of both local
factors. This includes field order four.

The source application lifts this through the original solvable-core
quotient in the diagram row of Aschbacher–Smith 5.1.11(3) and 5.2.1,
printed pp.635,646 (`refs/quasithin.pdf`).
-/

public section
open Subgroup Theory.GroupTheory
open Theory.SpecificGroups.SymplecticFour
open Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms
open Theory.SpecificGroups.SymplecticFour.EvenBorelTorus

noncomputable section
variable {F : Type*} [Field F] [Finite F] [CharP F 2]
variable {G : Type*} [Group G]

namespace Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms

/-- The two-core of a marked Borel overgroup normalizes both actual local factors. -/
theorem twoCore_normalizes_local_pair {n : ℕ} (hF : Nat.card F = 2 ^ n) (hn : 1 < n)
    (N M : Subgroup G) [N.Normal] (e : Sp F ≃* N)
    (hM : M.comap (N.subtype.comp e.toMonoidHom) = borel) :
    M.pCoreIn 2 ≤ normalizer (pointLocal.map (N.subtype.comp e.toMonoidHom) : Set G) ⊓
      normalizer (planeLocal.map (N.subtype.comp e.toMonoidHom) : Set G) := by
  let f := N.subtype.comp e.toMonoidHom
  have hf : Function.Injective f := N.subtype_injective.comp e.injective
  let j : (borel (F := F)) →* M :=
    (f.comp (borel (F := F)).subtype).codRestrict M (fun x => by
      change f x.val ∈ M
      exact (show x.val ∈ M.comap f from hM.symm ▸ x.property))
  have hj : Function.Injective j := by
    intro x y h
    exact Subtype.ext (hf (show f x.val = f y.val from congrArg (fun z : M => z.val) h))
  have hcore : (pCore 2 M).comap j ≤ pCore 2 (borel (F := F)) :=
    le_sSup ⟨inferInstance, pCore_isPGroup.comap_of_injective j hj⟩
  rintro _ ⟨s, hs, rfl⟩
  let a := extensionAction N e s.val
  have ha (x : Sp F) : f (a x) = s.val * f x * s.val⁻¹ :=
    extensionAction_apply N e s.val x
  have hB : (borel (F := F)).map a.toMonoidHom = borel := by
    apply eq_of_le_of_card_ge
    · rintro _ ⟨x,hx,rfl⟩
      rw [← hM]
      change f (a x) ∈ M
      rw [ha]
      have hxM : f x ∈ M := show x ∈ M.comap f from hM.symm ▸ hx
      exact M.mul_mem (M.mul_mem s.property hxM) (M.inv_mem s.property)
    · rw [card_map_of_injective a.injective]
  have hfix (x : Fˣ × Fˣ) : borelCharacters
      ⟨a (torusSection x).val,hB.le (mem_map_of_mem _ (torusSection x).property)⟩ = x := by
    let t := torusSection x
    let b : borel (F := F) := ⟨a t.val,hB.le (mem_map_of_mem _ t.property)⟩
    have hb : b * t⁻¹ ∈ pCore 2 (borel (F := F)) := by
      apply hcore
      change j (b * t⁻¹) ∈ pCore 2 M
      have he : j (b * t⁻¹) = s * j t * s⁻¹ * (j t)⁻¹ := by
        apply Subtype.ext
        change f (a t.val * t.val⁻¹) = s.val * f t.val * s.val⁻¹ * (f t.val)⁻¹
        rw [map_mul,map_inv,ha]
      rw [he]
      exact (commutator_le_left (pCore 2 M) ⊤)
        (commutator_mem_commutator hs (mem_top (j t)))
    rw [twoCore_eq_unipotent hF,←characters_ker,MonoidHom.mem_ker,
      map_mul,map_inv,mul_inv_eq_one] at hb
    exact hb.trans (characters_torusSection x)
  have hd := FullTorusFixer.preservesDiagram_of_fixed_torus hF hn a hB hfix
  have hU := FullTorusFixer.map_unipotent_of_map_borel hF a hB
  have hl := local_pair_map_of_unipotent_map hF hn a hd hU
  have lift (R : Subgroup (Sp F)) (hr : R.map a.toMonoidHom = R) :
      s.val ∈ normalizer (R.map f : Set G) := by
    apply mem_normalizer_iff_map_conj_eq.mpr
    calc
      (R.map f).map (MulAut.conj s.val).toMonoidHom =
          (R.map a.toMonoidHom).map f := by
        rw [map_map,map_map]
        congr 1
        ext x
        exact (ha x).symm
      _ = R.map f := by rw [hr]
  exact ⟨lift _ hl.1,lift _ hl.2⟩

end Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms
