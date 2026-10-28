module
public import Theory.Representation.BinaryPermutation.PointOrbit
public import Mathlib.RepresentationTheory.Irreducible
public import Mathlib.Data.Set.Card

/-!
# Deleted five-point coordinates from the actual spanning orbit

The five-element orbit of a vector is itself the permutation set. Relabeling
that literal orbit constructs a homomorphism from the original actor to S₅.
Its point stabilizer fixes the original vector, so the point-orbit quotient
supplies deleted permutation coordinates in dimension four. The full
five-dimensional alternative is excluded by dimension. The permutation
kernel is exactly the original representation kernel because the orbit spans.

The odd-degree core-to-deleted equivalence gives core coordinates for the
same action. Irreducibility supplies the spanning hypothesis for any nonzero
seed. No classification of the actor or an arbitrary cover is used.
-/

public noncomputable section
namespace BinaryPermutation
open Representation Subgroup
variable {M W : Type*} [Group M] [AddCommGroup W] [Module (ZMod 2) W]

/-- The literal spanning five-orbit determines a deleted marking, preserving
the original seed and the exact action kernel. -/
theorem deleted_marking_of_spanning_five_orbit
    (ρ : Representation (ZMod 2) M W) (hd : Module.finrank (ZMod 2) W = 4)
    (w : W) (hfive : (Set.range (fun g : M => ρ g w)).ncard = 5)
    (hspan : Submodule.span (ZMod 2) (Set.range (fun g : M => ρ g w)) = ⊤) :
    ∃ (α : M →* Equiv.Perm (Fin 5)) (i : Fin 5) (c : Deleted (Fin 5) ≃ₗ[ZMod 2] W),
      α.ker = ρ.ker ∧ (∀ i j : Fin 5, ∃ g : M, α g i = j) ∧
        c ((constants (Fin 5)).mkQ (Pi.single i 1)) = w ∧
        ∀ g v, c (deletedRepresentation (Fin 5) (α g) v) = ρ g (c v) := by
  classical
  let : MulAction M W := {
    smul g x := ρ g x
    one_smul x := by change ρ 1 x = x; rw [map_one]; rfl
    mul_smul g h x := by change ρ (g*h) x = ρ g (ρ h x); rw [map_mul]; rfl }
  let O := MulAction.orbit M w
  have hO : Nat.card O = 5 := hfive
  let : Finite O := (Set.finite_of_ncard_pos (show 0 < O.ncard from by rw [show O.ncard = 5 from hO]; omega)).to_subtype
  let e : O ≃ Fin 5 := Finite.equivFinOfCardEq hO
  let α : M →* Equiv.Perm (Fin 5) :=
    (Equiv.permCongrHom e).toMonoidHom.comp (MulAction.toPermHom M O)
  have he (g : M) (o : O) : α g (e o) = e (g • o) := by
    simp [α,Equiv.permCongrHom]
  have ht : ∀ i j : Fin 5, ∃ g : M, α g i = j := by
    intro i j
    obtain ⟨g,hg⟩ := MulAction.exists_smul_eq M (e.symm i) (e.symm j)
    refine ⟨g,?_⟩
    have hh := he g (e.symm i)
    simpa only [e.apply_symm_apply,hg] using hh
  have hk : α.ker = ρ.ker := by
    ext g
    change α g = 1 ↔ ρ g = 1
    constructor
    · intro hg
      have hfix (o : O) : ρ g (o:W) = o := by
        have hh := he g o
        rw [hg] at hh
        exact congrArg Subtype.val (e.injective hh.symm)
      apply LinearMap.ext_on_range hspan
      intro h
      exact hfix ⟨ρ h w,⟨h,rfl⟩⟩
    · intro hg
      apply Equiv.ext
      intro i
      obtain ⟨o,rfl⟩ := e.surjective i
      rw [he]
      change e (g • o) = e o
      apply congrArg e
      apply Subtype.ext
      change ρ g (o:W) = o
      rw [hg]
      rfl
  let o : O := ⟨w,MulAction.mem_orbit_self w⟩
  have hw : ∀ g : M, α g (e o) = e o → ρ g w = w := by
    intro g hg
    exact congrArg Subtype.val (e.injective ((he g o).symm.trans hg))
  rcases five_point_marking ρ α ht (e o) w hw hspan (by omega) with hf | hc
  · obtain ⟨c,_,_⟩ := hf
    have hh := c.finrank_eq
    rw [finrank_full,hd] at hh
    norm_num at hh
  · obtain ⟨c,hcw,hce⟩ := hc
    exact ⟨α,e o,c,hk,ht,hcw,hce⟩

/-- Core coordinates for the same original representation and the same
internally constructed five-point action, retaining exact kernel equality. -/
theorem core_marking_of_spanning_five_orbit
    (ρ : Representation (ZMod 2) M W) (hd : Module.finrank (ZMod 2) W = 4)
    (w : W) (hfive : (Set.range (fun g : M => ρ g w)).ncard = 5)
    (hspan : Submodule.span (ZMod 2) (Set.range (fun g : M => ρ g w)) = ⊤) :
    ∃ (α : M →* Equiv.Perm (Fin 5)) (c : core (Fin 5) ≃ₗ[ZMod 2] W),
      α.ker = ρ.ker ∧ (∀ i j : Fin 5, ∃ g : M, α g i = j) ∧
        ∀ g v, c (coreRepresentation (Fin 5) (α g) v) = ρ g (c v) := by
  obtain ⟨α,_,c,hk,ht,_,he⟩ := deleted_marking_of_spanning_five_orbit ρ hd w hfive hspan
  refine ⟨α,(coreEquivDeleted (Fin 5) (by decide)).trans c,hk,ht,?_⟩
  intro g v
  exact he g ((constants (Fin 5)).mkQ v.val)

private theorem orbit_span_of_irreducible
    (ρ : Representation (ZMod 2) M W) [ρ.IsIrreducible] (w : W) (hw : w ≠ 0) :
    Submodule.span (ZMod 2) (Set.range (fun g : M => ρ g w)) = ⊤ := by
  let S := Submodule.span (ZMod 2) (Set.range (fun g : M => ρ g w))
  let D : Subrepresentation ρ := {
    toSubmodule := S
    apply_mem_toSubmodule g x hx := by
      induction hx using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨h,rfl⟩ := hx
        exact Submodule.subset_span ⟨g*h,by change ρ (g*h) w = ρ g (ρ h w); rw [map_mul]; rfl⟩
      | zero => rw [map_zero]; exact S.zero_mem
      | add x y _ _ hx hy => rw [map_add]; exact S.add_mem hx hy
      | smul a x _ hx => rw [map_smul]; exact S.smul_mem a hx }
  have hwD : w ∈ D := by
    change w ∈ S
    have h : ρ (1:M) w ∈ S := Submodule.subset_span ⟨1,rfl⟩
    simpa only [map_one,Module.End.one_apply] using h
  rcases (inferInstance : ρ.IsIrreducible).eq_bot_or_eq_top D with hb | ht
  · have hz : w ∈ (⊥ : Subrepresentation ρ) := hb ▸ hwD
    exact (hw hz).elim
  · exact congrArg Subrepresentation.toSubmodule ht

/-- Irreducibility discharges orbit spanning for the actual nonzero seed. -/
theorem core_marking_of_irreducible_five_orbit
    (ρ : Representation (ZMod 2) M W) [ρ.IsIrreducible]
    (hd : Module.finrank (ZMod 2) W = 4) (w : W) (hw : w ≠ 0)
    (hfive : (Set.range (fun g : M => ρ g w)).ncard = 5) :
    ∃ (α : M →* Equiv.Perm (Fin 5)) (c : core (Fin 5) ≃ₗ[ZMod 2] W),
      α.ker = ρ.ker ∧ (∀ i j : Fin 5, ∃ g : M, α g i = j) ∧
        ∀ g v, c (coreRepresentation (Fin 5) (α g) v) = ρ g (c v) :=
  core_marking_of_spanning_five_orbit ρ hd w hfive (orbit_span_of_irreducible ρ w hw)

end BinaryPermutation
