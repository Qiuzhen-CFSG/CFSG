module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.FFSelection.Solvable.Construction.Products.NormalThompson.Maximum.Singleton.HyperplaneTransfer.Reduction

/-!
# The native first action on the selected S₃ fixed complement

The faithful S₃ moved plane splits off its actual fixed subspace. The first
factor fixes that plane, so its restriction to the fixed complement remains
faithful. Mapping its displacement span back into the original space gives
exactly the first native moved space, of dimension three. Mapping its fixed
space gives the original global fixed space. Consequently the source
hyperplane clause rules out a fixed supplement on the complement.

The first-coordinate projection acts on precisely this complement; the last
lemma identifies its fixed codimension with that of the original ambient
subgroup. No quotient-module decomposition replaces the native moved spaces.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, B.5.6(5),
printed p.105, used in the maximum construction of 13.6.13, printed p.929.
-/

public section
open Subgroup Representation Representation.BinaryOffender
open CFSG.Quasithin.ChapterB.SourceInduction CFSG.Quasithin.ChapterB.QuasisimpleSource
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.Solvable.Construction.Products.NormalThompson.Maximum.Singleton.HyperplaneTransfer.FixedPartEstimate

variable {D V : Type*} [Group D] [AddCommGroup V] [Module (ZMod 2) V]
  {ρ : Representation (ZMod 2) D V} (c : HyperplaneCase ρ)

@[expose] noncomputable def firstAction : Representation (ZMod 2) c.first (fixedPart c).toSubmodule :=
  (fixedPart c).toRepresentation.comp c.first.subtype

private theorem moved_eq_coinvariants (B : Subgroup D) :
    moved ρ B = Coinvariants.ker (ρ.comp B.subtype) := by
  unfold moved subspaceCommutator Coinvariants.ker
  congr 1
  ext w
  constructor
  · rintro ⟨g, hg, v, _, rfl⟩
    exact ⟨(⟨g, hg⟩, v), rfl⟩
  · rintro ⟨⟨g, v⟩, rfl⟩
    exact ⟨g, g.property, v, Submodule.mem_top, rfl⟩

private theorem second_isCompl_fixed [Finite D] (hf : Function.Injective ρ)
    (e : c.second ≃* Equiv.Perm (Fin 3))
    (hd : Module.finrank (ZMod 2) (moved ρ c.second) = 2) :
    IsCompl c.secondSpace.toSubmodule (fixedPart c).toSubmodule := by
  change IsCompl c.secondSpace.toSubmodule (Representation.invariants (ρ.comp c.second.subtype))
  rw [c.secondSpace_eq, moved_eq_coinvariants]
  apply BinaryPlaneNormalizer.symmetric_three_split (ρ.comp c.second.subtype)
    (hf.comp c.second.subtype_injective) e
  rwa [moved_eq_coinvariants] at hd

private theorem first_fixes_second (a : c.first) (w : c.secondSpace.toSubmodule) : ρ a w = w := by
  apply sub_eq_zero.mp
  apply Submodule.disjoint_def.mp c.disjoint
  · exact Submodule.subset_span ⟨a, a.property, w, Submodule.mem_top, rfl⟩
  · rw [← c.secondSpace_eq]
    exact c.secondSpace.toSubmodule.sub_mem
      (c.secondSpace.apply_mem_toSubmodule a w.property) w.property

private theorem action_eq_first (g : D) (w : (fixedPart c).toSubmodule) :
    (fixedPart c).toRepresentation g w = firstAction c (c.product.fst g) w := by
  apply Subtype.ext
  change ρ g w = ρ (c.product.fst g : D) w
  have hg : g = (c.product.fst g : D) * (c.product.snd g : D) :=
    (c.product.equiv.apply_symm_apply g).symm.trans (c.product.apply_eq _ _)
  conv_lhs => rw [hg, map_mul, Module.End.mul_apply]
  rw [show ρ (c.product.snd g : D) w = w from w.property (c.product.snd g)]

theorem firstAction_faithful [Finite D] (hf : Function.Injective ρ)
    (e : c.second ≃* Equiv.Perm (Fin 3))
    (hd : Module.finrank (ZMod 2) (moved ρ c.second) = 2) :
    Function.Injective (firstAction c) := by
  intro a b hab
  apply c.first.subtype_injective
  apply hf
  ext v
  obtain ⟨w, hw, t, ht, rfl⟩ := Submodule.mem_sup.mp
    (show v ∈ c.secondSpace.toSubmodule ⊔ (fixedPart c).toSubmodule from
      (second_isCompl_fixed c hf e hd).sup_eq_top ▸ Submodule.mem_top)
  have ht' := congrArg Subtype.val (LinearMap.congr_fun hab ⟨t, ht⟩)
  change ρ (a : D) t = ρ (b : D) t at ht'
  change ρ (a : D) (w + t) = ρ (b : D) (w + t)
  rw [map_add, map_add, first_fixes_second c a ⟨w, hw⟩,
    first_fixes_second c b ⟨w, hw⟩, ht']

private theorem first_moved_map [Finite D] (hf : Function.Injective ρ)
    (e : c.second ≃* Equiv.Perm (Fin 3))
    (hd : Module.finrank (ZMod 2) (moved ρ c.second) = 2) :
    (Coinvariants.ker (firstAction c)).map (fixedPart c).toSubmodule.subtype =
      moved ρ c.first := by
  apply le_antisymm
  · rw [Submodule.map_le_iff_le_comap]
    apply Submodule.span_le.mpr
    rintro _ ⟨⟨a, v⟩, rfl⟩
    exact Submodule.subset_span ⟨a, a.property, v, Submodule.mem_top, rfl⟩
  · apply Submodule.span_le.mpr
    rintro _ ⟨a, ha, v, _, rfl⟩
    obtain ⟨w, hw, t, ht, rfl⟩ := Submodule.mem_sup.mp
      (show v ∈ c.secondSpace.toSubmodule ⊔ (fixedPart c).toSubmodule from
        (second_isCompl_fixed c hf e hd).sup_eq_top ▸ Submodule.mem_top)
    have heq : ρ a (w + t) - (w + t) = ρ a t - t := by
      rw [map_add, first_fixes_second c ⟨a, ha⟩ ⟨w, hw⟩]
      abel
    rw [heq]
    exact ⟨firstAction c ⟨a, ha⟩ ⟨t, ht⟩ - ⟨t, ht⟩,
      Coinvariants.sub_mem_ker (ρ := firstAction c) ⟨a, ha⟩ ⟨t, ht⟩, rfl⟩

theorem first_moved_dimension [Finite D] [FiniteDimensional (ZMod 2) V]
    (hf : Function.Injective ρ) (e : c.second ≃* Equiv.Perm (Fin 3))
    (hd : Module.finrank (ZMod 2) (moved ρ c.second) = 2) :
    Module.finrank (ZMod 2) (Coinvariants.ker (firstAction c)) = 3 := by
  rw [← Submodule.finrank_map_subtype_eq, first_moved_map c hf e hd, c.firstDimension]

private theorem first_fixed_map :
    (firstAction c).invariants.map (fixedPart c).toSubmodule.subtype = ρ.invariants := by
  ext v
  constructor
  · rintro ⟨w, hw, rfl⟩ g
    exact congrArg Subtype.val ((action_eq_first c g w).trans (hw (c.product.fst g)))
  · intro hv
    refine ⟨⟨v, fun b => hv b⟩, ?_, rfl⟩
    intro a
    exact Subtype.ext (hv a)

theorem first_nonsplit [Finite D] (hf : Function.Injective ρ)
    (e : c.second ≃* Equiv.Perm (Fin 3))
    (hd : Module.finrank (ZMod 2) (moved ρ c.second) = 2) :
    Coinvariants.ker (firstAction c) ⊔ (firstAction c).invariants ≠ ⊤ := by
  intro htop
  have heq := congrArg (Submodule.map (fixedPart c).toSubmodule.subtype) htop
  rw [Submodule.map_sup, first_moved_map c hf e hd, first_fixed_map,
    Submodule.map_top, Submodule.range_subtype] at heq
  have hfull : moved ρ ⊤ ⊔ ρ.invariants = ⊤ := by
    rw [c.moved_eq, sup_right_comm, heq]
    rw [sup_comm, ← c.secondSpace_eq]
    exact (second_isCompl_fixed c hf e hd).sup_eq_top
  have hh := c.hyperplane
  rw [hfull] at hh
  have hz : Module.finrank (ZMod 2) (V ⧸ (⊤ : Submodule (ZMod 2) V)) = 0 :=
    Module.finrank_zero_of_subsingleton
  omega

theorem first_projection_codim [FiniteDimensional (ZMod 2) V] (A : Subgroup D) :
    fixedCodim (firstAction c) (A.map c.product.fst) =
      fixedCodim (fixedPart c).toRepresentation A := by
  exact (fixedCodim_map_equivariant (fixedPart c).toRepresentation (firstAction c)
    c.product.fst (LinearEquiv.refl _ _) (action_eq_first c) A).symm

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.Solvable.Construction.Products.NormalThompson.Maximum.Singleton.HyperplaneTransfer.FixedPartEstimate

end
