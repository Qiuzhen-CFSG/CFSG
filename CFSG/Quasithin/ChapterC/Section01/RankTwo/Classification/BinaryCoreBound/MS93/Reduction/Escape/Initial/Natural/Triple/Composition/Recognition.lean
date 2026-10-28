module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.AbelianCore.QuotientRecognition.ExtensionControl.Head
public import Theory.Representation.NormalPSubgroupKernel
public import Theory.Representation.Quotient
public import Theory.Representation.BinaryOffender.EquivariantOffender

/-!
# Recognizing irreducible factors of the binary cover

The normal two-group kernel fixes every irreducible binary module. Descent
preserves the original vector space and its action, as well as irreducibility.
The rank-one endpoint actor gives an FF-module over the actual SL₃(2), so the
proved dimension bound excludes its eight-dimensional irreducible. The two
natural orientations are expressed by an equivariant linear equivalence with
an explicit automorphism marking. No semisimplicity is used.

Source: Meierfrankenfeld–Stellmacher (1993), (1.4)–(1.5), pp.842–843;
the binary irreducible catalogue is Aschbacher–Smith H.6.1.
-/

public section

open Representation Representation.BinaryOffender Subgroup
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.Initial.Natural.Triple.Composition
open CFSG.Quasithin.ChapterC.BinaryMS.AbelianCore.QuotientRecognition.ExtensionControl
variable {G E : Type*} [Group G] [Finite G] [AddCommGroup E] [Module (ZMod 2) E]
  [FiniteDimensional (ZMod 2) E]

/-- Descent of an irreducible section on its original vector space. -/
theorem irreducible_descent (π : G →* BinaryLinearThree.Group)
    (hπ : Function.Surjective π) (hk : IsPGroup 2 π.ker)
    (ρ : Representation (ZMod 2) G E) [IsIrreducible ρ] :
    ∃ σ : Representation (ZMod 2) BinaryLinearThree.Group E,
      σ.comp π = ρ ∧ IsIrreducible σ := by
  have hker := normal_p_subgroup_le_ker ρ π.ker hk
  let e := QuotientGroup.quotientKerEquivOfSurjective π hπ
  let σ : Representation (ZMod 2) BinaryLinearThree.Group E :=
    (quotientOfLEKer ρ π.ker hker).comp e.symm.toMonoidHom
  have he (g : G) : e.symm (π g) = QuotientGroup.mk' π.ker g :=
    e.symm_apply_apply (QuotientGroup.mk' π.ker g)
  have hc : σ.comp π = ρ := by
    ext g v
    change quotientOfLEKer ρ π.ker hker (e.symm (π g)) v = ρ g v
    rw [he]
    rfl
  refine ⟨σ, hc, (irreducible_comp_surjective_iff π hπ σ).mp ?_⟩
  rw [hc]
  infer_instance

omit [Finite G] [FiniteDimensional (ZMod 2) E] in
private theorem full_commutator_of_irreducible
    (ρ : Representation (ZMod 2) G E) [IsIrreducible ρ]
    (hn : ∃ g v, ρ g v ≠ v) : subspaceCommutator ρ ⊤ ⊤ = ⊤ := by
  let C : Subrepresentation ρ := {
    toSubmodule := subspaceCommutator ρ ⊤ ⊤
    apply_mem_toSubmodule g := by
      intro w hw
      induction hw using Submodule.span_induction with
      | mem w hw =>
        obtain ⟨a, _, v, _, rfl⟩ := hw
        have h1 : ρ (g * a) v - v ∈ subspaceCommutator ρ ⊤ ⊤ :=
          Submodule.subset_span ⟨g * a, mem_top _, v, Submodule.mem_top, rfl⟩
        have h2 : ρ g v - v ∈ subspaceCommutator ρ ⊤ ⊤ :=
          Submodule.subset_span ⟨g, mem_top _, v, Submodule.mem_top, rfl⟩
        convert (subspaceCommutator ρ ⊤ ⊤).sub_mem h1 h2 using 1
        simp only [map_sub, map_mul, Module.End.mul_apply]
        abel
      | zero => simp
      | add x y hx hy ihx ihy => simpa using (subspaceCommutator ρ ⊤ ⊤).add_mem ihx ihy
      | smul a x hx ih => simpa using (subspaceCommutator ρ ⊤ ⊤).smul_mem a ih }
  rcases eq_bot_or_eq_top C with hb | ht
  · have hz : subspaceCommutator ρ ⊤ ⊤ = ⊥ := congrArg Subrepresentation.toSubmodule hb
    obtain ⟨g, v, hv⟩ := hn
    exact False.elim (hv ((subspaceCommutator_eq_bot_iff ρ ⊤ ⊤).mp hz
      Submodule.mem_top ⟨g, mem_top _⟩))
  · exact congrArg Subrepresentation.toSubmodule ht

/-- A nontrivial irreducible factor with the inherited rank-one bound is a
literal natural module, with an automorphism allowing the dual orientation. -/
theorem irreducible_natural (π : G →* BinaryLinearThree.Group)
    (hπ : Function.Surjective π) (hk : IsPGroup 2 π.ker)
    (A : Subgroup G) (hA : IsElementaryAbelian 2 A) (hc : Nat.card (A.map π) = 2)
    (ρ : Representation (ZMod 2) G E) [IsIrreducible ρ]
    (hd : fixedCodim ρ A ≤ 1) (hn : ∃ g v, ρ g v ≠ v) :
    ∃ a : BinaryLinearThree.Group ≃* BinaryLinearThree.Group,
      Nonempty (ρ.Equiv ((BinaryLinearThree.W.comp a.toMonoidHom).comp π)) := by
  obtain ⟨σ, hσ, hirr⟩ := irreducible_descent π hπ hk ρ
  let := hirr
  have hmove : ∃ g v, σ g v ≠ v := by
    obtain ⟨g, v, hv⟩ := hn
    exact ⟨π g, v, by simpa only [← hσ, MonoidHom.comp_apply] using hv⟩
  have he : fixedCodim ρ A = fixedCodim σ (A.map π) := by
    rw [← hσ]
    exact fixedCodim_map_equivariant (σ.comp π) σ π (LinearEquiv.refl _ _) (fun _ _ => rfl) A
  have hFF : IsFFModule σ := by
    let := hA
    refine ⟨A.map π, ⟨?_, IsElementaryAbelian.map π⟩, ?_⟩
    · intro hb
      have : Nat.card (A.map π) = 1 := by rw [hb]; exact Nat.card_unique
      omega
    · rw [rank, hc]
      change fixedCodim σ (A.map π) ≤ 1
      exact he ▸ hd
  have hdim := finrank_le_six σ (full_commutator_of_irreducible σ hmove) hFF
  obtain ⟨a, ⟨e⟩⟩ := (naturalOrDual_of_irreducible σ hdim hmove).marked
  refine ⟨a, ⟨Representation.Equiv.mk e.toLinearEquiv ?_⟩⟩
  intro g
  simpa only [← hσ, MonoidHom.comp_apply] using e.isIntertwining' (π g)
end CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.Initial.Natural.Triple.Composition
