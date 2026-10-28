module
public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceCompletion.ChiefImages
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.Classification.NilpotentRadical
public import Theory.Representation.Clifford
public import Theory.Representation.NormalInvariants
public import Theory.GroupTheory.GeneralizedFitting.QuasisimpleTransfer

/-!
# Faithful constituents of noncentral chief images

Modular Clifford theory decomposes an ambient irreducible chief image over its
normal component. A.3.6 says the component center has order one or three.
A nonzero constituent kernel is either the whole component or its full center;
either would supply nonzero invariants for a normal ambient subgroup and
contradict ambient faithfulness. Thus each actual component constituent is
faithful. This preserves the original chief-section central kernel.

The final theorem applies the decomposition to each literal noncentral factor
of the constructed B.5.1 flag. A.2.1 and A.3.6 remain genuine earlier inputs;
neither constituent semisimplicity nor a B.5.1 classifier is assumed.

Source: Aschbacher--Smith B.5.1, p.100, following (+); A.3.6; Isaacs 6.5.
-/

@[expose] public noncomputable section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open scoped BigOperators ENNReal IsMulCommutative
namespace CFSG.Quasithin.ChapterB.QuasisimpleSource.SourceCompletion
universe u v
variable {G : Type u} [Group G] {V : Type v} [AddCommGroup V] [Module (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V)

private theorem center_card_of_a36_common [Finite G] [IsQuasisimple G]
    (h : Chapter1.Section02.A36Common G) :
    Nat.card (center G) = 1 ∨ Nat.card (center G) = 3 := by
  rcases h.2.2.1 with hf | hc
  · have ht : fittingSubgroup G = ⊤ := hf.1.trans generalizedFitting_eq_top_of_quasisimple
    have hnil : Group.IsNilpotent (⊤ : Subgroup G) := ht ▸
      inferInstanceAs (Group.IsNilpotent (fittingSubgroup G))
    let := hnil
    let : Group.IsNilpotent G := Group.nilpotent_of_mulEquiv (topEquiv : (⊤ : Subgroup G) ≃* G)
    let : IsSimpleGroup (G ⧸ center G) := IsQuasisimple.simple
    let : Nontrivial G := (QuotientGroup.mk'_surjective (center G)).nontrivial
    exact (Group.IsPerfect.not_isNilpotent G inferInstance).elim
  · simpa only [hc.1] using hc.2.2

/-- A.3.6 supplies the actual center order on an SQTK quasisimple image. -/
theorem center_order_of_a36 [Finite G] [IsQuasisimple G] {K : GroupClass.{u}}
    (h36 : Chapter1.Section02.A36Input K) (hsq : IsSQTK K G) (hcore : pCore 2 G = ⊥) :
    Nat.card (center G) = 1 ∨ Nat.card (center G) = 3 := by
  let : IsQuasisimple (⊤ : Subgroup G) := IsQuasisimple.of_mulEquiv topEquiv.symm
  have ht : IsComponent G ⊤ :=
    ⟨(inferInstance : (⊤ : Subgroup G).Normal).isSubnormal, inferInstance⟩
  have hc := center_card_of_a36_common (h36 G hsq hcore ⊤ ht.isCComponent).2
  have he := Nat.card_congr (centerCongr (topEquiv : (⊤ : Subgroup G) ≃* G)).toEquiv
  rwa [he] at hc

/-- Every nonzero C-submodule of an ambient irreducible faithful action is
faithful on C when C is quasisimple and its center has order one or three.
Only the actual component image is used; this says nothing about a covering
component before its kernel quotient. -/
theorem constituent_faithful [Finite G]
    (hf : Function.Injective ρ) (hi : IsIrreducible ρ)
    (C : Subgroup G) [C.Normal] [IsQuasisimple C]
    (hc : Nat.card (center C) = 1 ∨ Nat.card (center C) = 3)
    (W : Subrepresentation (ρ.comp C.subtype)) (hW : W ≠ ⊥) :
    Function.Injective W.toRepresentation := by
  let := hi
  have hWsub : W.toSubmodule ≠ ⊥ := fun he => hW (Subrepresentation.toSubmodule_injective he)
  have hnormal (N : Subgroup G) [N.Normal]
      (hfix : W.toSubmodule ≤ fixedSpace ρ N) : N = ⊥ := by
    have hn : Representation.invariants (ρ.comp N.subtype) ≠ ⊥ := by
      intro hz
      apply hWsub
      exact bot_unique (hfix.trans_eq hz)
    exact bot_unique ((le_ker_of_normal_invariants_ne_bot ρ N hn).trans
      ((MonoidHom.ker_eq_bot_iff _).mpr hf).le)
  apply (MonoidHom.ker_eq_bot_iff _).mp
  rcases IsQuasisimple.normal_le_center_or_eq_top W.toRepresentation.ker with hk | hk
  · rcases hc with hc | hc
    · exact bot_unique (hk.trans_eq (Subgroup.card_eq_one.mp hc))
    have hd : Nat.card W.toRepresentation.ker ∣ 3 := hc ▸ card_dvd_of_le hk
    rcases (Nat.dvd_prime Nat.prime_three).mp hd with h1 | h3
    · exact Subgroup.card_eq_one.mp h1
    have hker : W.toRepresentation.ker = center C :=
      Subgroup.eq_of_le_of_card_ge hk (by omega)
    let Z := (center C).map C.subtype
    let : Z.Normal := ConjAct.normal_of_characteristic_of_normal
    have hZ : Z = ⊥ := hnormal Z (by
      intro v hv
      rintro ⟨_, z, hz, rfl⟩
      have hm : z ∈ W.toRepresentation.ker := hker.symm ▸ hz
      exact congrArg Subtype.val (LinearMap.congr_fun hm (⟨v, hv⟩ : W.toSubmodule)))
    have hz : center C = ⊥ := (Subgroup.map_eq_bot_iff_of_injective _ C.subtype_injective).mp hZ
    rw [hz, Subgroup.card_bot] at hc
    omega
  · have hC : C = ⊥ := hnormal C (by
      intro v hv c
      have hm : c ∈ W.toRepresentation.ker := hk.symm ▸ Subgroup.mem_top c
      exact congrArg Subtype.val (LinearMap.congr_fun hm (⟨v, hv⟩ : W.toSubmodule)))
    let : IsSimpleGroup (C ⧸ center C) := IsQuasisimple.simple
    let : Nontrivial C := (QuotientGroup.mk'_surjective (center C)).nontrivial
    exact ((Subgroup.nontrivial_iff_ne_bot C).mp inferInstance hC).elim

/-- Modular Clifford theory gives the full internal direct-sum decomposition
on the actual normal component before any natural-module identification. -/
theorem constituent_decomposition [Finite G] [FiniteDimensional (ZMod 2) V]
    (hi : IsIrreducible ρ) (C : Subgroup G) [C.Normal] :
    ∃ (n : ℕ) (W : Fin n → Subrepresentation (ρ.comp C.subtype)),
      DirectSum.IsInternal (fun i => (W i).asSubmodule) ∧
        ∀ i, IsIrreducible (W i).toRepresentation := by
  let := hi
  let : Nontrivial V := Subrepresentation.irreducible_module_nontrivial ρ
  obtain ⟨W, hW⟩ := Subrepresentation.irreducible_subrepresentation_of_finite_dimensional
    (ρ.comp C.subtype)
  obtain ⟨n, g, hd, hi, _⟩ := Representation.isaacs_theorem_6_5.{0,u,v,v} ρ C hi W hW
  exact ⟨n, fun i => Representation.conjugateSubrepresentation ρ C W (g i), hd, hi⟩

/-- With the A.3.6 center alternatives every summand is faithful on the actual
component, while the decomposition retains its original vector subspaces. -/
theorem faithful_constituent_decomposition [Finite G] [FiniteDimensional (ZMod 2) V]
    (hf : Function.Injective ρ) (hi : IsIrreducible ρ)
    (C : Subgroup G) [C.Normal] [IsQuasisimple C]
    (hc : Nat.card (center C) = 1 ∨ Nat.card (center C) = 3) :
    ∃ (n : ℕ) (W : Fin n → Subrepresentation (ρ.comp C.subtype)),
      DirectSum.IsInternal (fun i => (W i).asSubmodule) ∧
        ∀ i, IsIrreducible (W i).toRepresentation ∧ Function.Injective (W i).toRepresentation := by
  obtain ⟨n, W, hd, hiW⟩ := constituent_decomposition ρ hi C
  refine ⟨n, W, hd, fun i => ⟨hiW i, ?_⟩⟩
  exact constituent_faithful ρ hf hi C hc (W i)
    ((Subrepresentation.irreducible_iff_isAtom _).mp (hiW i)).ne_bot

/-- The full decomposition, on the original vector subspaces. -/
def FaithfulConstituentDecomposition (C : Subgroup G) : Prop :=
  ∃ (n : ℕ) (W : Fin n → Subrepresentation (ρ.comp C.subtype)),
    DirectSum.IsInternal (fun i => (W i).asSubmodule) ∧
      ∀ i, IsIrreducible (W i).toRepresentation ∧ Function.Injective (W i).toRepresentation

/-- The actual noncentral chief image has faithful irreducible component
constituents. The only earlier inputs here are A.2.1 for the SQTK image and
A.3.6 for its center; no B.5.1 conclusion is used. -/
theorem ChiefImage.faithful_constituents [Finite G] [FiniteDimensional (ZMod 2) V]
    {K : GroupClass.{u}}
    (hsemisimple : SourceInduction.HighThreeRank.CoverCentralizer.SourceConstruction.SemisimpleInput K)
    (h36 : Chapter1.Section02.A36Input K)
    (L : Subgroup G) [L.Normal] [IsQuasisimple L]
    (hL : IsSQTK K L) (hi : IsIrreducible ρ)
    (hn : subspaceCommutator ρ ⊤ L ≠ ⊥) :
    FaithfulConstituentDecomposition (KernelQuotient.action ρ) (ChiefImage.component ρ L) := by
  let C := ChiefImage.component ρ L
  let : C.Normal := ChiefImage.component_normal ρ L
  let : IsQuasisimple C := ChiefImage.component_quasisimple ρ L hn
  have hsq := ChiefImage.component_sqtk ρ hsemisimple L hL hn
  have hcore : pCore 2 C = ⊥ := by
    apply (Subgroup.map_eq_bot_iff_of_injective _ C.subtype_injective).mp
    apply bot_unique
    have hm : (pCore 2 C).map C.subtype ≤ pCore 2 (KernelQuotient.Actor ρ) :=
      le_sSup ⟨ConjAct.normal_of_characteristic_of_normal, pCore_isPGroup.map C.subtype⟩
    exact hm.trans_eq (ChiefImage.twoCore_eq_bot ρ hi)
  exact faithful_constituent_decomposition (KernelQuotient.action ρ)
    (KernelQuotient.faithful ρ) (ChiefImage.irreducible ρ hi) C
    (center_order_of_a36 h36 hsq hcore)

/-- Faithful component semisimplicity on each literal noncentral section of
the source flag, with its original quotient carrier and kernel projection. -/
theorem faithful_flag_constituents [Finite G] [FiniteDimensional (ZMod 2) V]
    {K : GroupClass.{u}}
    (hsemisimple : SourceInduction.HighThreeRank.CoverCentralizer.SourceConstruction.SemisimpleInput K)
    (h36 : Chapter1.Section02.A36Input K)
    [IsQuasisimple (generalizedFitting G)] (hL : IsSQTK K (generalizedFitting G))
    (f : ReducibleChiefFlag ρ (generalizedFitting G)) {i : ℕ} (hi : i ∈ f.noncentral) :
    let τ := sectionRepresentation ρ (f.chain i) (f.chain (i + 1))
    FaithfulConstituentDecomposition (KernelQuotient.action τ)
      (ChiefImage.component τ (generalizedFitting G)) :=
  ChiefImage.faithful_constituents _ hsemisimple h36 (generalizedFitting G) hL
    (f.irreducible ρ ((f.mem_noncentral i).mp hi).1) ((f.mem_noncentral i).mp hi).2

end CFSG.Quasithin.ChapterB.QuasisimpleSource.SourceCompletion
