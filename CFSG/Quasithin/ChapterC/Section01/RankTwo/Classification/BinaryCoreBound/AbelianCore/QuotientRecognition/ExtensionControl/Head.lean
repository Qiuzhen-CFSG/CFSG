module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.AbelianCore.QuotientRecognition.ExtensionControl.Dimension
public import Theory.Representation.PSL3Two.IrreducibleCatalogue
public import Theory.Representation.PSL3Two.AutomorphismAction.NaturalDual
public import Theory.Representation.SimpleHeadQuotient
public import Theory.Representation.BinaryOffender.IrreducibleExistence

/-!
# Natural heads in dimension at most six

Choose a maximal proper invariant subspace. Full commutator generation makes
its irreducible quotient nontrivial, and dimension at most six excludes the
eight-dimensional model from the concrete irreducible catalogue. The quotient
is therefore natural or dual-natural, and its kernel has dimension at most
three. Simplicity and the order 168 exclude nontrivial binary actions in
dimension at most two; perfectness consequently makes any nontrivial action
in dimension three irreducible. Thus the kernel is either fixed or natural.
In the fixed case it is the entire fixed space, since the head has no invariants.

Explicit coordinates finish the fixed-kernel branch, and a separately proved
split pair with one common marking gives two-copy coordinates. No assertion
that the two-factor extension splits is made here.

Source: the binary reduction in Aschbacher–Smith B.5.1, printed pp.99–101,
and the two-factor branch of B.4.9, pp.92–95, combined manuscript of 1 March 2004.
-/

public section
open Representation Representation.BinaryOffender
open scoped Matrix
namespace CFSG.Quasithin.ChapterC.BinaryMS.AbelianCore.QuotientRecognition.ExtensionControl

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

/-- The actual subrepresentation of vectors fixed by the whole matrix group. -/
private noncomputable def fixedSubrepresentation (ρ : Representation (ZMod 2) SL V) :
    Subrepresentation ρ where
  toSubmodule := fixedSpace ρ ⊤
  apply_mem_toSubmodule g v hv := by
    have hg : ρ g v = v := hv ⟨g, Subgroup.mem_top g⟩
    rw [hg]
    exact hv

/-- Either of the two actual natural orientations, expressed by intertwining equivalences. -/
@[expose] def NaturalOrDual (ρ : Representation (ZMod 2) SL V) : Prop :=
  Nonempty (ρ.Equiv BinaryLinearThree.W) ∨ Nonempty (ρ.Equiv BinaryLinearThree.W.dual)

/-- Each natural orientation has dimension three. -/
theorem NaturalOrDual.finrank {ρ : Representation (ZMod 2) SL V} (h : NaturalOrDual ρ) :
    Module.finrank (ZMod 2) V = 3 := by
  rcases h with h | h <;> obtain ⟨e⟩ := h
  · rw [e.toLinearEquiv.finrank_eq]
    simp [BinaryLinearThree.Vector, Matrix.PSL3Two.Fano.Vector]
  · rw [e.toLinearEquiv.finrank_eq, Subspace.dual_finrank_eq]
    simp [BinaryLinearThree.Vector, Matrix.PSL3Two.Fano.Vector]

variable [FiniteDimensional (ZMod 2) V] (ρ : Representation (ZMod 2) SL V)

private theorem action_trivial_of_finrank_le_two (hd : Module.finrank (ZMod 2) V ≤ 2) :
    ∀ g v, ρ g v = v := by
  let : IsSimpleGroup SL := Atlas.Comparisons.Exceptional.sl3Two_simple
  rcases (inferInstance : ρ.ker.Normal).eq_bot_or_eq_top with hb | ht
  · have hinj := ρ.ker_eq_bot_iff.mp hb
    let : Finite (Module.End (ZMod 2) V) := Module.finite_of_finite (ZMod 2)
    have hc := Nat.card_le_card_of_injective ρ hinj
    rw [Matrix.PSL3Two.card_SL, Module.natCard_eq_pow_finrank (K := ZMod 2),
      Nat.card_zmod, Module.finrank_linearMap] at hc
    have hp : 2 ^ (Module.finrank (ZMod 2) V * Module.finrank (ZMod 2) V) ≤ 2 ^ 4 :=
      Nat.pow_le_pow_right (by decide) (by nlinarith)
    norm_num at hp
    omega
  · have he : ρ = 1 := MonoidHom.ker_eq_top_iff.mp ht
    intro g v
    rw [he]
    rfl

private theorem irreducible_of_finrank_le_three
    (hd : Module.finrank (ZMod 2) V ≤ 3) (hn : ∃ g v, ρ g v ≠ v) :
    IsIrreducible ρ := by
  let : Nontrivial V := by
    obtain ⟨g,v,hv⟩ := hn
    exact ⟨⟨ρ g v, v, hv⟩⟩
  let : Group.IsPerfect SL := Atlas.sl_perfect (F := ZMod 2) 3 (by decide)
  refine ⟨fun U => ?_⟩
  by_cases hb : U = ⊥
  · exact Or.inl hb
  by_cases ht : U = ⊤
  · exact Or.inr ht
  exfalso
  have ht' : U.toSubmodule ≠ ⊤ := fun h => ht (Subrepresentation.toSubmodule_injective h)
  have hb' : U.toSubmodule ≠ ⊥ := fun h => hb (Subrepresentation.toSubmodule_injective h)
  have hdim := U.toSubmodule.finrank_quotient_add_finrank
  have hsmall := Submodule.finrank_lt ht'
  let : Nontrivial U.toSubmodule := Submodule.nontrivial_iff_ne_bot.mpr hb'
  have hpos : 0 < Module.finrank (ZMod 2) U.toSubmodule := Module.finrank_pos
  have hfixU := action_trivial_of_finrank_le_two U.toRepresentation (by omega)
  have hfixQ := action_trivial_of_finrank_le_two U.quotientRepresentation (by omega)
  have hC : subspaceCommutator ρ ⊤ ⊤ ≤ fixedSpace ρ ⊤ := by
    apply Submodule.span_le.mpr
    rintro _ ⟨g, _, v, _, rfl⟩
    have hv : ρ g v - v ∈ U.toSubmodule :=
      (Submodule.Quotient.eq U.toSubmodule).mp (hfixQ g (U.toSubmodule.mkQ v))
    intro a
    exact congrArg Subtype.val (hfixU a.val ⟨ρ g v - v, hv⟩)
  have hall := le_fixedSpace_of_commutator_le_fixedSpace ρ ⊤ ⊤
    (le_subspaceStabilizer ρ ⊤ (by simp)) hC
  obtain ⟨g,v,hv⟩ := hn
  exact hv (hall Submodule.mem_top ⟨g, Subgroup.mem_top g⟩)

/-- The irreducible catalogue excludes the adjoint model below dimension eight. -/
theorem naturalOrDual_of_irreducible [IsIrreducible ρ]
    (hd : Module.finrank (ZMod 2) V ≤ 6) (hn : ∃ g v, ρ g v ≠ v) : NaturalOrDual ρ := by
  rcases BinaryLinearThree.IrreducibleCatalogue.classify_nontrivial ρ hn with hw | hd' | hs
  · exact Or.inl hw
  · exact Or.inr hd'
  · obtain ⟨e⟩ := hs
    have hdim := e.toLinearEquiv.finrank_eq
    rw [BinaryLinearThree.finrank_steinberg] at hdim
    omega

omit [FiniteDimensional (ZMod 2) V] in
private theorem quotient_nontrivial_action
    (hfull : subspaceCommutator ρ ⊤ ⊤ = ⊤) (N : Subrepresentation ρ) (hN : N ≠ ⊤) :
    ∃ g w, N.quotientRepresentation g w ≠ w := by
  by_contra! h
  apply hN
  apply Subrepresentation.toSubmodule_injective
  apply top_unique
  rw [← hfull]
  apply Submodule.span_le.mpr
  rintro _ ⟨g, _, v, _, rfl⟩
  exact (Submodule.Quotient.eq N.toSubmodule).mp (h g (N.toSubmodule.mkQ v))

omit [FiniteDimensional (ZMod 2) V] in
private theorem fixed_le_kernel_of_irreducible_head (N : Subrepresentation ρ)
    [IsIrreducible N.quotientRepresentation]
    (hmove : ∃ g v, N.quotientRepresentation g v ≠ v) :
    fixedSpace ρ ⊤ ≤ N.toSubmodule := by
  have hzero : fixedSpace N.quotientRepresentation ⊤ = ⊥ := by
    rcases eq_bot_or_eq_top (fixedSubrepresentation N.quotientRepresentation) with hb | ht
    · exact congrArg Subrepresentation.toSubmodule hb
    · obtain ⟨g,v,hv⟩ := hmove
      have hv' : v ∈ fixedSubrepresentation N.quotientRepresentation := ht ▸ trivial
      exact False.elim (hv (hv' ⟨g, Subgroup.mem_top g⟩))
  intro v hv
  apply (Submodule.Quotient.mk_eq_zero _).mp
  have hf : N.toSubmodule.mkQ v ∈ fixedSpace N.quotientRepresentation ⊤ := by
    intro g
    change N.toSubmodule.mkQ (ρ g v) = N.toSubmodule.mkQ v
    exact congrArg N.toSubmodule.mkQ (hv g)
  rw [hzero] at hf
  exact hf

/-- A nonzero commutator-generated module of dimension at most six has a natural
head whose kernel is either exactly the fixed space or another natural factor. -/
theorem exists_natural_head [Nontrivial V]
    (hd : Module.finrank (ZMod 2) V ≤ 6) (hfull : subspaceCommutator ρ ⊤ ⊤ = ⊤) :
    ∃ N : Subrepresentation ρ, NaturalOrDual N.quotientRepresentation ∧
      (N.toSubmodule = fixedSpace ρ ⊤ ∨ NaturalOrDual N.toRepresentation) := by
  let : IsCoatomic (Subrepresentation ρ) := SimpleHeadQuotient.subrepresentation_coatomic ρ
  obtain ⟨N,hN⟩ := IsCoatomic.exists_coatom (Subrepresentation ρ)
  let : IsIrreducible N.quotientRepresentation :=
    SimpleHeadQuotient.irreducible_quotient_of_isCoatom N hN
  have hdim := N.toSubmodule.finrank_quotient_add_finrank
  have hn := naturalOrDual_of_irreducible N.quotientRepresentation (by omega)
    (quotient_nontrivial_action ρ hfull N hN.1)
  refine ⟨N, hn, ?_⟩
  by_cases hc : N.toSubmodule ≤ fixedSpace ρ ⊤
  · exact Or.inl (le_antisymm hc (fixed_le_kernel_of_irreducible_head ρ N
      (quotient_nontrivial_action ρ hfull N hN.1)))
  · have hmove : ∃ g v, N.toRepresentation g v ≠ v := by
      by_contra! h
      apply hc
      intro v hv g
      exact congrArg Subtype.val (h g.val ⟨v,hv⟩)
    have hthree := hn.finrank
    let : IsIrreducible N.toRepresentation :=
      irreducible_of_finrank_le_three N.toRepresentation (by omega) hmove
    exact Or.inr (naturalOrDual_of_irreducible N.toRepresentation (by omega) hmove)


omit [FiniteDimensional (ZMod 2) V] in
/-- A natural or dual-natural factor admits one explicit automorphism marking. -/
theorem NaturalOrDual.marked {ρ : Representation (ZMod 2) SL V} (h : NaturalOrDual ρ) :
    ∃ a : SL ≃* SL, Nonempty (ρ.Equiv (BinaryLinearThree.W.comp a.toMonoidHom)) := by
  rcases h with h | h <;> obtain ⟨e⟩ := h
  · exact ⟨MulEquiv.refl SL, ⟨e⟩⟩
  · exact ⟨BinaryLinearThree.AutomorphismAction.graph,
      ⟨e.trans BinaryLinearThree.AutomorphismAction.graphNaturalDual.symm⟩⟩

omit [FiniteDimensional (ZMod 2) V] in
/-- Actual quotient coordinates in the branch with a natural head and central kernel. -/
theorem moduleQuotient_one_of_natural_head (N : Subrepresentation ρ)
    (hn : NaturalOrDual N.quotientRepresentation) (hker : N.toSubmodule = fixedSpace ρ ⊤) :
    Nonempty (ModuleQuotient ρ 1) := by
  obtain ⟨a,⟨e⟩⟩ := hn.marked
  refine ⟨{
    marking := a
    projection := LinearMap.pi fun _ : Fin 1 => e.toLinearEquiv.toLinearMap.comp N.toSubmodule.mkQ
    surjective := ?_
    kernel := ?_
    equivariant := ?_
  }⟩
  · intro w
    obtain ⟨v,hv⟩ := N.toSubmodule.mkQ_surjective (e.toLinearEquiv.symm (w 0))
    refine ⟨v, ?_⟩
    funext i
    have hi : i = 0 := Subsingleton.elim _ _
    subst i
    change e (N.toSubmodule.mkQ v) = w 0
    rw [hv]
    exact e.toLinearEquiv.apply_symm_apply (w 0)
  · ext v
    change (fun _ : Fin 1 => e (N.toSubmodule.mkQ v)) = 0 ↔ v ∈ fixedSpace ρ ⊤
    rw [← hker]
    constructor
    · intro h
      apply (Submodule.Quotient.mk_eq_zero _).mp
      apply e.toLinearEquiv.injective
      exact (congrFun h 0).trans (map_zero e.toLinearEquiv).symm
    · intro h
      funext i
      change e (N.toSubmodule.mkQ v) = 0
      have hz : N.toSubmodule.mkQ v = 0 := (Submodule.Quotient.mk_eq_zero _).mpr h
      rw [hz]
      exact map_zero e.toLinearEquiv
  · intro g v i
    exact LinearMap.congr_fun (e.isIntertwining' g) (N.toSubmodule.mkQ v)

private theorem natural_fixed_zero (v : BinaryLinearThree.Vector)
    (h : ∀ g : SL, BinaryLinearThree.W g v = v) : v = 0 := by
  have hc : ∀ v : BinaryLinearThree.Vector,
      (∀ g : SL, g.val *ᵥ v = v) → v = 0 := by decide +kernel
  exact hc v h

omit [FiniteDimensional (ZMod 2) V] in
/-- One common marking on a split pair gives the required two-copy coordinates. -/
theorem moduleQuotient_two_of_equiv (a : SL ≃* SL)
    (e : ρ.Equiv (Representation.prod (BinaryLinearThree.W.comp a.toMonoidHom)
      (BinaryLinearThree.W.comp a.toMonoidHom))) : Nonempty (ModuleQuotient ρ 2) := by
  let p : V →ₗ[ZMod 2] (Fin 2 → BinaryLinearThree.Vector) := {
    toFun v := ![(e.toLinearEquiv v).1, (e.toLinearEquiv v).2]
    map_add' v w := by ext i; fin_cases i <;> simp
    map_smul' c v := by ext i; fin_cases i <;> simp
  }
  have hfixed : fixedSpace ρ ⊤ = ⊥ := by
    apply le_bot_iff.mp
    intro v hv
    apply e.toLinearEquiv.injective
    rw [map_zero]
    apply Prod.ext
    · apply natural_fixed_zero
      intro g
      have he := LinearMap.congr_fun (e.isIntertwining' (a.symm g)) v
      change e.toLinearEquiv (ρ (a.symm g) v) =
        (BinaryLinearThree.W (a (a.symm g)) (e.toLinearEquiv v).1,
         BinaryLinearThree.W (a (a.symm g)) (e.toLinearEquiv v).2) at he
      have hv' : ρ (a.symm g) v = v := hv ⟨a.symm g, Subgroup.mem_top _⟩
      rw [hv', a.apply_symm_apply] at he
      exact (congrArg Prod.fst he).symm
    · apply natural_fixed_zero
      intro g
      have he := LinearMap.congr_fun (e.isIntertwining' (a.symm g)) v
      change e.toLinearEquiv (ρ (a.symm g) v) =
        (BinaryLinearThree.W (a (a.symm g)) (e.toLinearEquiv v).1,
         BinaryLinearThree.W (a (a.symm g)) (e.toLinearEquiv v).2) at he
      have hv' : ρ (a.symm g) v = v := hv ⟨a.symm g, Subgroup.mem_top _⟩
      rw [hv', a.apply_symm_apply] at he
      exact (congrArg Prod.snd he).symm
  refine ⟨{marking := a, projection := p, surjective := ?_, kernel := ?_, equivariant := ?_}⟩
  · intro w
    refine ⟨e.toLinearEquiv.symm (w 0, w 1), ?_⟩
    funext i
    fin_cases i
    · exact congrArg Prod.fst (e.toLinearEquiv.apply_symm_apply (w 0, w 1))
    · exact congrArg Prod.snd (e.toLinearEquiv.apply_symm_apply (w 0, w 1))
  · rw [hfixed]
    apply LinearMap.ker_eq_bot.mpr
    intro v w he
    apply e.toLinearEquiv.injective
    apply Prod.ext
    · exact congrFun he 0
    · exact congrFun he 1
  · intro g v i
    have he := LinearMap.congr_fun (e.isIntertwining' g) v
    fin_cases i
    · exact congrArg Prod.fst he
    · exact congrArg Prod.snd he

end CFSG.Quasithin.ChapterC.BinaryMS.AbelianCore.QuotientRecognition.ExtensionControl
