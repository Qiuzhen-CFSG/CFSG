module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.LinearThree

/-!
# Quotient model transport for the source L₃(2) branch

The block module identifies the literal quotient U/C_U(K). Transporting its
intrinsic carrier along K's inclusion constructs the ambient model, with actor
induced by the original isomorphism K/O₂(K). An inner change of coordinates
conjugates this actor and applies the same matrix to the module, preserving
naturality and using one marking on all summands.

Source: Aschbacher--Smith, combined 1 March 2004 manuscript, 13.6.22, p.932.
-/

@[expose] public section
open Subgroup Representation
open CFSG.Quasithin.ChapterC
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.LinearThreeBranch
variable {G A V : Type*} [Group G] [Group A] [AddCommGroup V] [Module (ZMod 2) V]
variable (K : Subgroup G) (ρ : Representation (ZMod 2) A V)
/-- The block quotient with its actual ambient conjugation and fixed kernel. -/
noncomputable def of_block_model (r : A →* MulAut (Multiplicative V))
    (b : BlockModuleModel K r)
    (hr : ∀ (g : A) (v : Multiplicative V), Multiplicative.toAdd (r g v) =
      ρ g (Multiplicative.toAdd v)) :
    ConjugationQuotientModel K ((blockU K).map K.subtype) ρ := by
  let e := (blockU K).equivMapOfInjective K.subtype K.subtype_injective
  let f := b.moduleIso.toMonoidHom.comp
    ((QuotientGroup.mk' (blockFixed K)).comp e.symm.toMonoidHom)
  have hn : K ≤ normalizer (((blockU K).map K.subtype : Subgroup G) : Set G) := by
    have h := (blockU K).le_normalizer_map K.subtype
    rw [normalizer_eq_top, ← MonoidHom.range_eq_map, range_subtype] at h
    exact h
  refine { normalizes := hn
           actor := b.quotientIso.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 K))
           quotient := f
           surjective := b.moduleIso.surjective.comp
             ((QuotientGroup.mk'_surjective _).comp e.symm.surjective)
           kernel := ?_
           equivariant := ?_ }
  · ext u
    obtain ⟨u, rfl⟩ := e.surjective u
    change b.moduleIso (QuotientGroup.mk' (blockFixed K) (e.symm (e u))) = 1 ↔ _
    rw [e.symm_apply_apply, map_eq_one_iff b.moduleIso b.moduleIso.injective,
      QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    change (u : K) ∈ center K ↔ (e u : G) ∈ centralizer (K : Set G)
    rw [mem_center_iff]
    constructor
    · intro h g hg
      exact congrArg Subtype.val (h ⟨g, hg⟩)
    · intro h g
      apply Subtype.ext
      exact h g g.property
  · intro k u
    obtain ⟨u, rfl⟩ := e.surjective u
    have he : e.symm
        (((blockU K).map K.subtype).normalizerMonoidHom ⟨k, hn k.property⟩ (e u)) =
        blockConjugate K k u := by
      apply e.injective
      rw [e.apply_symm_apply]
      apply Subtype.ext
      rfl
    change b.moduleIso (QuotientGroup.mk' (blockFixed K) (e.symm _)) = _
    rw [he, b.intertwining]
    apply Multiplicative.toAdd.injective
    simpa only [f, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, e.symm_apply_apply, toAdd_ofAdd]
      using hr (b.quotientIso (QuotientGroup.mk' (pCore 2 K) k))
        (b.moduleIso (QuotientGroup.mk' (blockFixed K) u))

/-! C.1's ordinary `L₃(2)` block clause already carries the exact
equivariant model needed by the ambient quotient. -/
theorem natural_model_of_isLinearTwoBlock (K : Subgroup G)
    (h : IsLinearTwoBlock K 3) :
    Nonempty (ConjugationQuotientModel K ((blockU K).map K.subtype)
      BinaryLinearThree.W) := by
  obtain ⟨r, ⟨b⟩, hr⟩ := h.2.2.2
  exact ⟨of_block_model K BinaryLinearThree.W r b hr⟩
end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.LinearThreeBranch
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.LinearThreeBranch
variable {G A V : Type*} [Group G] [Group A] [AddCommGroup V] [Module (ZMod 2) V]
  {K U : Subgroup G} {ρ : Representation (ZMod 2) A V}

/-! A C.1 section model can be transported directly when its kernel is the
literal ambient centralizer. This keeps the section quotient and its actor in
the model, instead of replacing them by a dimension or family tag. -/
noncomputable def of_section_model {D E : Subgroup G}
    (actor : K →* A) (hKD : K ≤ normalizer (D : Set G))
    (hn : (E.subgroupOf D).Normal)
    (e : (D ⧸ E.subgroupOf D) ≃* Multiplicative V)
    (he : ∀ k : K, ∀ d d' : D,
      (d' : G) = (k : G) * (d : G) * (k : G)⁻¹ →
      Multiplicative.toAdd (e (QuotientGroup.mk' _ d')) =
        ρ (actor k) (Multiplicative.toAdd (e (QuotientGroup.mk' _ d))))
    (hCE : (centralizer (K : Set G)).subgroupOf D = E.subgroupOf D) :
    ConjugationQuotientModel K D ρ := by
  letI := hn
  let q : D →* Multiplicative V := e.toMonoidHom.comp (QuotientGroup.mk' _)
  refine { normalizes := hKD
           actor := actor
           quotient := q
           surjective := e.surjective.comp (QuotientGroup.mk'_surjective _)
           kernel := ?_
           equivariant := ?_ }
  · rw [hCE]
    ext d
    change e (QuotientGroup.mk' _ d) = 1 ↔ _
    rw [map_eq_one_iff e e.injective, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  · intro k d
    exact he k d (D.normalizerMonoidHom ⟨k, hKD k.property⟩ d) rfl

/-- An inner change of actor coordinates preserves the specified representation. -/
def conjugate (m : ConjugationQuotientModel K U ρ) (g : A) :
    ConjugationQuotientModel K U ρ := by
  let e : V ≃+ V :=
    { toFun := ρ g
      invFun := ρ g⁻¹
      left_inv := ρ.inv_self_apply g
      right_inv := ρ.self_inv_apply g
      map_add' := (ρ g).map_add }
  refine { normalizes := m.normalizes
           actor := (MulAut.conj g).toMonoidHom.comp m.actor
           quotient := e.toMultiplicative.toMonoidHom.comp m.quotient
           surjective := e.toMultiplicative.surjective.comp m.surjective
           kernel := ?_
           equivariant := ?_ }
  · rw [← m.kernel]
    ext u
    change e.toMultiplicative (m.quotient u) = 1 ↔ m.quotient u = 1
    exact map_eq_one_iff e.toMultiplicative e.toMultiplicative.injective
  · intro k u
    apply Multiplicative.toAdd.injective
    change ρ g (Multiplicative.toAdd (m.quotient _)) =
      ρ (g * m.actor k * g⁻¹) (ρ g (Multiplicative.toAdd (m.quotient u)))
    rw [m.equivariant]
    change ρ g (ρ (m.actor k) (Multiplicative.toAdd (m.quotient u))) = _
    simp only [← Module.End.mul_apply, ← map_mul, inv_mul_cancel_right]
end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.LinearThreeBranch
