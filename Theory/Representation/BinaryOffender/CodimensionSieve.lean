module

public import Theory.Representation.BinaryOffender.SectionLinear
public import Theory.Representation.BinaryOffender.FaithfulRankOne
public import Theory.Representation.BinaryOffender.SubspaceAction

/-!
# Offender deductions from a subspace of small codimension

If `[D,A]` lies in an invariant subspace `W`, then the image of `D` is fixed
in `V/W`. If `D ∩ W` is fixed, the corresponding bound holds on `W`.
In either case `dim(V/D) ≤ m(A)` produces an offender, and maximization
produces an FF-star offender. Unless a strong FF-star offender occurs,
equality of dimensions forces respectively `W ≤ D` or `W + D = V`.

Two faithful sections each contribute positive fixed codimension. When the
total is at most two, both contributions are one and every fixed quotient
vector lifts to a fixed vector. A line-valued displacement condition then
forces a larger subgroup into the pointwise centralizer on one section.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, combined
manuscript (1 March 2004), the linear arguments in 13.8.22–23, printed
pp.957–958. These results use actual restricted and quotient representations;
the construction of the critical subgroups and the component hypotheses
needed to establish faithfulness are separate source obligations.
-/

public section

namespace Representation.BinaryOffender
variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V] (ρ : Representation (ZMod 2) G V)

private theorem quotient_dim_mono {E F : Submodule (ZMod 2) V} (h : E ≤ F) :
    Module.finrank (ZMod 2) (V ⧸ F) ≤ Module.finrank (ZMod 2) (V ⧸ E) := by
  have := E.finrank_quotient_add_finrank
  have := F.finrank_quotient_add_finrank
  have := Submodule.finrank_mono h
  omega

private theorem eq_of_quotient_dim_eq {E F : Submodule (ZMod 2) V} (h : E ≤ F)
    (heq : Module.finrank (ZMod 2) (V ⧸ E) =
      Module.finrank (ZMod 2) (V ⧸ F)) : E = F := by
  have := E.finrank_quotient_add_finrank
  have := F.finrank_quotient_add_finrank
  apply Submodule.eq_of_le_of_finrank_eq h
  omega

/-- The quotient half of the offender sieve, including the equality case.
The strong alternative requires a best offender inside the given actor. -/
theorem quotient_offender_sieve [Finite G]
    (W : Subrepresentation ρ) (D : Submodule (ZMod 2) V) {A : Subgroup G}
    (hA : IsElementaryTwo A)
    (hcomm : ∀ a ∈ A, ∀ d ∈ D, ρ a d - d ∈ W.toSubmodule)
    (hdim : Module.finrank (ZMod 2) (V ⧸ D) ≤ rank A) :
    IsOffender W.quotientRepresentation A ∧
      (∃ B ≤ A, IsBestOffender W.quotientRepresentation B) ∧
      ((∃ B ≤ A, IsBestOffender W.quotientRepresentation B ∧
          IsStrongOffender W.quotientRepresentation B) ∨
        (W.toSubmodule ≤ D ∧
          D.map W.toSubmodule.mkQ = fixedSpace W.quotientRepresentation A ∧
          fixedCodim W.quotientRepresentation A = rank A ∧
          Module.finrank (ZMod 2) (V ⧸ D) = rank A)) := by
  let E := D.map W.toSubmodule.mkQ
  have hEC : E ≤ fixedSpace W.quotientRepresentation A := by
    rintro _ ⟨d, hd, rfl⟩ a
    exact (Submodule.Quotient.eq W.toSubmodule).mpr (hcomm a a.property d hd)
  have hcodim : fixedCodim W.quotientRepresentation A ≤
      Module.finrank (ZMod 2) ((V ⧸ W.toSubmodule) ⧸ E) :=
    quotient_dim_mono hEC
  have heq : Module.finrank (ZMod 2) ((V ⧸ W.toSubmodule) ⧸ E) =
      Module.finrank (ZMod 2) (V ⧸ (W.toSubmodule ⊔ D)) :=
    (Submodule.quotientQuotientEquivQuotientSup W.toSubmodule D).finrank_eq
  have hsup : Module.finrank (ZMod 2) (V ⧸ (W.toSubmodule ⊔ D)) ≤
      Module.finrank (ZMod 2) (V ⧸ D) := quotient_dim_mono le_sup_right
  have hoff : IsOffender W.quotientRepresentation A := ⟨hA, by omega⟩
  refine ⟨hoff, hoff.exists_bestOffender _, ?_⟩
  by_cases hlt : fixedCodim W.quotientRepresentation A < rank A
  · exact Or.inl (IsStrongOffender.exists_bestOffender _ ⟨hA, hlt⟩)
  · right
    have hequal : fixedCodim W.quotientRepresentation A = rank A := by omega
    have hDeq : D = W.toSubmodule ⊔ D :=
      eq_of_quotient_dim_eq le_sup_right (by omega)
    exact ⟨hDeq.symm ▸ le_sup_left,
      eq_of_quotient_dim_eq hEC (by
        change Module.finrank (ZMod 2) ((V ⧸ W.toSubmodule) ⧸ E) =
          fixedCodim W.quotientRepresentation A
        omega),
      hequal, by omega⟩

/-- The submodule half of the offender sieve. In the equality case the
submodule supplements `D`, and its fixed space is exactly its intersection with `D`. -/
theorem submodule_offender_sieve [Finite G]
    (W : Subrepresentation ρ) (D : Submodule (ZMod 2) V) {A : Subgroup G}
    (hA : IsElementaryTwo A)
    (hfixed : W.toSubmodule ⊓ D ≤ fixedSpace ρ A)
    (hdim : Module.finrank (ZMod 2) (V ⧸ D) ≤ rank A) :
    IsOffender W.toRepresentation A ∧
      (∃ B ≤ A, IsBestOffender W.toRepresentation B) ∧
      ((∃ B ≤ A, IsBestOffender W.toRepresentation B ∧
          IsStrongOffender W.toRepresentation B) ∨
        (W.toSubmodule ⊔ D = ⊤ ∧
          D.comap W.toSubmodule.subtype = fixedSpace W.toRepresentation A ∧
          fixedCodim W.toRepresentation A = rank A ∧
          Module.finrank (ZMod 2) (V ⧸ D) = rank A)) := by
  let E := D.comap W.toSubmodule.subtype
  have hEC : E ≤ fixedSpace W.toRepresentation A := by
    intro w hw a
    apply Subtype.ext
    exact hfixed ⟨w.property, hw⟩ a
  have hcodim : fixedCodim W.toRepresentation A ≤
      Module.finrank (ZMod 2) (W.toSubmodule ⧸ E) := quotient_dim_mono hEC
  let e : E ≃ₗ[ZMod 2] (W.toSubmodule ⊓ D : Submodule (ZMod 2) V) :=
    { toFun := fun w => ⟨w.val, w.val.property, w.property⟩
      invFun := fun w => ⟨⟨w, w.property.1⟩, w.property.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have he := e.finrank_eq
  have hE := E.finrank_quotient_add_finrank
  have hD := D.finrank_quotient_add_finrank
  have hsum := W.toSubmodule.finrank_sup_add_finrank_inf_eq D
  have htop := (W.toSubmodule ⊔ D).finrank_le
  have hoff : IsOffender W.toRepresentation A := ⟨hA, by omega⟩
  refine ⟨hoff, hoff.exists_bestOffender _, ?_⟩
  by_cases hlt : fixedCodim W.toRepresentation A < rank A
  · exact Or.inl (IsStrongOffender.exists_bestOffender _ ⟨hA, hlt⟩)
  · right
    have hequal : fixedCodim W.toRepresentation A = rank A := by omega
    refine ⟨Submodule.eq_top_of_finrank_eq (by omega),
      eq_of_quotient_dim_eq hEC ?_, hequal, by omega⟩
    change Module.finrank (ZMod 2) (W.toSubmodule ⧸ E) = fixedCodim W.toRepresentation A
    omega

/-- A module with faithful submodule and quotient has no nonidentity
action of fixed codimension one. -/
theorem faithful_sections_fixedCodim_ge_two
    (W : Subrepresentation ρ) (hW : Function.Injective W.toRepresentation)
    (hQ : Function.Injective W.quotientRepresentation) {A : Subgroup G} (hA : A ≠ ⊥) :
    2 ≤ fixedCodim ρ A := by
  have := fixedCodim_pos_of_faithful W.toRepresentation hW hA
  have := fixedCodim_pos_of_faithful W.quotientRepresentation hQ hA
  have := fixedCodim_quotient_add_subrepresentation_le ρ W A
  omega

/-- Two faithful sections sharing total fixed codimension at most two
each have fixed codimension one; the ambient fixed codimension is two. -/
theorem faithful_sections_of_fixedCodim_le_two
    (W : Subrepresentation ρ) (hW : Function.Injective W.toRepresentation)
    (hQ : Function.Injective W.quotientRepresentation) {A : Subgroup G} (hA : A ≠ ⊥)
    (hsmall : fixedCodim ρ A ≤ 2) :
    fixedCodim W.toRepresentation A = 1 ∧
      fixedCodim W.quotientRepresentation A = 1 ∧ fixedCodim ρ A = 2 := by
  have := fixedCodim_pos_of_faithful W.toRepresentation hW hA
  have := fixedCodim_pos_of_faithful W.quotientRepresentation hQ hA
  have := fixedCodim_quotient_add_subrepresentation_le ρ W A
  omega

/-- Equality in the fixed-codimension bound makes every fixed quotient
vector the image of an ambient fixed vector. -/
theorem fixedSpace_quotient_eq_map_of_fixedCodim_eq
    (W : Subrepresentation ρ) (A : Subgroup G)
    (heq : fixedCodim W.quotientRepresentation A + fixedCodim W.toRepresentation A =
      fixedCodim ρ A) :
    (fixedSpace ρ A).map W.toSubmodule.mkQ = fixedSpace W.quotientRepresentation A := by
  let C := fixedSpace ρ A
  let f := W.toSubmodule.mkQ.domRestrict C
  have hr : LinearMap.range f ≤ fixedSpace W.quotientRepresentation A := by
    rintro _ ⟨v, rfl⟩ a
    change W.toSubmodule.mkQ (ρ a v) = W.toSubmodule.mkQ v
    exact congrArg W.toSubmodule.mkQ (v.property a)
  let e : LinearMap.ker f ≃ₗ[ZMod 2]
      (W.toSubmodule ⊓ C : Submodule (ZMod 2) V) :=
    { toFun := fun v => ⟨v.val, (Submodule.Quotient.mk_eq_zero W.toSubmodule).mp v.property,
          v.val.property⟩
      invFun := fun v => ⟨⟨v, v.property.2⟩,
          (Submodule.Quotient.mk_eq_zero W.toSubmodule).mpr v.property.1⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hnull := f.finrank_range_add_finrank_ker
  have hker := e.finrank_eq
  have hfixed := (subrepresentationFixedEquiv ρ W A).finrank_eq
  have hv := fixedCodim_add_finrank ρ A
  have hw := fixedCodim_add_finrank W.toRepresentation A
  have hq := fixedCodim_add_finrank W.quotientRepresentation A
  have hdim := W.toSubmodule.finrank_quotient_add_finrank
  change Module.finrank (ZMod 2) (LinearMap.range f) +
    Module.finrank (ZMod 2) (LinearMap.ker f) = Module.finrank (ZMod 2) C at hnull
  change _ = Module.finrank (ZMod 2)
    (W.toSubmodule ⊓ fixedSpace ρ A : Submodule (ZMod 2) V) at hker
  change fixedCodim ρ A + Module.finrank (ZMod 2) C = Module.finrank (ZMod 2) V at hv
  have he : LinearMap.range f = fixedSpace W.quotientRepresentation A :=
    Submodule.eq_of_le_of_finrank_eq hr (by omega)
  have hmap : LinearMap.range f = C.map W.toSubmodule.mkQ := by
    ext v
    constructor
    · rintro ⟨c, rfl⟩
      exact ⟨c, c.property, rfl⟩
    · rintro ⟨c, hc, rfl⟩
      exact ⟨⟨c, hc⟩, rfl⟩
  exact hmap.symm.trans he

omit [FiniteDimensional (ZMod 2) V] in
/-- A properly larger subgroup fixing the same fixed space witnesses a
strictly larger pointwise centralizer in the actual acting group. -/
theorem lt_pointwiseKernel_fixedSpace {A B : Subgroup G} (hAB : A < B)
    (hfix : fixedSpace ρ A ≤ fixedSpace ρ B) :
    A < subspaceKernel ρ (fixedSpace ρ A) ⊤ := by
  have hB : B ≤ subspaceKernel ρ (fixedSpace ρ A) ⊤ := by
    intro b hb
    exact ⟨Subgroup.mem_top _, fun v hv => hfix hv ⟨b, hb⟩⟩
  exact hAB.trans_le hB

omit [FiniteDimensional (ZMod 2) V] in
/-- A representation nontrivial on a subgroup contained in every
nontrivial normal subgroup is faithful. Normality is in the acting group. -/
theorem faithful_of_nontrivial_on_monolith
    (K : Subgroup G)
    (hK : ∀ N : Subgroup G, N.Normal → N ≠ ⊥ → K ≤ N)
    (hnontrivial : ∃ k ∈ K, ∃ v : V, ρ k v ≠ v) : Function.Injective ρ := by
  have hk : ρ.asGroupHom.ker = ⊥ := by
    by_contra hn
    obtain ⟨k, hk, v, hv⟩ := hnontrivial
    have he : ρ.asGroupHom k = 1 := hK _ inferInstance hn hk
    have he' : ρ k = 1 := congrArg Units.val he
    exact hv (congrArg (fun f : Module.End (ZMod 2) V => f v) he')
  intro x y hxy
  apply (ρ.asGroupHom.ker_eq_bot_iff.mp hk)
  exact Units.ext hxy

/-- The line-valued displacement argument of 13.8.23(3)–(4), conditional
on the faithful sections and the larger critical actor. The pointwise
centralizers are the actual subspace kernels in the original acting group. -/
theorem faithful_sections_centralizer_sieve
    (W : Subrepresentation ρ) (S : Submodule (ZMod 2) V) (hS : IsAtom S)
    (hW : Function.Injective W.toRepresentation)
    (hQ : Function.Injective W.quotientRepresentation) {A B : Subgroup G}
    (hA : A ≠ ⊥) (hAB : A < B) (hsmall : fixedCodim ρ A ≤ 2)
    (hcomm : ∀ b ∈ B, ∀ c ∈ fixedSpace ρ A, ρ b c - c ∈ S) :
    (S ≤ W.toSubmodule ∧
      fixedSpace W.quotientRepresentation A ≤ fixedSpace W.quotientRepresentation B ∧
      A < subspaceKernel W.quotientRepresentation
        (fixedSpace W.quotientRepresentation A) ⊤) ∨
    (¬ S ≤ W.toSubmodule ∧
      fixedSpace W.toRepresentation A ≤ fixedSpace W.toRepresentation B ∧
      A < subspaceKernel W.toRepresentation (fixedSpace W.toRepresentation A) ⊤) := by
  obtain ⟨hw, hq, hu⟩ := faithful_sections_of_fixedCodim_le_two ρ W hW hQ hA hsmall
  by_cases hSW : S ≤ W.toSubmodule
  · have hmap := fixedSpace_quotient_eq_map_of_fixedCodim_eq ρ W A (by omega)
    have hfix : fixedSpace W.quotientRepresentation A ≤
        fixedSpace W.quotientRepresentation B := by
      rw [← hmap]
      rintro _ ⟨c, hc, rfl⟩ b
      exact (Submodule.Quotient.eq W.toSubmodule).mpr (hSW (hcomm b b.property c hc))
    exact Or.inl ⟨hSW, hfix, lt_pointwiseKernel_fixedSpace _ hAB hfix⟩
  · have hdisjoint : S ⊓ W.toSubmodule = ⊥ :=
      disjoint_iff.mp (hS.not_le_iff_disjoint.mp hSW)
    have hfix : fixedSpace W.toRepresentation A ≤ fixedSpace W.toRepresentation B := by
      intro c hc b
      have hc' : (c : V) ∈ fixedSpace ρ A :=
        fun a => congrArg Subtype.val (hc a)
      have hmem : ρ b c - c ∈ S ⊓ W.toSubmodule :=
        ⟨hcomm b b.property c hc',
          W.toSubmodule.sub_mem (W.apply_mem_toSubmodule b c.property) c.property⟩
      rw [hdisjoint] at hmem
      apply Subtype.ext
      exact sub_eq_zero.mp hmem
    exact Or.inr ⟨hSW, hfix, lt_pointwiseKernel_fixedSpace _ hAB hfix⟩

/-- A nonzero commutator subspace contained in a space of dimension at
most one equals that space. -/
theorem subspaceCommutator_eq_of_le_one_dimensional
    (W S : Submodule (ZMod 2) V) (A : Subgroup G)
    (hnontrivial : ¬ W ≤ fixedSpace ρ A)
    (hle : subspaceCommutator ρ W A ≤ S) (hdim : Module.finrank (ZMod 2) S ≤ 1) :
    subspaceCommutator ρ W A = S := by
  have hne : subspaceCommutator ρ W A ≠ ⊥ :=
    fun h => hnontrivial ((subspaceCommutator_eq_bot_iff ρ W A).mp h)
  have hpos := Submodule.finrank_lt_finrank_of_lt (bot_lt_iff_ne_bot.mpr hne)
  simp only [finrank_bot] at hpos
  exact Submodule.eq_of_le_of_finrank_le hle (by omega)

end Representation.BinaryOffender
