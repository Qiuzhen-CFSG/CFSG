module

public import Theory.GroupTheory.NoncentralChiefRefinement
public import Theory.Representation.SubspaceQuotient
public import Mathlib.RepresentationTheory.Equiv

/-!+# Counting noncentral sections of binary representation flags

The terms are literal invariant subspaces, and adjacent terms cover in their
lattice. Centrality is the displacement condition for the actual quotient.
The diamond identity preserves this condition, so Jordan–Hölder makes its
count independent of the chief flag. Equivariant linear isomorphisms transport
both chiefness and centrality. This is the representation counterpart of the
ambient-normal accounting in `NoncentralChiefRefinement`.

Source application: Aschbacher–Smith 14.7.22(2) and 14.7.72, using H.6.3(3).
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false

open Representation
namespace BinaryLinearThree.ParabolicCyclic.ChiefCounts

variable {G M N : Type*} [Group G]
  [AddCommGroup M] [Module (ZMod 2) M]
  [AddCommGroup N] [Module (ZMod 2) N]
  {ρ : Representation (ZMod 2) G M} {σ : Representation (ZMod 2) G N}

instance subrepresentation_modular : IsModularLattice (Subrepresentation ρ) where
  sup_inf_le_assoc_of_le := by
    intro U V W h
    let e := Subrepresentation.subrepresentationSubmoduleOrderIso (ρ := ρ)
    apply e.le_iff_le.mp
    simp only [OrderIso.map_inf, OrderIso.map_sup]
    exact sup_inf_le_assoc_of_le _ (e.monotone h)

/-- A section is central exactly when every actor displacement lies in its
lower term. The endpoints are invariant subspaces of the same actual action. -/
def Central (U V : Subrepresentation ρ) : Prop :=
  ∀ g v, v ∈ V → ρ g v - v ∈ U

/-- The lower endpoint as an invariant subspace of the upper endpoint. -/
def sectionKernel (U V : Subrepresentation ρ) : Subrepresentation V.toRepresentation where
  toSubmodule := U.toSubmodule.comap V.toSubmodule.subtype
  apply_mem_toSubmodule g _ hv := U.apply_mem_toSubmodule g hv

/-- The literal quotient action on V/(U ∩ V). For a flag U ≤ V. -/
abbrev sectionRepresentation (U V : Subrepresentation ρ) :=
  (sectionKernel U V).quotientRepresentation

theorem central_iff_quotient_action (U V : Subrepresentation ρ) :
    Central U V ↔ ∀ g x, sectionRepresentation U V g x = x := by
  constructor
  · intro h g x
    induction x using Submodule.Quotient.induction_on with
    | _ v =>
      change (sectionKernel U V).toSubmodule.mkQ (V.toRepresentation g v) =
        (sectionKernel U V).toSubmodule.mkQ v
      rw [← sub_eq_zero, ← map_sub, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
      exact h g v v.property
  · intro h g v hv
    have he := h g ((sectionKernel U V).toSubmodule.mkQ ⟨v, hv⟩)
    change (sectionKernel U V).toSubmodule.mkQ (V.toRepresentation g ⟨v, hv⟩) =
      (sectionKernel U V).toSubmodule.mkQ ⟨v, hv⟩ at he
    rw [← sub_eq_zero, ← map_sub, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at he
    exact he

/-- A series has actual chief sections. Its endpoints are specified separately. -/
abbrev Series (ρ : Representation (ZMod 2) G M) := CompositionSeries (Subrepresentation ρ)

/-- Count the actual noncentral intervals, without dimension or order tags. -/
noncomputable def Series.count (s : Series ρ) : ℕ :=
  Nat.card {i : Fin s.length // ¬ Central (s i.castSucc) (s i.succ)}

/-- There is a complete chief flag with the stated number of noncentral sections. -/
def HasCount (ρ : Representation (ZMod 2) G M) (n : ℕ) : Prop :=
  ∃ s : Series ρ, s.head = ⊥ ∧ s.last = ⊤ ∧ s.count = n

private theorem central_diamond (U V : Subrepresentation ρ) :
    Central U (U ⊔ V) ↔ Central (U ⊓ V) V := by
  constructor
  · intro h g v hv
    exact ⟨h g v ((show V ≤ U ⊔ V from le_sup_right) hv),
      V.toSubmodule.sub_mem (V.apply_mem_toSubmodule g hv) hv⟩
  · intro h g v hv
    obtain ⟨u, hu, w, hw, rfl⟩ := Submodule.mem_sup.mp hv
    have hu' := U.toSubmodule.sub_mem (U.apply_mem_toSubmodule g hu) hu
    have hw' := (h g w hw).1
    rw [map_add, add_sub_add_comm]
    exact U.toSubmodule.add_mem hu' hw'

theorem central_iff_of_iso {U V U' V' : Subrepresentation ρ}
    (h : JordanHolderLattice.Iso (U, V) (U', V')) : Central U V ↔ Central U' V' := by
  exact h.rel (fun x y => Central x.1 x.2 ↔ Central y.1 y.2)
    Iff.rfl Iff.symm Iff.trans (fun _ => central_diamond _ _)

/-- The noncentral count agrees for all chief series with the same endpoints. -/
theorem Series.count_eq (s t : Series ρ) (h0 : s.head = t.head) (h1 : s.last = t.last) :
    s.count = t.count := by
  obtain ⟨e, he⟩ := CompositionSeries.jordan_holder s t h0 h1
  exact Nat.card_congr (e.subtypeEquiv fun i => not_congr (central_iff_of_iso (he i)))

theorem HasCount.unique {a b : ℕ} (ha : HasCount ρ a) (hb : HasCount ρ b) : a = b := by
  obtain ⟨s, hs0, hs1, hs⟩ := ha
  obtain ⟨t, ht0, ht1, ht⟩ := hb
  exact hs.symm.trans ((s.count_eq t (hs0.trans ht0.symm) (hs1.trans ht1.symm)).trans ht)

/-- A supplied complete chief refinement has the same count. -/
theorem HasCount.count_eq {n : ℕ} (h : HasCount ρ n) (s : Series ρ)
    (h0 : s.head = ⊥) (h1 : s.last = ⊤) : s.count = n := by
  exact (show HasCount ρ s.count from ⟨s, h0, h1, rfl⟩).unique h

/-- Equivariant linear transport on the literal invariant subspaces. -/
noncomputable def equivOrderIso (e : ρ.Equiv σ) :
    Subrepresentation ρ ≃o Subrepresentation σ where
  toFun U := {
    toSubmodule := U.toSubmodule.map e.toLinearEquiv.toLinearMap
    apply_mem_toSubmodule g v hv := by
      obtain ⟨w, hw, rfl⟩ := hv
      exact ⟨ρ g w, U.apply_mem_toSubmodule g hw,
        IntertwiningMap.isIntertwining _ _ e.toIntertwiningMap g w⟩ }
  invFun V := {
    toSubmodule := V.toSubmodule.comap e.toLinearEquiv.toLinearMap
    apply_mem_toSubmodule g v hv := by
      change e (ρ g v) ∈ V
      change e.toIntertwiningMap (ρ g v) ∈ V
      rw [IntertwiningMap.isIntertwining _ _ e.toIntertwiningMap]
      exact V.apply_mem_toSubmodule g hv }
  left_inv U := Subrepresentation.toSubmodule_injective
    (Submodule.comap_map_eq_of_injective e.toLinearEquiv.injective U.toSubmodule)
  right_inv V := Subrepresentation.toSubmodule_injective
    (Submodule.map_comap_eq_of_surjective e.toLinearEquiv.surjective V.toSubmodule)
  map_rel_iff' := by
    intro U V
    exact Submodule.map_le_map_iff_of_injective e.toLinearEquiv.injective _ _

theorem central_equiv (e : ρ.Equiv σ) (U V : Subrepresentation ρ) :
    Central (equivOrderIso e U) (equivOrderIso e V) ↔ Central U V := by
  have he g v : e.toLinearEquiv (ρ g v - v) = σ g (e v) - e v := by
    rw [map_sub]
    exact congrArg (fun w => w - e v)
      (IntertwiningMap.isIntertwining _ _ e.toIntertwiningMap g v)
  constructor
  · intro h g v hv
    obtain ⟨w, hw, hwv⟩ := h g (e v) ⟨v, hv, rfl⟩
    have hwv' : e.toLinearEquiv w = e.toLinearEquiv (ρ g v - v) := hwv.trans (he g v).symm
    exact e.toLinearEquiv.injective hwv' ▸ hw
  · intro h g v hv
    obtain ⟨w, hw, rfl⟩ := hv
    exact ⟨ρ g w - w, h g w hw, he g w⟩

noncomputable def Series.mapEquiv (s : Series ρ) (e : ρ.Equiv σ) : Series σ :=
  ⟨s.length, fun i => equivOrderIso e (s i),
    fun i => (apply_covBy_apply_iff (equivOrderIso e)).mpr (s.step i)⟩

theorem Series.count_mapEquiv (s : Series ρ) (e : ρ.Equiv σ) :
    (s.mapEquiv e).count = s.count := by
  apply Nat.card_congr
  exact Equiv.subtypeEquivRight fun i => not_congr (central_equiv e _ _)

theorem HasCount.mapEquiv {n : ℕ} (h : HasCount ρ n) (e : ρ.Equiv σ) : HasCount σ n := by
  obtain ⟨s, h0, h1, hn⟩ := h
  refine ⟨s.mapEquiv e, ?_, ?_, (s.count_mapEquiv e).trans hn⟩
  · change equivOrderIso e s.head = ⊥
    rw [h0, OrderIso.map_bot]
  · change equivOrderIso e s.last = ⊤
    rw [h1, OrderIso.map_top]

open scoped MonoidAlgebra in
/-- Covers give simple modules for the actual group-algebra action. -/
theorem chiefFactor_simple (U V : Subrepresentation ρ) (h : U ⋖ V) :
    IsSimpleModule (ZMod 2)[G]
      (V.asSubmodule ⧸ Submodule.comap V.asSubmodule.subtype U.asSubmodule) := by
  have hc : U.asSubmodule ⋖ V.asSubmodule :=
    (apply_covBy_apply_iff Subrepresentation.subrepresentationSubmoduleOrderIso).mpr h
  exact (covBy_iff_quot_is_simple hc.le).mp hc

/-- An explicit list of noncentral sections computes the actual count. -/
theorem Series.count_eq_card (s : Series ρ) (I : Finset (Fin s.length))
    (hI : ∀ i, i ∈ I ↔ ¬ Central (s i.castSucc) (s i.succ)) : s.count = I.card := by
  classical
  change Nat.card {i : Fin s.length // ¬ Central (s i.castSucc) (s i.succ)} = _
  rw [Nat.card_congr (Equiv.subtypeEquivRight fun i => (hI i).symm)]
  exact Nat.card_eq_fintype_card.trans (Fintype.card_coe I)

/-- Literal quotient coordinates compare module centrality with the existing
ambient-normal convention. No claim about dimensions replaces the action. -/
theorem central_iff_of_sectionCoordinates
    {U V : NoncentralChiefRefinement.NormalNode G}
    (c : NoncentralChiefRefinement.SectionCoordinates U V ρ 1) :
    NoncentralChiefRefinement.IsCentral U V ↔ ∀ g v, ρ g v = v := by
  rw [NoncentralChiefRefinement.isCentral_iff_action]
  constructor
  · intro h g v
    obtain ⟨x, hx⟩ := c.equiv.surjective (Multiplicative.ofAdd (fun _ : Fin 1 => v))
    have he := c.equivariant g x 0
    rw [h, hx] at he
    exact he.symm
  · intro h g x
    apply c.equiv.injective
    apply Multiplicative.toAdd.injective
    funext i
    exact (c.equivariant g x i).trans (h g _)

/-- Actual action-preserving matching compares a source normal chief
refinement with a module flag. Binary structure follows from the coordinates. -/
theorem Series.count_eq_normal_matching (s : Series ρ)
    (t : NoncentralChiefRefinement.ChiefSeries G)
    (e : Fin s.length ≃ Fin t.length)
    (c : ∀ i, NoncentralChiefRefinement.SectionCoordinates
      (t (e i).castSucc) (t (e i).succ)
      (sectionRepresentation (s i.castSucc) (s i.succ)) 1) :
    s.count = t.noncentralTwoCount := by
  apply Nat.card_congr
  apply e.subtypeEquiv
  intro i
  have hc : NoncentralChiefRefinement.IsCentral
      (t (e i).castSucc) (t (e i).succ) ↔ Central (s i.castSucc) (s i.succ) :=
    (central_iff_of_sectionCoordinates (c i)).trans
      (central_iff_quotient_action _ _).symm
  exact (not_congr hc.symm).trans (and_iff_right (c i).isPGroup).symm

/-- Concatenating adjacent chief flags adds their noncentral counts. -/
theorem Series.count_smash (s t : Series ρ) (h : s.last = t.head) :
    Series.count (s.smash t h) = s.count + t.count := by
  classical
  let P := fun i : Fin (s.length + t.length) =>
    ¬ Central ((s.smash t h) i.castSucc) ((s.smash t h) i.succ)
  let e := Equiv.subtypeEquivOfSubtype (p := P)
    (finSumFinEquiv : Fin s.length ⊕ Fin t.length ≃ Fin (s.length + t.length))
  change Nat.card {i // P i} = _
  rw [← Nat.card_congr e, Nat.card_congr Equiv.subtypeSum, Nat.card_sum]
  congr 1
  · apply Nat.card_congr
    exact Equiv.subtypeEquivRight fun i => by
      simp only [P, finSumFinEquiv_apply_left, RelSeries.smash_castAdd,
        RelSeries.smash_succ_castAdd]
  · apply Nat.card_congr
    exact Equiv.subtypeEquivRight fun i => by
      simp only [P, finSumFinEquiv_apply_right, RelSeries.smash_natAdd,
        RelSeries.smash_succ_natAdd]

end BinaryLinearThree.ParabolicCyclic.ChiefCounts
