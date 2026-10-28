module

public import CFSG.Quasithin.ChapterD.Section02.FittingOffenders.Configurations.Defs
public import CFSG.Quasithin.ChapterD.Section02.FittingOffenders.Configurations.LinearBudget
public import CFSG.Quasithin.ChapterD.Section02.FittingOffenders.Configurations.FourDimensionalMarking.Core
public import CFSG.Quasithin.ChapterD.Section02.SmallSupportDecomposition
public import Theory.Representation.BinaryOffender.MovedSpaceTransport

/-!
# Transitivity of the original actor on the two support factors

Every given factor belongs to the canonical order-three plane-support family
of D.2.12. Any further canonical factor would fix all the given supports,
hence the whole module, contradicting faithfulness. Ambient conjugation
therefore permutes precisely the supplied factors.

The four-dimensional module forces two factors. If the original actor did
not exchange them, it would preserve both support planes. A two-group acting
on a binary plane has a nonzero fixed vector. The literal direct sum would
then give at least two fixed dimensions, contradicting fixed codimension
three from the starred-offender budget.

This proves the transitivity clause of Aschbacher--Smith D.2.14(7)(i),
printed p.187, conditional only on the supplied support decomposition and
the reduced source hypotheses. Construction and diagonal marking of the
decomposition belong to the separate assembly.
-/

public section

open Representation.BinaryOffender
open CFSG.Quasithin.ChapterD
namespace CFSG.Quasithin.ChapterD.FittingConfigurations
variable {G V : Type*} [Group G] [Finite G]
  [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V)

omit [Finite G] in
private theorem factor_canonical {P A : Subgroup G} {s : ℕ}
    (h : Reduced ρ P A s) (d : SupportFactors ρ P s) (i : Fin s) :
    let := Representation.BinaryGroupAction.action ρ
    d.ambient i ∈ smallSupportFactors G (Multiplicative V) 1 := by
  let := Representation.BinaryGroupAction.action ρ
  let : IsElementaryAbelian 3 P := h.elementary
  let : CommGroup P := IsMulCommutative.instCommGroup
  have hp : P ≤ fittingSubgroup G := le_sSup ⟨h.normal, inferInstance⟩
  refine ⟨?_, ?_, ?_⟩
  · rintro x ⟨p, hp', rfl⟩
    exact hp p.property
  · exact (Subgroup.card_map_of_injective P.subtype_injective).trans (d.card_factor i)
  · rw [Representation.BinaryGroupAction.commutator_card]
    exact congrArg (fun n : ℕ => 2 ^ n) (d.support_dim i)

private theorem canonical_eq_factor {P A : Subgroup G} {s : ℕ}
    (h : Reduced ρ P A s) (d : SupportFactors ρ P s) {X : Subgroup G}
    (hX : letI := Representation.BinaryGroupAction.action ρ
      X ∈ smallSupportFactors G (Multiplicative V) 1) :
    ∃ i, X = d.ambient i := by
  classical
  let := Representation.BinaryGroupAction.action ρ
  let := Representation.BinaryGroupAction.elementary (V := V)
  let := Representation.BinaryGroupAction.faithful ρ h.faithful
  let : Finite V := Module.finite_of_finite (ZMod 2)
  by_contra hn
  have hne (i : Fin s) : X ≠ d.ambient i := fun he => hn ⟨i, he⟩
  have hfix (i : Fin s) : subspaceCommutator ρ ⊤ (d.ambient i) ≤ fixedSpace ρ X := by
    have hh := smallSupportFactors_cross_fixed (V := Multiplicative V) (Or.inl rfl)
      hX (factor_canonical ρ h d i) (hne i)
    rw [Representation.BinaryGroupAction.commutator_eq,
      Representation.BinaryGroupAction.fixedPoints_eq] at hh
    exact (Representation.BinaryGroupAction.submoduleEquivSubgroup (V := V)).le_iff_le.mp hh
  have hx1 (x : X) : (x : G) = 1 := by
    apply h.faithful
    ext v
    obtain ⟨w, hw⟩ := d.add_bijective.2 v
    simp only [map_one, Module.End.one_apply]
    rw [← hw, map_sum]
    exact Finset.sum_congr rfl (fun i _ => hfix i (w i).property x)
  have he : X = ⊥ := by
    apply bot_unique
    intro x hx
    exact hx1 ⟨x, hx⟩
  have hc := hX.2.1
  rw [he, Subgroup.card_bot] at hc
  norm_num at hc

private theorem factor_conj_closed {P A : Subgroup G} {s : ℕ}
    (h : Reduced ρ P A s) (d : SupportFactors ρ P s) (i : Fin s) (a : G) :
    ∃ j, (d.ambient i).conjBy a = d.ambient j := by
  let := Representation.BinaryGroupAction.action ρ
  exact canonical_eq_factor ρ h d (smallSupportFactors_conjBy (factor_canonical ρ h d i) a)

omit [Finite G] in
private theorem fixed_vector {A : Subgroup G} (hA : IsPGroup 2 A)
    (U : Submodule (ZMod 2) V) (hd : Module.finrank (ZMod 2) U = 2)
    (hU : A ≤ subspaceStabilizer ρ U) :
    ∃ v : V, v ∈ U ⊓ fixedSpace ρ A ∧ v ≠ 0 := by
  let σ := (stabilizerRepresentation ρ U).comp (Subgroup.inclusion hU)
  let := Representation.BinaryGroupAction.action σ
  let : Finite U := Module.finite_of_finite (ZMod 2)
  have hc : 2 ∣ Nat.card (Multiplicative U) := by
    change 2 ∣ Nat.card U
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod, hd]
    decide
  obtain ⟨v, hv, hn⟩ := hA.exists_fixed_point_of_prime_dvd_card_of_fixed_point
    (Multiplicative U) hc (a := 1) (by intro a; exact smul_one a)
  refine ⟨v.toAdd.val, ⟨v.toAdd.property, ?_⟩, ?_⟩
  · intro a
    exact congrArg (fun w : Multiplicative U => w.toAdd.val) (hv a)
  · intro he
    apply hn
    exact congrArg Multiplicative.ofAdd (Subtype.ext he.symm)

omit [Finite G] [FiniteDimensional (ZMod 2) V] in
private theorem support_disjoint {P : Subgroup G} (d : SupportFactors ρ P 2) :
    Disjoint (subspaceCommutator ρ ⊤ (d.ambient 0))
      (subspaceCommutator ρ ⊤ (d.ambient 1)) := by
  classical
  apply Submodule.disjoint_def.mpr
  intro v hv hw
  let f : (i : Fin 2) → subspaceCommutator ρ ⊤ (d.ambient i) := Pi.single 0 ⟨v, hv⟩
  let g : (i : Fin 2) → subspaceCommutator ρ ⊤ (d.ambient i) := Pi.single 1 ⟨v, hw⟩
  have he : (∑ i, (f i : V)) = ∑ i, (g i : V) := by
    simp [f, g, Fin.sum_univ_two]
  have hh := congrArg (fun x => ((x 0 : subspaceCommutator ρ ⊤ (d.ambient 0)) : V))
    (d.add_bijective.1 he)
  simpa [f, g] using hh

private theorem not_all_normalized {P A : Subgroup G}
    (h : Reduced ρ P A 2) (hlow : 1 < cubicRatio ρ)
    (hdim : Module.finrank (ZMod 2) V = 4) (d : SupportFactors ρ P 2)
    (hN : ∀ i, A ≤ Subgroup.normalizer (d.ambient i : Set G)) : False := by
  let : IsElementaryAbelian 2 A := h.starred.1.2.1.2
  let U := fun i => subspaceCommutator ρ ⊤ (d.ambient i)
  let W := fun i => U i ⊓ fixedSpace ρ A
  have hpos (i : Fin 2) : 1 ≤ Module.finrank (ZMod 2) (W i) := by
    obtain ⟨v, hv, hn⟩ := fixed_vector ρ (IsElementaryAbelian.isPGroup 2 A) (U i)
      (d.support_dim i) (subspaceCommutator_invariant_normalizer ρ
        (fun _ _ _ => iff_of_true Submodule.mem_top Submodule.mem_top) (hN i))
    apply Submodule.one_le_finrank_iff.mpr
    intro he
    have hv' : v ∈ W i := hv
    rw [he] at hv'
    exact hn hv'
  have hdis : Disjoint (W 0) (W 1) :=
    (support_disjoint ρ d).mono inf_le_left inf_le_left
  have he := Submodule.finrank_sup_add_finrank_inf_eq (W 0) (W 1)
  rw [hdis.eq_bot, finrank_bot] at he
  have hle := Submodule.finrank_mono
    (show W 0 ⊔ W 1 ≤ fixedSpace ρ A from sup_le inf_le_right inf_le_right)
  have hc := (h.small_dimension_ratio ρ hlow (by omega)).1
  have hf := fixedCodim_add_finrank ρ A
  have h0 := hpos 0
  have h1 := hpos 1
  omega

/-- The given actor is transitive by actual ambient conjugation on every
supplied support decomposition in the full four-dimensional branch. -/
theorem Reduced.fullSupport_transitivity {P A : Subgroup G} {s : ℕ}
    (h : Reduced ρ P A s) (hlow : 1 < cubicRatio ρ)
    (hfull : FullSupport ρ P A) (d : SupportFactors ρ P s) : d.IsTransitive A := by
  classical
  obtain ⟨Z, hZ, hmove, hdim⟩ := hfull
  have hs := h.core_rank_eq_two_of_finrank_four ρ hdim
  subst s
  intro i j
  by_cases hij : i = j
  · subst j
    exact ⟨1, (d.ambient i).conjBy_one⟩
  by_contra hn
  have hcases (k : Fin 2) : k = i ∨ k = j := by
    fin_cases i <;> fin_cases j <;> fin_cases k <;> simp_all
  apply not_all_normalized ρ h hlow hdim d
  intro k
  apply subgroup_le_normalizer_of_conj_mem
  intro a x hx
  have he : (d.ambient k).conjBy (a : G) = d.ambient k := by
    obtain ⟨l, hl⟩ := factor_conj_closed ρ h d k (a : G)
    rcases hcases k with hki | hkj
    · rcases hcases l with hli | hlj
      · simpa only [hki, hli] using hl
      · exact (hn ⟨a, by simpa only [hki, hlj, Subgroup.conjBy] using hl⟩).elim
    · rcases hcases l with hli | hlj
      · have hj : (d.ambient j).conjBy (a : G) = d.ambient i := by
          simpa only [hkj, hli] using hl
        have hi : (d.ambient i).conjBy ((a⁻¹ : A) : G) = d.ambient j := by
          rw [← hj]
          exact (d.ambient j).conjBy_inv (a : G)
        exact (hn ⟨a⁻¹, hi⟩).elim
      · simpa only [hkj, hlj] using hl
  rw [← he]
  exact Subgroup.mem_map_of_mem (MulAut.conj (a : G)).toMonoidHom hx

/-- The original local-group application obtains the strict ratio bound from
its noncentralized hyperplane fixed space, using the same actor and factors. -/
theorem local_generated_fullSupport_transitivity
    (P A B : Subgroup G)
    (σ : Representation (ZMod 2) (P ⊔ A : Subgroup G) V) {s : ℕ}
    (h : Reduced σ (P.subgroupOf (P ⊔ A)) (A.subgroupOf (P ⊔ A)) s)
    (hBA : B ≤ A) (hrB : rank (B.subgroupOf (P ⊔ A)) = 1)
    (hn : subspaceCommutator σ (fixedSpace σ (B.subgroupOf (P ⊔ A)))
      (A.subgroupOf (P ⊔ A)) ≠ ⊥)
    (hfull : FullSupport σ (P.subgroupOf (P ⊔ A)) (A.subgroupOf (P ⊔ A)))
    (d : SupportFactors σ (P.subgroupOf (P ⊔ A)) s) :
    d.IsTransitive (A.subgroupOf (P ⊔ A)) := by
  apply h.fullSupport_transitivity σ _ hfull d
  exact h.one_lt_ratio_of_moved_hyperplane σ (fun _ hb => hBA hb) hrB hn

end CFSG.Quasithin.ChapterD.FittingConfigurations
