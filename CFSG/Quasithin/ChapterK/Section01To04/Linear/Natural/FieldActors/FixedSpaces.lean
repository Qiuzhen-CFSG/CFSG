module

public import CFSG.Quasithin.ChapterK.Section01To04.Linear.Natural.FieldActors.Coefficients
public import Theory.Representation.SL2NaturalOffenders.FieldAction.Basic

/-!
# Common fixed spaces of noncyclic outer elementary actors

An elementary group of rank greater than one has a nonidentity element in
its linear kernel, since finite-field automorphisms form a cyclic group.
Faithfulness makes the field-span of its common fixed space proper. A scalar
moved by an outer involution separates that fixed space from its scalar
multiple; both lie in a field-space of dimension at most two. Counting gives
binary fixed dimension at most 2s, hence displacement at least 4s.

Source: Aschbacher–Smith, K.3.2.1, printed p.455 (1 March 2004).
-/

public section

open Representation Representation.BinaryOffender
open CFSG.Quasithin.ChapterB.QuasisimpleSource
namespace CFSG.Quasithin.ChapterK.Linear.Natural.FieldActors
variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V) (L : Subgroup G) (F : BinaryField)
  (e : ActionEquiv (ρ.comp L.subtype) (linearNatural F 3))

lemma elementary_square_one {A : Subgroup G} (hA : IsElementaryAbelian 2 A) (a : A) :
    (a : G) ^ 2 = 1 := by
  have ha := (Monoid.exponent_dvd_iff_forall_pow_eq_one.mp hA.exponent_dvd_p) a
  exact congrArg Subtype.val ha

/-- A rank-greater-than-one elementary actor has a nonidentity linear element. -/
theorem exists_nontrivial_linear_element [Finite G]
    (hs : IsSemilinearExtension ρ L F 3 e) {A : Subgroup G}
    (hA : IsElementaryTwo A) (hr : 1 < rank A) :
    ∃ b : A, (b : G) ≠ 1 ∧ coefficientAction ρ L F e hs b = 1 := by
  let φ := (coefficientAction ρ L F e hs).comp A.subtype
  let : Finite φ.range := Finite.of_surjective φ.rangeRestrict φ.rangeRestrict_surjective
  have hcard := SL2NaturalOffenders.fieldAction_range_card_le_two A hA.2 φ
  have hn : φ.ker ≠ ⊥ := by
    intro he
    have hi := (φ.ker_eq_bot_iff).mp he
    have hrange : Function.Injective φ.rangeRestrict := by
      intro x y h
      exact hi (congrArg Subtype.val h)
    have hle := (Nat.card_le_card_of_injective _ hrange).trans hcard
    rw [hA.card_eq_two_pow_rank] at hle
    have hlt : 2 ^ 1 < 2 ^ rank A := (Nat.pow_lt_pow_iff_right (by decide)).mpr hr
    norm_num at hlt
    omega
  obtain ⟨b, hb⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hn
  exact ⟨b.val, fun he => hb (Subtype.ext (Subtype.ext he)), b.property⟩

private theorem fixed_span_finrank_le_two
    (τ : Representation (ZMod 2) G (Fin 3 → F.Carrier)) (hf : Function.Injective τ)
    (A : Subgroup G) (b : A) (hb : (b : G) ≠ 1)
    (hl : ∀ (c : F.Carrier) (v : Fin 3 → F.Carrier), τ b (c • v) = c • τ b v) :
    Module.finrank F.Carrier (Submodule.span F.Carrier (fixedSpace τ A : Set (Fin 3 → F.Carrier))) ≤ 2 := by
  let W := Submodule.span F.Carrier (fixedSpace τ A : Set (Fin 3 → F.Carrier))
  have hfix (v : Fin 3 → F.Carrier) (hv : v ∈ W) : τ b v = v := by
    induction hv using Submodule.span_induction with
    | mem v hv => exact hv b
    | zero => exact map_zero _
    | add v w _ _ hv hw => rw [map_add, hv, hw]
    | smul c v _ hv => rw [hl, hv]
  have hn : W ≠ ⊤ := by
    intro he
    apply hb
    apply hf
    apply LinearMap.ext
    intro v
    simpa only [map_one, Module.End.one_apply] using hfix v (he ▸ Submodule.mem_top)
  have hd := Submodule.finrank_lt hn
  rw [Module.finrank_pi, Fintype.card_fin] at hd
  exact Nat.le_of_lt_succ hd

private theorem double_fixedSpace_card_le_span_card
    (τ : Representation (ZMod 2) G (Fin 3 → F.Carrier))
    (A : Subgroup G) (a : A) (σ : F.Carrier ≃+* F.Carrier) (hne : σ ≠ 1)
    (hσ : ∀ (c : F.Carrier) (v : Fin 3 → F.Carrier), τ a (c • v) = σ c • τ a v) :
    Nat.card (fixedSpace τ A) ^ 2 ≤
      Nat.card (Submodule.span F.Carrier (fixedSpace τ A : Set (Fin 3 → F.Carrier))) := by
  obtain ⟨c, hc⟩ : ∃ c, σ c ≠ c := by
    by_contra! h
    exact hne (RingEquiv.ext h)
  let W := Submodule.span F.Carrier (fixedSpace τ A : Set (Fin 3 → F.Carrier))
  have hfixed (v : fixedSpace τ A) : τ (a : G) v.val = v.val := v.property a
  let f : fixedSpace τ A × fixedSpace τ A → W := fun x =>
    ⟨x.1.val + c • x.2.val, W.add_mem (Submodule.subset_span x.1.property)
      (W.smul_mem c (Submodule.subset_span x.2.property))⟩
  have hf : Function.Injective f := by
    intro x y he
    have he : x.1.val + c • x.2.val = y.1.val + c • y.2.val := congrArg Subtype.val he
    have he' := congrArg (τ (a : G)) he
    simp only [map_add, hσ, hfixed] at he'
    have hz : (σ c - c) • (x.2.val - y.2.val) = 0 := by
      calc
        _ = ((x.1.val + σ c • x.2.val) - (y.1.val + σ c • y.2.val)) -
            ((x.1.val + c • x.2.val) - (y.1.val + c • y.2.val)) := by
          simp only [sub_smul, smul_sub]
          abel
        _ = 0 := by rw [he, he']; simp
    have h2 : x.2.val = y.2.val :=
      sub_eq_zero.mp ((smul_eq_zero.mp hz).resolve_left (sub_ne_zero.mpr hc))
    have h1 : x.1.val = y.1.val := by rw [h2] at he; exact add_right_cancel he
    exact Prod.ext (Subtype.ext h1) (Subtype.ext h2)
  have hb := Nat.card_le_card_of_injective f hf
  simpa only [Nat.card_prod, pow_two] using hb

/-- The common fixed space of a noncyclic elementary actor containing an outer
involution has binary dimension at most 2s. -/
theorem outer_elementary_fixedSpace_finrank [Finite G]
    (hf : Function.Injective ρ) (hs : IsSemilinearExtension ρ L F 3 e)
    {A : Subgroup G} (hA : IsElementaryTwo A) (hr : 1 < rank A)
    (a : A) (haL : (a : G) ∉ L) (s : ℕ) (hdegree : F.degree = 2 * s) :
    Module.finrank (ZMod 2) (fixedSpace ρ A) ≤ 2 * s := by
  let τ := coordinateAction ρ L F e
  obtain ⟨b, hb, hbφ⟩ := exists_nontrivial_linear_element ρ L F e hs hA hr
  have hdim := fixed_span_finrank_le_two F τ (coordinateAction_faithful ρ L F e hf) A b hb
    ((coefficientAction_eq_one_iff ρ L F e hs b).mp hbφ)
  have hcount := double_fixedSpace_card_le_span_card F τ A a (coefficientAction ρ L F e hs a)
    (outer_coefficient_ne_one ρ L F e hf hs a (elementary_square_one hA.2 a) haL)
    (coefficientAction_smul ρ L F e hs a)
  rw [Module.natCard_eq_pow_finrank (K := F.Carrier)
    (V := Submodule.span F.Carrier (fixedSpace τ A : Set (Fin 3 → F.Carrier)))] at hcount
  have hcount' := hcount.trans (Nat.pow_le_pow_right (Nat.card_pos (α := F.Carrier)) hdim)
  rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod,
    F.card_eq, hdegree, ← pow_mul, ← pow_mul] at hcount'
  have hle := (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp hcount'
  have he := fixedSpace_map_equivariant ρ τ (MonoidHom.id G) e.linearEquiv
    (coordinateAction_intertwines ρ L F e) A
  simp only [Subgroup.map_id] at he
  have hd : Module.finrank (ZMod 2) (fixedSpace ρ A) =
      Module.finrank (ZMod 2) (fixedSpace τ A) := by
    rw [← he, e.linearEquiv.finrank_map_eq]
  rw [hd]
  omega

/-- The equivalent displacement bound on the original module and its actual
quotient by the common fixed space. -/
theorem outer_elementary_fixedCodim [Finite G] [FiniteDimensional (ZMod 2) V]
    (hf : Function.Injective ρ) (hs : IsSemilinearExtension ρ L F 3 e)
    {A : Subgroup G} (hA : IsElementaryTwo A) (hr : 1 < rank A)
    (a : A) (haL : (a : G) ∉ L) (s : ℕ) (hdegree : F.degree = 2 * s) :
    4 * s ≤ fixedCodim ρ A := by
  have hfix := outer_elementary_fixedSpace_finrank ρ L F e hf hs hA hr a haL s hdegree
  have hadd := fixedCodim_add_finrank ρ A
  have hdim := e.linearEquiv.finrank_eq
  simp only [Module.finrank_pi_fintype, field_finrank, hdegree, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hdim
  omega

/-- Application with the literal natural source data. -/
theorem source_outer_elementary_fixedCodim [Finite G] [FiniteDimensional (ZMod 2) V]
    {K : GroupClass} (h : SourceInput ρ L F 3 K)
    {A : Subgroup G} (hA : IsElementaryTwo A) (hr : 1 < rank A)
    (a : A) (haL : (a : G) ∉ L) (s : ℕ) (hdegree : F.degree = 2 * s) :
    4 * s ≤ fixedCodim ρ A :=
  outer_elementary_fixedCodim ρ L F h.natural h.faithful h.semilinear hA hr a haL s hdegree

end CFSG.Quasithin.ChapterK.Linear.Natural.FieldActors
