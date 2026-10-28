module

public import Theory.GroupTheory.FrattiniNormalizerWitness
public import Theory.GroupTheory.SubgroupEnumeration
public import Theory.Frattini.PGroup
/-!
# Frattini normalizer certificates on generators

In a finite group, if every displacement of a generating family belongs to the
embedded Frattini subgroup, conjugation maps the subgroup into itself and hence
normalizes it. The induced quotient action fixes the generators, so it is the
identity. An outside conjugating element is therefore a Frattini witness.

For two-groups, products of squares of generator words provide explicit
certificates for these displacements. This is the binary specialization of
Burnside's Frattini generation theorem, via `Theory.Frattini.PGroup`.
-/

namespace Subgroup
variable {G : Type*} [Group G] [Finite G] {ι : Type*}

/-- Generator displacements suffice to certify an outside Frattini witness. -/
public theorem hasFrattiniNormalizerWitness_of_generator_displacements (U : Subgroup G) (s : ι → G)
    (hs : U = closure (Set.range s)) (g : G) (hout : g ∉ U)
    (hd : ∀ i, (s i)⁻¹ * (g * s i * g⁻¹) ∈ (frattini U).map U.subtype) :
    U.HasFrattiniNormalizerWitness := by
  have hmem (i : ι) : s i ∈ U := hs ▸ subset_closure (Set.mem_range_self i)
  have hF : (frattini U).map U.subtype ≤ U := by
    rintro x ⟨y, _, rfl⟩
    exact y.property
  have hc : U.map (MulAut.conj g).toMonoidHom ≤ U := by
    apply map_le_iff_le_comap.mpr
    conv_lhs => rw [hs]
    apply (closure_le _).mpr
    rintro _ ⟨i, rfl⟩
    change g * s i * g⁻¹ ∈ U
    simpa only [mul_inv_cancel_left] using U.mul_mem (hmem i) (hF (hd i))
  have hn : g ∈ normalizer (U : Set G) := by
    apply mem_normalizer_iff_map_conj_eq.mpr
    exact eq_of_le_of_card_ge hc
      (Nat.card_congr (U.equivMapOfInjective (MulAut.conj g).toMonoidHom
        (MulAut.conj g).injective).toEquiv).le
  refine ⟨⟨g, hn⟩, hout, ?_⟩
  let a := U.normalizerMonoidHom ⟨g, hn⟩
  let q := QuotientGroup.mk' (frattini U)
  let L := (q.comp a.toMonoidHom).eqLocus q
  have hle : U ≤ L.map U.subtype := by
    conv_lhs => rw [hs]
    apply (closure_le _).mpr
    rintro _ ⟨i, rfl⟩
    refine ⟨⟨s i, hmem i⟩, ?_, rfl⟩
    change q (a ⟨s i, hmem i⟩) = q ⟨s i, hmem i⟩
    apply Eq.symm
    apply QuotientGroup.eq.mpr
    obtain ⟨z, hz, he⟩ := hd i
    have he' : z = (⟨s i, hmem i⟩ : U)⁻¹ * a ⟨s i, hmem i⟩ := Subtype.ext he
    exact he' ▸ hz
  apply MulEquiv.ext
  intro x
  induction x using QuotientGroup.induction_on with
  | H x =>
    change quotientAut (frattini U) a (q x) = q x
    rw [quotientAut_apply_mk]
    obtain ⟨y, hy, he⟩ := hle x.property
    exact (show y = x from Subtype.ext he) ▸ hy

open Theory.GroupTheory Theory.GroupTheory.SubgroupEnumeration in
/-- Products of squares of generator words certify the binary Frattini action. -/
public theorem hasFrattiniNormalizerWitness_of_square_word_displacements {n : ℕ} (U : Subgroup G)
    (hU : IsPGroup 2 U) (s : Fin n → G) (hs : U = closure (Set.range s))
    (g : G) (hout : g ∉ U) (words : Fin n → List (List (Fin n)))
    (hd : ∀ i, (s i)⁻¹ * (g * s i * g⁻¹) =
      ((words i).map (fun w => evalWord s w ^ 2)).prod) :
    U.HasFrattiniNormalizerWitness := by
  let : Fact (IsPGroup 2 U) := ⟨hU⟩
  apply hasFrattiniNormalizerWitness_of_generator_displacements U s hs g hout
  intro i
  rw [hd i]
  apply list_prod_mem
  intro x hx
  obtain ⟨w, _, rfl⟩ := List.mem_map.mp hx
  have hw : evalWord s w ∈ U :=
    evalWord_mem s U (fun j => hs ▸ subset_closure (Set.mem_range_self j)) w
  exact mem_map_of_mem U.subtype
    (pth_power_mem_frattini_of_isPGroup (p := 2) (⟨evalWord s w, hw⟩ : U))
end Subgroup
