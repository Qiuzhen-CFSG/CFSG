module
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.Seven.OriginalSource.SmallModules.Spectrum
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.Seven.PairsBranch.ModuleSelection.Basic
public import Theory.Representation.AlternatingSevenSmallQuadratic.Degree
public import Theory.Representation.CubicClifford.IndexTwoRestriction
public import Theory.Representation.CubicClifford.TwoGroupExtension
public import Theory.Representation.AlternatingSevenConjugatePair.Model.OuterDual
/-!
# Compatible small quadratic alternatives for the original A₇ source

A faithful simple binary representation of a marked group between A₇ and S₇
has degree at most twelve under the small-actor bound. A simple constituent
of its restriction is faithful. The complete split catalogue identifies it
with one of the two marked four-spaces or the literal natural core.

The core extends through the same seven-point action; the binary two-group
quotient fixes an intertwiner and identifies the whole module with that
extension. At index two the four-space either is the whole restriction or
has its actual odd conjugate as a complementary summand. The established
outer-duality pairing then gives four plus its actual dual, with unchanged
actor marking. No component irreducibility or recognition conclusion is
assumed. This discharges the SmallQuadraticInput consumed by both partition
branches of 13.8.24; original-source assembly remains with this task.

Source: Aschbacher–Smith, 13.8.24, printed pp.958–959/PDF pp.975–976;
B.4.2 and B.4.5 together with the stated Clifford extension step.
-/

public section
open Representation Representation.BinaryOffender Subgroup
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.Seven.OriginalSource
open PairsBranch.ModuleSelection
open Representation.AlternatingSevenSmallQuadratic
open Representation.AlternatingSevenConjugatePair
noncomputable section

private def pullEquiv {F P Q U W : Type*} [Field F] [Group P] [Group Q]
    [AddCommGroup U] [Module F U] [AddCommGroup W] [Module F W]
    {σ : Representation F P U} {τ : Representation F P W}
    (e : σ.Equiv τ) (f : Q →* P) : Representation.Equiv (σ.comp f) (τ.comp f) :=
  .mk e.toLinearEquiv (fun q => e.isIntertwining' (f q))

private theorem irreducible_of_comp {F P Q U : Type*} [Field F] [Group P] [Group Q]
    [AddCommGroup U] [Module F U] (σ : Representation F P U) (f : Q →* P)
    (h : IsIrreducible (σ.comp f)) : IsIrreducible σ := by
  let : IsIrreducible (σ.comp f) := h
  let : Nontrivial U := Subrepresentation.irreducible_module_nontrivial (σ.comp f)
  refine ⟨fun N => ?_⟩
  let M : Subrepresentation (σ.comp f) := ⟨N.toSubmodule, fun q _ hv => N.apply_mem_toSubmodule (f q) hv⟩
  rcases IsSimpleOrder.eq_bot_or_eq_top M with hm | hm
  · left
    apply Subrepresentation.toSubmodule_injective
    have hh := congrArg (fun S : Subrepresentation (σ.comp f) => S.toSubmodule) hm
    exact hh
  · right
    apply Subrepresentation.toSubmodule_injective
    have hh := congrArg (fun S : Subrepresentation (σ.comp f) => S.toSubmodule) hm
    exact hh

variable {H V : Type*} [Group H] [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V]
  (φ : H →* Equiv.Perm (Fin 7)) (hi : Function.Injective φ)
  (K : Subgroup H) (hK : K.map φ = alternatingGroup (Fin 7))

include φ hi hK in
private theorem component_comap : K = (alternatingGroup (Fin 7)).comap φ := by
  rw [← hK, Subgroup.comap_map_eq_self_of_injective hi]

include φ hi hK in
private theorem component_normal : K.Normal := by
  rw [component_comap φ hi K hK]
  infer_instance

include φ hi hK in
private theorem component_index_dvd : K.index ∣ 2 := by
  rw [component_comap φ hi K hK, Subgroup.index_comap]
  simpa only [alternatingGroup.index_eq_two] using
    (alternatingGroup (Fin 7)).relIndex_dvd_index_of_normal φ.range

include φ hi hK in
private theorem quotient_two [K.Normal] : IsPGroup 2 (H ⧸ K) := by
  have hd := component_index_dvd φ hi K hK
  rcases (Nat.dvd_prime Nat.prime_two).mp hd with h | h
  · exact IsPGroup.of_card (p := 2) (n := 0) (by simpa only [Subgroup.index, pow_zero] using h)
  · exact IsPGroup.of_card (p := 2) (n := 1) (by simpa only [Subgroup.index, pow_one] using h)

private theorem natural_occurrence [K.Normal]
    (ρ : Representation (ZMod 2) H V) [IsIrreducible ρ]
    (A : Subrepresentation (ρ.comp K.subtype))
    (e : Representation.Equiv (A.toRepresentation.comp (componentEquiv φ hi K hK).symm.toMonoidHom)
      (BinaryPermutation.alternatingCoreRepresentation (Fin 7))) :
    IsNatural ρ φ := by
  let τ := (BinaryPermutation.coreRepresentation (Fin 7)).comp φ
  have hτ : τ.comp (componentInclusion φ hi K hK) =
      BinaryPermutation.alternatingCoreRepresentation (Fin 7) := by
    apply MonoidHom.ext
    intro a
    apply LinearMap.ext
    intro v
    change BinaryPermutation.coreRepresentation (Fin 7)
      (φ (componentInclusion φ hi K hK a)) v = _
    rw [componentInclusion_compatible]
    rfl
  let : IsIrreducible τ := irreducible_of_comp τ (componentInclusion φ hi K hK)
    (hτ ▸ Representation.AlternatingSevenBinarySmallModels.core_irreducible)
  let E := componentEquiv φ hi K hK
  let d : A.toRepresentation.Equiv (τ.comp K.subtype) := .mk e.toLinearEquiv (by
    intro k
    have he := e.isIntertwining' (E k)
    change e.toLinearEquiv.toLinearMap ∘ₗ A.toRepresentation (E.symm (E k)) =
      BinaryPermutation.alternatingCoreRepresentation (Fin 7) (E k) ∘ₗ
        e.toLinearEquiv.toLinearMap at he
    rw [E.symm_apply_apply] at he
    have hk : φ k.val = (E k).val := rfl
    change e.toLinearEquiv.toLinearMap ∘ₗ A.toRepresentation k =
      BinaryPermutation.coreRepresentation (Fin 7) (φ k.val) ∘ₗ e.toLinearEquiv.toLinearMap
    rw [hk]
    exact he)
  exact Representation.CubicClifford.equiv_of_extending_constituent K
    (quotient_two φ hi K hK) τ ρ A d

omit [FiniteDimensional (ZMod 2) V] in
private theorem faithful_constituent [K.Normal] [IsSimpleGroup K]
    (ρ : Representation (ZMod 2) H V) [IsIrreducible ρ]
    (hf : Function.Injective ρ)
    (A : Subrepresentation (ρ.comp K.subtype)) (hA : IsIrreducible A.toRepresentation) :
    Function.Injective A.toRepresentation := by
  rcases A.toRepresentation.normal_ker.eq_bot_or_eq_top with hk | hk
  · exact A.toRepresentation.ker_eq_bot_iff.mp hk
  let : IsIrreducible A.toRepresentation := hA
  let : Nontrivial A.toSubmodule := Subrepresentation.irreducible_module_nontrivial A.toRepresentation
  obtain ⟨v, hv⟩ := exists_ne (0 : A.toSubmodule)
  have hn : invariants (ρ.comp K.subtype) ≠ ⊥ := by
    intro hz
    have hvfix : v.val ∈ invariants (ρ.comp K.subtype) := by
      intro k
      have he : A.toRepresentation k = 1 := by
        apply MonoidHom.mem_ker.mp
        rw [hk]
        trivial
      exact congrArg Subtype.val (LinearMap.congr_fun he v)
    rw [hz, Submodule.mem_bot] at hvfix
    exact hv (Subtype.ext hvfix)
  have hker := ρ.le_ker_of_normal_invariants_ne_bot K hn
  obtain ⟨k, hk⟩ := exists_ne (1 : K)
  exact (hk (Subtype.ext (hf ((hker k.property).trans ρ.map_one.symm)))).elim
private def subrepresentationFullEquiv {F Q U : Type*} [Field F] [Group Q]
    [AddCommGroup U] [Module F U] (σ : Representation F Q U)
    (A : Subrepresentation σ) (ha : A = ⊤) : A.toRepresentation.Equiv σ :=
  .mk (LinearEquiv.ofBijective A.toSubmodule.subtype ⟨Subtype.val_injective,
    fun v => ⟨⟨v, by rw [ha]; trivial⟩, rfl⟩⟩) (fun _ => rfl)

private def prodEquiv {F Q U U' W W' : Type*} [Field F] [Group Q]
    [AddCommGroup U] [Module F U] [AddCommGroup U'] [Module F U']
    [AddCommGroup W] [Module F W] [AddCommGroup W'] [Module F W']
    {σ : Representation F Q U} {σ' : Representation F Q U'}
    {τ : Representation F Q W} {τ' : Representation F Q W'}
    (e : σ.Equiv σ') (d : τ.Equiv τ') :
    (σ.prod τ).Equiv (σ'.prod τ') :=
  .mk (e.toLinearEquiv.prodCongr d.toLinearEquiv) (by
    intro q
    apply LinearMap.ext
    intro v
    exact Prod.ext (LinearMap.congr_fun (e.isIntertwining' q) v.1)
      (LinearMap.congr_fun (d.isIntertwining' q) v.2))

include hi hK in
private theorem transposition_lift (hind : K.index = 2) :
    ∃ t : H, φ t = Model.transposition ∧ t ∉ K := by
  have hh := K.index_map φ
  rw [hK, alternatingGroup.index_eq_two, φ.ker_eq_bot hi, sup_bot_eq, hind] at hh
  have hr : φ.range = ⊤ := Subgroup.index_eq_one.mp (by omega)
  obtain ⟨t, ht⟩ := MonoidHom.range_eq_top.mp hr Model.transposition
  refine ⟨t, ht, ?_⟩
  intro hk
  have hh : φ t ∈ alternatingGroup (Fin 7) := by
    rw [← hK]
    exact Subgroup.mem_map_of_mem φ hk
  rw [ht] at hh
  exact (by rw [Equiv.Perm.mem_alternatingGroup]; decide : Model.transposition ∉ alternatingGroup (Fin 7)) hh

private theorem conjugate_mark [K.Normal] (t : H) (ht : φ t = Model.transposition)
    (a : A7) :
    (componentEquiv φ hi K hK)
      ⟨t * ((componentEquiv φ hi K hK).symm a : H) * t⁻¹,
        (inferInstance : K.Normal).conj_mem _ ((componentEquiv φ hi K hK).symm a).property t⟩ =
      Model.outer a := by
  apply Subtype.ext
  change φ (t * ((componentEquiv φ hi K hK).symm a : H) * t⁻¹) = _
  rw [map_mul, map_mul, map_inv, ht]
  have ha := componentInclusion_compatible φ hi K hK a
  change φ ((componentEquiv φ hi K hK).symm a : H) = a.val at ha
  rw [ha]
  change Model.transposition * a.val * Model.transposition⁻¹ =
    Model.transposition * a.val * Model.transposition
  rw [show Model.transposition⁻¹ = Model.transposition by
    simp [Model.transposition]]

private def conjugateMarkedEquiv [K.Normal]
    {U W : Type*} [AddCommGroup U] [Module (ZMod 2) U]
    [AddCommGroup W] [Module (ZMod 2) W]
    (σ : Representation (ZMod 2) K U) (τ : Representation (ZMod 2) A7 W)
    (e : Representation.Equiv (σ.comp (componentEquiv φ hi K hK).symm.toMonoidHom) τ)
    (t : H) (ht : φ t = Model.transposition) :
    Representation.Equiv
      ((conjugateRep σ t).comp (componentEquiv φ hi K hK).symm.toMonoidHom)
      (τ.comp Model.outer.toMonoidHom) :=
  .mk e.toLinearEquiv (by
    intro a
    have he := e.isIntertwining' (Model.outer a)
    have hx := conjugate_mark φ hi K hK t ht a
    have hsym : (componentEquiv φ hi K hK).symm (Model.outer a) =
        ⟨t * ((componentEquiv φ hi K hK).symm a : H) * t⁻¹,
          (inferInstance : K.Normal).conj_mem _ ((componentEquiv φ hi K hK).symm a).property t⟩ := by
      rw [← hx, MulEquiv.symm_apply_apply]
    simpa only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, hsym,
      conjugateRep_apply] using he)

private def outer_outer_equiv :
    Representation.Equiv (Model.outerNatural.comp Model.outer.toMonoidHom) Model.natural :=
  .mk (LinearEquiv.refl (ZMod 2) Model.Four) (by
    intro a
    change Model.natural (Model.outer (Model.outer a)) = Model.natural a
    congr 1
    apply Subtype.ext
    change Model.transposition * (Model.transposition * a.val * Model.transposition) *
      Model.transposition = a.val
    simp [Model.transposition, mul_assoc])

omit [FiniteDimensional (ZMod 2) V] in
private theorem four_pair_natural [K.Normal]
    (ρ : Representation (ZMod 2) H V)
    (A : Subrepresentation (ρ.comp K.subtype))
    (e : Representation.Equiv
      (A.toRepresentation.comp (componentEquiv φ hi K hK).symm.toMonoidHom) Model.natural)
    (t : H) (ht : φ t = Model.transposition)
    (p : Representation.Equiv (ρ.comp K.subtype)
      (A.toRepresentation.prod (conjugateRep A.toRepresentation t))) :
    IsFourPlusDual ρ (componentInclusion φ hi K hK) := by
  let d := conjugateMarkedEquiv φ hi K hK A.toRepresentation Model.natural e t ht
  let ee := prodEquiv e (d.trans Model.outerDualEquiv)
  let pp := pullEquiv p (componentEquiv φ hi K hK).symm.toMonoidHom
  exact ⟨Model.natural, Model.natural_faithful, ⟨(pp.trans ee).symm⟩⟩

omit [FiniteDimensional (ZMod 2) V] in
private theorem four_pair_outer [K.Normal]
    (ρ : Representation (ZMod 2) H V)
    (A : Subrepresentation (ρ.comp K.subtype))
    (e : Representation.Equiv
      (A.toRepresentation.comp (componentEquiv φ hi K hK).symm.toMonoidHom) Model.outerNatural)
    (t : H) (ht : φ t = Model.transposition)
    (p : Representation.Equiv (ρ.comp K.subtype)
      (A.toRepresentation.prod (conjugateRep A.toRepresentation t))) :
    IsFourPlusDual ρ (componentInclusion φ hi K hK) := by
  let d := conjugateMarkedEquiv φ hi K hK A.toRepresentation Model.outerNatural e t ht
  let ee := prodEquiv (e.trans Model.outerDualEquiv) (d.trans outer_outer_equiv)
  let pp := pullEquiv p (componentEquiv φ hi K hK).symm.toMonoidHom
  let cc : (Model.natural.dual.prod Model.natural).Equiv
      (Model.natural.prod Model.natural.dual) :=
    .mk (LinearEquiv.prodComm (ZMod 2) _ _) (fun _ => rfl)
  exact ⟨Model.natural, Model.natural_faithful, ⟨(pp.trans (ee.trans cc)).symm⟩⟩

/-- The full compatible four-, six-, or four-plus-dual classification for
an ambient simple binary representation with a small elementary actor. -/
theorem source_small_quadratic :
    SmallQuadraticInput φ (componentInclusion φ hi K hK) := by
  intro U _ _ _ ρ hf hirr A hA _hquad hsmall
  let : Finite H := Finite.of_injective φ hi
  let : K.Normal := component_normal φ hi K hK
  let E := componentEquiv φ hi K hK
  let : IsSimpleGroup A7 := alternatingGroup.isSimpleGroup (by simp)
  let : IsSimpleGroup K := E.isSimpleGroup
  let : IsIrreducible ρ := hirr
  let : Nontrivial U := Subrepresentation.irreducible_module_nontrivial ρ
  have hd := finrank_le_twelve ρ φ hi E (fun _ => rfl) hf A hA hsmall
  obtain ⟨C, hC⟩ := Subrepresentation.irreducible_subrepresentation_of_finite_dimensional
    (ρ.comp K.subtype)
  let σ := C.toRepresentation.comp E.symm.toMonoidHom
  let : IsIrreducible C.toRepresentation := hC
  let : IsIrreducible σ :=
    (irreducible_comp_surjective_iff E.symm.toMonoidHom E.symm.surjective C.toRepresentation).mpr hC
  have hfC := faithful_constituent K ρ hf C hC
  have hfσ : Function.Injective σ := hfC.comp E.symm.injective
  have hdim : Module.finrank (ZMod 2) C.toSubmodule ≤ 12 := C.toSubmodule.finrank_le.trans hd
  have hc := small_simple_equiv σ hfσ hdim
  have hfour (τ : Representation (ZMod 2) A7 Model.Four) (ht : Function.Injective τ)
      (ee : Representation.Equiv σ τ) (hR : IsIrreducible (ρ.comp K.subtype)) :
      IsFour ρ (componentInclusion φ hi K hK) := by
    let : IsIrreducible (ρ.comp K.subtype) := hR
    have hCne : C ≠ ⊥ := (Subrepresentation.irreducible_iff_isAtom C).mp hC |>.ne_bot
    have htop : C = ⊤ := (IsSimpleOrder.eq_bot_or_eq_top C).resolve_left hCne
    let d := pullEquiv (subrepresentationFullEquiv (ρ.comp K.subtype) C htop) E.symm.toMonoidHom
    exact ⟨τ, ht, ⟨ee.symm.trans d⟩⟩
  rcases hc with hc | hc | hc <;> obtain ⟨ee⟩ := hc
  all_goals first
    | exact Or.inr (Or.inl (natural_occurrence φ hi K hK ρ C ee))
    | skip
  all_goals
    by_cases htop : K = ⊤
    · have hs : Function.Surjective K.subtype := by
        intro h
        exact ⟨⟨h, by rw [htop]; trivial⟩, rfl⟩
      have hR := (irreducible_comp_surjective_iff K.subtype hs ρ).mpr hirr
      first
      | exact Or.inl (hfour _ Model.natural_faithful ee hR)
      | exact Or.inl (hfour _ Model.outerNatural_faithful ee hR)
    · have hind : K.index = 2 := ((Nat.dvd_prime Nat.prime_two).mp
          (component_index_dvd φ hi K hK)).resolve_left (fun hh => htop (Subgroup.index_eq_one.mp hh))
      obtain ⟨t, ht, htK⟩ := transposition_lift φ hi K hK hind
      rcases Representation.CubicClifford.Inertia.restriction_dichotomy ρ K hind t htK C hC with hR | ⟨_, ⟨p⟩⟩
      · first
        | exact Or.inl (hfour _ Model.natural_faithful ee hR)
        | exact Or.inl (hfour _ Model.outerNatural_faithful ee hR)
      · right; right
        first
        | exact four_pair_natural φ hi K hK ρ C ee t ht p
        | exact four_pair_outer φ hi K hK ρ C ee t ht p

end
end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.Seven.OriginalSource
