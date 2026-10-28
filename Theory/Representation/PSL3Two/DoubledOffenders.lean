module

public import Theory.Representation.PSL3Two.DoubledOffenders.Model
public import Theory.Representation.PSL3Two.DoubledOffenders.Component
public import Theory.GroupTheory.SylowNormalIntersection
/-!
# All doubled-natural offenders in a Sylow of the full normalizer

For a subgroup between the diagonal SL₃(2) and its full linear normalizer,
intersect the given Sylow with the normal diagonal component. This is a
component Sylow, hence a component conjugate of the upper-triangular subgroup.
Every offender lies in the component by the intrinsic doubled-natural estimate;
the upper-triangular calculation therefore identifies all offenders, not only
best offenders. Conjugation transports the full-normalizer pointwise-fixer
calculation with exactly the same marking.

The final result retains the two successive subgroup maps: first conjugation
inside SL₃(2), then the actual homomorphism `(W.prod W).asGroupHom`.
Source: Aschbacher–Smith, combined manuscript of 1 March 2004, the central
branch of 13.6.20, printed p.931, and its B.2.20 input, printed p.82.
-/

@[expose] public section
open Matrix Representation Representation.BinaryOffender Subgroup
open Matrix.PSL3Two
open scoped Pointwise
noncomputable section
namespace BinaryLinearThree.DoubledOffenders

private instance : Finite D :=
  Finite.of_injective (fun x : D => (τ x : (Vector × Vector) → Vector × Vector))
    (fun _ _ h => Units.ext (LinearMap.ext (fun v => congrFun h v)))

lemma radical_le_borel : R ≤ borelSL := by
  rintro _ ⟨a, rfl⟩
  rw [mem_borelSL_iff]
  exact ⟨rfl, rfl, rfl⟩

private lemma map_conj_cancel {F : Type*} [_root_.Group F] (A : Subgroup F) (g : F) :
    (A.map (MulAut.conj g).toMonoidHom).map (MulAut.conj g⁻¹).toMonoidHom = A := by
  rw [Subgroup.map_map]
  have he : (MulAut.conj g⁻¹).toMonoidHom.comp (MulAut.conj g).toMonoidHom =
      MonoidHom.id F := by
    ext a
    simp [MulAut.conj_apply, mul_assoc]
  rw [he, Subgroup.map_id]

private lemma offender_conj {F V : Type*} [_root_.Group F] [AddCommGroup V]
    [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
    (ρ : Representation (ZMod 2) F V) {A : Subgroup F} (hA : IsOffender ρ A) (g : F) :
    IsOffender ρ (A.map (MulAut.conj g).toMonoidHom) := by
  refine ⟨hA.1.map_conj g, ?_⟩
  rw [fixedCodim_map_conj, rank_map_conj]
  exact hA.2

lemma offender_borel_conjugate_iff (g : Group) (E : Subgroup Group)
    (hEB : E ≤ borelSL.map (MulAut.conj g).toMonoidHom) :
    IsOffender (W.prod W) E ↔ E = R.map (MulAut.conj g).toMonoidHom := by
  constructor
  · intro hE
    have hle := map_mono (f := (MulAut.conj g⁻¹).toMonoidHom) hEB
    rw [map_conj_cancel] at hle
    have he := (offender_borel_iff _ hle).mp (offender_conj (W.prod W) hE g⁻¹)
    have hh := congrArg (fun A : Subgroup Group => A.map (MulAut.conj g).toMonoidHom) he
    have hc := map_conj_cancel E g⁻¹
    rw [inv_inv] at hc
    rw [hc] at hh
    exact hh
  · rintro rfl
    exact offender_conj (W.prod W) DoubledFixedSpace.radical_isOffender g

lemma offender_comap {E : Subgroup D} (hE : IsOffender τ E) (hEC : E ≤ δ.range) :
    IsOffender (W.prod W) (E.comap δ) := by
  let I := E.comap δ
  have hm : I.map δ = E := map_comap_eq_self hEC
  let : IsElementaryAbelian 2 E := hE.1.2
  let : IsElementaryAbelian 2 (I.map δ) := hm.symm ▸ hE.1.2
  let e := I.equivMapOfInjective δ δ_injective
  let : IsElementaryAbelian 2 I :=
    IsElementaryAbelian.of_surjective e.symm.toMonoidHom e.symm.surjective
  have hf : fixedCodim (W.prod W) I = fixedCodim τ E := by
    rw [← hm]
    exact fixedCodim_map_equivariant (W.prod W) τ δ (LinearEquiv.refl _ _)
      (fun _ _ => rfl) I
  refine ⟨⟨?_, inferInstance⟩, ?_⟩
  · intro hb
    change I = ⊥ at hb
    apply hE.1.1
    rw [← hm, hb, Subgroup.map_bot]
  · rw [hf, ← rank_map_injective δ δ_injective I, hm]
    exact hE.2

/-- The supplied Sylow meets the literal diagonal component in a component Sylow. -/
lemma sylow_component_intersection (H : Subgroup D) (hCH : δ.range ≤ H)
    (hHN : H ≤ N) (P : Sylow 2 H) :
    ∃ Q : Sylow 2 Group, (Q : Subgroup Group).map δ =
      (P : Subgroup H).map H.subtype ⊓ δ.range := by
  let f : Group →* H := δ.codRestrict H (fun g => hCH ⟨g, rfl⟩)
  have hi : Function.Injective f := fun x y he => δ_injective (congrArg Subtype.val he)
  have hr : f.range = δ.range.subgroupOf H := by
    ext x
    constructor
    · rintro ⟨g, rfl⟩
      exact ⟨g, rfl⟩
    · rintro ⟨g, hg⟩
      exact ⟨g, Subtype.ext hg⟩
  let : f.range.Normal := hr.symm ▸ (normal_subgroupOf_iff_le_normalizer hCH).mpr hHN
  obtain ⟨S, hS⟩ := P.exists_subgroupOf_eq_of_normal f.range
  let e : Group ≃* f.range := MonoidHom.ofInjective hi
  let Q := S.mapSurjective (f := e.symm.toMonoidHom) e.symm.surjective
  have hQ (g : Group) : g ∈ (Q : Subgroup Group) ↔ f g ∈ (P : Subgroup H) := by
    change g ∈ (S : Subgroup f.range).map e.symm.toMonoidHom ↔ _
    rw [mem_map_equiv, hS]
    rfl
  refine ⟨Q, ?_⟩
  ext x
  constructor
  · rintro ⟨g, hg, rfl⟩
    exact ⟨⟨f g, (hQ g).mp hg, rfl⟩, ⟨g, rfl⟩⟩
  · rintro ⟨⟨a, ha, rfl⟩, g, hg⟩
    refine ⟨g, (hQ g).mpr ?_, hg⟩
    have he : f g = a := Subtype.ext hg
    exact he.symm ▸ ha

lemma conjugate_radical_eq (g : Group) :
    (R.map (MulAut.conj g).toMonoidHom).map δ =
      radical.map (MulAut.conj (δ g)).toMonoidHom := by
  change (R.map (MulAut.conj g).toMonoidHom).map δ =
    (R.map δ).map (MulAut.conj (δ g)).toMonoidHom
  rw [Subgroup.map_map, Subgroup.map_map]
  apply congrArg (fun f : Group →* D => R.map f)
  apply MonoidHom.ext
  intro a
  change δ (g * a * g⁻¹) = δ g * δ a * (δ g)⁻¹
  rw [map_mul, map_mul, map_inv]

/-- Pointwise fixation holds in the full normalizer for every component conjugate. -/
lemma fixes_conjugate_fixedSpace_iff (g : Group) (x : D) (hx : x ∈ N) :
    (∀ u ∈ fixedSpace τ ((R.map (MulAut.conj g).toMonoidHom).map δ), τ x u = u) ↔
      x ∈ (R.map (MulAut.conj g).toMonoidHom).map δ := by
  rw [conjugate_radical_eq]
  constructor
  · intro hf
    let h := δ g
    have hh : h ∈ N := δ.range.le_normalizer ⟨g, rfl⟩
    have hn : h⁻¹ * x * h ∈ N := N.mul_mem (N.mul_mem (N.inv_mem hh) hx) hh
    have hm : h⁻¹ * x * h ∈ radical := (fixes_fixedSpace_iff _ hn).mp (by
      intro u hu
      have hv : τ h u ∈ fixedSpace τ (radical.map (MulAut.conj h).toMonoidHom) := by
        rintro ⟨_, a, ha, rfl⟩
        change τ (h * a * h⁻¹) (τ h u) = τ h u
        rw [map_mul, map_mul]
        change τ h (τ a (τ h⁻¹ (τ h u))) = τ h u
        have hinv : τ h⁻¹ (τ h u) = u := by
          change (τ h⁻¹ * τ h) u = u
          rw [← map_mul, inv_mul_cancel, map_one]
          rfl
        have hau : τ a u = u := hu ⟨a, ha⟩
        rw [hinv, hau]
      change τ (h⁻¹ * x * h) u = u
      rw [map_mul, map_mul]
      change τ h⁻¹ (τ x (τ h u)) = u
      rw [hf _ hv]
      change (τ h⁻¹ * τ h) u = u
      rw [← map_mul, inv_mul_cancel, map_one]
      rfl)
    refine ⟨h⁻¹ * x * h, hm, ?_⟩
    change h * (h⁻¹ * x * h) * h⁻¹ = x
    simp [mul_assoc]
  · intro hm u hu
    exact hu ⟨x, hm⟩

/-- Every allowed Sylow has exactly one offender, a literal component conjugate of R,
and the pointwise fixer of that offender's fixed space inside the Sylow is itself. -/
theorem sylow_offenders (H : Subgroup D) (hCH : δ.range ≤ H) (hHN : H ≤ N)
    (P : Sylow 2 H) : ∃ g : Group,
      let A := (R.map (MulAut.conj g).toMonoidHom).map δ
      let S := (P : Subgroup H).map H.subtype
      A ≤ S ∧
      (∀ E : Subgroup D, E ≤ S → (IsOffender τ E ↔ E = A)) ∧
      (∀ x ∈ S, (∀ u ∈ fixedSpace τ A, τ x u = u) ↔ x ∈ A) := by
  have hSH : (P : Subgroup H).map H.subtype ≤ H := by
    rintro _ ⟨p, _, rfl⟩
    exact p.property
  obtain ⟨Q, hQ⟩ := sylow_component_intersection H hCH hHN P
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq Group SourceFlag.flagSylow Q
  have hQg : (Q : Subgroup Group) = borelSL.map (MulAut.conj g).toMonoidHom := by
    rw [← hg, Sylow.coe_subgroup_smul]
    rfl
  refine ⟨g, ?_, ?_, ?_⟩
  · have hle := map_mono (f := δ)
      (map_mono (f := (MulAut.conj g).toMonoidHom) radical_le_borel)
    rw [← hQg, hQ] at hle
    exact hle.trans inf_le_left
  · intro E hES
    constructor
    · intro hE
      have hEN : E ≤ N := hES.trans (hSH.trans hHN)
      have hEC := offender_le_component hE hEN
      have hEQ : E.comap δ ≤ (Q : Subgroup Group) := by
        intro a ha
        have hh : δ a ∈ (Q : Subgroup Group).map δ := by
          rw [hQ]
          exact ⟨hES ha, ⟨a, rfl⟩⟩
        obtain ⟨b, hb, hba⟩ := hh
        exact δ_injective hba ▸ hb
      rw [hQg] at hEQ
      have hER := (offender_borel_conjugate_iff g _ hEQ).mp (offender_comap hE hEC)
      rw [← map_comap_eq_self hEC, hER]
    · rintro rfl
      exact (offender_conj (W.prod W) DoubledFixedSpace.radical_isOffender g).map_equivariant
        (W.prod W) τ δ δ_injective (LinearEquiv.refl _ _) (fun _ _ => rfl)
  · intro x hx
    exact fixes_conjugate_fixedSpace_iff g x
      (hHN (hSH hx))

/-- The actual subgroup fixing every vector of a specified subspace. -/
def pointwiseFixer (U : Submodule (ZMod 2) (Vector × Vector)) : Subgroup D where
  carrier := {x | ∀ u ∈ U, τ x u = u}
  one_mem' := by intro u _; rfl
  mul_mem' {x y} hx hy := by
    intro u hu
    change τ x (τ y u) = u
    rw [hy u hu, hx u hu]
  inv_mem' {x} hx := by
    intro u hu
    have he := congrArg (fun v => τ x⁻¹ v) (hx u hu)
    change (τ x⁻¹ * τ x) u = τ x⁻¹ u at he
    rw [← map_mul, inv_mul_cancel, map_one] at he
    exact he.symm

/-- The same classification, with the pointwise-fixer conclusion as a subgroup equality. -/
theorem sylow_offenders_and_fixer (H : Subgroup D) (hCH : δ.range ≤ H) (hHN : H ≤ N)
    (P : Sylow 2 H) : ∃ g : Group,
      let A := (R.map (MulAut.conj g).toMonoidHom).map δ
      let S := (P : Subgroup H).map H.subtype
      A ≤ S ∧
      (∀ E : Subgroup D, E ≤ S → (IsOffender τ E ↔ E = A)) ∧
      S ⊓ pointwiseFixer (fixedSpace τ A) = A := by
  obtain ⟨g, hAS, hE, hfix⟩ := sylow_offenders H hCH hHN P
  refine ⟨g, hAS, hE, ?_⟩
  apply le_antisymm
  · intro x hx
    exact (hfix x hx.1).mp hx.2
  · intro x hx
    exact ⟨hAS hx, (hfix x (hAS hx)).mpr hx⟩
end BinaryLinearThree.DoubledOffenders
