module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Nonnormalization.Reductions
public import Theory.GroupTheory.PGroup.NormalizedSylowConjugation

/-!
# Reciprocal Sylow transport for source 11.2.4

When V normalizes A = Vᵍ, conjugating backwards puts V^(g⁻¹) in N_G(V).
Sylow conjugacy inside that normalizer moves the reciprocal actor into the
original T. The uniform parabolic conclusion can therefore be applied to
this actor as well. Its commutator is a conjugate of the original one.
If [V,A] = V₂, containment and equality of orders identify its plane and
produce the explicit normalizer element g l⁻¹ g⁻¹ required for alignment.

The same transport identifies the two centralizer indices. Computing a flag
preimage's index through the original surjective quotient gives corank 2n
for the symplectic plane, with no assumption that C_V(L) is zero or split.
The final theorem applies this alignment to the actual abelian-span consumer.
The uniform parabolic and preceding point-orbit results remain explicit.

Source: Aschbacher--Smith, 11.2.4, printed pp.769--770. This is a Sylow
transport proof of the equality branch's symmetry argument.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation
open CFSG.Quasithin.Chapter12.Section02
open CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry
open CFSG.Quasithin.ChapterE
open CFSG.Quasithin.ChapterB.QuasisimpleSource
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Nonnormalization.NormalizedPlane
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    {D : ChosenModule T L V} (S : D.NonbinaryNaturalInput)

omit [Finite G] in
private theorem conjugate_cancel (U : Subgroup G) (g : G) :
    (U.map (MulAut.conj g).toMonoidHom).map (MulAut.conj g⁻¹).toMonoidHom = U := by
  rw [offender_map_conj_map, inv_mul_cancel]
  have he : (MulAut.conj (1 : G)).toMonoidHom = MonoidHom.id G := by ext; simp
  rw [he, map_id]

include S in
/-- Place the reciprocal conjugate in T without changing the original seed. -/
theorem reciprocal_conjugate (g : G)
    (hn : V ≤ normalizer (V.map (MulAut.conj g).toMonoidHom : Set G)) :
    ∃ l ∈ normalizer (V : Set G),
      V.map (MulAut.conj (l * g⁻¹)).toMonoidHom ≤ T := by
  have hB : V.map (MulAut.conj g⁻¹).toMonoidHom ≤ normalizer (V : Set G) := by
    apply le_normalizer_iff_commutator_le_right.mpr
    have h := map_mono (f := (MulAut.conj g⁻¹).toMonoidHom)
      (le_normalizer_iff_commutator_le_right.mp hn)
    rwa [map_commutator, conjugate_cancel] at h
  obtain ⟨l, hl, hT⟩ := IsPGroup.exists_conj_le_sylow_of_normalized T
    (normalizer (V : Set G)) (V.map (MulAut.conj g⁻¹).toMonoidHom)
    (S.sylow_normalizes.trans (normalizer _).le_normalizer)
    ((T.isPGroup'.to_le D.le_sylow).map (MulAut.conj g⁻¹).toMonoidHom) hB
  exact ⟨l, hl, by rwa [offender_map_conj_map] at hT⟩

omit [Finite G] in
private theorem reciprocal_seed (g l : G) (hl : l ∈ normalizer (V : Set G)) :
    (V.map (MulAut.conj g).toMonoidHom).map
      (MulAut.conj (l * g⁻¹)).toMonoidHom = V := by
  rw [← offender_map_conj_map, conjugate_cancel]
  exact mem_normalizer_iff_map_conj_eq.mp hl

omit [Finite G] in
/-- The reciprocal commutator is a literal ambient conjugate. -/
theorem reciprocal_commutator (g l : G) (hl : l ∈ normalizer (V : Set G)) :
    ⁅V, V.map (MulAut.conj (l * g⁻¹)).toMonoidHom⁆ =
      (⁅V, V.map (MulAut.conj g).toMonoidHom⁆).map
        (MulAut.conj (l * g⁻¹)).toMonoidHom := by
  rw [map_commutator, reciprocal_seed g l hl, commutator_comm]

omit [Finite G] in
/-- Reciprocal transport exchanges the two original centralizers. -/
theorem reciprocal_centralizer (g l : G) (hl : l ∈ normalizer (V : Set G)) :
    ((V.map (MulAut.conj g).toMonoidHom) ⊓ centralizer (V : Set G)).map
      (MulAut.conj (l * g⁻¹)).toMonoidHom =
        V ⊓ centralizer (V.map (MulAut.conj (l * g⁻¹)).toMonoidHom : Set G) := by
  rw [map_inf _ _ _ (MulAut.conj (l * g⁻¹)).injective,
    reciprocal_seed g l hl, Theory.GroupTheory.map_centralizer_equiv]
  rfl

variable {S} {c : Coordinates D S.field} (f : InvariantFlag c)

/-- The full-commutator branch gives the requested left-conjugation alignment.
Uniformity applies the same parabolic result to the reciprocal actor in T. -/
theorem alignment_of_equal_commutator
    (hp : ∀ k : G, V.map (MulAut.conj k).toMonoidHom ≤ T →
      ⁅V, V.map (MulAut.conj k).toMonoidHom⁆ ≠ ⊥ →
      ParabolicGeometry f (V.map (MulAut.conj k).toMonoidHom))
    (g : G) (hne : ⁅V, V.map (MulAut.conj g).toMonoidHom⁆ ≠ ⊥)
    (hn : V ≤ normalizer (V.map (MulAut.conj g).toMonoidHom : Set G))
    (he : ⁅V, V.map (MulAut.conj g).toMonoidHom⁆ = f.Vi 1) :
    Alignment (f.Vi 1) V g := by
  obtain ⟨l, hl, hB⟩ := reciprocal_conjugate S g hn
  have hneB : ⁅V, V.map (MulAut.conj (l * g⁻¹)).toMonoidHom⁆ ≠ ⊥ := by
    rw [reciprocal_commutator g l hl]
    exact fun hz => hne ((map_eq_bot_iff_of_injective _
      (MulAut.conj (l * g⁻¹)).injective).mp hz)
  have hgeom := hp (l * g⁻¹) hB hneB
  have hplane : (f.Vi 1).map (MulAut.conj (l * g⁻¹)).toMonoidHom = f.Vi 1 := by
    apply eq_of_le_of_card_ge
    · have hb : ⁅V, V.map (MulAut.conj (l * g⁻¹)).toMonoidHom⁆ ≤ f.Vi 1 :=
        le_sup_left.trans_eq hgeom.quotient_plane
      rwa [reciprocal_commutator g l hl, he] at hb
    · rw [card_map_of_injective (MulAut.conj (l * g⁻¹)).injective]
  have hpoint : (f.Vi 1).map (MulAut.conj (g * l⁻¹)).toMonoidHom = f.Vi 1 := by
    apply mem_normalizer_iff_map_conj_eq.mp
    simpa only [mul_inv_rev, inv_inv] using
      (normalizer (f.Vi 1 : Set G)).inv_mem (mem_normalizer_iff_map_conj_eq.mpr hplane)
  refine ⟨g * l⁻¹ * g⁻¹, ?_, ?_⟩
  · apply mem_normalizer_iff_map_conj_eq.mpr
    change (V.map (MulAut.conj g).toMonoidHom).map
      (MulAut.conj (g * l⁻¹ * g⁻¹)).toMonoidHom = V.map (MulAut.conj g).toMonoidHom
    have hl' : l⁻¹ ∈ normalizer (V : Set G) := (normalizer _).inv_mem hl
    have hlV : V.map (MulAut.conj l⁻¹).toMonoidHom = V :=
      mem_normalizer_iff_map_conj_eq.mp hl'
    rw [offender_map_conj_map]
    simp only [mul_assoc, inv_mul_cancel, mul_one]
    rw [← offender_map_conj_map, hlV]
  · rw [offender_map_conj_map]
    simpa only [mul_assoc, inv_mul_cancel, mul_one] using hpoint

/-- Symmetry of the two actual actions, retaining their original kernels. -/
theorem action_coranks_equal
    (hp : ∀ k : G, V.map (MulAut.conj k).toMonoidHom ≤ T →
      ⁅V, V.map (MulAut.conj k).toMonoidHom⁆ ≠ ⊥ →
      ParabolicGeometry f (V.map (MulAut.conj k).toMonoidHom))
    (g : G) (hg : V.map (MulAut.conj g).toMonoidHom ≤ T)
    (hne : ⁅V, V.map (MulAut.conj g).toMonoidHom⁆ ≠ ⊥)
    (hn : V ≤ normalizer (V.map (MulAut.conj g).toMonoidHom : Set G)) :
    subgroupCorank (V.map (MulAut.conj g).toMonoidHom)
        (V.map (MulAut.conj g).toMonoidHom ⊓ centralizer (V : Set G)) =
      subgroupCorank V (f.Vi 1) ∧
    subgroupCorank V (V ⊓ centralizer (V.map (MulAut.conj g).toMonoidHom : Set G)) =
      subgroupCorank V (f.Vi 1) := by
  refine ⟨?_, by rw [(hp g hg hne).fixed_plane]⟩
  obtain ⟨l, hl, hB⟩ := reciprocal_conjugate S g hn
  have hneB : ⁅V, V.map (MulAut.conj (l * g⁻¹)).toMonoidHom⁆ ≠ ⊥ := by
    rw [reciprocal_commutator g l hl]
    exact fun hz => hne ((map_eq_bot_iff_of_injective _
      (MulAut.conj (l * g⁻¹)).injective).mp hz)
  unfold subgroupCorank
  rw [← relIndex_map_map_of_injective (f := (MulAut.conj (l * g⁻¹)).toMonoidHom)
      _ _ (MulAut.conj (l * g⁻¹)).injective,
    reciprocal_centralizer g l hl, reciprocal_seed g l hl, (hp _ hB hneB).fixed_plane]

/-- A quotient-preimage index is computed on the literal field quotient. -/
theorem corank_preimage (U : Submodule S.field.Carrier c.Space) :
    subgroupCorank V (c.preimage U) =
      S.field.degree * Module.finrank S.field.Carrier (c.Space ⧸ U) := by
  let : Finite c.Space := Finite.of_surjective
    (fun v : V => (c.projection v).toAdd) (Multiplicative.toAdd.surjective.comp c.projection_surjective)
  let : Module.Finite S.field.Carrier c.Space := Module.Finite.of_finite
  have he : (c.preimage U).subgroupOf V = U.toAddSubgroup.toSubgroup.comap c.projection := by
    change ((U.toAddSubgroup.toSubgroup.comap c.projection).map V.subtype).comap V.subtype = _
    exact comap_map_eq_self_of_injective V.subtype_injective _
  rw [subgroupCorank, relIndex, he,
    index_comap_of_surjective _ c.projection_surjective, AddSubgroup.index_toSubgroup]
  change Nat.log 2 (Nat.card (c.Space ⧸ U)) = _
  rw [Module.natCard_eq_pow_finrank (K := S.field.Carrier), S.field.card_eq,
    ← pow_mul, Nat.log_pow Nat.one_lt_two]

/-- The plane preimage has corank 2n even in a nonsplit central cover. -/
theorem sp4_plane_corank
    (m : ActionEquiv D.centralQuotientAction
      (restrictScalars (k := ZMod 2) (symplecticNatural (k := S.field.Carrier) 2)))
    (f : InvariantFlag (Coordinates.sp4 m)) :
    subgroupCorank V (f.Vi 1) = 2 * S.field.degree := by
  let : Module.Finite S.field.Carrier (Coordinates.sp4 m).Space :=
    inferInstanceAs (Module.Finite S.field.Carrier ((Fin 2 ⊕ Fin 2) → S.field.Carrier))
  rw [InvariantFlag.Vi, corank_preimage]
  have hd := Submodule.finrank_quotient_add_finrank (f.space 1)
  have hfull : Module.finrank S.field.Carrier (Coordinates.sp4 m).Space = 4 := by
    change Module.finrank S.field.Carrier ((Fin 2 ⊕ Fin 2) → S.field.Carrier) = 4
    simp
  rw [f.dimension 1, hfull] at hd
  have hq : Module.finrank S.field.Carrier ((Coordinates.sp4 m).Space ⧸ f.space 1) = 2 := by
    omega
  rw [hq, Nat.mul_comm]

/-- The actual abelian-span application of the equality branch. -/
theorem centralizes_of_equal_commutator
    (hab : IsMulCommutative (Source.conjugateSpan (normalizer (f.Vi 0 : Set G)) V))
    (horbit : ∀ y ∈ normalizer (f.Vi 1 : Set G), ∃ l ∈ f.Li 1,
      (f.Vi 0).map (MulAut.conj y).toMonoidHom =
        (f.Vi 0).map (MulAut.conj l).toMonoidHom)
    (hp : ∀ k : G, V.map (MulAut.conj k).toMonoidHom ≤ T →
      ⁅V, V.map (MulAut.conj k).toMonoidHom⁆ ≠ ⊥ →
      ParabolicGeometry f (V.map (MulAut.conj k).toMonoidHom))
    (g : G) (hne : ⁅V, V.map (MulAut.conj g).toMonoidHom⁆ ≠ ⊥)
    (hn : V ≤ normalizer (V.map (MulAut.conj g).toMonoidHom : Set G))
    (he : ⁅V, V.map (MulAut.conj g).toMonoidHom⁆ = f.Vi 1) :
    ⁅V, V.map (MulAut.conj g).toMonoidHom⁆ = ⊥ :=
  centralizes_of_plane_alignment f hab horbit g (alignment_of_equal_commutator f hp g hne hn he)

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Nonnormalization.NormalizedPlane
