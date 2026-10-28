module
public import Theory.GroupTheory.Recognition.JankoFour.SourceIncidence.Markers
public import Theory.GroupTheory.Recognition.JankoFour.SourceCycleBase.Native.PlaneCardinality

public import Theory.GroupTheory.Recognition.JankoFour.SourceFusion.Defs

/-!
# The two Todd involution orbits and ambient nonfusion

Pair vectors and sextet vectors, together with zero, exhaust the cocode:
their disjoint parametrizations have cardinalities 276 and 1771. The original
Todd embedding transports both orbits to E. Fusion control by the elementary
Thompson normalizer separates them even under ambient conjugacy. The second
representative is the image of the pair {0,1} under that same embedding.

Source: Aschbacher–Segev, Invent. Math. 105 (1991), (6.3)(1), p.602.
-/

@[expose] public section
open Subgroup
open scoped Pointwise IsMulCommutative
namespace Theory.GroupTheory.Recognition.JankoFour.SourceFusion
open LocalGeometry LocalGeometry.LocalSubgroups SourceIncidence
open Sporadic.Mathieu Sporadic.Mathieu.M24LocalGeometry MathieuCode
variable {G : Type*} [Group G] [Finite G] {z : G} {h : IsTypeJ4 z}

private noncomputable def vectorCatalogue : Unit ⊕ (PointPair ⊕ Sextet) → Cocode
  | .inl _ => 0
  | .inr (.inl B) => pairVector B
  | .inr (.inr S) => sextetVector S

private theorem catalogue_injective : Function.Injective vectorCatalogue := by
  intro x y he
  rcases x with x | (B | S) <;> rcases y with y | (C | T)
  · exact congrArg Sum.inl (Subsingleton.elim _ _)
  · exact (pairVector_ne_zero C he.symm).elim
  · exact (sextetVector_ne_zero T he.symm).elim
  · exact (pairVector_ne_zero B he).elim
  · exact congrArg (Sum.inr ∘ Sum.inl) (pairVector_injective he)
  · exact (pairVector_ne_sextetVector T B he).elim
  · exact (sextetVector_ne_zero S he).elim
  · exact (pairVector_ne_sextetVector S C he.symm).elim
  · exact congrArg (Sum.inr ∘ Sum.inr) (sextetVector_injective he)

theorem cocode_cases (v : Cocode) :
    v = 0 ∨ (∃ B : PointPair, v = pairVector B) ∨ ∃ S : Sextet, v = sextetVector S := by
  have hc : Nat.card Cocode = 2048 := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2), finrank_cocode, Nat.card_zmod]
    decide
  have hp : Nat.card PointPair = 276 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_finset_len]
    decide
  have hs : Function.Surjective vectorCatalogue :=
    (catalogue_injective.bijective_of_nat_card_le (by
      rw [Nat.card_sum, Nat.card_sum, hc, hp, SourceCycleBase.Native.plane_card]
      norm_num)).2
  obtain ⟨x, rfl⟩ := hs v
  rcases x with x | (B | S)
  · exact Or.inl rfl
  · exact Or.inr (Or.inl ⟨B,rfl⟩)
  · exact Or.inr (Or.inr ⟨S,rfl⟩)

theorem sextet_vector_action (S : Sextet) (g : M24) :
    cocodeRepresentation g (sextetVector S) = sextetVector (g • S) := by
  obtain ⟨B,hB⟩ := sextet_parts_nonempty S
  rw [sextetVector_eq S hB, evenSetVector_equivariant]
  exact (sextetVector_eq (g • S) (Finset.smul_mem_smul_finset hB)).symm

theorem vector_conj (P : PointData z) (m : P.M) (v : Cocode) :
    MulAut.conj (m : G) (P.vectorEmbedding (Multiplicative.ofAdd v)) =
      P.vectorEmbedding (Multiplicative.ofAdd (cocodeRepresentation (P.projection m) v)) := by
  let j := P.M.subtype.comp P.toddEquiv.toMonoidHom
  have he : P.toddEquiv.symm m * SemidirectProduct.inl (Multiplicative.ofAdd v) *
      (P.toddEquiv.symm m)⁻¹ =
      SemidirectProduct.inl (toddAction (P.projection m) (Multiplicative.ofAdd v)) := by
    ext
    · simp [PointData.projection, mul_comm, mul_left_comm]
    · simp
  have hv : toddAction (P.projection m) (Multiplicative.ofAdd v) =
      Multiplicative.ofAdd (cocodeRepresentation (P.projection m) v) := rfl
  rw [hv] at he
  have hj := congrArg j he
  simpa only [j, PointData.vectorEmbedding, MonoidHom.comp_apply,
    MulEquiv.coe_toMonoidHom, map_mul, map_inv, MulEquiv.apply_symm_apply,
    Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.subtype_apply, MulAut.conj_apply] using hj

noncomputable def second (a : LocalData h) : G :=
  a.P.vectorEmbedding (Multiplicative.ofAdd (pairVector ⟨{0,1},by decide⟩))

theorem second_mem (a : LocalData h) : second a ∈ a.P.E := ⟨_,rfl⟩

theorem second_ne_one (a : LocalData h) : second a ≠ 1 := by
  intro he
  have he' := a.P.vectorEmbedding_injective (he.trans (map_one _).symm)
  exact pairVector_ne_zero ⟨{0,1},by decide⟩ (congrArg Multiplicative.toAdd he')

theorem second_order (a : LocalData h) : orderOf (second a) = 2 := by
  let := a.P.E_elementary
  have hp : second a ^ 2 = 1 := by
    have he := Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
      (IsElementaryAbelian.exponent_dvd_p 2 a.P.E) (⟨second a,second_mem a⟩ : a.P.E)
    exact congrArg Subtype.val he
  exact orderOf_eq_prime hp (second_ne_one a)

theorem not_isConj_second (a : LocalData h) : ¬ IsConj z (second a) := by
  intro hc
  obtain ⟨m,hm,he⟩ := a.controls_marker_fusion (second_mem a) hc
  have he0 := (congrArg (MulAut.conj m) a.marker_vector).trans he
  rw [vector_conj a.P ⟨m,hm⟩, sextet_vector_action] at he0
  have hv := a.P.vectorEmbedding_injective he0
  exact pairVector_ne_sextetVector _ ⟨{0,1},by decide⟩
    (congrArg Multiplicative.toAdd hv).symm

theorem E_orbits (a : LocalData h) (u : G) (hu : u ∈ a.P.E) (hu1 : u ≠ 1) :
    (∃ m ∈ a.P.M, MulAut.conj m z = u) ∨
    ∃ m ∈ a.P.M, MulAut.conj m (second a) = u := by
  obtain ⟨v,rfl⟩ := hu
  rcases cocode_cases v.toAdd with hz | ⟨B,hB⟩ | ⟨S,hS⟩
  · have he : v = 1 := congrArg Multiplicative.ofAdd hz
    exact (hu1 (he ▸ map_one _)).elim
  · obtain ⟨g,hg⟩ := weightTwoOrbit_transitive ⟨{0,1},by decide⟩ B
    obtain ⟨m,hm⟩ := a.projection_surjective g
    refine Or.inr ⟨m,m.property,?_⟩
    rw [second,vector_conj,hm,hg,←hB]
    rfl
  · obtain ⟨g,hg⟩ := MulAction.exists_smul_eq M24 a.sextet S
    obtain ⟨m,hm⟩ := a.projection_surjective g
    refine Or.inl ⟨m,m.property,?_⟩
    calc
      MulAut.conj (m : G) z = _ := congrArg (MulAut.conj (m : G)) a.marker_vector.symm
      _ = _ := vector_conj a.P m (sextetVector a.sextet)
      _ = _ := by rw [hm,sextet_vector_action,hg,←hS]; rfl

end Theory.GroupTheory.Recognition.JankoFour.SourceFusion

