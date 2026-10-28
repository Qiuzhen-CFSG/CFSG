module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Quotient.LargeBranch.RankOne.Recognition.Sections.FromFrame.Basic
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Quotient.LargeBranch.RankOne.Recognition.Sections.FromFrame.Residual
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Quotient.LargeBranch.RankOne.Recognition.Sections.FromFrame.Second

/-!
# Rank-one sections from a supplied marked frame

The two literal sections of Meierfrankenfeld--Stellmacher (1993), (4.6.12),
are assembled here from a supplied `Sections.Frame`.  The first quotient is
the actual natural binary plane.  The second quotient is an actual direct sum
of natural planes, represented by a surjective map from `K` whose kernel is
exactly the printed denominator `Y`.

Both actions descend through the same source projection and the same marked
quotient `H/(H ∩ Q_beta) ≃ SL₂(2)'`.  Thus the matrix actor in the conclusions
is the literal derived subgroup of `SL₂(2)`, and every displayed map retains
the original ambient conjugation equation.

Source: Meierfrankenfeld--Stellmacher, *Pushing up weak BN-pairs of rank two*
(1993), (4.6.12)(1)--(2), printed p.910.
-/

@[expose] public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
open scoped commutatorElement
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.LargeBranch.RankOne.Sections
open Flags.RankOne
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.LargeBranch.RankOne
open Representation

variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}
  {source : LocalSource L R} {geometry : Geometry R}

set_option linter.style.haveILetI false in
noncomputable def firstCRepresentation (common : CommonFacts R source geometry)
    (radius : RadiusFacts R geometry) (f : Frame source) (hb : geometry.b R = 4)
    (s : CriticalSegment geometry) (hbc : Adjacent R (beta R) s.middle)
    (d : LayerModule source (V R (alpha R))) :
    Representation (ZMod 2) BinarySL2Residual.C
      (d.Space ⧸ d.subspace (intersection s.middle)) := by
  let ρ := firstRepresentation common radius f s hbc d
  let K := (Q R (beta R)).subgroupOf (flagResidual source f.orientation)
  letI : Representation.IsTrivial (ρ.comp K.subtype) := ⟨by
    intro g
    have hg := firstRepresentation_kernel_contains_edge common radius f hb s hbc d g.property
    change ρ g = 1
    exact MonoidHom.mem_ker.mp hg⟩
  exact (ρ.ofQuotient K).comp (markedResidualQuotientEquiv source f).symm.toMonoidHom

set_option linter.style.haveILetI false in
theorem firstCRepresentation_apply (common : CommonFacts R source geometry)
    (radius : RadiusFacts R geometry) (f : Frame source) (hb : geometry.b R = 4)
    (s : CriticalSegment geometry) (hbc : Adjacent R (beta R) s.middle)
    (d : LayerModule source (V R (alpha R)))
    (g : flagResidual source f.orientation)
    (z : d.Space ⧸ d.subspace (intersection s.middle)) :
    firstCRepresentation common radius f hb s hbc d (markedResidualProjection source f g) z =
      firstRepresentation common radius f s hbc d g z := by
  let ρ := firstRepresentation common radius f s hbc d
  let K := (Q R (beta R)).subgroupOf (flagResidual source f.orientation)
  letI : Representation.IsTrivial (ρ.comp K.subtype) := ⟨by
    intro g
    have hg := firstRepresentation_kernel_contains_edge common radius f hb s hbc d g.property
    change ρ g = 1
    exact MonoidHom.mem_ker.mp hg⟩
  have hq : (markedResidualQuotientEquiv source f).symm
      (markedResidualProjection source f g) =
      @QuotientGroup.mk' _ _ K (markedResidualProjection_normal source f) g := by
    apply (markedResidualQuotientEquiv source f).injective
    rw [MulEquiv.apply_symm_apply, markedResidualQuotientEquiv_mk]
  change (ρ.ofQuotient K)
      ((markedResidualQuotientEquiv source f).symm (markedResidualProjection source f g)) z = ρ g z
  rw [hq]
  exact Representation.ofQuotient_coe_apply ρ K g z

set_option linter.style.haveILetI false in
theorem firstCRepresentation_invariants_eq_bot (common : CommonFacts R source geometry)
    (radius : RadiusFacts R geometry) (f : Frame source) (hb : geometry.b R = 4)
    (s : CriticalSegment geometry) (hbc : Adjacent R (beta R) s.middle)
    (d : LayerModule source (V R (alpha R))) :
    Representation.invariants (firstCRepresentation common radius f hb s hbc d) = ⊥ := by
  let ρ := firstRepresentation common radius f s hbc d
  let K := (Q R (beta R)).subgroupOf (flagResidual source f.orientation)
  letI : Representation.IsTrivial (ρ.comp K.subtype) := ⟨by
    intro g
    have hg := firstRepresentation_kernel_contains_edge common radius f hb s hbc d g.property
    change ρ g = 1
    exact MonoidHom.mem_ker.mp hg⟩
  rw [Submodule.eq_bot_iff]
  intro z hz
  have hzH : z ∈ Representation.invariants ρ := by
    intro g
    calc
      ρ g z = firstCRepresentation common radius f hb s hbc d
          (markedResidualProjection source f g) z :=
        (firstCRepresentation_apply common radius f hb s hbc d g z).symm
      _ = z := hz (markedResidualProjection source f g)
  rw [firstRepresentation_invariants_eq_bot common radius f hb s hbc d] at hzH
  change z = 0 at hzH
  exact hzH

set_option linter.style.haveILetI false in
theorem exists_first_natural (common : CommonFacts R source geometry)
    (radius : RadiusFacts R geometry) (f : Frame source) (hb : geometry.b R = 4)
    (s : CriticalSegment geometry) (hbc : Adjacent R (beta R) s.middle)
    (d : LayerModule source (V R (alpha R))) :
    ∃ e : (d.Space ⧸ d.subspace (intersection s.middle)) ≃ₗ[ZMod 2]
        (Fin 2 → ZMod 2),
      ∀ (g : flagResidual source f.orientation) (w),
        e (firstRepresentation common radius f s hbc d g w) =
          (markedResidualProjection source f g).val.val.mulVec (e w) := by
  let W := d.Space ⧸ d.subspace (intersection s.middle)
  letI : Finite W := Finite.of_surjective
    (d.subspace (intersection s.middle)).mkQ
    (d.subspace (intersection s.middle)).mkQ_surjective
  let ρ := firstCRepresentation common radius f hb s hbc d
  have hcard : Nat.card W = 4 := first_quotient_card common radius f hb s hbc d
  letI : Nontrivial W := Finite.one_lt_card_iff_nontrivial.mp (by rw [hcard]; decide)
  obtain ⟨_, e, he⟩ := BinarySL2Residual.natural_of_card_le_four ρ
    (firstCRepresentation_invariants_eq_bot common radius f hb s hbc d) (by rw [hcard])
  refine ⟨e, ?_⟩
  intro g w
  rw [← firstCRepresentation_apply common radius f hb s hbc d g w]
  exact he (markedResidualProjection source f g) w

theorem exists_first_natural_map (common : CommonFacts R source geometry)
    (radius : RadiusFacts R geometry) (f : Frame source) (hb : geometry.b R = 4)
    (s : CriticalSegment geometry) (hbc : Adjacent R (beta R) s.middle)
    (d : LayerModule source (V R (alpha R))) :
    ∃ (e : (d.Space ⧸ d.subspace (intersection s.middle)) ≃ₗ[ZMod 2]
        (Fin 2 → ZMod 2))
      (φ : V R (alpha R) →* Multiplicative (Fin 2 → ZMod 2)),
      Function.Surjective φ ∧
      φ.ker = (intersection s.middle).subgroupOf (V R (alpha R)) ∧
      (∀ v, Multiplicative.toAdd (φ v) =
        e ((d.quotientMap (intersection s.middle) v).toAdd)) ∧
      ∀ (g : flagResidual source f.orientation) (v w : V R (alpha R)),
        (w : FreeAmalgam R) = g * (v : FreeAmalgam R) * (g : FreeAmalgam R)⁻¹ →
        Multiplicative.toAdd (φ w) =
          (markedResidualProjection source f g).val.val.mulVec
            (Multiplicative.toAdd (φ v)) := by
  obtain ⟨e, he⟩ := exists_first_natural common radius f hb s hbc d
  let φ : V R (alpha R) →* Multiplicative (Fin 2 → ZMod 2) :=
    (AddEquiv.toMultiplicative e.toAddEquiv).toMonoidHom.comp
      (d.quotientMap (intersection s.middle))
  refine ⟨e, φ, ?_, ?_, ?_, ?_⟩
  · exact (AddEquiv.toMultiplicative e.toAddEquiv).surjective.comp
      (d.quotientMap_surjective (intersection s.middle))
  · rw [show φ = (AddEquiv.toMultiplicative e.toAddEquiv).toMonoidHom.comp
        (d.quotientMap (intersection s.middle)) by rfl,
      MonoidHom.ker_comp_of_injective
        (d.quotientMap (intersection s.middle))
        (AddEquiv.toMultiplicative e.toAddEquiv).toMonoidHom
        (AddEquiv.toMultiplicative e.toAddEquiv).injective]
    exact d.quotientMap_kernel (intersection s.middle)
      (Z_le_intersection common s.first_distance)
  · intro v
    rfl
  · intro g v w hw
    have ha := firstRepresentation_action common radius f s hbc d g v w hw
    change e (d.quotientMap (intersection s.middle) w).toAdd =
      (markedResidualProjection source f g).val.val.mulVec
        (e (d.quotientMap (intersection s.middle) v).toAdd)
    rw [ha]
    exact he g ((d.quotientMap (intersection s.middle) v).toAdd)

set_option linter.style.haveILetI false in
noncomputable def secondCRepresentation (common : CommonFacts R source geometry)
    (radius : RadiusFacts R geometry) (f : Frame source) (hb : geometry.b R = 4)
    (s : CriticalSegment geometry) (hbc : Adjacent R (beta R) s.middle)
    (d : LayerModule source (V R (alpha R))) :
    Representation (ZMod 2) BinarySL2Residual.C
      ((d.subspace (intersection s.middle)) ⧸
        (d.subspace (fixedPreimage s.middle)).comap (d.subspace (intersection s.middle)).subtype) := by
  let ρ := secondRepresentation common radius f s hbc d
  let K := (Q R (beta R)).subgroupOf (flagResidual source f.orientation)
  letI : Representation.IsTrivial (ρ.comp K.subtype) := ⟨by
    intro g
    have hg := secondRepresentation_kernel_contains_edge common radius f hb s hbc d g.property
    change ρ g = 1
    exact MonoidHom.mem_ker.mp hg⟩
  exact (ρ.ofQuotient K).comp (markedResidualQuotientEquiv source f).symm.toMonoidHom

set_option linter.style.haveILetI false in
theorem secondCRepresentation_apply (common : CommonFacts R source geometry)
    (radius : RadiusFacts R geometry) (f : Frame source) (hb : geometry.b R = 4)
    (s : CriticalSegment geometry) (hbc : Adjacent R (beta R) s.middle)
    (d : LayerModule source (V R (alpha R)))
    (g : flagResidual source f.orientation)
    (z : (d.subspace (intersection s.middle)) ⧸
      (d.subspace (fixedPreimage s.middle)).comap (d.subspace (intersection s.middle)).subtype) :
    secondCRepresentation common radius f hb s hbc d (markedResidualProjection source f g) z =
      secondRepresentation common radius f s hbc d g z := by
  let ρ := secondRepresentation common radius f s hbc d
  let K := (Q R (beta R)).subgroupOf (flagResidual source f.orientation)
  letI : Representation.IsTrivial (ρ.comp K.subtype) := ⟨by
    intro g
    have hg := secondRepresentation_kernel_contains_edge common radius f hb s hbc d g.property
    change ρ g = 1
    exact MonoidHom.mem_ker.mp hg⟩
  have hq : (markedResidualQuotientEquiv source f).symm
      (markedResidualProjection source f g) =
      @QuotientGroup.mk' _ _ K (markedResidualProjection_normal source f) g := by
    apply (markedResidualQuotientEquiv source f).injective
    rw [MulEquiv.apply_symm_apply, markedResidualQuotientEquiv_mk]
  change (ρ.ofQuotient K)
      ((markedResidualQuotientEquiv source f).symm (markedResidualProjection source f g)) z = ρ g z
  rw [hq]
  exact Representation.ofQuotient_coe_apply ρ K g z

set_option linter.style.haveILetI false in
theorem secondCRepresentation_invariants_eq_bot (common : CommonFacts R source geometry)
    (radius : RadiusFacts R geometry) (f : Frame source) (hb : geometry.b R = 4)
    (s : CriticalSegment geometry) (hbc : Adjacent R (beta R) s.middle)
    (d : LayerModule source (V R (alpha R))) :
    Representation.invariants (secondCRepresentation common radius f hb s hbc d) = ⊥ := by
  obtain ⟨T, hT, _⟩ := exists_marked_cubic source f
  let ρ := secondRepresentation common radius f s hbc d
  let K := (Q R (beta R)).subgroupOf (flagResidual source f.orientation)
  letI : Representation.IsTrivial (ρ.comp K.subtype) := ⟨by
    intro g
    have hg := secondRepresentation_kernel_contains_edge common radius f hb s hbc d g.property
    change ρ g = 1
    exact MonoidHom.mem_ker.mp hg⟩
  rw [Submodule.eq_bot_iff]
  intro z hz
  have hzH : z ∈ Representation.invariants ρ := by
    intro g
    calc
      ρ g z = secondCRepresentation common radius f hb s hbc d
          (markedResidualProjection source f g) z :=
        (secondCRepresentation_apply common radius f hb s hbc d g z).symm
      _ = z := hz (markedResidualProjection source f g)
  rw [secondRepresentation_invariants_eq_bot common radius f hb s hbc T hT d] at hzH
  change z = 0 at hzH
  exact hzH

set_option linter.style.haveILetI false in
theorem exists_second_natural (common : CommonFacts R source geometry)
    (radius : RadiusFacts R geometry) (f : Frame source) (hb : geometry.b R = 4)
    (s : CriticalSegment geometry) (hbc : Adjacent R (beta R) s.middle)
    (d : LayerModule source (V R (alpha R))) :
    ∃ (n : ℕ)
      (e : ((d.subspace (intersection s.middle)) ⧸
        (d.subspace (fixedPreimage s.middle)).comap (d.subspace (intersection s.middle)).subtype) ≃ₗ[ZMod 2]
          (Fin n → Fin 2 → ZMod 2))
      (φ : intersection s.middle →* Multiplicative (Fin n → Fin 2 → ZMod 2)),
      Function.Surjective φ ∧
      φ.ker = (fixedPreimage s.middle).subgroupOf (intersection s.middle) ∧
      (∀ v : intersection s.middle,
        Multiplicative.toAdd (φ v) = e ((d.sectionMap (intersection s.middle)
          (fixedPreimage s.middle) (by rw [intersection]; exact inf_le_left) v).toAdd)) ∧
      ∀ (g : flagResidual source f.orientation) (v w : intersection s.middle) (j : Fin n),
        (w : FreeAmalgam R) = g * (v : FreeAmalgam R) * (g : FreeAmalgam R)⁻¹ →
        (Multiplicative.toAdd (φ w)) j =
          ((markedResidualProjection source f g).val.val.mulVec
            ((Multiplicative.toAdd (φ v)) j)) := by
  let W := (d.subspace (intersection s.middle)) ⧸
    (d.subspace (fixedPreimage s.middle)).comap (d.subspace (intersection s.middle)).subtype
  letI : Finite W := Finite.of_surjective
    ((d.subspace (fixedPreimage s.middle)).comap (d.subspace (intersection s.middle)).subtype).mkQ
    ((d.subspace (fixedPreimage s.middle)).comap (d.subspace (intersection s.middle)).subtype).mkQ_surjective
  let ρ := secondCRepresentation common radius f hb s hbc d
  obtain ⟨n, e, he⟩ := BinarySL2Residual.exists_natural_decomposition ρ
    (secondCRepresentation_invariants_eq_bot common radius f hb s hbc d)
  have hK : intersection s.middle ≤ V R (alpha R) := by
    rw [intersection]
    exact inf_le_left
  let φ : intersection s.middle →* Multiplicative (Fin n → Fin 2 → ZMod 2) :=
    (AddEquiv.toMultiplicative e.toAddEquiv).toMonoidHom.comp
      (d.sectionMap (intersection s.middle) (fixedPreimage s.middle) hK)
  refine ⟨n, e, φ, ?_, ?_, ?_, ?_⟩
  · exact (AddEquiv.toMultiplicative e.toAddEquiv).surjective.comp
      (d.sectionMap_surjective (intersection s.middle) (fixedPreimage s.middle) hK)
  · rw [show φ = (AddEquiv.toMultiplicative e.toAddEquiv).toMonoidHom.comp
        (d.sectionMap (intersection s.middle) (fixedPreimage s.middle) hK) by rfl,
      MonoidHom.ker_comp_of_injective
        (d.sectionMap (intersection s.middle) (fixedPreimage s.middle) hK)
        (AddEquiv.toMultiplicative e.toAddEquiv).toMonoidHom
        (AddEquiv.toMultiplicative e.toAddEquiv).injective]
    exact d.sectionMap_kernel (intersection s.middle) (fixedPreimage s.middle) hK
      (Z_le_fixedPreimage common s.first_distance)
  · intro v
    rfl
  · intro g v w j hw
    have ha := secondRepresentation_action common radius f s hbc d g v w hw
    have heq := he (markedResidualProjection source f g)
      ((d.sectionMap (intersection s.middle) (fixedPreimage s.middle) hK v).toAdd) j
    change e ((d.sectionMap (intersection s.middle) (fixedPreimage s.middle) hK w).toAdd) j =
      ((markedResidualProjection source f g).val.val.mulVec
        ((e ((d.sectionMap (intersection s.middle) (fixedPreimage s.middle) hK v).toAdd)) j))
    rw [ha]
    rw [← secondCRepresentation_apply common radius f hb s hbc d g]
    exact heq

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.LargeBranch.RankOne.Sections
