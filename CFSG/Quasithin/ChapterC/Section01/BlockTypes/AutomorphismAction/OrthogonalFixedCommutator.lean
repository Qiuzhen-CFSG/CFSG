module

public import CFSG.Quasithin.ChapterC.Section01.BlockTypes.AutomorphismAction.OrthogonalInvolutionCoordinates
public import Theory.Representation.SL2OrthogonalCover.FixedSylowCommutatorRows

/-!
# Literal ambient commutators from orthogonal involution coordinates

The coordinate packet embeds the universal orthogonal cover into the original
ambient group through the actual two-core and block inclusions. Its equivariance
identities identify model root actions with conjugation by the original root
lifts and make each fixed lift commute with the semilinear actor.

Two distinct fixed nonidentity roots generate every fixed vector of the Sylow
fixed plane by commutators inside the ambient fixed subgroup. A single root
always supplies a nonsingular fixed commutator whose coordinate is outside the
orthogonal radical: its displacement line and the radical are distinct lines.
These conclusions retain the original core element, quotient map, and ambient
subgroup commutator, including the field-four exception.

Source: Aschbacher–Smith, the field-involution cases of Lemma 2.4.21,
printed p.536, using the orthogonal geometry of I.2.3 and 2.4.12(2).
-/

public section
noncomputable section

open Subgroup Representation Representation.OneCohomology
open scoped commutatorElement
namespace CFSG.Quasithin.ChapterC.OrthogonalInvolutionCoordinates
variable {G : Type*} [Group G] {L : Subgroup G} {n : ℕ} {b : MulAut L}
variable (c : OrthogonalInvolutionCoordinates L n b)

/-- The literal embedding through the two-core and block inclusions. -/
@[expose] def ambientCore : Multiplicative (SL2OrthogonalCover.Space c.F) →* G :=
  L.subtype.comp ((pCore 2 L).subtype.comp c.core.symm.toMonoidHom)

/-- Coordinates recover the original ambient core element. -/
theorem ambientCore_core (u : pCore 2 L) :
    c.ambientCore (c.core u) = ((u : L) : G) := by
  change ((c.core.symm (c.core u) : L) : G) = _
  rw [c.core.symm_apply_apply]

/-- A model root acts by its actual block lift under the ambient embedding. -/
theorem ambientCore_conjugation (r : L) (v : SL2OrthogonalCover.Space c.F) :
    c.ambientCore (Multiplicative.ofAdd (SL2OrthogonalCover.action
      (c.quotient (QuotientGroup.mk' (pCore 2 L) r)) v)) =
      (r : G) * c.ambientCore (Multiplicative.ofAdd v) * (r : G)⁻¹ := by
  let u := c.core.symm (Multiplicative.ofAdd v)
  have he := c.conjugation_equivariant r u
  have heu : (c.core u).toAdd = v := congrArg Multiplicative.toAdd (c.core.apply_symm_apply _)
  rw [heu] at he
  have hm : c.core (MulAut.conjNormal r u) = Multiplicative.ofAdd
      (SL2OrthogonalCover.action (c.quotient (QuotientGroup.mk' (pCore 2 L) r)) v) :=
    Multiplicative.ext he
  rw [←hm,c.ambientCore_core]
  rfl

/-- The transported actor is the original ambient conjugation action. -/
theorem ambientCore_actor (a : G) (hb : ∀ l : L, (b l : G) = a*l*a⁻¹)
    (v : SL2OrthogonalCover.Space c.F) :
    c.ambientCore (Multiplicative.ofAdd (c.actor v)) =
      a * c.ambientCore (Multiplicative.ofAdd v) * a⁻¹ := by
  let u := c.core.symm (Multiplicative.ofAdd v)
  have he := c.core_equivariant u
  have heu : (c.core u).toAdd = v := congrArg Multiplicative.toAdd (c.core.apply_symm_apply _)
  rw [heu] at he
  have hm : c.core (MulAut.characteristic (pCore 2 L) b u) =
      Multiplicative.ofAdd (c.actor v) := Multiplicative.ext he
  rw [←hm,c.ambientCore_core]
  exact hb u.val

/-- A fixed block lift induces a root action commuting with the packet actor. -/
theorem actor_commutes_of_fixed (r : L) (hr : b r = r) :
    ∀ v, c.actor (SL2OrthogonalCover.action
      (c.quotient (QuotientGroup.mk' (pCore 2 L) r)) v) =
      SL2OrthogonalCover.action (c.quotient (QuotientGroup.mk' (pCore 2 L) r)) (c.actor v) := by
  intro v
  rw [c.normalizer_equivariant]
  have hq : MulAut.congr c.quotient (quotientAut (pCore 2 L) b)
      (c.quotient (QuotientGroup.mk' (pCore 2 L) r)) =
        c.quotient (QuotientGroup.mk' (pCore 2 L) r) := by
    change c.quotient (quotientAut (pCore 2 L) b
      (c.quotient.symm (c.quotient (QuotientGroup.mk' (pCore 2 L) r)))) = _
    rw [c.quotient.symm_apply_apply,quotientAut_apply_mk,hr]
  rw [hq]

/-- Fixedness in the original core is equivalent to fixedness of its coordinate. -/
theorem core_fixed_iff (u : pCore 2 L) :
    MulAut.characteristic (pCore 2 L) b u = u ↔
      c.actor (c.core u).toAdd = (c.core u).toAdd := by
  rw [←c.core_equivariant]
  exact (Multiplicative.toAdd.injective.comp c.core.injective).eq_iff.symm

private theorem fixed_image_mem (I : Subgroup G)
    (hq : ∀ u : pCore 2 L, MulAut.characteristic (pCore 2 L) b u = u → ((u : L) : G) ∈ I) :
    ∀ v, c.actor v = v → c.ambientCore (Multiplicative.ofAdd v) ∈ I := by
  intro v hv
  let u := c.core.symm (Multiplicative.ofAdd v)
  apply hq u
  apply (c.core_fixed_iff u).mpr
  change c.actor (c.core (c.core.symm (Multiplicative.ofAdd v))).toAdd =
    (c.core (c.core.symm (Multiplicative.ofAdd v))).toAdd
  rw [c.core.apply_symm_apply]
  exact hv

/-- Two fixed root lifts put every fixed core element in the Sylow fixed plane
into the literal ambient subgroup commutator. -/
theorem fixed_core_mem_commutator_of_two_roots
    (I : Subgroup G)
    (hq : ∀ u : pCore 2 L, MulAut.characteristic (pCore 2 L) b u = u → ((u : L) : G) ∈ I)
    (P : Sylow 2 (SL2OrthogonalCover.SL c.F))
    (r t : L) (hr : (r : G) ∈ I) (ht : (t : G) ∈ I)
    (hbr : b r = r) (hbt : b t = t)
    (hrP : c.quotient (QuotientGroup.mk' (pCore 2 L) r) ∈ P)
    (htP : c.quotient (QuotientGroup.mk' (pCore 2 L) t) ∈ P)
    (hr1 : c.quotient (QuotientGroup.mk' (pCore 2 L) r) ≠ 1)
    (ht1 : c.quotient (QuotientGroup.mk' (pCore 2 L) t) ≠ 1)
    (hrt : c.quotient (QuotientGroup.mk' (pCore 2 L) r) ≠
      c.quotient (QuotientGroup.mk' (pCore 2 L) t))
    (u : pCore 2 L) (hu : MulAut.characteristic (pCore 2 L) b u = u)
    (huP : (c.core u).toAdd ∈ fixed
      ((SL2OrthogonalCover.action (F := c.F)).comp P.toSubgroup.subtype)) :
    ((u : L) : G) ∈ ⁅I,I⁆ := by
  have hh := SL2OrthogonalCover.fixed_sylow_mem_commutator c.coefficient
    c.coefficient_involutive c.coefficient_ne c.actor c.actor_involutive c.semilinear
    P _ _ hrP htP hr1 ht1 hrt (c.actor_commutes_of_fixed r hbr) (c.actor_commutes_of_fixed t hbt)
    I c.ambientCore (c.fixed_image_mem I hq) r.val t.val hr ht
    (c.ambientCore_conjugation r) (c.ambientCore_conjugation t)
    (c.core u).toAdd huP ((c.core_fixed_iff u).mp hu)
  change c.ambientCore (c.core u) ∈ ⁅I,I⁆ at hh
  rwa [c.ambientCore_core] at hh


private theorem displacement_not_radical
    (P : Sylow 2 (SL2OrthogonalCover.SL c.F)) (g : SL2OrthogonalCover.SL c.F)
    (hg : g ∈ P) (hg1 : g ≠ 1) (v : SL2OrthogonalCover.Space c.F)
    (hvm : v ∈ SL2OrthogonalCover.movedSpace g) (hvf : SL2OrthogonalCover.form v ≠ 0) :
    v ∉ (SL2OrthogonalCover.form (F := c.F)).polarBilin.ker := by
  have hv0 : v ≠ 0 := by
    intro h
    apply hvf
    rw [h,QuadraticMap.map_zero]
  have hd := SL2OrthogonalCover.sylow_displacement_geometry P g hg hg1
  intro hvr
  have hm : Submodule.span c.F {v} = SL2OrthogonalCover.movedSpace g :=
    Submodule.eq_of_le_of_finrank_eq
      (Submodule.span_le.mpr (Set.singleton_subset_iff.mpr hvm))
      ((finrank_span_singleton hv0).trans hd.1.symm)
  have hr : Submodule.span c.F {v} = (SL2OrthogonalCover.form (F := c.F)).polarBilin.ker :=
    Submodule.eq_of_le_of_finrank_eq
      (Submodule.span_le.mpr (Set.singleton_subset_iff.mpr hvr))
      ((finrank_span_singleton hv0).trans SL2OrthogonalCover.radical_dimension.symm)
  exact hd.2.2.2 (hm.symm.trans hr)

/-- A single fixed nonidentity root supplies an actual nonsingular fixed core
commutator outside the orthogonal radical, including the smallest field case. -/
theorem exists_fixed_core_nonsingular_commutator
    (I : Subgroup G)
    (hq : ∀ u : pCore 2 L, MulAut.characteristic (pCore 2 L) b u = u → ((u : L) : G) ∈ I)
    (P : Sylow 2 (SL2OrthogonalCover.SL c.F))
    (r : L) (hr : (r : G) ∈ I) (hbr : b r = r)
    (hrP : c.quotient (QuotientGroup.mk' (pCore 2 L) r) ∈ P)
    (hr1 : c.quotient (QuotientGroup.mk' (pCore 2 L) r) ≠ 1) :
    ∃ u : pCore 2 L, MulAut.characteristic (pCore 2 L) b u = u ∧
      (c.core u).toAdd ∈ SL2OrthogonalCover.movedSpace
        (c.quotient (QuotientGroup.mk' (pCore 2 L) r)) ∧
      SL2OrthogonalCover.form (c.core u).toAdd ≠ 0 ∧
      (c.core u).toAdd ∉ (SL2OrthogonalCover.form (F := c.F)).polarBilin.ker ∧
      ((u : L) : G) ∈ ⁅I,I⁆ := by
  obtain ⟨v,hv,hvm,hvf,hvI⟩ := SL2OrthogonalCover.exists_fixed_sylow_commutator
    c.coefficient c.coefficient_involutive c.coefficient_ne c.actor c.actor_involutive
    c.semilinear P _ hrP hr1 (c.actor_commutes_of_fixed r hbr)
    I c.ambientCore (c.fixed_image_mem I hq) r.val hr (c.ambientCore_conjugation r)
  let u := c.core.symm (Multiplicative.ofAdd v)
  have heu : (c.core u).toAdd = v := congrArg Multiplicative.toAdd (c.core.apply_symm_apply _)
  refine ⟨u, (c.core_fixed_iff u).mpr ?_, ?_, ?_, ?_, hvI⟩
  · rwa [heu]
  · rwa [heu]
  · rwa [heu]
  · rw [heu]
    exact c.displacement_not_radical P _ hrP hr1 v hvm hvf
end CFSG.Quasithin.ChapterC.OrthogonalInvolutionCoordinates
