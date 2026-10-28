module

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.PairedOffenders.QuotientGeometry.Consequences
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.PairedOffenders.QuotientGeometry.Conjugation
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.PairedOffenders.QuotientGeometry.ParabolicModel

/-!
# Assembling the paired quotient calculations for local actions

A genuine equivalence with the two-block parabolic transports its intrinsic
 two-core to the concrete Klein-four product. A commuting action diagram then
 supplies the block-kernel identity required by the quotient rank calculations.

The local quotient diagrams used for conjugation also give the Sylow diagrams
 used for ranks, by restricting attention to the whole local actor group.
 Thus the two actions need only be defined on S. The proved SD16 interchange
 and the actual GL2(3) Sylow equivalence yield a strict upper bound against the
 two natural fixed codimensions. An inner quotient conjugator gives the same
 strict bound in every common case except disjoint transpositions. In that
 remaining case the bound is six, the sum of the actual fixed codimensions.

These bounds feed `paired_offender_rank_inequality` and
 `paired_replacement_mem_max` in the parent assembly. The actual parabolic
 identifications, action-kernel identities and conjugation diagrams are explicit
 inputs; no quotient position, rank tuple or case pairing is assumed here.
 The source theorem's eliminations and terminal assembly remain with the parent.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), proof of
 15.3.25, printed pp.1133–1134 (PDF pp.1150–1151).
-/

@[expose] public section

open Subgroup Representation.BinaryOffender BinaryPermutation
open CFSG.Quasithin.ChapterB.Offenders
open CFSG.Quasithin.ChapterB.Offenders.Eight

namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.PairedQuotient

variable {G H K : Type*} [Group G] [Group H] [Group K]

/-- Every genuine identification with the two-block parabolic transports its
intrinsic two-core to the concrete Klein-four product. -/
theorem parabolic_core_image (e : K ≃* parabolic) :
    (pCore 2 K).map (parabolic.subtype.comp e.toMonoidHom) = blockCore := by
  rw [← map_map, pCore_map_iso]
  exact parabolic_pCoreIn

/-- The actual action diagram and the core identity in its parabolic quotient
give the block-kernel identity used by the numerical calculations. -/
theorem kernel_image_of_parabolic_equiv
    (f : G →* Perm) (q : G →* H) (a : G →* K) (e : K ≃* parabolic)
    (hact : ∀ x, f x = (e (a x) : Perm))
    (hcore : q.ker.map a = pCore 2 K) : q.ker.map f = blockCore := by
  have hf : f = (parabolic.subtype.comp e.toMonoidHom).comp a :=
    MonoidHom.ext hact
  rw [hf, ← map_map, hcore]
  exact parabolic_core_image e

namespace Conjugation.LocalCoordinates

variable {f g : G →* Perm} {q : G →* H}

/-- A surjective local quotient diagram is a Sylow diagram with the whole local
actor group as domain. This requires no action on its module-swapping overgroup. -/
def toSylowCoordinates (d : LocalCoordinates f q) (hq : Function.Surjective q) :
    SylowCoordinates ⊤ f q where
  action_le := by rw [← MonoidHom.range_eq_map]; exact d.action_le
  quotientEquiv :=
    ((MulEquiv.subgroupCongr (by
      rw [← MonoidHom.range_eq_map, MonoidHom.range_eq_top.mpr hq])).trans
        Subgroup.topEquiv).trans d.quotientEquiv
  compatible s := d.compatible s

/-- The two exact ranks for an action defined only on the local actor group. -/
theorem ranks_of_realizes (d : LocalCoordinates f q) (hq : Function.Surjective q)
    {A : Subgroup G} {c : EightCase}
    (hP : q.ker.map f = blockCore) (hA : c.Realizes (A.map f)) :
    rank (A.map q) = quotientRank c ∧
      rank (A.map f ⊓ q.ker.map f) = kernelRank c :=
  (d.toSylowCoordinates hq).ranks_of_realizes le_top hP hA

/-- The three source ranks are bounded using the two local action diagrams. -/
theorem paired_rank_bound (d : LocalCoordinates f q) (e : LocalCoordinates g q)
    (hq : Function.Surjective q) {A : Subgroup G} {c c' : EightCase}
    (hP : q.ker.map f = blockCore) (hP' : q.ker.map g = blockCore)
    (hA : c.Realizes (A.map f)) (hA' : c'.Realizes (A.map g)) :
    rank (A.map q) + rank (A.map f ⊓ q.ker.map f) + rank ((A ⊓ q.ker).map g) ≤
      quotientRank c + kernelRank c + kernelRank c' :=
  paired_rank_bound_of_realizes (d.toSylowCoordinates hq) (e.toSylowCoordinates hq)
    le_top hP hP' hA hA'

/-- In the semidihedral extension, the proved conjugation comparison forces a
strict bound against the actual two natural fixed codimensions. -/
theorem paired_rank_lt_of_semidihedral
    (d : LocalCoordinates f q) (e : LocalCoordinates g q)
    (hq : Function.Surjective q) (σ : MulAut G) (α : MulAut H)
    (hquot : ∀ s, q (σ s) = α (q s)) (r : Perm)
    (hact : ∀ s, g (σ s) = r * f s * r⁻¹)
    (v : K ≃* SD16) (j : H →* K) (hj : Function.Injective j)
    (t : K) (ht : t ∉ j.range) (hconj : ∀ x, j (α x) = t * j x * t⁻¹)
    {A : Subgroup G} {c c' : EightCase}
    (hP : q.ker.map f = blockCore) (hP' : q.ker.map g = blockCore)
    (hA : c.Realizes (A.map f)) (hA' : c'.Realizes (A.map g)) :
    rank (A.map q) + rank (A.map f ⊓ q.ker.map f) + rank ((A ⊓ q.ker).map g) <
      fixedCodim (naturalRepresentation (Fin 8)) (A.map f) +
        fixedCodim (naturalRepresentation (Fin 8)) (A.map g) := by
  rw [(EightCase.dimensions hA).2, (EightCase.dimensions hA').2]
  have hc := d.cases_of_semidihedral e hq σ α hquot r hact v j hj t ht hconj hA hA'
  rcases hc with hc | hc | ⟨rfl, rfl⟩
  · exact paired_rank_lt_of_regular_transposition
      (d.toSylowCoordinates hq) (e.toSylowCoordinates hq) le_top hP hP' hA hA' (Or.inl hc)
  · exact paired_rank_lt_of_regular_transposition
      (d.toSylowCoordinates hq) (e.toSylowCoordinates hq) le_top hP hP' hA hA' (Or.inr hc)
  · exact paired_rank_lt_of_same_case
      (d.toSylowCoordinates hq) (e.toSylowCoordinates hq) le_top hP hP' hA hA' (by decide)

/-- The larger quotient can be specified as an actual Sylow subgroup of GL2(3).
Its semidihedral comparison and all case restrictions are proved, not inputs. -/
theorem paired_rank_lt_of_GL2_three
    (d : LocalCoordinates f q) (e : LocalCoordinates g q)
    (hq : Function.Surjective q) (σ : MulAut G) (α : MulAut H)
    (hquot : ∀ s, q (σ s) = α (q s)) (r : Perm)
    (hact : ∀ s, g (σ s) = r * f s * r⁻¹)
    (P : Sylow 2 (GL (Fin 2) (ZMod 3))) (v : K ≃* P)
    (j : H →* K) (hj : Function.Injective j)
    (t : K) (ht : t ∉ j.range) (hconj : ∀ x, j (α x) = t * j x * t⁻¹)
    {A : Subgroup G} {c c' : EightCase}
    (hP : q.ker.map f = blockCore) (hP' : q.ker.map g = blockCore)
    (hA : c.Realizes (A.map f)) (hA' : c'.Realizes (A.map g)) :
    rank (A.map q) + rank (A.map f ⊓ q.ker.map f) + rank ((A ⊓ q.ker).map g) <
      fixedCodim (naturalRepresentation (Fin 8)) (A.map f) +
        fixedCodim (naturalRepresentation (Fin 8)) (A.map g) := by
  obtain ⟨pSD⟩ := GL2_three_sylow_equiv P
  exact d.paired_rank_lt_of_semidihedral e hq σ α hquot r hact
    (v.trans pSD) j hj t ht hconj hP hP' hA hA'

/-- When the quotient conjugator is internal, conjugation gives equal cases;
every case except disjoint transpositions has a strict numerical bound. -/
theorem paired_rank_lt_of_inner
    (d : LocalCoordinates f q) (e : LocalCoordinates g q)
    (hq : Function.Surjective q) (σ : MulAut G) (α : MulAut H)
    (hquot : ∀ s, q (σ s) = α (q s)) (r : Perm)
    (hact : ∀ s, g (σ s) = r * f s * r⁻¹)
    (j : H →* K) (hj : Function.Injective j)
    (t : K) (ht : t ∈ j.range) (hconj : ∀ x, j (α x) = t * j x * t⁻¹)
    {A : Subgroup G} {c c' : EightCase}
    (hP : q.ker.map f = blockCore) (hP' : q.ker.map g = blockCore)
    (hA : c.Realizes (A.map f)) (hA' : c'.Realizes (A.map g)) (hc : c ≠ .disjoint) :
    rank (A.map q) + rank (A.map f ⊓ q.ker.map f) + rank ((A ⊓ q.ker).map g) <
      fixedCodim (naturalRepresentation (Fin 8)) (A.map f) +
        fixedCodim (naturalRepresentation (Fin 8)) (A.map g) := by
  have he := d.cases_of_inner e hq σ α hquot r hact j hj t ht hconj hA hA'
  subst c'
  rw [(EightCase.dimensions hA).2, (EightCase.dimensions hA').2]
  exact paired_rank_lt_of_same_case
    (d.toSylowCoordinates hq) (e.toSylowCoordinates hq) le_top hP hP' hA hA' hc

/-- In the disjoint/disjoint case the upper bound is six, the sum of the actual
fixed codimensions. This is the numerical input for paired replacement. -/
theorem disjoint_replacement_bound
    (d : LocalCoordinates f q) (e : LocalCoordinates g q)
    (hq : Function.Surjective q) {A : Subgroup G}
    (hP : q.ker.map f = blockCore) (hP' : q.ker.map g = blockCore)
    (hA : EightCase.disjoint.Realizes (A.map f))
    (hA' : EightCase.disjoint.Realizes (A.map g)) :
    rank (A.map q) + rank (A.map f ⊓ q.ker.map f) + rank ((A ⊓ q.ker).map g) ≤
      fixedCodim (naturalRepresentation (Fin 8)) (A.map f) +
        fixedCodim (naturalRepresentation (Fin 8)) (A.map g) := by
  rw [(EightCase.dimensions hA).2, (EightCase.dimensions hA').2]
  exact d.paired_rank_bound e hq hP hP' hA hA'

end Conjugation.LocalCoordinates
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.PairedQuotient

end
