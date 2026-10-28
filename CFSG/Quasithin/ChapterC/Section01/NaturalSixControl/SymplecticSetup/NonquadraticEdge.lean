module
public import CFSG.Quasithin.ChapterC.Section01.NaturalSixControl.SymplecticSetup.EdgeOffenders
public import Theory.SpecificGroups.SymmetricSix.BinaryFlags.QuadraticPointCore.Conjugation

/-!
# Nonquadratic action on native symplectic edges

The full point radical has order eight, whereas a quadratic subgroup of its
actual natural symmetric-six action has order at most four. Source coordinates
therefore show that the second commutator [W,R,R] is nontrivial. The faithful
amalgam embedding and edge conjugation transport this obstruction to [U_a,Q_t,Q_t]
on every edge with a symplectic endpoint. Since the maximal-offender join is
Q_t, it cannot act quadratically either.

The final theorem retains the literal characteristic replacement and its
point marking. It supplies the terminal contradiction when the source path
argument forces this action to be quadratic.

Source: MS93 (5.10), (5.12), printed pp.922--925; the finite natural-module
calculation is the quadratic point-core bound used in Aschbacher--Smith 13.5.7.
-/

public section
open Subgroup Theory.GroupTheory BinaryPermutation
open Theory.SpecificGroups.SymmetricSix.BinaryFlags
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
open scoped commutatorElement
namespace CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup.Source
variable {M : Type*} [Group M] [Finite M] {L R W : Subgroup M} [L.Normal] [W.Normal]
  (s : Source L R W)

omit [Finite M] in
private theorem nonquadratic_commutator_coordinates (a : M) (w : W) :
    (s.coordinates ⟨⁅a,(w : M)⁆,W.mul_mem
      ((inferInstance : W.Normal).conj_mem _ w.property a) (W.inv_mem w.property)⟩).toAdd =
      Model.rho (s.projection a) (s.coordinates w).toAdd-(s.coordinates w).toAdd := by
  have he : (⟨⁅a,(w : M)⁆,W.mul_mem
      ((inferInstance : W.Normal).conj_mem _ w.property a) (W.inv_mem w.property)⟩ : W) =
      MulAut.conjNormal a w*w⁻¹ := by
    apply Subtype.ext
    rfl
  rw [he,map_mul,map_inv]
  simp only [toAdd_mul,toAdd_inv,s.action,sub_eq_add_neg]

omit [Finite M] in
/-- The full point-radical image is not quadratic on the actual source module. -/
theorem module_double_commutator_ne_bot (u : Model.S)
    (hfull : R.map s.projection = Model.E.map (MulAut.conj u).toMonoidHom) :
    ⁅⁅W,R⁆,R⁆ ≠ ⊥ := by
  intro hzero
  have hcentral := commutator_eq_bot_iff_le_centralizer.mp hzero
  have hquad : QuadraticPointCore.Quadratic (R.map s.projection) := by
    rintro _ ⟨a,ha,rfl⟩ _ ⟨b,hb,rfl⟩ v
    let w := s.coordinates.symm (Multiplicative.ofAdd v)
    have hzW : ⁅b,(w:M)⁆∈W := W.mul_mem
      ((inferInstance : W.Normal).conj_mem _ w.property b) (W.inv_mem w.property)
    let z : W := ⟨⁅b,(w:M)⁆,hzW⟩
    have hzR : (z:M)∈⁅W,R⁆ := by
      rw [commutator_comm]
      exact commutator_mem_commutator hb w.property
    have hz : MulAut.conjNormal a z=z := by
      apply Subtype.ext
      change a*(z:M)*a⁻¹=(z:M)
      rw [hcentral hzR a ha,mul_inv_cancel_right]
    have hcz : (s.coordinates z).toAdd=Model.rho (s.projection b) v-v := by
      change (s.coordinates ⟨⁅b,(w:M)⁆,hzW⟩).toAdd=_
      rw [s.nonquadratic_commutator_coordinates]
      simp only [w,MulEquiv.apply_symm_apply]
      rfl
    have hact := s.action a z
    rw [hz,hcz] at hact
    exact hact.symm
  have hbound := QuadraticPointCore.conjugate_core_bound (R.map s.projection) u
    (by rw [Model.pointCore_eq_exceptional]; exact hfull.le) hquad
  rw [hfull,card_map_of_injective (MulAut.conj u).injective,
    ←Model.pointCore_eq_exceptional,pointCore_card] at hbound
  omega

/-- The actual edge kernel has nonzero double commutator on its natural layer. -/
theorem edge_double_commutator_ne_bot (h : NativeCentralLayer s) (u : Model.S)
    (hfull : R.map s.projection = Model.E.map (MulAut.conj u).toMonoidHom)
    {a t : Vertex R} (ha : color R a = false) (hat : Adjacent R a t) :
    ⁅⁅U R a,Q R t⁆,Q R t⁆ ≠ ⊥ := by
  have hbase : ⁅⁅U R (alpha R),Q R (beta R)⁆,Q R (beta R)⁆ ≠ ⊥ := by
    rw [h.U_eq_module,Q_beta,←map_commutator,←map_commutator]
    intro hz
    apply s.module_double_commutator_ne_bot u hfull
    apply map_injective (embedM_injective R)
    simpa only [Subgroup.map_bot] using hz
  obtain ⟨g,hg|hg⟩ := (adjacent_iff_exists_common R a t).mp hat
  · rcases hg with ⟨rfl,rfl⟩
    intro hz
    apply hbase
    apply map_injective (f := (MulAut.conj g⁻¹).toMonoidHom) (MulAut.conj g⁻¹).injective
    rw [map_commutator,map_commutator,←U_act,←Q_act]
    simp only [alpha,beta,act_mVertex,act_hVertex,one_mul,Subgroup.map_bot]
    exact hz
  · rw [hg.1] at ha
    cases ha

/-- The maximal-offender join on the same edge cannot act quadratically. -/
theorem edgeOffenderJoin_double_commutator_ne_bot (h : NativeCentralLayer s) (u : Model.S)
    (hfull : R.map s.projection = Model.E.map (MulAut.conj u).toMonoidHom)
    {a t : Vertex R} (ha : color R a = false) (hat : Adjacent R a t) :
    ⁅⁅U R a,edgeOffenderJoin a t⁆,edgeOffenderJoin a t⁆ ≠ ⊥ := by
  rw [s.edgeOffenderJoin_eq h u hfull ha hat]
  exact s.edge_double_commutator_ne_bot h u hfull ha hat

end CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup.Source

namespace CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup.SourceData
variable {K : Type*} [Group K] [Finite K] {L V : Subgroup K} [L.Normal] [V.Normal]
  {T : Sylow 2 K} (d : NaturalSixControl.SourceData L V T)

/-- Each literal replacement either gives the alternating block or has the
nonquadratic obstruction on every symplectic edge. -/
theorem reducedSource_block_or_nonquadratic_edges (h : IntrinsicMSPair d)
    (r : CharacteristicReduction (L.subgroupOf (L⊔d.B)) (d.B.subgroupOf (L⊔d.B))) :
    IsAlternatingBlock L 6 ∨ ∀ (a t : Vertex r.radical), color r.radical a=false →
      Adjacent r.radical a t →
      ⁅⁅U r.radical a,Q r.radical t⁆,Q r.radical t⁆≠⊥ ∧
      ⁅⁅U r.radical a,edgeOffenderJoin a t⁆,edgeOffenderJoin a t⁆≠⊥ := by
  rcases reducedSource_block_or_full_point_image d h r with hb|hf
  · exact Or.inl hb
  · rw [Model.pointCore_eq_exceptional] at hf
    refine Or.inr (fun a t ha hat => ⟨?_,?_⟩)
    · exact Source.edge_double_commutator_ne_bot ((originalSource d h).reduce r)
        (reduced_nativeCentralLayer d h r) d.relabeler.val⁻¹ hf ha hat
    · exact Source.edgeOffenderJoin_double_commutator_ne_bot ((originalSource d h).reduce r)
        (reduced_nativeCentralLayer d h r) d.relabeler.val⁻¹ hf ha hat

end CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup.SourceData
