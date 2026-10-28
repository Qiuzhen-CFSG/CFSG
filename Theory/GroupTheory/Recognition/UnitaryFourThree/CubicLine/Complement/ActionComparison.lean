module
public import Theory.GroupTheory.Recognition.UnitaryFourThree.CubicLine.Complement.QuotientCoordinates

/-!
# Compatibility of the original complement and commutator-space identifications

The canonical coordinates make the original quaternion factor, cubic and
rotation have matching images. These generate the actual complements, so
faithfulness identifies the complements. Rescaling the center by the ratio
of the two form coefficients makes this quotient equivalence preserve the
original commutator pairing. The chosen cubic and rotation are preserved.

Source: Aschbacher, *Sporadic Groups* (1994), 45.11, p.248.
-/

public section
open Subgroup
namespace Theory.GroupTheory.Recognition.UnitaryFourThree.CubicGeometry.SourceConfiguration
open Theory.Representation.QuaternionSixteenTernary
variable {G : Type*} [Group G] [Finite G] {z : G} {h : IsType z}
  {P : Sylow 3 (centralizer z)} (c : SourceConfiguration h P)

noncomputable def coordinateAction (E : (c.D ⧸ center c.D) ≃* Multiplicative V) :
    c.K →* MulAut (Multiplicative V) :=
  (MulAut.congr E).toMonoidHom.comp c.complementQuotientAction

omit [Finite G] in
@[simp] theorem coordinateAction_apply (E : (c.D ⧸ center c.D) ≃* Multiplicative V)
    (k : c.K) (v : Multiplicative V) :
    c.coordinateAction E k v=E (c.complementQuotientAction k (E.symm v)) := by
  change MulAut.congr E (c.complementQuotientAction k) v=_
  rw [MulAut.congr_apply]
  rfl

theorem coordinateAction_injective (E : (c.D ⧸ center c.D) ≃* Multiplicative V) :
    Function.Injective (c.coordinateAction E) :=
  (MulAut.congr E).injective.comp c.complementQuotientAction_injective

omit [Finite G] in
private theorem range_le_of_generator_images {H : Type*} [Group H]
    (f : c.K →* H) (S : Subgroup H)
    (hC : ∀ g : c.K, (g:G)∈h.toCentralizerHypothesis.factorData.rightCore → f g∈S)
    (hY : f ⟨c.actors.y,mem_sup_left (mem_sup_right (mem_zpowers _))⟩∈S)
    (hR : f ⟨c.marking.s*c.marking.t,mem_sup_right (mem_zpowers _)⟩∈S) : f.range≤S := by
  let L := (S.comap f).map c.K.subtype
  have hCL : h.toCentralizerHypothesis.factorData.rightCore≤L := by
    intro g hg
    exact ⟨⟨g,mem_sup_left (mem_sup_left hg)⟩,hC _ hg,rfl⟩
  have hYL : (c.actors.y:G)∈L := ⟨⟨c.actors.y,mem_sup_left (mem_sup_right (mem_zpowers _))⟩,hY,rfl⟩
  have hRL : c.marking.s*c.marking.t∈L := ⟨⟨c.marking.s*c.marking.t,mem_sup_right (mem_zpowers _)⟩,hR,rfl⟩
  have hKL : c.K≤L := sup_le (sup_le hCL (zpowers_le.mpr hYL)) (zpowers_le.mpr hRL)
  rintro x ⟨g,rfl⟩
  obtain ⟨t,ht,he⟩ := hKL g.property
  have ht' : t=g := Subtype.ext he
  exact ht' ▸ ht

variable {G' : Type*} [Group G'] [Finite G'] {z' : G'} {h' : IsType z'}
  {P' : Sylow 3 (centralizer z')} (c' : SourceConfiguration h' P')

/-- Two faithful complement actions with matching images determine the actual
complement isomorphism and intertwine the literal quotient maps. -/
theorem complement_equiv_of_action_range
    (E : (c.D ⧸ center c.D) ≃* Multiplicative V)
    (E' : (c'.D ⧸ center c'.D) ≃* Multiplicative V)
    (hrange : (c.coordinateAction E).range=(c'.coordinateAction E').range) :
    ∃ eK : c.K ≃* c'.K, ∀ k v,
      E' (c'.complementQuotientAction (eK k) v)=
        E (c.complementQuotientAction k (E.symm (E' v))) := by
  let f := c.coordinateAction E
  let f' := c'.coordinateAction E'
  let eK := (MonoidHom.ofInjective (c.coordinateAction_injective E)).trans
    ((MulEquiv.subgroupCongr hrange).trans (MonoidHom.ofInjective (c'.coordinateAction_injective E')).symm)
  have heK (k : c.K) : f' (eK k)=f k := by
    change f' ((MonoidHom.ofInjective (c'.coordinateAction_injective E')).symm
      (MulEquiv.subgroupCongr hrange (MonoidHom.ofInjective (c.coordinateAction_injective E) k)))=f k
    rw [MonoidHom.apply_ofInjective_symm,MulEquiv.subgroupCongr_apply,MonoidHom.ofInjective_apply]
  refine ⟨eK,?_⟩
  intro k v
  have hh := DFunLike.congr_fun (heK k) (E' v)
  simpa only [f,f',coordinateAction_apply,MulEquiv.symm_apply_apply] using hh
end Theory.GroupTheory.Recognition.UnitaryFourThree.CubicGeometry.SourceConfiguration

public section
open Subgroup
namespace Theory.GroupTheory.Recognition.UnitaryFourThree.CubicGeometry.SourceConfiguration
open Theory.Representation.QuaternionSixteenTernary
variable {G : Type*} [Group G] [Finite G] {z : G} {h : IsType z}
  {P : Sylow 3 (centralizer z)} (c : SourceConfiguration h P)
  {G' : Type*} [Group G'] [Finite G'] {z' : G'} {h' : IsType z'}
  {P' : Sylow 3 (centralizer z')} (c' : SourceConfiguration h' P')

omit [Finite G] [Finite G'] in
private theorem coordinateAction_eq_of_equations
    (E : (c.D ⧸ center c.D) ≃* Multiplicative V)
    (E' : (c'.D ⧸ center c'.D) ≃* Multiplicative V) (g : c.K) (g' : c'.K) (F : V → V)
    (hE : ∀ v, (E (c.complementQuotientAction g v)).toAdd=F (E v).toAdd)
    (hE' : ∀ v, (E' (c'.complementQuotientAction g' v)).toAdd=F (E' v).toAdd) :
    c.coordinateAction E g=c'.coordinateAction E' g' := by
  apply MulEquiv.ext
  intro v
  apply Multiplicative.toAdd.injective
  simp only [coordinateAction_apply,hE,hE',MulEquiv.apply_symm_apply]

/-- The actual source configurations have compatible quotient, center and
complement identifications, with their selected cubic and rotation preserved. -/
theorem exists_pairing_action_equivalences :
    ∃ (eQ : (c.D ⧸ center c.D) ≃* (c'.D ⧸ center c'.D))
      (eZ : center c.D ≃* center c'.D) (eK : c.K ≃* c'.K),
      (∀ x y, eZ (c.oddCommutatorPairing x y)=c'.oddCommutatorPairing (eQ x) (eQ y)) ∧
      (∀ k v, eQ (c.complementQuotientAction k v)=c'.complementQuotientAction (eK k) (eQ v)) ∧
      eK ⟨c.actors.y,mem_sup_left (mem_sup_right (mem_zpowers _))⟩=
        ⟨c'.actors.y,mem_sup_left (mem_sup_right (mem_zpowers _))⟩ ∧
      eK ⟨c.marking.s*c.marking.t,mem_sup_right (mem_zpowers _)⟩=
        ⟨c'.marking.s*c'.marking.t,mem_sup_right (mem_zpowers _)⟩ := by
  obtain ⟨E,b,hb,hR,hY,hC,hC',hB⟩ := c.exists_quotient_pairing_coordinates
  obtain ⟨E',b',hb',hR',hY',hD,hD',hB'⟩ := c'.exists_quotient_pairing_coordinates
  let f := c.coordinateAction E
  let f' := c'.coordinateAction E'
  have hr : (c.coordinateAction E).range=(c'.coordinateAction E').range := by
    apply le_antisymm
    · apply c.range_le_of_generator_images f f'.range
      · intro g hg
        obtain ⟨j,hj⟩ := hC g hg
        obtain ⟨g',_,hg'⟩ := hD' j
        exact ⟨g',(c.coordinateAction_eq_of_equations c' E E' g g' (q j) hj hg').symm⟩
      · exact ⟨_,(c.coordinateAction_eq_of_equations c' E E' _ _ (lin y0) hY hY').symm⟩
      · exact ⟨_,(c.coordinateAction_eq_of_equations c' E E' _ _ r hR hR').symm⟩
    · apply c'.range_le_of_generator_images f' f.range
      · intro g hg
        obtain ⟨j,hj⟩ := hD g hg
        obtain ⟨g',_,hg'⟩ := hC' j
        exact ⟨g',(c'.coordinateAction_eq_of_equations c E' E g g' (q j) hj hg').symm⟩
      · exact ⟨_,(c'.coordinateAction_eq_of_equations c E' E _ _ (lin y0) hY' hY).symm⟩
      · exact ⟨_,(c'.coordinateAction_eq_of_equations c E' E _ _ r hR' hR).symm⟩
  obtain ⟨eK,heK⟩ := c.complement_equiv_of_action_range c' E E' hr
  let eQ := E.trans E'.symm
  let scale : ZMod 3 ≃+ ZMod 3 :=
    (LinearEquiv.smulOfNeZero (ZMod 3) (ZMod 3) (b'/b) (div_ne_zero hb' hb)).toAddEquiv
  let eZ := c.oddCenterCoordinate.trans (scale.toMultiplicative.trans c'.oddCenterCoordinate.symm)
  have heQ (v) : E' (eQ v)=E v := by simp only [eQ,MulEquiv.trans_apply,MulEquiv.apply_symm_apply]
  have heZ (v) : (c'.oddCenterCoordinate (eZ v)).toAdd=(b'/b)*(c.oddCenterCoordinate v).toAdd := by
    simp only [eZ,MulEquiv.trans_apply,MulEquiv.apply_symm_apply]
    rfl
  have ha (k v) : eQ (c.complementQuotientAction k v)=c'.complementQuotientAction (eK k) (eQ v) := by
    apply E'.injective
    rw [heQ,heK,heQ,MulEquiv.symm_apply_apply]
  have mark (g : c.K) (g' : c'.K) (F : V→V)
      (hg : ∀ v, (E (c.complementQuotientAction g v)).toAdd=F (E v).toAdd)
      (hg' : ∀ v, (E' (c'.complementQuotientAction g' v)).toAdd=F (E' v).toAdd) : eK g=g' := by
    apply c'.complementQuotientAction_injective
    apply MulEquiv.ext
    intro v
    apply E'.injective
    apply Multiplicative.toAdd.injective
    rw [heK,hg,hg',MulEquiv.apply_symm_apply]
  refine ⟨eQ,eZ,eK,?_,ha,mark _ _ (lin y0) hY hY',mark _ _ r hR hR'⟩
  intro x y
  apply c'.oddCenterCoordinate.injective
  apply Multiplicative.toAdd.injective
  rw [heZ,hB,hB',heQ,heQ]
  field_simp
end Theory.GroupTheory.Recognition.UnitaryFourThree.CubicGeometry.SourceConfiguration
