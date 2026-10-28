module
public import CFSG.Quasithin.ChapterI.Section04To05.G2Recognition.MaximalCubicForms
public import Theory.SpecificGroups.G2.TernaryEndpointCoordinates
public import CFSG.Quasithin.ChapterI.Section04To05.G2Recognition.AtlasEndpointActions

/-!
# Full Atlas actions on the original cubic cores

The original marked central involution maps to -I in the actual GL₂(3)
Levi quotient and inverts the entire abelianization. The original center
plane is exactly the radical of the scalar commutator form. Consequently
the Weyl normalization applies to the already simultaneous cubic/form
coordinates, retaining their opposite-core actor and opposite derived line.
No Weyl equation or full representation comparison is assumed.

The resulting coordinates identify both complete GL₂(3) actions. The
short-to-long transport uses its actual determinant twist. Applying the
construction to each original core supplies both endpoint comparisons;
the right endpoint retains the previously constructed Sylow aligner.
Chapter14WeylCoordinates constructs both endpoint isomorphisms from these
comparisons. Their restrictions to the whole common middle must still be
matched before completion recognition; the strongly-three-embedded source
branch remains independent. Source: Aschbacher–Smith I.4.5, printed p.417.
-/

public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.ChapterI.Section04To05.G2Recognition
open Chapter14.Section04.DimensionFour
variable {G : Type*} [Group G] [Finite G] {c : G2ThreeConfiguration G}
namespace CubicTorus
variable (t : CubicTorus c)

theorem cubicGLAbelianizationAction_central (hc : Nat.card (cubicOddCore c t.x)=243)
    (v : cubicOddCore c t.x ⧸ cubicCoreLine c t.x) :
    t.cubicGLAbelianizationAction hc (-1) v=v⁻¹ := by
  let z : t.leftCubicLevi := ⟨t.z,mem_sup_left (mem_map_of_mem c.H.subtype
    ((t.central_line ▸ mem_zpowers t.z).2))⟩
  have hz2 : z*z=1 := by
    apply Subtype.ext
    change (t.z:G)*(t.z:G)=1
    exact congrArg (fun x : c.H=>(x:G)) (show t.z*t.z=1 by
      simpa only [←pow_two,t.z_order] using pow_orderOf_eq_one t.z)
  have hzne : z≠1 := by
    intro h
    have hz : t.z=1 := by
      apply Subtype.ext
      exact congrArg (fun x : t.leftCubicLevi=>(x:G)) h
    have hh := t.z_order
    simp [hz] at hh
  have hzcomm (a : t.leftCubicLevi) : z*a=a*z := by
    apply Subtype.ext
    exact (mem_centralizer_singleton_iff.mp
      (t.centralizer ▸ t.cubicLevi_le_H a.property)).symm
  let e := t.cubicLeviLinearEquiv hc
  have hez : e z=-1 := by
    apply Atlas.G2.TernaryLevi.eq_central_of_commuting_generators
    · rw [←map_mul,hz2,map_one]
    · exact fun h=>hzne (e.injective (h.trans e.map_one.symm))
    · rw [←e.apply_symm_apply (Atlas.G2.TernaryLevi.generator false),←map_mul,←map_mul,hzcomm]
    · rw [←e.apply_symm_apply (Atlas.G2.TernaryLevi.generator true),←map_mul,←map_mul,hzcomm]
  rw [←hez]
  have heq := t.cubicAbelianizationAction_factor hc (inclusion t.cubicLevi_le_normalizer z)
  have hzmap : t.cubicLinearAction hc (inclusion t.cubicLevi_le_normalizer z)=e z := rfl
  rw [hzmap] at heq
  rw [←heq]
  obtain ⟨v,rfl⟩ := QuotientGroup.mk'_surjective (cubicCoreLine c t.x) v
  exact t.left_oddCore_quotient_inverted v

private theorem scalarLine_eq_one (hc : Nat.card (cubicOddCore c t.x)=243)
    (v w : cubicOddCore c t.x ⧸ cubicCoreLine c t.x) :
    t.cubicLineScalar (t.cubicCommutatorLine hc v w)=1 ↔ t.cubicCommutatorPairing v w=1 := by
  rw [map_eq_one_iff _ t.cubicLineScalar.injective]
  constructor
  · intro h
    apply Subtype.ext
    exact congrArg (fun z : cubicCoreLine c t.x=>(z:cubicOddCore c t.x)) h
  · intro h
    apply Subtype.ext
    exact congrArg (fun z : center (cubicOddCore c t.x)=>(z:cubicOddCore c t.x)) h

theorem shortFormCoordinates_centerPlane (hc : Nat.card (cubicOddCore c t.x)=243)
    (e : (cubicOddCore c t.x ⧸ cubicCoreLine c t.x) ≃* Atlas.G2.TernaryCore.V)
    (hform : ∀ v w,t.cubicLineScalar (t.cubicCommutatorLine hc v w)=
      Multiplicative.ofAdd (Atlas.G2.TernaryCore.shortForm (e v) (e w)))
    (v : cubicOddCore c t.x ⧸ cubicCoreLine c t.x) :
    v∈t.cubicCenterPlane ↔ (e v).toAdd 0=0 ∧ (e v).toAdd 3=0 := by
  rw [←t.cubicCommutatorPairing_radical,←Atlas.G2.TernaryCore.shortForm_radical]
  constructor
  · intro h w
    obtain ⟨w,rfl⟩ := e.surjective w
    have hh := (t.scalarLine_eq_one hc v w).mpr (h w)
    rw [hform] at hh
    exact congrArg Multiplicative.toAdd hh
  · intro h w
    apply (t.scalarLine_eq_one hc v w).mp
    rw [hform,h]
    rfl

/-- A simultaneous cubic/form comparison extends to the whole original actor
without imposing a Weyl-action premise. -/
theorem extend_shortRoot_form_coordinates (hc : Nat.card (cubicOddCore c t.x)=243)
    (κ : Atlas.G2.TernaryLevi.GL23 ≃* Atlas.G2.TernaryLevi.GL23)
    (e : (cubicOddCore c t.x ⧸ cubicCoreLine c t.x) ≃* Atlas.G2.TernaryCore.V)
    (he : ∀ v,e (t.cubicGLAbelianizationAction hc
      (κ.symm (Atlas.G2.TernaryLevi.generator false)) v)=
        Atlas.G2.TernaryLevi.shortQuotientAction (Atlas.G2.TernaryLevi.generator false) (e v))
    (hform : ∀ v w,t.cubicLineScalar (t.cubicCommutatorLine hc v w)=
      Multiplicative.ofAdd (Atlas.G2.TernaryCore.shortForm (e v) (e w))) :
    ∃ l : t.ShortQuotientComparison hc,
      l.actor.symm (Atlas.G2.TernaryLevi.generator false)=κ.symm (Atlas.G2.TernaryLevi.generator false) ∧
      (∀ v,(l.coordinates v).toAdd 0=0 ∧ (l.coordinates v).toAdd 2=0 ∧ (l.coordinates v).toAdd 3=0 ↔
        (e v).toAdd 0=0 ∧ (e v).toAdd 2=0 ∧ (e v).toAdd 3=0) := by
  let ρ := (MulAut.congr e).toMonoidHom.comp
    ((t.cubicGLAbelianizationAction hc).comp κ.symm.toMonoidHom)
  have hρU (v) : ρ (Atlas.G2.TernaryLevi.generator false) v=Atlas.G2.TernaryCore.shortRoot v := by
    change e (t.cubicGLAbelianizationAction hc
      (κ.symm (Atlas.G2.TernaryLevi.generator false)) (e.symm v))=_
    rw [he,e.apply_symm_apply,Atlas.G2.TernaryLevi.shortQuotientAction_root]
  have hρC (v) : ρ (-1) v=v⁻¹ := by
    change e (t.cubicGLAbelianizationAction hc (κ.symm (-1)) (e.symm v))=_
    rw [Atlas.G2.TernaryLevi.mulEquiv_central,t.cubicGLAbelianizationAction_central,
      map_inv,e.apply_symm_apply]
  have hρP (v : Atlas.G2.TernaryCore.V) (h0 : v.toAdd 0=0) (h3 : v.toAdd 3=0) :
      (ρ (Atlas.G2.TernaryLevi.generator true) v).toAdd 0=0 ∧
      (ρ (Atlas.G2.TernaryLevi.generator true) v).toAdd 3=0 := by
    let a := inclusion t.cubicLevi_le_normalizer ((t.cubicLeviLinearEquiv hc).symm
      (κ.symm (Atlas.G2.TernaryLevi.generator true)))
    have hv : e.symm v∈t.cubicCenterPlane := (t.shortFormCoordinates_centerPlane hc e hform _).mpr
      (by rw [e.apply_symm_apply]; exact ⟨h0,h3⟩)
    have hp : t.cubicAbelianizationAction a (e.symm v)∈t.cubicCenterPlane := by
      rw [←t.cubicCenterPlane_invariant a]
      exact mem_map_of_mem _ hv
    have ha : t.cubicLinearAction hc a=κ.symm (Atlas.G2.TernaryLevi.generator true) :=
      (t.cubicLeviLinearEquiv hc).apply_symm_apply _
    have heq := t.cubicAbelianizationAction_factor hc a
    rw [ha] at heq
    change (e (t.cubicGLAbelianizationAction hc (κ.symm (Atlas.G2.TernaryLevi.generator true)) (e.symm v))).toAdd 0=0 ∧
      (e (t.cubicGLAbelianizationAction hc (κ.symm (Atlas.G2.TernaryLevi.generator true)) (e.symm v))).toAdd 3=0
    rw [←heq]
    exact (t.shortFormCoordinates_centerPlane hc e hform _).mp hp
  obtain ⟨τ,n,hτ,hn,hf,hl⟩ := Atlas.G2.TernaryCore.exists_shortAction_normalization ρ hρU hρC hρP
  have hfull (a v) : (e.trans n) (t.cubicGLAbelianizationAction hc a v)=
      Atlas.G2.TernaryLevi.shortQuotientAction ((κ.trans τ) a) ((e.trans n) v) := by
    have hh := hn (κ a) (e v)
    change n (e (t.cubicGLAbelianizationAction hc (κ.symm (κ a)) (e.symm (e v))))=_ at hh
    rw [κ.symm_apply_apply,e.symm_apply_apply] at hh
    exact hh
  let l : t.ShortQuotientComparison hc := {
    coordinates := e.trans n
    actor := κ.trans τ
    form := by
      intro v w
      change t.cubicLineScalar (t.cubicCommutatorLine hc v w)=
        Multiplicative.ofAdd (Atlas.G2.TernaryCore.shortForm (n (e v)) (n (e w)))
      rw [hf,hform]
    intertwines := by
      intro a v
      rw [t.cubicAbelianizationAction_factor hc]
      have ha : t.cubicLinearAction hc (inclusion t.cubicLevi_le_normalizer
          ((t.cubicLeviLinearEquiv hc).symm a))=a := (t.cubicLeviLinearEquiv hc).apply_symm_apply a
      rw [ha]
      exact hfull a v }
  refine ⟨l,?_,fun v=>hl (e v)⟩
  change κ.symm (τ.symm (Atlas.G2.TernaryLevi.generator false))=_
  have hτ' : τ.symm (Atlas.G2.TernaryLevi.generator false)=Atlas.G2.TernaryLevi.generator false := by
    apply τ.injective
    rw [τ.apply_symm_apply]
    exact hτ.symm
  rw [hτ']

/-- A full short comparison gives the literal long comparison on the same core,
with the proved determinant twist in its actor convention. -/
noncomputable def ShortQuotientComparison.toLong
    {hc : Nat.card (cubicOddCore c t.x)=243} (l : t.ShortQuotientComparison hc) :
    t.LongQuotientComparison hc where
  coordinates := l.coordinates.trans Atlas.G2.TernaryCore.shortLongCoordinates
  actor := l.actor.trans Atlas.G2.TernaryLevi.determinantTwist
  form := by
    intro v w
    change t.cubicLineScalar (t.cubicCommutatorLine hc v w)=Multiplicative.ofAdd
      (Atlas.G2.TernaryCore.longForm (Atlas.G2.TernaryCore.shortLongCoordinates (l.coordinates v))
        (Atlas.G2.TernaryCore.shortLongCoordinates (l.coordinates w)))
    rw [Atlas.G2.TernaryCore.shortLongCoordinates_form,l.form]
  intertwines := by
    intro a v
    change Atlas.G2.TernaryCore.shortLongCoordinates (l.coordinates
      (t.cubicAbelianizationAction (inclusion t.cubicLevi_le_normalizer
        ((t.cubicLeviLinearEquiv hc).symm a)) v))=_
    rw [l.intertwines,Atlas.G2.TernaryCore.shortLongCoordinates_action]
    rfl

end CubicTorus
namespace AlignedCubicPair
variable {t : CubicTorus c} (p : AlignedCubicPair t)

/-- Both generators, the commutator form and original opposite derived line
are now compatible on one set of coordinates. The original cubic is retained. -/
theorem exists_shortQuotientComparison (r : p.rightCore) (hr : (r:G)∉p.leftCore) :
    ∃ (s : p.rightCore) (l : t.ShortQuotientComparison p.core_order),
      (s=r ∨ s=r*r) ∧ (s:G)∉p.leftCore ∧
      t.cubicGLAbelianizationAction p.core_order
        (l.actor.symm (Atlas.G2.TernaryLevi.generator false))=p.oppositeAbelianizationActor s ∧
      (∀ v,v∈(⁅p.rightCore,p.rightCore⁆.subgroupOf p.leftCore).map
        (QuotientGroup.mk' (cubicCoreLine c t.x)) ↔
          (l.coordinates v).toAdd 0=0 ∧ (l.coordinates v).toAdd 2=0 ∧ (l.coordinates v).toAdd 3=0) := by
  obtain ⟨s,κ,e,hs,hsD,hκ,he,hform,hline⟩ := p.exists_shortRoot_form_comparison r hr
  obtain ⟨l,hl,hh⟩ := t.extend_shortRoot_form_coordinates p.core_order κ e he hform
  exact ⟨s,l,hs,hsD,by rw [hl,hκ],fun v=>(hline v).trans (hh v).symm⟩

/-- The two full endpoint comparisons are constructed from the original large
cores. Their later agreement on the entire common middle is not assumed here. -/
theorem nonempty_endpoint_comparisons :
    Nonempty (t.ShortQuotientComparison p.core_order) ∧
      Nonempty (t.swap.LongQuotientComparison p.right_core_order) := by
  obtain ⟨r,hr,_⟩ := p.exists_oppositeDisplacement_nonquadratic
  obtain ⟨s,l,_⟩ := p.exists_shortQuotientComparison r hr
  obtain ⟨q⟩ := t.swap.nonempty_alignedCubicPair p.right_core_order
  obtain ⟨r',hr',_⟩ := q.exists_oppositeDisplacement_nonquadratic
  obtain ⟨s',l',_⟩ := q.exists_shortQuotientComparison r' hr'
  exact ⟨⟨l⟩,⟨CubicTorus.ShortQuotientComparison.toLong t.swap l'⟩⟩

end AlignedCubicPair
end CFSG.Quasithin.ChapterI.Section04To05.G2Recognition

