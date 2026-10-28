module
public import CFSG.Quasithin.Chapter15.Section02.SourcePlaneUniqueness.OrdinaryComponents.QuotientRank
public import CFSG.Quasithin.Chapter15.Section02.SourcePlaneUniqueness.CharacteristicTwo.SmallActions
public import Theory.SpecificGroups.Janko4.Model.InvolutionCentralizers.TwoResidual

/-!
# The original J4 residual section inside Kc

For the same marked ordinary component, the two-residual of its fixed
subgroup has intrinsic two-core quotient 3.M22. Map that literal residual
back into G. The original centralizer identity places it in Mc; its cubic
generation and the original identity Kc = O^{3′}(Mc) place it in Kc itself.
Every map and covering center is retained. The remaining source step is to
exclude this section using the exact structural alternatives of 15.2.12(2).
Those alternatives retain their existing plane-geometry producer and final
chosen-action discharge; they are not assumed proved in this module.
Source: Aschbacher--Smith, proof of 15.2.15, printed p.1118, refs/quasithin.pdf.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory Sporadic.Mathieu
namespace CFSG.Quasithin.Chapter15.Section02.OrdinaryComponents
open Section01 Section03 Candidates.ComponentStructure ClassificationModels
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc V H ZS I : Subgroup G}
variable {hsource : ChosenSmallSource T M Mc V}
variable (d : PlaneUniquenessPreceding hsource H ZS)
variable {P : Sylow 2 I} {z : G}
variable (c : ComponentData (T := T) (Mc := Mc) I P z)

/-- The exact remaining J4 row has the source two-residual quotient, with its triple center retained. -/
theorem janko_four_fixed_residual_quotient
    (a : MulAut c.component)
    (e : (c.component ⧸ pCore 2 c.component) ≃* Janko4.Model)
    (hai : TwoCentralInner a) :
    Nonempty ((pResidual 2 a.fixedSubgroup ⧸ pCore 2 (pResidual 2 a.fixedSubgroup)) ≃*
      M22TripleCover) := by
  obtain ⟨t,ht,htc,hact⟩ := quotient_twoCentral_of_inner c e a hai
  obtain ⟨_,hao,Q,hQ⟩ := hai
  exact Janko4.InvolutionCentralizers.fixed_twoResidualCoreQuotient
    c.center_eq.symm.le e a hao Q (fun x hx => hQ ⟨x,hx⟩) t ht htc hact

/-- The ambient image of the literal O² of the marked component fixed subgroup. -/
def markedFixedResidual (a : MulAut c.component) : Subgroup G :=
  (pResidual 2 a.fixedSubgroup).map
    (I.subtype.comp (c.component.subtype.comp a.fixedSubgroup.subtype))

include d in
/-- The original J4 row produces the genuine triple Mathieu section inside Kc. -/
theorem janko_four_residual_section_in_Kc
    (hI : PlaneEscapes Mc ZS I)
    (hz : z ∈ centralInvolutions T) (hzne : z ≠ 1)
    (a : MulAut c.component)
    (ha : ∀ x : c.component, ((a x : I) : G) = z * (x : G) * z⁻¹)
    (e : (c.component ⧸ pCore 2 c.component) ≃* Janko4.Model)
    (hai : TwoCentralInner a) :
    markedFixedResidual c a ≤ smallActionKc H Mc ∧
      Nonempty ((markedFixedResidual c a ⧸ pCore 2 (markedFixedResidual c a)) ≃*
        M22TripleCover) := by
  obtain ⟨er⟩ := janko_four_fixed_residual_quotient c a e hai
  let R := pResidual 2 a.fixedSubgroup
  let f0 := I.subtype.comp (c.component.subtype.comp a.fixedSubgroup.subtype)
  have hf0 : Function.Injective f0 :=
    I.subtype_injective.comp (c.component.subtype_injective.comp a.fixedSubgroup.subtype_injective)
  let eR := R.equivMapOfInjective f0 hf0
  have hMc (x : a.fixedSubgroup) : f0 x ∈ Mc := by
    apply (marked_centralizer d hI hz hzne).2.le
    apply mem_centralizer_singleton_iff.mpr
    have hh := ha x
    rw [(MulAut.mem_fixedSubgroup _ _).mp x.property] at hh
    exact (mul_inv_eq_iff_eq_mul.mp hh.symm).symm
  let f : R →* Mc := (f0.comp R.subtype).codRestrict Mc (fun x => hMc x)
  have hres : primeToResidual 3 R = ⊤ :=
    Janko4.InvolutionCentralizers.cubic_generated_of_twoPerfect_cover
      (isPPerfect_pResidual 2) er
  have hmap := map_primeToResidual_le_of_hom 3 f
  rw [hres,←MonoidHom.range_eq_map] at hmap
  constructor
  · change R.map f0 ≤ smallActionKc H Mc
    rw [show smallActionKc H Mc = (primeToResidual 3 Mc).map Mc.subtype from d.orbit_residual]
    rintro x ⟨y,hy,rfl⟩
    exact mem_map_of_mem Mc.subtype (hmap ⟨⟨y,hy⟩,rfl⟩)
  · exact ⟨(QuotientGroup.congr _ _ eR.symm (pCore_map_iso 2 eR.symm)).trans er⟩

end CFSG.Quasithin.Chapter15.Section02.OrdinaryComponents
