module
public import CFSG.Quasithin.ChapterB.Section06To07.ChiefActions.NaturalSource
public import CFSG.Quasithin.ChapterB.Section06To07.Structure.CoreQuotient
public import Theory.GroupTheory.GeneralizedFitting.QuasisimpleRadicalTwoExtension
public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.ComponentReduction.ProductGeometry.ModelFacts

/-!
# A common literal kernel for the nonsolvable chief actions

The canonical core of a minimal parabolic is solvable. Every nontrivial
reduced chief action has kernel in that core. The faithful nonsolvable FF
classification has trivial solvable radical: its single rank-one component
is centerless, while its two factors are exchanged by the prescribed Sylow
and have only two-group proper normal quotients. The core of each faithful
image is therefore trivial, so its kernel equals the original canonical core.

Consequently the chief factors in original3.1.9(5) have the same literal
quotient actor in the nonsolvable branch. Equality of Sylow intersections
alone is not used to identify these kernels. Source: Aschbacher–Smith
B.6.8–9 and3.1.9, printed pp.114–116 and577–578.
-/

public section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
namespace CFSG.Quasithin.ChapterB
open SourceInduction QuasisimpleSource
variable {G D V : Type*} [Group G] [Finite G] [Group D] [Finite D]
 [AddCommGroup V] [Module (ZMod 2) V]

private theorem radical_bot_of_normal_quotients
    (hs : ¬ Group.IsSolvable D)
    (hn : ∀ (N : Subgroup D) [N.Normal], N ≠ ⊥ → IsPGroup 2 (D ⧸ N)) :
    solvableRadical D = ⊥ := by
  by_contra h
  let : Group.IsNilpotent (D ⧸ solvableRadical D) := (hn _ h).isNilpotent
  exact hs ((Group.isSolvable_iff_subgroup_quotient (solvableRadical D)).mpr
    ⟨inferInstance,inferInstance⟩)

private theorem radical_bot_of_normal_two_quotient (N : Subgroup G) [N.Normal]
    (hN : solvableRadical N = ⊥) (hq : IsPGroup 2 (G ⧸ N))
    (hc : pCore 2 G = ⊥) : solvableRadical G = ⊥ := by
  let R := solvableRadical G
  let f : R →* G ⧸ N := (QuotientGroup.mk' N).comp R.subtype
  have hf : Function.Injective f := by
    apply (MonoidHom.ker_eq_bot_iff f).mp
    apply bot_unique
    intro x hx
    apply Subtype.ext
    have hxN : (x : G) ∈ N := (QuotientGroup.eq_one_iff _).mp hx
    have hxR : (⟨x,hxN⟩ : N) ∈ solvableRadical N := by
      rw [← radical_subgroupOf_normal N]
      exact x.property
    have he : (⟨x,hxN⟩ : N) = 1 := hN.le hxR
    exact congrArg (fun z : N => (z : G)) he
  have hR : IsPGroup 2 R := hq.of_injective f hf
  exact bot_unique ((le_sSup ⟨inferInstance,hR⟩ : R ≤ pCore 2 G).trans hc.le)

private theorem radical_bot_of_product {A B : Subgroup D}
    (d : InternalProduct A B) (ha : solvableRadical A = ⊥) (hb : solvableRadical B = ⊥) :
    solvableRadical D = ⊥ := by
  let f := (MonoidHom.fst A B).comp d.equiv.symm.toMonoidHom
  let g := (MonoidHom.snd A B).comp d.equiv.symm.toMonoidHom
  have hf : Function.Surjective f := Prod.fst_surjective.comp d.equiv.symm.surjective
  have hg : Function.Surjective g := Prod.snd_surjective.comp d.equiv.symm.surjective
  apply bot_unique
  intro x hx
  have hxf : f x = 1 := ha.le ((map_solvableRadical_le_of_surjective f hf) (mem_map_of_mem f hx))
  have hxg : g x = 1 := hb.le ((map_solvableRadical_le_of_surjective g hg) (mem_map_of_mem g hx))
  apply d.equiv.symm.injective
  apply Prod.ext
  · simpa [f] using hxf
  · simpa [g] using hxg

theorem source_pair_radical_eq_bot
    (ρ : Representation (ZMod 2) G V) [FiniteDimensional (ZMod 2) V]
    (T : Sylow 2 G) (hP : IsMinimalParabolicOver T ⊤)
    (hs : ¬ Group.IsSolvable G) (hcore : pCore 2 G = ⊥) (hff : IsFFModule ρ)
    (d : SourceTwoFactorCase (ρ.comp (offenderSubgroup ρ).subtype)) :
    solvableRadical G = ⊥ := by
  let Y := offenderSubgroup ρ
  let := offenderSubgroup_normal ρ
  have hr := (offender_generation T hP ρ hff hcore).1
  have hquot : IsPGroup 2 (G ⧸ Y) := (pResidual_le_iff_isPGroup_quotient 2 Y).mp hr
  have hy : ¬ Group.IsSolvable Y := by
    intro hy
    let := hy
    let : Group.IsNilpotent (G ⧸ Y) := hquot.isNilpotent
    exact hs ((Group.isSolvable_iff_subgroup_quotient Y).mpr ⟨inferInstance,inferInstance⟩)
  obtain ⟨t,ht,_⟩ := source_offender_two_factor_exists_sylow_exchange ρ T hP hff hcore d
  let e : d.first ≃* d.second :=
    (d.first.equivMapOfInjective (MulAut.conjNormal (t : G)).toMonoidHom
      (MulAut.conjNormal (t : G)).injective).trans (MulEquiv.subgroupCongr ht)
  have ha : ¬ Group.IsSolvable d.first := by
    intro ha
    let := ha
    let : Group.IsSolvable d.second := Group.isSolvable_of_surjective (f := e.toMonoidHom) e.surjective
    exact hy (Group.isSolvable_of_surjective (f := d.product.equiv.toMonoidHom) d.product.equiv.surjective)
  have hb : ¬ Group.IsSolvable d.second := by
    intro hb
    let := hb
    exact ha (Group.isSolvable_of_surjective (f := e.symm.toMonoidHom) e.symm.surjective)
  exact radical_bot_of_normal_two_quotient Y
    (radical_bot_of_product d.product
      (radical_bot_of_normal_quotients ha d.firstCase.normal_quotient_two)
      (radical_bot_of_normal_quotients hb d.secondCase.normal_quotient_two)) hquot hcore

private theorem centerless_of_equiv {A B : Type*} [Group A] [Group B]
    (e : A ≃* B) (hz : center B = ⊥) : center A = ⊥ := by
  apply bot_unique
  intro x hx
  have he : e x = 1 := hz.le (show e x ∈ center B from
    (centerCongr e ⟨x,hx⟩).property)
  exact e.injective (he.trans e.map_one.symm)

theorem minimalParabolic_nonsolvable_ff_radical_eq_bot
    (ρ : Representation (ZMod 2) G V) [FiniteDimensional (ZMod 2) V]
    (T : Sylow 2 G) (hP : IsMinimalParabolicOver T ⊤)
    (hs : ¬ Group.IsSolvable G) (hcore : pCore 2 G = ⊥)
    (hf : Function.Injective ρ) (hff : IsFFModule ρ)
    (hcover : Nonempty (SQTKQuotient KnownSimple.IsKnownSimple G)) :
    solvableRadical G = ⊥ := by
  rcases nonsolvable_offender_natural_source ρ T hP hs hf hff hcore hcover
      with ⟨hqs,c,hmodel⟩ | ⟨d,_,_⟩
  · let Y := offenderSubgroup ρ
    let := offenderSubgroup_normal ρ
    let A := generalizedFitting Y
    have hz : center A = ⊥ := by
      rcases hmodel with ⟨F,hn⟩ | ⟨m⟩
      · exact (ComponentReduction.ProductGeometry.linearTwo_faithful_center c.sectionData F hn).2
      · obtain ⟨m⟩ := m
        exact centerless_of_equiv m.subgroupEquiv (alternatingGroup.center_eq_bot (by simp))
    have hr := source_quasisimple_fitting_eq_residual T hP Y
      (offender_generation T hP ρ hff hcore).2 hqs
    let e : A ≃* pResidual 2 G :=
      (A.equivMapOfInjective Y.subtype Y.subtype_injective).trans (MulEquiv.subgroupCongr hr.1)
    have hzR : center (pResidual 2 G) = ⊥ := centerless_of_equiv e.symm hz
    let := hr.2
    have hrad := radical_isTwoGroup_of_quasisimple_two_quotient (pResidual 2 G)
      (by rw [hzR]; exact IsPGroup.of_bot)
      (isPGroup_quotient_pResidual 2)
    exact bot_unique ((le_sSup ⟨inferInstance,hrad⟩ : solvableRadical G ≤ pCore 2 G).trans hcore.le)
  · exact source_pair_radical_eq_bot ρ T hP hs hcore hff d


universe u
theorem minimalParabolic_nonsolvable_chief_kernel
    {H W : Type u} [Group H] [Finite H] [AddCommGroup W]
    [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W]
    (ρ : Representation (ZMod 2) H W) [IsIrreducible ρ]
    (hH : IsSQTK KnownSimple.IsKnownSimple H)
    (T : Sylow 2 H) (hP : IsMinimalParabolicOver T ⊤)
    (hs : ¬ Group.IsSolvable H)
    (hff : IsFFModule (Representation.BinaryOffender.imageRepresentation ρ)) :
    ρ.ker = minimalParabolicCore T hP := by
  let q := actionHom ρ
  have hq : Function.Surjective q := ρ.asGroupHom.rangeRestrict_surjective
  have hc := irreducible_image_twoCore_eq_bot ρ
  have hn : q.ker ≠ ⊤ := by
    intro he
    obtain ⟨A,hA⟩ := hff
    obtain ⟨a,ha⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hA.1.1
    obtain ⟨g,hg⟩ := hq (a : actionImage ρ)
    apply ha
    apply Subtype.ext
    change (a : actionImage ρ) = 1
    rw [← hg]
    exact (show g ∈ q.ker from he ▸ mem_top g)
  obtain ⟨hk,hP'⟩ := minimalParabolic_reduced_image T hP q hq hc hn
  have hi : ¬ Group.IsSolvable (actionImage ρ) := by
    intro hi
    let := hi
    let := minimalParabolic_core_solvable T hP
    let : Group.IsSolvable q.ker :=
      Group.isSolvable_of_isSolvable_injective (inclusion_injective hk)
    let : Group.IsSolvable (H ⧸ q.ker) :=
      Group.isSolvable_of_surjective
        (f := (QuotientGroup.quotientKerEquivOfSurjective q hq).symm.toMonoidHom)
        (QuotientGroup.quotientKerEquivOfSurjective q hq).symm.surjective
    exact hs ((Group.isSolvable_iff_subgroup_quotient q.ker).mpr ⟨inferInstance,inferInstance⟩)
  let c : SQTKQuotient KnownSimple.IsKnownSimple (actionImage ρ) := {
    Cover := H
    kernel := q.ker
    sqtk := hH
    equiv := QuotientGroup.quotientKerEquivOfSurjective q hq }
  have hz := minimalParabolic_nonsolvable_ff_radical_eq_bot
    (Representation.BinaryOffender.imageRepresentation ρ) (T.mapSurjective hq) hP'
    hi hc (imageRepresentation_injective ρ) hff ⟨c⟩
  have hmap := minimalParabolicCore_map_core T hP q hq hk
  rw [minimalParabolic_nonsolvable_core_eq_radical _ _ hi,hz] at hmap
  rw [← actionHom_ker_eq ρ]
  exact le_antisymm hk ((Subgroup.map_eq_bot_iff _).mp hmap)

end CFSG.Quasithin.ChapterB
