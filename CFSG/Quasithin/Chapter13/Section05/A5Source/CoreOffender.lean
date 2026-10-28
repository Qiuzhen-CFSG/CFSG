module
public import CFSG.Quasithin.Chapter13.Section02.A5Local.FullAction
public import Stellmacher.ElementaryAbelianMaxFamilyMap

/-!
# Maximum elementary odd actors on the original five-point module

If the elementary Thompson subgroup of R moves the natural module V≤R,
a maximum elementary generator has nontrivial conjugation image. The
replacement inequality makes this image an offender. Transport through
the original module map identifies its action on the five-point core;
every such offender contains an odd permutation.

Both the ambient inclusion and the supplied action homomorphism are retained.
The original commuting-core application uses this with R equal to one core
and V the opposite module. Source: Aschbacher--Smith B.2.7, B.3.2(4), and
13.2.4(1), printed pp.76--77,83,879.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section05.A5Source.Context
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ : Subgroup G}
  (d : Context T L V V₁ V₂ V₃)

theorem max_elementary_odd_cross_action
    (J R : Subgroup G) (hVJ : V ≤ J) (hVR : V ≤ R) (hRJ : R ≤ J)
    (q : J →* Equiv.Perm (Fin 5))
    (hk : q.ker = centralizer (V.subgroupOf J : Set J))
    (hJV : J ≤ normalizer (V : Set G))
    (he : ∀ j : J, ∀ v : BinaryPermutation.core (Fin 5),
      j.val * d.flag.module.map (Multiplicative.ofAdd v) * j.val⁻¹ =
        d.flag.module.map (Multiplicative.ofAdd
          (BinaryPermutation.coreRepresentation (Fin 5) (q j) v)))
    (hm : ¬ elementaryAbelianMaxJ R ≤ centralizer (V : Set G)) :
    ∃ A ∈ elementaryAbelianMaxSubgroups R,
      ¬ (A.subgroupOf J).map q ≤ alternatingGroup (Fin 5) := by
  let U := V.subgroupOf J
  let : U.Normal := normal_subgroupOf_of_le_normalizer hJV
  let := d.elementary
  let : IsElementaryAbelian 2 U := IsElementaryAbelian.subgroupOf hVJ
  let qr := q.rangeRestrict
  have hkr : qr.ker = centralizer (U : Set J) := q.ker_rangeRestrict.trans hk
  let f : Multiplicative (BinaryPermutation.core (Fin 5)) →* U := {
    toFun := fun v => ⟨⟨d.flag.module.map v,hVJ (d.flag.module.range_eq.le ⟨v,rfl⟩)⟩,
      d.flag.module.range_eq.le ⟨v,rfl⟩⟩
    map_one' := Subtype.ext (Subtype.ext (map_one _))
    map_mul' := fun a b => Subtype.ext (Subtype.ext (map_mul _ a b)) }
  have hfi : Function.Injective f := fun a b h =>
    d.flag.module.injective (congrArg (fun x : U => (x.val : G)) h)
  have hfs : Function.Surjective f := by
    intro v
    obtain ⟨x,hx⟩ := d.flag.module.range_eq.ge v.property
    exact ⟨x,Subtype.ext (Subtype.ext hx)⟩
  let b := MulEquiv.ofBijective f ⟨hfi,hfs⟩
  let a := b.symm.toAdditive.trans (AddEquiv.additiveMultiplicative _)
  let c : Additive U ≃ₗ[ZMod 2] BinaryPermutation.core (Fin 5) :=
    { a with map_smul' := ZMod.map_smul a }
  let ρ := NormalElementaryQuotient.representation U qr q.rangeRestrict_surjective hkr
  have hc (g : q.range) (v : Additive U) :
      c (ρ g v) = BinaryPermutation.coreRepresentation (Fin 5) g.val (c v) := by
    obtain ⟨g,rfl⟩ := q.rangeRestrict_surjective g
    apply Multiplicative.toAdd.injective
    change Multiplicative.ofAdd (c (ρ (qr g) v)) =
      Multiplicative.ofAdd (BinaryPermutation.coreRepresentation (Fin 5) (q g) (c v))
    apply b.injective
    change b (b.symm ((ρ (qr g) v).toMul)) = f _
    rw [b.apply_symm_apply]
    apply Subtype.ext
    apply Subtype.ext
    rw [NormalElementaryQuotient.representation_apply]
    have hv : d.flag.module.map (Multiplicative.ofAdd (c v)) = (v.toMul.val : G) :=
      congrArg (fun x : U => (x.val : G)) (b.apply_symm_apply v.toMul)
    exact (congrArg (fun x : G => g.val * x * g.val⁻¹) hv).symm.trans (he g (c v))
  have hJR : (elementaryAbelianMaxJ (R.subgroupOf J)).map J.subtype =
      elementaryAbelianMaxJ R := by
    rw [←elementaryAbelianMaxJ_map_injective J.subtype J.subtype_injective,
      map_subgroupOf_eq_of_le hRJ]
  have hmove : ¬ elementaryAbelianMaxJ (R.subgroupOf J) ≤ qr.ker := by
    intro hn
    apply hm
    rw [←hJR]
    rintro x ⟨x,hx,rfl⟩ v hv
    exact congrArg J.subtype ((hkr ▸ hn hx) ⟨v,hVJ hv⟩ hv)
  have hex : ∃ A ∈ elementaryAbelianMaxSubgroups (R.subgroupOf J), ¬ A ≤ qr.ker := by
    by_contra hn
    push Not at hn
    exact hmove (sSup_le hn)
  obtain ⟨A,hA,hAk⟩ := hex
  have hoff := NormalElementaryQuotient.maxElementary_isOffender U qr
    q.rangeRestrict_surjective hkr (R.subgroupOf J) A (fun _ hx => hVR hx) hA hAk
  have hmodel := hoff.map_equivariant ρ (BinaryPermutation.coreRepresentation (Fin 5))
    q.range.subtype q.range.subtype_injective c hc
  have hnot := ChapterB.Offenders.core_offender_not_le_alternating (Or.inl rfl) hmodel
  refine ⟨A.map J.subtype,?_,?_⟩
  · have hh := (maxFamily_map_injective_iff J.subtype J.subtype_injective
      (R.subgroupOf J) A).mpr hA
    rwa [map_subgroupOf_eq_of_le hRJ] at hh
  · rw [subgroupOf,comap_map_eq_self_of_injective J.subtype_injective]
    simpa only [map_map,qr,MonoidHom.subtype_comp_rangeRestrict] using hnot
end CFSG.Quasithin.Chapter13.Section05.A5Source.Context
