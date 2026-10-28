module
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable.JankoRecognition.J3Ambient.CubicDerivedFactor
public import Theory.SpecificGroups.AlternatingSix.PGLNineCubicFusion

/-!
# Actual normalizer fusion of cubics in the canonical A₆ factor

The derived subgroup of the full cubic centralizer is characteristic there
and normal in the full cubic normalizer. Its intersection with the entire
cubic kernel is trivial. Consequently the actual PGL₂(9) quotient's cubic
fusion lifts exactly to the original derived factor, with a conjugator in
the literal ambient cubic normalizer and no residual central error.
-/

public noncomputable section
open Subgroup
namespace CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable.J3Ambient
open Janko23.J3Recognition.LocalSixteen Janko23.J3Recognition.Ambient
open Representation.CentralCubicNaturalFour
open Sporadic.Janko3.SourceRecognition
open Sporadic.Janko3.SourceRecognition.BaumeisterParabolics

/-- All actual derived-factor cubics fuse within the full original cubic normalizer. -/
theorem literal_derived_cubics_fuse
    {G : Type*} [Group G] [Finite G] {D : Seed G}
    (P : ReturningPair D) (hc : Janko23.OneInvolutionClass G)
    (A : Subgroup G) (C : Subgroup (normalizer (A : Set G)))
    (l : C ≃* LinearGroup) (a : A ≃* Plane)
    (ha : ∀ (c : C) (x : A), a (A.normalizerMonoidHom c x) = naturalAction (l c) (a x))
    (j : SingerField.Model →* G) (hj : PlaneTransport.FieldEmbedding A C a j)
    (x y : _root_.commutator (centralizer ({j cubic} : Set G)))
    (hx : orderOf x = 3) (hy : orderOf y = 3) :
    ∃ n ∈ normalizer (zpowers (j cubic) : Set G),
      n * ((x : centralizer ({j cubic} : Set G)) : G) * n⁻¹ =
        ((y : centralizer ({j cubic} : Set G)) : G) := by
  let s := j cubic
  let Z := centralizer ({s} : Set G)
  let N := normalizer (zpowers s : Set G)
  let H := Z.subgroupOf N
  let D0 := _root_.commutator Z
  have hZN : Z ≤ N := cubic_centralizer_le_normalizer s
  let i : Z →* N := inclusion hZN
  let f : D0 →* N := i.comp D0.subtype
  have hf : Function.Injective f := (inclusion_injective hZN).comp D0.subtype_injective
  have hi : i.range = H := by
    ext z
    constructor
    · rintro ⟨c,rfl⟩
      exact c.property
    · intro hz
      exact ⟨⟨z,hz⟩,rfl⟩
  let : H.Normal := by
    have he : centralizer (zpowers s : Set G) = Z := by
      rw [zpowers_eq_closure,centralizer_closure]
    change (Z.subgroupOf N).Normal
    rw [←he]
    infer_instance
  have hfR : f.range = ⁅H,H⁆ := by
    rw [MonoidHom.range_comp,range_subtype,map_commutator_eq,hi]
  let : f.range.Normal := hfR ▸ inferInstance
  obtain ⟨hcomp,_⟩ := literal_cubic_derived_factor P hc A C l a ha j hj
  obtain ⟨_,⟨eN⟩⟩ := literal_field_cubic_projective P hc A C a j hj
  let q : N →* GorensteinWalter.PGL2 Atlas.Comparisons.Exceptional.Nine.F :=
    eN.toMonoidHom.comp (QuotientGroup.mk' (cubicNormalizerKernel s))
  have hq : Function.Surjective q := eN.surjective.comp (QuotientGroup.mk'_surjective _)
  let d := q.comp f
  have hd : Function.Injective d := by
    apply (injective_iff_map_eq_one d).mpr
    intro z hz
    have hzq : QuotientGroup.mk' (cubicNormalizerKernel s) (f z) = 1 :=
      eN.injective (hz.trans eN.map_one.symm)
    have hzker : (z:Z) ∈ cubicKernel s := (QuotientGroup.eq_one_iff (f z)).mp hzq
    exact Subtype.ext (disjoint_def.mp hcomp.disjoint hzker z.property)
  obtain ⟨b,hb⟩ := isConj_iff.mp
    (AlternatingSix.PGLNineCubicFusion.cubic_isConj (d x) (d y)
      ((orderOf_injective d hd _).trans hx) ((orderOf_injective d hd _).trans hy))
  obtain ⟨n,rfl⟩ := hq b
  have hw : n * f x * n⁻¹ ∈ f.range :=
    (inferInstance : f.range.Normal).conj_mem _ ⟨x,rfl⟩ n
  obtain ⟨w,hw⟩ := hw
  have he : w = y := by
    apply hd
    change q (f w) = q (f y)
    rw [hw,map_mul,map_mul,map_inv]
    exact hb
  subst w
  exact ⟨n,n.property,congrArg Subtype.val hw.symm⟩

end CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable.J3Ambient
