module
public import CFSG.Quasithin.Chapter10.SourceA5PointSylow.NaturalActor
public import Theory.Representation.BinaryConjugationSection.NormalizingActors
public import Theory.Representation.SL2NaturalFixedLifting.PointSylow

/-!
# Original natural-cover vectors fixed by conjugate Thompson subgroups

The faithful original L-action identifies the action of every subgroup of
L C_G(W) with a linear SL₂ actor on W=[V,L]. The natural quotient and its
entire fixed kernel are retained. Each vector is fixed by a conjugate
of the given two-subgroup, because its natural quotient is fixed by a
root Sylow subgroup and fixed-kernel lifting preserves every lift.
The original maximum-elementary argument places J(T) in that actor,
so no action-factorization premise remains in the Thompson application.
Source: Aschbacher–Smith 10.2.9, printed pp.750–751, using I.2.3.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.OneCohomology
open scoped IsMulCommutative MatrixGroups Pointwise
namespace CFSG.Quasithin.Chapter10
open Chapter3.Section02
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
  (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
local instance pointSylowNaturalPointElementary :
    IsElementaryAbelian 2 (⁅D.fullModule,L⁆ : Subgroup G) :=
  source_original_full_moved_elementary D
local instance pointSylowNaturalPointAlgebra :
    Algebra (ZMod 2) (Representation.OrthogonalFourMinus.FiniteModel.Field 1) :=
  ZMod.algebra _ 2

/-- Literal component conjugation fixes each original natural-cover vector. -/
theorem source_a5_natural_conjugate_point_fixed_of_linear_actor
    (f : alternatingGroup (Fin 5) ≃* SL(2,Representation.OrthogonalFourMinus.FiniteModel.Field 1))
    (c : BinaryConjugationSection L ⁅D.fullModule,L⁆ (sourceMovedFixed D)
      (SL2.BinarySmall.natural.comp
        (f.toMonoidHom.comp (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))))))
    (P : Subgroup G) (hP : IsPGroup 2 P)
    (hactor : P ≤ L ⊔ centralizer (↑(⁅D.fullModule,L⁆ : Subgroup G) : Set G))
    {v : G} (hv : v ∈ ⁅D.fullModule,L⁆) :
    ∃ l : L, P.map (MulAut.conj (l : G)).toMonoidHom ≤ centralizer ({v} : Set G) := by
  let W := ⁅D.fullModule,L⁆
  let π := f.toMonoidHom.comp (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L)))
  have hπ : Function.Surjective π := f.surjective.comp (e.surjective.comp (QuotientGroup.mk'_surjective _))
  obtain ⟨σ₀,hσ₀inj,hσ₀⟩ := source_a5_original_moved_action D e
  let σ := σ₀.comp f.symm.toMonoidHom
  have hσinj : Function.Injective σ := hσ₀inj.comp f.symm.injective
  have hσ : ∀ (l : L) (w : Additive W), ((σ (π l) w).toMul : G) = l*w.toMul*(l : G)⁻¹ := by
    intro l w
    change ((σ₀ (f.symm (f (e (QuotientGroup.mk' (pCore 2 L) l)))) w).toMul : G) = _
    rw [f.symm_apply_apply]
    exact hσ₀ l w
  have hPW : P ≤ normalizer (W : Set G) :=
    hactor.trans (sup_le c.normalized (Subgroup.centralizer_le_normalizer _))
  let τ := BinaryConjugationSection.originalNormalizerAction hPW
  have hex (p : P) : ∃ g, σ g = τ p := by
    have hp : (p : G) ∈ ((L ⊔ centralizer (W : Set G) : Subgroup G) : Set G) := hactor p.property
    rw [coe_mul_of_left_le_normalizer_right L (centralizer (W : Set G))
      (c.normalized.trans (normalizer_le_normalizer_centralizer W))] at hp
    obtain ⟨l,hl,z,hz,hp⟩ := hp
    refine ⟨π ⟨l,hl⟩,?_⟩
    apply LinearMap.ext
    intro w
    apply Additive.toMul.injective
    apply Subtype.ext
    rw [hσ]
    rw [BinaryConjugationSection.originalNormalizerAction_apply_coe]
    change l*(w.toMul:G)*l⁻¹ = (p:G)*w.toMul*(p:G)⁻¹
    rw [←hp]
    have hzv : z*(w.toMul:G)=(w.toMul:G)*z := (hz w.toMul w.toMul.property).symm
    calc
      l*(w.toMul:G)*l⁻¹ = l*(z*(w.toMul:G)*z⁻¹)*l⁻¹ := by rw [hzv,mul_inv_cancel_right]
      _ = (l*z)*(w.toMul:G)*(l*z)⁻¹ := by group
  choose θ hθ using hex
  let θh : P →* SL(2,Representation.OrthogonalFourMinus.FiniteModel.Field 1) := {
    toFun := θ
    map_one' := hσinj (by rw [hθ,map_one,map_one])
    map_mul' p r := hσinj (by simp only [map_mul,hθ]) }
  obtain ⟨q,hq,_⟩ := c.exists_cover_of_fully_moved SL2.BinarySmall.natural π hπ σ hσ
    inf_le_right (source_full_moved_eq_commutator D)
  let w : Additive W := Additive.ofMul ⟨v,hv⟩
  obtain ⟨g,hg⟩ := SL2NaturalFixedLifting.exists_conjugate_fixed_of_fixed_kernel σ
    q.toLinearMap.toAddMonoidHom hq.1 (fun a x => LinearMap.congr_fun (q.isIntertwining' a) x)
    (fun x hx a => hq.2.1 hx a) θh.range (hP.of_surjective θh.rangeRestrict θh.rangeRestrict_surjective) w
  obtain ⟨l,hl⟩ := hπ g
  refine ⟨l,?_⟩
  rintro _ ⟨p,hp,rfl⟩
  apply mem_centralizer_singleton_iff.mpr
  have hfix := hg (θh ⟨p,hp⟩) ⟨⟨p,hp⟩,rfl⟩
  have hfix' : σ g (τ ⟨p,hp⟩ (σ g⁻¹ w)) = w := by
    change σ (g*θ ⟨p,hp⟩*g⁻¹) w = w at hfix
    simpa only [map_mul,Module.End.mul_apply,hθ] using hfix
  have hlw : ((σ g⁻¹ w).toMul : G) = (l:G)⁻¹*v*l := by
    have hh := hσ l⁻¹ w
    rw [map_inv,hl] at hh
    simpa only [w,Subgroup.coe_inv,inv_inv,toMul_ofMul] using hh
  have hh := congrArg (fun x : Additive W => (x.toMul:G)) hfix'
  rw [←hl,hσ,hl,BinaryConjugationSection.originalNormalizerAction_apply_coe] at hh
  change (l:G)*(p*((σ g⁻¹ w).toMul:G)*p⁻¹)*(l:G)⁻¹=v at hh
  rw [hlw] at hh
  apply mul_inv_eq_iff_eq_mul.mp
  change ((MulAut.conj (l:G)) p)*v*((MulAut.conj (l:G)) p)⁻¹=v
  calc
    ((MulAut.conj (l:G)) p)*v*((MulAut.conj (l:G)) p)⁻¹ =
      (l:G)*(p*((l:G)⁻¹*v*l)*p⁻¹)*(l:G)⁻¹ := by simp only [MulAut.conj_apply]; group
    _ = v := hh

/-- Every vector of the original natural cover is fixed by a component conjugate
of the actual Thompson subgroup, including vectors in the fixed kernel. -/
theorem source_a5_natural_thompson_point_fixed
    (f : alternatingGroup (Fin 5) ≃* SL(2,Representation.OrthogonalFourMinus.FiniteModel.Field 1))
    (c : BinaryConjugationSection L ⁅D.fullModule,L⁆ (sourceMovedFixed D)
      (SL2.BinarySmall.natural.comp
        (f.toMonoidHom.comp (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))))))
    {v : G} (hv : v ∈ ⁅D.fullModule,L⁆) :
    ∃ l : L, (Stellmacher.elementaryAbelianMaxJ (T : Subgroup G)).map
      (MulAut.conj (l : G)).toMonoidHom ≤ centralizer ({v} : Set G) :=
  source_a5_natural_conjugate_point_fixed_of_linear_actor D e f c _
    (T.isPGroup'.to_le (sSup_le fun _ hA => hA.1))
    (source_a5_natural_thompson_le_linear_actor D e f c) hv

end CFSG.Quasithin.Chapter10
