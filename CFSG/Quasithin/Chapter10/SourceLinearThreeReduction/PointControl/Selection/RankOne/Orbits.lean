module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.Selection.RankOne.Actor
public import Theory.Representation.BinaryConjugationSection.NormalizingActors
public import Theory.Representation.SL2NaturalFixedLifting.PointSylow
public import CFSG.Quasithin.Chapter10.SourceA5PointSylow.OriginalOrbits
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.Selection.Contracts

/-!
# Baumann fixed orbits in the rank-one natural cover

Root Sylow subgroups fix every lift of a fixed natural vector through the
original central kernel. The Thompson actor placement therefore gives an
L-conjugate fixed representative for every vector of [V,L], including kernel
vectors. The elementary Thompson fixed subgroup is Baumann-fixed. Literal
conjugation transfers this statement to the specified opposite moved factor.
This proves the fixed-orbits field of RankOnePointGeometry without saturation
or a fixed-layer hypothesis. Source: Aschbacher--Smith, 10.2.9, pp.750--751,
using I.2.3(1), p.413. The transport follows the existing A₅ NaturalPoint proof.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender Stellmacher
open scoped IsMulCommutative MatrixGroups Pointwise
namespace CFSG.Quasithin.Chapter10.PointControl.Selection.RankOne
open Chapter3.Section02 ChapterE
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
  {F : Type*} [Field F] [Finite F] [CharP F 2]
local instance : Algebra (ZMod 2) F := ZMod.algebra _ 2
local instance : IsElementaryAbelian 2 (⁅D.fullModule,L⁆ : Subgroup G) :=
  source_original_full_moved_elementary D
variable (e : (L ⧸ pCore 2 L) ≃* SL(2,F))
  (c : BinaryConjugationSection L ⁅D.fullModule,L⁆ (sourceMovedFixed D)
    (SL2.BinarySmall.natural.comp
      (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L)))))

include e c

/-- Each natural-cover vector is fixed by a component conjugate of a linear two-actor. -/
theorem conjugate_point_fixed_of_linear_actor
    (P : Subgroup G) (hP : IsPGroup 2 P)
    (hactor : P ≤ L ⊔ centralizer (↑(⁅D.fullModule,L⁆ : Subgroup G) : Set G))
    {v : G} (hv : v ∈ ⁅D.fullModule,L⁆) :
    ∃ l : L, P.map (MulAut.conj (l : G)).toMonoidHom ≤ centralizer ({v} : Set G) := by
  let W := ⁅D.fullModule,L⁆
  let π := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))
  have hπ : Function.Surjective π := e.surjective.comp (QuotientGroup.mk'_surjective _)
  obtain ⟨σ,hσinj,hσ⟩ := moved_action D e c
  change ∀ (l : L) (w : Additive W), ((σ (π l) w).toMul : G) =
    l*w.toMul*(l : G)⁻¹ at hσ
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
  let θh : P →* SL(2,F) := {
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

theorem thompson_point_fixed (hF : 2 < Nat.card F)
    {v : G} (hv : v ∈ ⁅D.fullModule,L⁆) :
    ∃ l : L, (elementaryAbelianMaxJ (T : Subgroup G)).map
      (MulAut.conj (l : G)).toMonoidHom ≤ centralizer ({v} : Set G) :=
  conjugate_point_fixed_of_linear_actor D e c _
    (T.isPGroup'.to_le (sSup_le fun _ hA => hA.1))
    (thompson_le_linear_actor D e c hF) hv

omit e c [Finite G] in
private theorem fixed_representative_of_conjugate_fixed
    (S W : Subgroup G) {v m : G} (hv : v ∈ W)
    (hm : m ∈ normalizer (W : Set G))
    (hfix : (elementaryAbelianMaxJ S).map (MulAut.conj m).toMonoidHom ≤ centralizer ({v} : Set G)) :
    (MulAut.conj m⁻¹) v ∈ W ⊓ centralizer (elementaryAbelianMaxJ S : Set G) := by
  refine ⟨(mem_normalizer_iff.mp ((normalizer (W : Set G)).inv_mem hm) v).mp hv,?_⟩
  intro j hj
  apply (MulAut.conj m).injective
  have hc : (MulAut.conj m) ((MulAut.conj m⁻¹) v) = v := by
    simp only [MulAut.conj_apply,inv_inv]; group
  simpa only [map_mul,hc,MulEquiv.coe_toMonoidHom] using
    (mem_centralizer_singleton_iff.mp (hfix (mem_map_of_mem (MulAut.conj m).toMonoidHom hj)))

/-- Every vector, including a kernel vector, has an original Thompson-fixed representative. -/
theorem thompson_fixed_representative (hF : 2 < Nat.card F)
    {v : G} (hv : v ∈ ⁅D.fullModule,L⁆) :
    ∃ l ∈ L, (MulAut.conj l) v ∈ ⁅D.fullModule,L⁆ ⊓
      centralizer (elementaryAbelianMaxJ (T : Subgroup G) : Set G) := by
  obtain ⟨l,hl⟩ := thompson_point_fixed D e c hF hv
  exact ⟨(l:G)⁻¹,L.inv_mem l.property,
    fixed_representative_of_conjugate_fixed _ _ hv (c.normalized l.property) hl⟩

/-- The literal partner orbit is fixed by conjugates of the original Baumann subgroup. -/
theorem partner_baumann_conjugate_fixed (hF : 2 < Nat.card F)
    {t v : G} (ht : t ∈ (T : Subgroup G))
    (hv : v ∈ (⁅D.fullModule,L⁆).map (MulAut.conj t).toMonoidHom) :
    ∃ m ∈ D.maximalLocal, (ChapterB.baumann (T : Subgroup G)).map
      (MulAut.conj m).toMonoidHom ≤ centralizer ({v} : Set G) :=
  source_a5_partner_baumann_conjugate_fixed_of_thompson_orbits D
    (fun _ hw => thompson_fixed_representative D e c hF hw) ht hv

omit e c in
/-- The exact natural-module input of the selection contract supplies all partner orbits. -/
theorem partner_baumann_conjugate_fixed_of_rankOneNatural
    (hmodel : RankOneNatural D)
    {t v : G} (ht : t ∈ (T : Subgroup G))
    (hv : v ∈ (⁅D.fullModule,L⁆).map (MulAut.conj t).toMonoidHom) :
    ∃ m ∈ D.maximalLocal, (ChapterB.baumann (T : Subgroup G)).map
      (MulAut.conj m).toMonoidHom ≤ centralizer ({v} : Set G) := by
  obtain ⟨n,hn,e,⟨c⟩⟩ := hmodel
  let : NeZero n := ⟨by omega⟩
  have hF : 2 < Nat.card (GaloisField 2 n) := by
    rw [GaloisField.card 2 n (by omega)]
    exact (show 2^1 < 2^n from pow_lt_pow_right₀ (by decide) hn)
  exact partner_baumann_conjugate_fixed D e c hF ht hv


end CFSG.Quasithin.Chapter10.PointControl.Selection.RankOne
