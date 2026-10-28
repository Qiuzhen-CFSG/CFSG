module

public import Theory.AlgebraicGroup.Instance.PGL2UnipotentStabilizer
public import Theory.AlgebraicGroup.Bor1.RankOneGeometry.RadicalFixed

/-!
# Rank-one source consequences of the actual projective-line action

An actual PGL₂ morphism with exact Borel point stabilizer has finite central
kernel. Its restriction to the supplied unipotent radical therefore gives
dimension at most one; B/N generation gives positive dimension. The radical's
torus-fixed subgroup is trivial, so its intersection with the central kernel
is trivial. For two distinct Borels through the same torus, factor an element
of their intersection as a torus point times a radical point. The latter fixes
two projective-line points and is trivial, proving that the intersection is
exactly the torus. No surjectivity or separability of the realizing morphism is
needed. This is Borel §§13.13--13.14, retaining the realization input discharged
by the independent curve and automorphism theorems in final assembly.
-/

public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace Theory.AlgebraicGroup.Bor1.RankOneGeometry
open Variety.Geometric
universe u
variable {k : Type u} [Field k] [IsAlgClosed k]
variable {G : Variety k} [AlgebraicGroup G]
local instance : MulAction (Variety.Point (pgl2Variety (k := k))) (Point (projectiveLine k)) :=
  pgl2ProjectiveLinePointMulAction

private theorem point_stabilizer_kernel_finite_central
    (hG : IsSemisimpleAlgebraicGroup G) (B : ClosedSubgroup G) (hB : IsBorelSubgroup B)
    (φ : AlgebraicGroup.Morphism G (pgl2Variety (k := k)))
    (p : Point (projectiveLine k))
    (hstab : ∀ g : Variety.Point G, φ.onPoints g • p=p ↔ g∈B.toSubgroup) :
    Finite (Variety.Point φ.kernelClosedSubgroup.carrierVariety) ∧
      φ.kernel ≤ Subgroup.center (Variety.Point G) := by
  apply semisimple_normal_le_borel_finite_central hG B hB φ.kernelClosedSubgroup
    (show φ.kernel.Normal from inferInstance)
  intro g hg
  apply (hstab g).mp
  rw [show φ.onPoints g=1 from hg,one_smul]

omit [IsAlgClosed k] in
private theorem finite_kernel_restrict
    {D : Variety k} [AlgebraicGroup D] (φ : AlgebraicGroup.Morphism G D)
    (hker : Finite (Variety.Point φ.kernelClosedSubgroup.carrierVariety))
    (V : ClosedSubgroup G) :
    Finite (Variety.Point (φ.comp V.inclusion).kernelClosedSubgroup.carrierVariety) := by
  let f := φ.comp V.inclusion
  let : Finite φ.kernel := Finite.of_equiv _ φ.kernelClosedSubgroup.pointEquiv
  let j : f.kernel → φ.kernel := fun v => ⟨V.inclusion.onPoints v.1,v.2⟩
  have hj : Function.Injective j := by
    intro v w he
    apply Subtype.ext
    apply V.inclusion_injective
    exact congrArg (fun z : φ.kernel => z.1) he
  let : Finite f.kernel := Finite.of_injective j hj
  let : Finite f.kernelClosedSubgroup.toSubgroup := (inferInstance : Finite f.kernel)
  exact Finite.of_equiv _ f.kernelClosedSubgroup.pointEquiv.symm

private theorem radical_connected_carrier
    (B V : ClosedSubgroup G) (hB : IsBorelSubgroup B) (hV : IsUnipotentRadicalOf B V) :
    Variety.IsConnected V.carrierVariety := by
  obtain ⟨V',hV',hc⟩ := exists_unipotentRadical_of_connected_solvable B hB.connected hB.solvable
  have he : V'=V := unipotent_radical_unique hV' hV
  subst V'
  let e := Variety.closedSubvarietyPointHomeomorph V.isZariskiClosed
  let : ConnectedSpace {x : Variety.Point G // x∈(V : Set (Variety.Point G))} :=
    Subtype.connectedSpace hc
  let : ConnectedSpace (Variety.Point V.carrierVariety) := e.connectedSpace_iff.mpr inferInstance
  exact connectedSpace_iff_univ.mp inferInstance

theorem unipotentRadical_dimension_eq_one_of_pgl2_realization
    (hG : IsSemisimpleAlgebraicGroup G)
    (T B V : ClosedSubgroup G) (hT : IsMaximalTorus T)
    (hdimT : Variety.dimension T.carrierVariety=1)
    (hB : IsBorelSubgroup B) (hTB : T≤B) (hV : IsUnipotentRadicalOf B V)
    (φ : AlgebraicGroup.Morphism G (pgl2Variety (k := k)))
    (p : Point (projectiveLine k))
    (hstab : ∀ g : Variety.Point G, φ.onPoints g • p=p ↔ g∈B.toSubgroup) :
    Variety.dimension V.carrierVariety=1 := by
  have hker := (point_stabilizer_kernel_finite_central hG B hB φ p hstab).1
  have hle := finite_kernel_unipotent_pgl2_point_fixer_dimension_le_one
    (radical_connected_carrier B V hB hV) hV.2.1 (φ.comp V.inclusion)
    (finite_kernel_restrict φ hker V) p (fun v => (hstab _).mpr (hV.1 (V.pointEquiv v).2))
  have hpos := unipotentRadical_dimension_pos hG T B V hT hdimT hB hTB hV
  exact le_antisymm hle (Cardinal.one_le_iff_pos.mpr hpos)

private theorem conjugate_fixes
    (B : ClosedSubgroup G) (φ : AlgebraicGroup.Morphism G (pgl2Variety (k := k)))
    (p : Point (projectiveLine k))
    (hstab : ∀ g : Variety.Point G, φ.onPoints g • p=p ↔ g∈B.toSubgroup)
    (g z : Variety.Point G) (hz : z∈B.conjugate g) :
    φ.onPoints z • (φ.onPoints g • p)=φ.onPoints g • p := by
  have h := (hstab _).mpr ((B.mem_conjugate_iff g z).mp hz)
  apply (MulAction.injective (φ.onPoints g)⁻¹)
  simpa only [map_mul,map_inv,mul_smul,inv_smul_smul] using h

theorem common_torus_borel_intersection_of_pgl2_realization
    (hG : IsSemisimpleAlgebraicGroup G)
    (T B V C : ClosedSubgroup G) (hT : IsMaximalTorus T)
    (hdimT : Variety.dimension T.carrierVariety=1)
    (hB : IsBorelSubgroup B) (hTB : T≤B) (hV : IsUnipotentRadicalOf B V)
    (hC : IsBorelSubgroup C) (hTC : T≤C) (hne : C≠B)
    (φ : AlgebraicGroup.Morphism G (pgl2Variety (k := k)))
    (p : Point (projectiveLine k))
    (hstab : ∀ g : Variety.Point G, φ.onPoints g • p=p ↔ g∈B.toSubgroup) :
    B.inter C=T := by
  obtain ⟨g,hCg⟩ := BorelGeometricConjugacy.conjugacy hB hC
  let q := φ.onPoints g • p
  have hpq : p≠q := by
    intro he
    have hgB := (hstab g).mp he.symm
    exact hne (hCg.trans (B.conjugate_eq_self_of_mem_normalizer g
      (B.toSubgroup.le_normalizer hgB)))
  have hdimV := unipotentRadical_dimension_eq_one_of_pgl2_realization hG T B V hT hdimT hB hTB hV φ p hstab
  have hcentral := (point_stabilizer_kernel_finite_central hG B hB φ p hstab).2
  have hkerV := central_kernel_inf_unipotentRadical_eq_bot_of_dimension_one
    hG T B V hT hdimT hB hTB hV hdimV φ.kernel hcentral
  apply SetLike.coe_injective
  apply Set.Subset.antisymm
  · intro z hz
    obtain ⟨t,v,ht,hv,hzv⟩ :=
      (maximalTorus_unipotentRadical_decomposition_of_connected_solvable
        hB.connected hB.solvable hV hT hTB).1 z hz.1
    have hzp : φ.onPoints v • p=p := (hstab v).mpr (hV.1 hv)
    have htq : φ.onPoints t • q=q := conjugate_fixes B φ p hstab g t (hCg ▸ hTC ht)
    have hzq : φ.onPoints z • q=q := conjugate_fixes B φ p hstab g z (hCg ▸ hz.2)
    have hvq : φ.onPoints v • q=q := by
      apply (MulAction.injective (φ.onPoints t))
      change φ.onPoints t • (φ.onPoints v • q)=φ.onPoints t • q
      calc
        _ = φ.onPoints (t*v) • q := by rw [map_mul,mul_smul]
        _ = q := by rw [←hzv];exact hzq
        _ = φ.onPoints t • q := htq.symm
    let vv := V.pointEquiv.symm ⟨v,hv⟩
    have hu := morphism_preserves_unipotentElement (φ.comp V.inclusion) vv (hV.2.1 vv)
    have hvv : V.inclusion.onPoints vv=v := congrArg Subtype.val (V.pointEquiv.apply_symm_apply _)
    change IsUnipotentElement (pgl2Variety (k := k)) (φ.onPoints (V.inclusion.onPoints vv)) at hu
    rw [hvv] at hu
    have hphi := unipotent_two_fixed_points_eq_one (φ.onPoints v) hu p q hpq hzp hvq
    have hv1 : v=1 := Subgroup.mem_bot.mp (hkerV ▸ (show v∈φ.kernel⊓V.toSubgroup from ⟨hphi,hv⟩))
    change z∈T.toSubgroup
    rw [hzv,hv1,mul_one]
    exact ht
  · intro t ht
    exact ⟨hTB ht,hTC ht⟩
end Theory.AlgebraicGroup.Bor1.RankOneGeometry
