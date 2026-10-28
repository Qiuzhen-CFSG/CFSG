module

public import Theory.AlgebraicGroup.Bor1.SeparatingBorel.CentralizerCharacters
public import Theory.AlgebraicGroup.Bor1.SeparatingBorel.CentralizerAttractor
public import Theory.AlgebraicGroup.Bor1.SeparatingBorel.BorelAttractor
public import Theory.AlgebraicGroup.Bor1.SeparatingBorel.PointStabilizer

/-!
# Borel IV, 13.12: a separating Borel

For two distinct codimension-one subtori with nonsolvable centralizers, use
one original Chevalley model of the Borel orbit. The two centralizer orbits
produce independent regular character ratios with those subtori as connected
kernels. An actual semiregular cocharacter gives these ratios opposite signs.
Its attracting Borel has the original fixed Borel on the first centralizer
and the other fixed Borel on the second centralizer.

This proves the original existential conclusion with literal pointwise
centralizers and no geometric-output premise.
Source: Borel, *Linear Algebraic Groups*, IV, 13.11--13.12,
`refs/KGroup/Bor1/Chapter4.tex`, lines 713--775.
-/

public section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open Theory.AlgebraicGroup.Variety.Geometric
open scoped LinearAlgebra.Projectivization
namespace Theory.AlgebraicGroup.Bor1.SeparatingBorel
open ProjectiveLimit
universe u
variable {k : Type u} [Field k] [IsAlgClosed k]
variable {G : Variety k} [AlgebraicGroup G]
attribute [local instance] ClosedSubgroup.carrierAlgebraicGroup

theorem exists_separating_borel
    (hG : Variety.IsConnected G) (T S Q B : ClosedSubgroup G)
    (hT : IsMaximalTorus T) (hS : IsSubtorus S) (hQ : IsSubtorus Q)
    (hST : S ≤ T) (hQT : Q ≤ T)
    (hScodim : Variety.dimension S.carrierVariety + 1 = Variety.dimension T.carrierVariety)
    (hQcodim : Variety.dimension Q.carrierVariety + 1 = Variety.dimension T.carrierVariety)
    (hSQ : S ≠ Q)
    (hSn : ¬ Group.IsSolvable (Variety.Point S.centralizer.carrierVariety))
    (hQn : ¬ Group.IsSolvable (Variety.Point Q.centralizer.carrierVariety))
    (hB : IsBorelSubgroup B) (hTB : T ≤ B) :
    ∃ B' : ClosedSubgroup G, IsBorelSubgroup B' ∧ T ≤ B' ∧
      B'.pointwiseCentralizer S = B.pointwiseCentralizer S ∧
      B'.pointwiseCentralizer Q ≠ B.pointwiseCentralizer Q := by
  obtain ⟨E,hEa,hEm,hEf,ρ,b,A,x,hρ,he,hx⟩ := TorusBorelGeneration.exists_projective_action_stabilizer B
  obtain ⟨v,hv0,rfl⟩ := exists_projective_vector b x
  let x : Point (projectiveSpace k E) :=
    projectivePointOfVector (b.equivFun v) (b.equivFun.map_ne_zero_iff.mpr hv0)
  obtain ⟨α,hv,_⟩ := weight_of_projective_fixed_vector ρ hρ T A b he v hv0 (by
    intro t
    exact (hx (T.includePoint t)).mpr (hTB (T.pointEquiv t).property))
  obtain ⟨wS,βS,hwS,hneS,hSorb,hSx,hScover,hSker⟩ :=
    exists_centralizer_orbit_character hG S T B hS hT hST hScodim hSn hB hTB ρ hρ A b he v α hv hx
  obtain ⟨wQ,βQ,hwQ,hneQ,hQorb,hQx,hQcover,hQker⟩ :=
    exists_centralizer_orbit_character hG Q T B hQ hT hQT hQcodim hQn hB hTB ρ hρ A b he v α hv hx
  have hαS : α * βS⁻¹ ≠ 1 := fun h => hneS (mul_inv_eq_one.mp h)
  have hαQ : α * βQ⁻¹ ≠ 1 := fun h => hneQ (mul_inv_eq_one.mp h)
  have hi : LinearIndependent ℤ ![Additive.ofMul (α * βS⁻¹), Additive.ofMul (α * βQ⁻¹)] := by
    apply characters_independent_of_connectedKernel_ne hT.1.isConnected _ _ hαS hαQ
    intro hh
    apply hSQ
    rw [← hSker, ← hQker]
    unfold TorusCharacter.ambientConnectedKernel
    rw [hh]
  obtain ⟨c,hcS,hcQ,hc⟩ := exists_separating_semiregular_cocharacter T hT.1 _ _ hi
  obtain ⟨U,y,hy,hyB,hyT,hyU,hcurve⟩ := exists_borel_attractor hG B hB ρ hρ A b he x hx T hT c hc
  have hxB : A.pointStabilizer x = B := by
    apply SetLike.coe_injective
    ext g
    change g ∈ (A.pointStabilizer x).toSubgroup ↔ g ∈ B.toSubgroup
    rw [A.mem_pointStabilizer]
    exact hx g
  have hxB' : IsBorelSubgroup (A.pointStabilizer x) := hxB.symm ▸ hB
  have hxT : T ≤ A.pointStabilizer x := hxB.symm ▸ hTB
  have hSsame := centralizer_attractor_stabilizer_eq hG S T hS hT hST ρ hρ A b he x y
    hxB' hxT hyB hyT hy c hc U hyU (fun z hz hu => (hcurve z hz).mp hu)
    v wS α βS hv hwS (by
      refine ⟨1,?_⟩
      change A.toMulAction.smul (S.centralizer.inclusion.onPoints 1) x = x
      rw [map_one]
      exact A.toMulAction.one_smul x)
    hScover (by simpa only [div_eq_mul_inv] using hcS)
  have hQpositive : 0 < characterCocharacterPairing T c (Additive.ofMul (βQ / α)) := by
    have hh : characterCocharacterPairing T c (Additive.ofMul (α * βQ⁻¹)) =
        characterCocharacterPairing T c (Additive.ofMul α) -
          characterCocharacterPairing T c (Additive.ofMul βQ) := map_sub _ _ _
    rw [hh] at hcQ
    apply (character_ratio_pairing_pos_iff T c βQ α).mpr
    omega
  have hQsame := centralizer_attractor_stabilizer_eq hG Q T hQ hT hQT ρ hρ A b he x y
    hxB' hxT hyB hyT hy c hc U hyU (fun z hz hu => (hcurve z hz).mp hu)
    wQ v βQ α hwQ hv hQorb (fun z hz ht => (hQcover z hz ht).symm) hQpositive
  refine ⟨A.pointStabilizer y,hyB,hyT,?_,?_⟩
  · apply (centralizer_preimage_eq_iff_pointwiseCentralizer_eq S _ B).mp
    rw [← hxB, ← pointStabilizer_restrict, ← pointStabilizer_restrict]
    exact hSsame
  · intro hbad
    have hp := (centralizer_preimage_eq_iff_pointwiseCentralizer_eq Q _ B).mpr hbad
    have hp' : (A.pullbackGroup Q.centralizer.inclusion).pointStabilizer y =
        (A.pullbackGroup Q.centralizer.inclusion).pointStabilizer x := by
      rw [pointStabilizer_restrict, pointStabilizer_restrict, hxB]
      exact hp
    have hBq := centralizer_restricted_stabilizer_isBorel hG A x Q hQ hxB'
      (fun q hq => hxT (hQT hq))
    have hQconn := SemisimpleCenterContainment.CartanGeometry.subtorus_centralizer_isConnected hG hQ
    apply hQx
    exact point_eq_of_borel_stabilizer_eq hQconn (A.pullbackGroup Q.centralizer.inclusion) x _ hBq
      hQorb (hQsame.symm.trans hp')
end Theory.AlgebraicGroup.Bor1.SeparatingBorel
