module
public import CFSG.Quasithin.Chapter13.Section09.CentralizerGrowth.OrthogonalAction
public import CFSG.Quasithin.Chapter13.Section09.CentralizerGrowth.ResidualFusion.Coordinates
public import Theory.SpecificGroups.SymmetricFourWreath.OrthogonalB.Actors

/-!
# The second dihedral factor in the centralizer two-residual

A cubic isometry fixing the marked first-axis involution lifts to its actual
centralizer. Its commutators generate the second nonnormal four-group. The
normal four-group already lies in the residual of the original symmetric-four
factor; together these two four-groups generate the second dihedral factor.
Source: Aschbacher--Smith, The Classification of Quasithin Groups, 13.9.5, printed pp.970--971.
-/

@[expose] public noncomputable section
namespace CFSG.Quasithin.Chapter13.Section09.Marking
open Subgroup SymmetricFourWreath SymmetricFourWreath.OrthogonalB
open scoped IsMulCommutative
variable {G : Type*} [Group G] [Finite G] {d : Configuration G} (m : Marking d)

def BVector (v:BinaryFourPlus.V) : m.B := (m.BLinearCoordinates.symm v).toMul

omit [Finite G] in
theorem BVector_coords (v:BinaryFourPlus.V) : m.BLinearCoordinates (Additive.ofMul (m.BVector v))=v :=
  m.BLinearCoordinates.apply_symm_apply v

omit [Finite G] in
theorem BVector_add (u v:BinaryFourPlus.V) : m.BVector (u+v)=m.BVector u*m.BVector v :=
  congrArg Additive.toMul (m.BLinearCoordinates.symm.map_add u v)

omit [Finite G] in
theorem BVector_sub (u v:BinaryFourPlus.V) : m.BVector (u-v)=m.BVector u*(m.BVector v)⁻¹ := by
  have he := congrArg Additive.toMul (m.BLinearCoordinates.symm.map_sub u v)
  change m.BVector (u-v)=m.BVector u / m.BVector v at he
  exact he.trans (div_eq_mul_inv _ _)

omit [Finite G] in
theorem BVector_native (v:BinaryFourPlus.V) :
    (m.BVector v:G)=m.embedding (((OrthogonalB.linearCoordinates.symm v).toMul):W) := by
  have he : m.BVector v=m.BModelEquiv ((OrthogonalB.linearCoordinates.symm v).toMul) := by
    apply Additive.ofMul.injective
    apply m.BLinearCoordinates.injective
    rw [m.BVector_coords,m.BLinearCoordinates_image]
    exact (OrthogonalB.linearCoordinates.apply_symm_apply v).symm
  exact congrArg Subtype.val he

omit [Finite G] in
theorem BVector_t : (m.BVector (BinaryFourPlus.nonzeroVector 2,0):G)=m.t := by
  rw [m.BVector_native,OrthogonalB.t_coordinate]
  rfl

omit [Finite G] in
theorem BVector_second (u:BinaryFourPlus.Plane) :
    (m.BVector (0,u):G)=m.embedding (SymmetricFourWreath.factor turn (square (planeWord u))) := by
  rw [m.BVector_native,OrthogonalB.second_coordinate]

omit [Finite G] in
theorem BVector_conjugate (g:normalizer (m.B:Set G)) (v:BinaryFourPlus.V) :
    (m.BVector (m.normalizerLinearAction g v):G)=(g:G)*(m.BVector v:G)*(g:G)⁻¹ := by
  have he : m.BVector (m.normalizerLinearAction g v)=m.B.normalizerMonoidHom g (m.BVector v) := by
    apply Additive.ofMul.injective
    apply m.BLinearCoordinates.injective
    rw [m.BVector_coords,←m.normalizerLinearAction_apply,m.BVector_coords]
  exact congrArg Subtype.val he

omit [Finite G] in
theorem B_le_centralizer_t : m.B≤centralizer ({m.t}:Set G) := by
  have ht : m.t∈m.B := m.BVector_t ▸ (m.BVector (BinaryFourPlus.nonzeroVector 2,0)).property
  intro b hb
  exact mem_centralizer_singleton_iff.mpr (congrArg Subtype.val
    ((IsElementaryAbelian.toIsMulCommutative (p:=2) (G:=m.B)).is_comm.comm
      (⟨b,hb⟩:m.B) ⟨m.t,ht⟩))

theorem second_plane_mem_residual
    {𝒦 : GroupClass} (hG:IsSimpleQTKE 𝒦 G)
    (hC : centralizer ({m.z}:Set G)=(d.T:Subgroup G)) (u:BinaryFourPlus.Plane) :
    (m.BVector (0,u):G)∈(pResidual 2 (centralizer ({m.t}:Set G))).map (centralizer ({m.t}:Set G)).subtype := by
  let ρ:=m.normalizerIsometryAction hG hC
  obtain ⟨g,hg⟩ := m.normalizerIsometryAction_surjective hG hC
    (BinaryFourPlus.wreathToIsometry secondCubicWord)
  have hgfix : (g:G)*m.t*(g:G)⁻¹=m.t := by
    rw [←m.BVector_t,←m.BVector_conjugate]
    change (m.BVector ((ρ g).val (BinaryFourPlus.nonzeroVector 2,0)):G)=_
    rw [hg,secondCubicWord_fix_first]
  have hgC : (g:G)∈centralizer ({m.t}:Set G) :=
    mem_centralizer_singleton_iff.mpr (mul_inv_eq_iff_eq_mul.mp hgfix)
  have hg3 : g^3∈ρ.ker := by
    rw [MonoidHom.mem_ker,map_pow,hg,←map_pow,secondCubicWord_cube,map_one]
  rw [m.normalizerIsometryAction_ker hG hC] at hg3
  have hg6 : (g:G)^6=1 := by
    have hgB : ((g:G)^3)∈m.B := hg3
    have h := elemPow_eq_one_of_isElementaryAbelian (p:=2) ((g:G)^3) hgB
    simpa only [←pow_mul] using h
  let C:=centralizer ({m.t}:Set G)
  let R:=pResidual 2 C
  let c:C:=⟨(g:G)^2,C.pow_mem hgC 2⟩
  have hc3 : c^3=1 := by
    apply Subtype.ext
    change ((g:G)^2)^3=1
    simpa only [←pow_mul] using hg6
  have hcR : c∈R := mem_pResidual_of_orderOf_coprime
    ((by decide : Nat.Coprime 2 3).of_dvd_right (orderOf_dvd_of_pow_eq_one hc3))
  obtain ⟨v,hv⟩ := secondCubicWord_difference u
  let b:C:=⟨(m.BVector (0,v):G),m.B_le_centralizer_t (m.BVector (0,v)).property⟩
  have heR : c*b*c⁻¹*b⁻¹∈R := by
    have hn := (inferInstance : R.Normal).conj_mem c⁻¹ (R.inv_mem hcR) b
    simpa only [mul_assoc] using R.mul_mem hcR hn
  refine ⟨c*b*c⁻¹*b⁻¹,heR,?_⟩
  change (g:G)^2*(m.BVector (0,v):G)*((g:G)^2)⁻¹*(m.BVector (0,v):G)⁻¹=(m.BVector (0,u):G)
  have hact : m.normalizerLinearAction (g^2) (0,v)=
      (BinaryFourPlus.wreathToIsometry (secondCubicWord^2)).val (0,v) := by
    change (ρ (g^2)).val _=_
    rw [map_pow,hg,←map_pow]
  have he := m.BVector_conjugate (g^2) (0,v)
  change (m.BVector (m.normalizerLinearAction (g^2) (0,v)):G)=
    (g:G)^2*(m.BVector (0,v):G)*((g:G)^2)⁻¹ at he
  rw [←he,hact]
  exact (congrArg Subtype.val (m.BVector_sub _ _).symm).trans
    (congrArg (fun w=>(m.BVector w:G)) hv)
omit [Finite G] in
def secondFactorCentralizerHom : S4 →* centralizer ({m.t}:Set G) :=
  (m.embedding.comp (SymmetricFourWreath.factor turn)).codRestrict _ (by
    intro a
    apply mem_centralizer_singleton_iff.mpr
    change m.embedding (SymmetricFourWreath.factor turn a)*m.embedding SymmetricFourWreath.t=
      m.embedding SymmetricFourWreath.t*m.embedding (SymmetricFourWreath.factor turn a)
    rw [←map_mul,←map_mul]
    exact congrArg m.embedding (factor_commute turn_ne_one a (square (DihedralGroup.r 2))).eq)

omit [Finite G] in
theorem normal_second_plane_mem_residual (a:plane true) :
    m.embedding (SymmetricFourWreath.factor turn (square a))∈
      (pResidual 2 (centralizer ({m.t}:Set G))).map (centralizer ({m.t}:Set G)).subtype := by
  obtain ⟨b,hb,hc⟩ := normal_plane_odd_products a
  have hmem (x:S4) (hx:x^3=1) : x∈pResidual 2 S4 :=
    mem_pResidual_of_orderOf_coprime
      ((by decide : Nat.Coprime 2 3).of_dvd_right (orderOf_dvd_of_pow_eq_one hx))
  have ha : square a∈pResidual 2 S4 := by
    simpa only [mul_inv_cancel_left] using (pResidual 2 S4).mul_mem (hmem b hb) (hmem _ hc)
  exact ⟨m.secondFactorCentralizerHom (square a),
    map_pResidual_le 2 m.secondFactorCentralizerHom (mem_map_of_mem _ ha),rfl⟩

theorem other_second_plane_mem_residual
    {𝒦 : GroupClass} (hG:IsSimpleQTKE 𝒦 G)
    (hC : centralizer ({m.z}:Set G)=(d.T:Subgroup G)) (a:plane false) :
    m.embedding (SymmetricFourWreath.factor turn (square a))∈
      (pResidual 2 (centralizer ({m.t}:Set G))).map (centralizer ({m.t}:Set G)).subtype := by
  obtain ⟨u,hu⟩ := planeHom_bijective.2 a
  change planeWord u.toAdd=a at hu
  have hm := m.second_plane_mem_residual hG hC u.toAdd
  rwa [m.BVector_second,hu] at hm

omit [Finite G] in
private theorem native_second_axis (a:D8) :
    sylowEmbedding (pair (1,a))=SymmetricFourWreath.factor turn (square a) := by
  apply RegularWreathProduct.ext
  · funext i
    rcases c2_eq_one_or_turn i with rfl|rfl <;>
      simp [sylowEmbedding,pair,SymmetricFourWreath.factor,turn_ne_one,Ne.symm turn_ne_one]
  · rfl

theorem second_factor_le_residual_of_centralizer_eq
    {𝒦 : GroupClass} (hG:IsSimpleQTKE 𝒦 G)
    (hC : centralizer ({m.z}:Set G)=(d.T:Subgroup G)) :
    m.factorSylow turn≤(pResidual 2 (centralizer ({m.t}:Set G))).map (centralizer ({m.t}:Set G)).subtype := by
  intro x hx
  have hxJ := m.factorSylow_le_dihedralBase turn hx
  rw [←m.range_baseProductEmbedding] at hxJ
  obtain ⟨⟨a,b⟩,rfl⟩ := hxJ
  have ha := (m.baseProductEmbedding_mem_second a b).mp hx
  subst a
  change m.embedding (sylowEmbedding (pair (1,b)))∈_
  rw [native_second_axis]
  obtain ⟨a,c,hb⟩ := dihedral_two_planes b
  rw [hb,map_mul,map_mul,map_mul]
  exact Subgroup.mul_mem _ (m.normal_second_plane_mem_residual a)
    (m.other_second_plane_mem_residual hG hC c)

end CFSG.Quasithin.Chapter13.Section09.Marking
