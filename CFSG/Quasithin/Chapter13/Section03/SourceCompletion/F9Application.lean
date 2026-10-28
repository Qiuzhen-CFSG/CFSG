module
public import CFSG.Quasithin.Chapter13.Section03.SourceCompletion.PointKernel
public import Theory.Representation.G2BinaryPointIrreducible
public import Theory.Representation.G2BinaryPlaneHyperplaneSpan
public import CFSG.Quasithin.Chapter13.Section03.SourceCompletion.PointClosure
/-!
# Constructing the original unitary F.9 hypothesis and abelian closure

The literal natural-six coordinates supply the point of order two, its
Sylow fixation and irreducibility of V₃/V₁. The original normalizer control
puts the quotient kernel into N(V); PointKernel proves its required
normal-core bound from faithful component action and uniqueness over LT.
Uniqueness also kills the core of ⟨LT,H⟩, while 13.3.17's intersection
conclusion gives the commutator-lifting clause. This constructs F.9.1 on
the exact original Setup, rather than assuming it.

The final consumer then proves V_H abelian with every F.9, hyperplane,
plane-core and cross-displacement premise discharged. Genuine earlier
13.3.2/12.2.2 chosen-module normality, reducedness, faithful kernel and
parabolic marking, 1.2.7 uniqueness, characteristic two, and 13.3.17's
normalizer/rank/intersection/noncentrality conclusions remain with their
source producers. These are not additional exclusions on Hypothesis13.3.1.

Source: Aschbacher–Smith 13.3.18(1–2), printed pp.894–895.
-/

public section
namespace CFSG.Quasithin.Chapter13.Section03.SourceCompletion
open Subgroup ChapterE Theory.GroupTheory Representation.BinaryOffender
open scoped IsMulCommutative
open Atlas.G2.Natural.BinaryPointFlag
variable {G:Type*} [Group G] [Finite G] {V:Subgroup G} [IsElementaryAbelian 2 V]

omit [Finite G] in
/-- The original point parabolic is irreducible on the marked seed modulo
its point; all invariant subgroups use literal ambient normalizers. -/
theorem point_seed_irreducible (U Z J:Subgroup G)
    (rho:Automizer V→*Atlas.G2.Model F) (E:Additive V≃ₗ[F]W)
    (he:∀a v,E (automizerRepresentation V a v)=
      Atlas.G2.Restricted.NaturalCoordinates.action F (rho a) (E v))
    (hs:pointCoordinateSubspace E U=seed) (hz:pointCoordinateSubspace E Z=pointLine)
    (hUV:U≤V)
    (hP:Atlas.G2.BinaryParabolicPair.derivedSecondAmbient≤(inducedAutomizer V J).map rho) :
    ∀A:Subgroup G,Z≤A→A≤U→J≤normalizer (A:Set G)→A=Z∨A=U := by
  intro A hZA hAU hJA
  have hlow:pointLine≤pointCoordinateSubspace E A :=
    hz ▸ pointCoordinateSubspace_mono E hZA
  have hhigh:pointCoordinateSubspace E A≤seed :=
    hs ▸ pointCoordinateSubspace_mono E hAU
  have hinv (a:Atlas.G2.Model F) (ha:a∈Atlas.G2.BinaryParabolicPair.derivedSecondAmbient)
      (v:W) (hv:v∈pointCoordinateSubspace E A) :
      Atlas.G2.Restricted.NaturalCoordinates.action F a v∈pointCoordinateSubspace E A := by
    obtain ⟨i,⟨n,hnJ,rfl⟩,rfl⟩:=hP ha
    obtain ⟨w,rfl⟩:=E.surjective v
    rw [←he,mem_pointCoordinateSubspace]
    exact (mem_normalizer_iff.mp (hJA hnJ) w.toMul.val).mp
      ((mem_pointCoordinateSubspace E A w).mp hv)
  rcases seed_point_invariant_interval (pointCoordinateSubspace E A) hlow hhigh
    (hinv _ point_actor_membership.1) (hinv _ point_actor_membership.2.1) with h|h
  · exact Or.inl (pointCoordinateSubspace_injective E (hAU.trans hUV)
      (hZA.trans (hAU.trans hUV)) (h.trans hz.symm))
  · exact Or.inr (pointCoordinateSubspace_injective E (hAU.trans hUV) hUV (h.trans hs.symm))

omit [Finite G] in
/-- The actual Sylow fixes the original marked point, using its literal
unipotent image rather than a separate flag-invariance assumption. -/
theorem sylow_centralizes_marked_point (T:Sylow 2 G) (Z:Subgroup G)
    (rho:Automizer V→*Atlas.G2.Model F) (E:Additive V≃ₗ[F]W)
    (he:∀a v,E (automizerRepresentation V a v)=
      Atlas.G2.Restricted.NaturalCoordinates.action F (rho a) (E v))
    (hz:pointCoordinateSubspace E Z=pointLine) (hZV:Z≤V)
    (hTN:(T:Subgroup G)≤normalizer (V:Set G))
    (hT:(inducedAutomizer V (T:Subgroup G)).map rho≤Atlas.G2.unipotent) :
    (T:Subgroup G)≤centralizer (Z:Set G) := by
  intro t ht z hz'
  let n:normalizer (V:Set G):=⟨t,hTN ht⟩
  let i:Automizer V:=V.normalizerMonoidHom.rangeRestrict n
  let v:Additive V:=Additive.ofMul ⟨z,hZV hz'⟩
  have hi:rho i∈Atlas.G2.unipotent:=hT ⟨i,⟨n,ht,rfl⟩,rfl⟩
  have hv:E v∈pointLine:=hz ▸ (mem_pointCoordinateSubspace E Z v).mpr hz'
  have hh:=unipotent_fixes_pointLine (rho i) hi (E v) hv
  rw [←he] at hh
  have hc:t*z*t⁻¹=z:=congrArg (fun w:Additive V=>(w.toMul:G)) (E.injective hh)
  exact (mul_inv_eq_iff_eq_mul.mp hc).symm


/-- F.9.1 follows for the original unitary point setup. The point order,
Sylow point action, seed irreducibility, normal-core kernel, generated core
and commutator-lifting clause are all derived here. -/
theorem f9_hypothesis_of_unitary_point_action
    (D:ChapterF.Section09.Setup G) (M:Subgroup G)
    [IsElementaryAbelian 2 D.V] [Group.IsPerfect D.L]
    (rho:Automizer D.V→*Atlas.G2.Model F) (E:Additive D.V≃ₗ[F]W)
    (he:∀a v,E (automizerRepresentation D.V a v)=
      Atlas.G2.Restricted.NaturalCoordinates.action F (rho a) (E v))
    (hs:pointCoordinateSubspace E D.Vplus=seed)
    (hz:pointCoordinateSubspace E D.V₁=pointLine)
    (hUV:D.Vplus≤D.V) (hZV:D.V₁≤D.V)
    (hT:(inducedAutomizer D.V (D.T:Subgroup G)).map rho≤Atlas.G2.unipotent)
    (hP:Atlas.G2.BinaryParabolicPair.derivedSecondAmbient≤
      (inducedAutomizer D.V (D.L₁⊔(D.T:Subgroup G))).map rho)
    (hres:pResidual 2 D.L=⊤)
    (hTL:(D.T:Subgroup G)≤normalizer (D.L:Set G))
    (hcharL:generalizedFitting D.L=pCore 2 D.L)
    (hVLT:D.V≤D.LT) (hred:IsPReduced 2 (D.V.subgroupOf D.LT))
    (hsyl:(D.T:Subgroup G)⊓centralizer (D.V:Set G)=D.LT.pCoreIn 2)
    (hH:D.H≤D.Gz) (hlocal:D.L₁⊔(D.T:Subgroup G)≤D.H)
    (hcharH:generalizedFitting D.H=pCore 2 D.H)
    (hlocalN:D.L₁⊔(D.T:Subgroup G)≤normalizer (D.Vplus:Set G))
    (hcontrol:D.H⊓normalizer (D.Vplus:Set G)≤normalizer (D.V:Set G))
    (hNL:normalizer (D.V:Set G)≤normalizer (D.L:Set G))
    (hfaith:D.L⊓centralizer (D.V:Set G)≤D.L.pCoreIn 2)
    (hu:∀N:Subgroup G,IsMaximalTwoLocal N→D.LT≤N→N=M)
    (hout:¬D.H≤M)
    (hcomm:∀g∈D.H,⁅D.V,D.V.map (MulAut.conj g).toMonoidHom⁆≤
      D.V⊓D.V.map (MulAut.conj g).toMonoidHom →
      ⁅D.V,D.V.map (MulAut.conj g).toMonoidHom⁆=⊥) : D.Hypothesis := by
  have hTN:(D.T:Subgroup G)≤normalizer (D.V:Set G) :=
    le_sup_right.trans ((normal_subgroupOf_iff_le_normalizer hVLT).mp hred.normal)
  have hLN:D.L≤normalizer (D.V:Set G) :=
    le_sup_left.trans ((normal_subgroupOf_iff_le_normalizer hVLT).mp hred.normal)
  have hTC:(D.T:Subgroup G)≤centralizer (D.V₁:Set G):=
    sylow_centralizes_marked_point D.T D.V₁ rho E he hz hZV hTN hT
  have hZ:D.V₁≤D.Vplus := by
    intro z hz'
    let v:Additive D.V:=Additive.ofMul ⟨z,hZV hz'⟩
    have hh:E v∈seed:=pointLine_le_seed (hz ▸ (mem_pointCoordinateSubspace E D.V₁ v).mpr hz')
    exact (mem_pointCoordinateSubspace E D.Vplus v).mp (hs.symm ▸ hh)
  have hZcard:Nat.card D.V₁=2 := by
    rw [←card_pointCoordinateSubspace E D.V₁ hZV,hz,card_pointLine]
  have hUcard:Nat.card D.Vplus=8 := by
    rw [←card_pointCoordinateSubspace E D.Vplus hUV,hs,card_seed]
  have hZlt:D.V₁<D.Vplus := lt_of_le_of_ne hZ (by intro h;rw [h] at hZcard;omega)
  have hVH:D.V≤D.H := by
    have hcore:D.V≤D.LT.pCoreIn 2 := by
      simpa only [pCoreIn,map_subgroupOf_eq_of_le hVLT] using
        map_mono (f:=D.LT.subtype) hred.le_pCore
    have ht:(D.T:Subgroup G)≤D.LT:=le_sup_right
    have hSyl:=pCoreIn_le_sylow D.LT (D.T.subtype ht)
    rw [Sylow.coe_subtype,map_subgroupOf_eq_of_le ht] at hSyl
    exact hcore.trans (hSyl.trans (le_sup_right.trans hlocal))
  refine {
    elementary:=inferInstance
    residual:=hres
    normalizes_L:=hTL
    characteristic_L:=hcharL
    V_le_LT:=hVLT
    reduced:=hred
    sylow_centralizer:=hsyl
    point_card:=hZcard
    normalizes_point:=hTC.trans (Subgroup.centralizer_le_normalizer _)
    point_lt:=hZlt
    plus_le:=hUV
    H_centralizes:=hH
    local_le:=hlocal
    characteristic_H:=hcharH
    kernel_core:=normalCore_point_kernel_le D.T D.L D.H M D.Vplus D.V₁ rho E he hs hUV hVH hZ hH
      hcontrol (le_sup_right.trans hlocal) hTL hLN hNL hfaith hu hout hcharH
    local_normalizes:=hlocalN
    irreducible:=point_seed_irreducible D.Vplus D.V₁ (D.L₁⊔(D.T:Subgroup G)) rho E he hs hz hUV hP
    normalizer_control:=le_inf inf_le_left hcontrol
    generated_core:=sup_twoCore_eq_bot_of_unique D.LT D.H M hu hout
    commutator_lifting:=?_ }
  intro g hg hc _ _
  have hh:=hcomm g hg hc
  constructor
  · exact le_bot_iff.mp ((commutator_mono hUV le_rfl).trans_eq hh)
  · exact le_bot_iff.mp ((commutator_mono (map_mono hUV) le_rfl).trans_eq
      ((commutator_comm _ _).trans hh))

open scoped IsKleinFour
/-- The original abelian-closure consumer, with F.9 applicability and all
subsequent point/hyperplane/cross-action premises discharged in one proof. -/
theorem unitary_closure_abelian_of_earlier_source
    (D:ChapterF.Section09.Setup G) (M:Subgroup G)
    [IsElementaryAbelian 2 D.V] [Group.IsPerfect D.L]
    (rho:Automizer D.V→*Atlas.G2.Model F) (E:Additive D.V≃ₗ[F]W)
    (he:∀a v,E (automizerRepresentation D.V a v)=
      Atlas.G2.Restricted.NaturalCoordinates.action F (rho a) (E v))
    (hs:pointCoordinateSubspace E D.Vplus=seed)
    (hz:pointCoordinateSubspace E D.V₁=pointLine)
    (hUV:D.Vplus≤D.V) (hZV:D.V₁≤D.V)
    (hT:(inducedAutomizer D.V (D.T:Subgroup G)).map rho≤Atlas.G2.unipotent)
    (hP:Atlas.G2.BinaryParabolicPair.derivedSecondAmbient≤
      (inducedAutomizer D.V (D.L₁⊔(D.T:Subgroup G))).map rho)
    (hres:pResidual 2 D.L=⊤)
    (hTL:(D.T:Subgroup G)≤normalizer (D.L:Set G))
    (hcharL:generalizedFitting D.L=pCore 2 D.L)
    (hVLT:D.V≤D.LT) (hred:IsPReduced 2 (D.V.subgroupOf D.LT))
    (hsyl:(D.T:Subgroup G)⊓centralizer (D.V:Set G)=D.LT.pCoreIn 2)
    (hH:D.H≤D.Gz) (hlocal:D.L₁⊔(D.T:Subgroup G)≤D.H)
    (hcharH:generalizedFitting D.H=pCore 2 D.H)
    (hlocalN:D.L₁⊔(D.T:Subgroup G)≤normalizer (D.Vplus:Set G))
    (hcontrol:D.H⊓normalizer (D.Vplus:Set G)≤normalizer (D.V:Set G))
    (hNL:normalizer (D.V:Set G)≤normalizer (D.L:Set G))
    (hfaith:D.L⊓centralizer (D.V:Set G)≤D.L.pCoreIn 2)
    (hu:∀N:Subgroup G,IsMaximalTwoLocal N→D.LT≤N→N=M)
    (hout:¬D.H≤M)
    (hcomm:∀g∈D.H,⁅D.V,D.V.map (MulAut.conj g).toMonoidHom⁆≤
      D.V⊓D.V.map (MulAut.conj g).toMonoidHom →
      ⁅D.V,D.V.map (MulAut.conj g).toMonoidHom⁆=⊥)
    (B X:Subgroup G) [IsKleinFour B] (hBV:B≤D.V) (hPB:D.V₁≤B)
    (hp:pointCoordinateSubspace E B=plane)
    (hXimage:Atlas.G2.BinaryParabolicPair.derivedFirstAmbient≤(inducedAutomizer D.V X).map rho)
    (hr:(3:ℕ∞)<globalR D.V) (hHfull:D.H=normalizer (D.V₁:Set G))
    (hTB:(D.T:Subgroup G)≤normalizer (B:Set G))
    (hXB:X≤normalizer (B:Set G)) (hTX:(D.T:Subgroup G)≤normalizer (X:Set G))
    (hX:IsPPerfect 2 X)
    (hx:Nat.card ((X.subgroupOf (normalizer (B:Set G))).map
      (Chapter13.Section05.AmbientSource.planeAction B))=3)
    (hkX:IsPGroup 2 (X⊓centralizer (B:Set G):Subgroup G))
    (hm:⁅D.QH,B⁆≠⊥) : IsMulCommutative D.VH := by
  have hD:=f9_hypothesis_of_unitary_point_action D M rho E he hs hz hUV hZV hT hP
    hres hTL hcharL hVLT hred hsyl hH hlocal hcharH hlocalN hcontrol hNL hfaith hu hout hcomm
  exact source_closure_abelian_of_point_plane_actions hD rho E he B X hBV hPB hs hp hT hP
    hXimage hcomm hr hHfull hTB hXB hTX hX hx hkX hm

end CFSG.Quasithin.Chapter13.Section03.SourceCompletion
