module
public import CFSG.Quasithin.Chapter13.Section03.SourceCompletion.MarkedAction
public import CFSG.Quasithin.Chapter13.Section03.UnitaryGeometry.StandardAlignment
/-!
# The original unitary intersection obstruction is discharged

The actual reduced module and its Sylow centralizer construct Hypothesis
E.6.1 from the original uniqueness and TI data. A single compatible flag
marking identifies the earlier three-space with the native standard space.
The point is contained in that three-space, so the original point/three-space
normalizer bound also controls its centralizer. The complete original pair
alignment theorem then rules out every nontrivial commutator contained in
the intersection of two conjugate modules.

Neither an E.6.1 package, a coordinate position, a three-space centralizer
bound nor the commutator conclusion is an additional premise.
Source: Aschbacher–Smith 13.3.12(4), 13.3.15 and 13.3.17(1), pp.889–895.
-/
public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section03.SourceCompletion
open ChapterE ChapterE.Section06
open Atlas.G2.Natural.BinaryPointFlag
variable {G : Type*} [Group G] [Finite G] {V : Subgroup G} [IsElementaryAbelian 2 V] {Kc:GroupClass}

omit [Finite G] in
private theorem point_coordinates_eq_ambient (E:Additive V≃ₗ[F]W) (A:Subgroup G) :
    pointCoordinateSubspace E A = (UnitaryGeometry.ambientSpace (V:=V) A).map E.toLinearMap := by
  ext w
  obtain ⟨v,rfl⟩ := E.surjective w
  rw [mem_pointCoordinateSubspace]
  constructor
  · intro hv
    exact ⟨v,hv,rfl⟩
  · rintro ⟨x,hx,hxv⟩
    exact E.injective hxv ▸ hx

omit [Finite G] in
private theorem standard_three_eq_of_flag (E:Additive V≃ₗ[F]W) (R:Subgroup G)
    (hRV:R≤V) (hR:pointCoordinateSubspace E R=seed) :
    UnitaryGeometry.standardThree E=R := by
  apply pointCoordinateSubspace_injective E (UnitaryGeometry.standardThree_le E) hRV
  rw [point_coordinates_eq_ambient,UnitaryGeometry.standardThree_space,hR]
  ext x
  rw [mem_seed]
  rfl

/-- The original core and uniqueness data construct the genuine E.6.1
hypothesis used in the unitary pair theorem. -/
theorem unitary_source_E61
    (hG:IsSimpleQTKE Kc G)
    (T:Sylow 2 G) (L M:Subgroup G) (hne:V≠⊥)
    (hVLT:V≤L⊔(T:Subgroup G))
    (hLTN:L⊔(T:Subgroup G)≤normalizer (V:Set G))
    (hLTM:L⊔(T:Subgroup G)≤M)
    (hsyl:(T:Subgroup G)⊓centralizer (V:Set G)=(L⊔(T:Subgroup G)).pCoreIn 2)
    (hu:∀N:Subgroup G,IsMaximalTwoLocal N→L⊔(T:Subgroup G)≤N→N=M)
    (hTI:∀g∈M,V⊓V.map (MulAut.conj g).toMonoidHom=⊥ ∨
      V.map (MulAut.conj g).toMonoidHom=V) :
    HypothesisE61 Kc T M V := by
  have hlocal:IsTwoLocal (normalizer (V:Set G)):=
    ⟨V,hne,IsElementaryAbelian.isPGroup 2 V,rfl⟩
  obtain ⟨N,hNV,hN⟩:=Finite.exists_le_maximal hlocal
  have hNM:=hu N hN (hLTN.trans hNV)
  have hM:IsMaximalTwoLocal M:=hNM ▸ hN
  have hVQ:V≤(L⊔(T:Subgroup G)).pCoreIn 2:=
    le_pCoreIn_of_normalizes (IsElementaryAbelian.isPGroup 2 V) hVLT hLTN
  have hVT:V≤(T:Subgroup G):=by rw [←hsyl] at hVQ;exact hVQ.trans inf_le_left
  refine ⟨hG,hM,le_sup_right.trans hLTM,hne,inferInstance,hVT,
    (normal_subgroupOf_iff_le_normalizer hVT).mpr (le_sup_right.trans hLTN),hTI,?_⟩
  intro K hK hbound
  apply hu K hK
  apply le_trans _ hbound
  refine le_inf (le_inf hLTM hLTN) ?_
  change L⊔(T:Subgroup G)≤normalizer (((T:Subgroup G)⊓centralizer (V:Set G):Subgroup G):Set G)
  rw [hsyl]
  exact (L⊔(T:Subgroup G)).le_normalizer.trans
    (normalizer_le_normalizer_characteristic_image _ (pCore 2 _))

omit [IsElementaryAbelian 2 V] in
/-- The original point/three-space normalizer bound discharges the full
noncommuting-intersection premise using the same original unitary flag. -/
theorem unitary_intersection_commutator_eq_bot_of_source
    (D:ChapterF.Section09.Setup G) [IsElementaryAbelian 2 D.V]
    (hG:IsSimpleQTKE Kc G)
    (e:inducedAutomizer D.V D.L≃*Atlas.G2.Natural.BinaryNormalizer.Derived)
    (E0:Additive D.V≃ₗ[F]Atlas.G2.Natural.Space F)
    (he0:∀(l:inducedAutomizer D.V D.L) v,E0 (automizerRepresentation D.V l v)=
      Atlas.G2.Natural.derivedAction F (e l) (E0 v))
    (hUV:D.Vplus≤D.V) (hZV:D.V₁≤D.V)
    (hTZ:(D.T:Subgroup G)≤normalizer (D.V₁:Set G))
    (hTU:(D.T:Subgroup G)≤normalizer (D.Vplus:Set G))
    (hZ:Nat.card D.V₁=2) (hU:Nat.card D.Vplus=8)
    (hTL:(D.T:Subgroup G)≤normalizer (D.L:Set G))
    (hVLT:D.V≤D.LT) (hred:IsPReduced 2 (D.V.subgroupOf D.LT))
    (hsyl:(D.T:Subgroup G)⊓centralizer (D.V:Set G)=D.LT.pCoreIn 2)
    (hcontrol:D.H⊓normalizer (D.Vplus:Set G)≤normalizer (D.V:Set G))
    (hNL:normalizer (D.V:Set G)≤normalizer (D.L:Set G))
    (hu:∀N:Subgroup G,IsMaximalTwoLocal N→D.LT≤N→N=normalizer (D.L:Set G))
    (B:Subgroup G) (hBV:B≤D.V)
    (hTB:(D.T:Subgroup G)≤normalizer (B:Set G)) (hB:Nat.card B=4)
    (hHfull:D.H=normalizer (D.V₁:Set G))
    (hTI:∀g∈normalizer (D.L:Set G),D.V⊓D.V.map (MulAut.conj g).toMonoidHom=⊥ ∨
      D.V.map (MulAut.conj g).toMonoidHom=D.V)
    (g:G) (hc:⁅D.V,D.V.map (MulAut.conj g).toMonoidHom⁆≤
      D.V⊓D.V.map (MulAut.conj g).toMonoidHom) :
    ⁅D.V,D.V.map (MulAut.conj g).toMonoidHom⁆=⊥ := by
  have hLTN:D.LT≤normalizer (D.V:Set G):=
    (normal_subgroupOf_iff_le_normalizer hVLT).mp hred.normal
  have hVn:D.V≠⊥ := by
    intro h
    have hz:D.V₁=⊥:=le_bot_iff.mp (h ▸ hZV)
    rw [hz,Subgroup.card_bot] at hZ
    omega
  have hE:=unitary_source_E61 hG D.T D.L (normalizer (D.L:Set G)) hVn hVLT hLTN
    (sup_le D.L.le_normalizer hTL) hsyl hu hTI
  obtain ⟨rho,E,he,_,hd,hz,_,hs⟩:=exists_unitary_flag_marking D.T D.L D.V₁ B D.Vplus
    (le_sup_left.trans hLTN) hNL e E0 he0 (le_sup_right.trans hLTN)
    hZV hBV hUV hTZ hTB hTU hZ hB hU
  have hZR:D.V₁≤D.Vplus := by
    intro z hzZ
    let v:Additive D.V:=Additive.ofMul ⟨z,hZV hzZ⟩
    have hv:E v∈pointLine:=hz ▸ (mem_pointCoordinateSubspace E D.V₁ v).mpr hzZ
    exact (mem_pointCoordinateSubspace E D.Vplus v).mp (hs.symm ▸ pointLine_le_seed hv)
  have hC:centralizer (D.Vplus:Set G)≤normalizer (D.L:Set G) := by
    apply le_trans _ (hcontrol.trans hNL)
    refine le_inf ?_ (Subgroup.centralizer_le_normalizer _)
    rw [hHfull]
    exact (centralizer_le hZR).trans (Subgroup.centralizer_le_normalizer _)
  have hstd:=standard_three_eq_of_flag E D.Vplus hUV hs
  exact UnitaryGeometry.source_commuting_intersections_of_three_centralizer hE E rho he hd
    D.L.le_normalizer (by rwa [hstd]) g hc

end CFSG.Quasithin.Chapter13.Section03.SourceCompletion
