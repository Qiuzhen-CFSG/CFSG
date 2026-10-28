module
public import Stellmacher.ElementaryAbelianMaxPair.NormalizerGeneration
public import Theory.SpecificGroups.SymplecticFour.ThompsonProduct
public import Theory.Representation.SymplecticConjugatePair.ElementaryGeometry.ParabolicWings
public import Theory.SpecificGroups.SymplecticFour.LocalStructure.ParabolicCores
public import Theory.SpecificGroups.SymplecticFour.Sylow.Parabolics
/-! # Actual symplectic wing normalizers generate the component
The two elementary wings are the literal point and plane radicals. Their
normalizers are the full parabolics, which generate Sp₄. The common
maximum-family generation theorem applies after a Sylow alignment of the
original quotient. No parabolic, radical, field-action or Sylow-placement
premise is retained.
Source: Aschbacher--Smith 2.5.7, printed p.555.
-/
public section
open Subgroup Theory.GroupTheory
namespace Theory.SpecificGroups.SymplecticFour.ThompsonInner
open CentralRootGeometry
variable {G F:Type*} [Group G] [Finite G] [Field F] [Finite F] [CharP F 2]
private noncomputable def radicalPair (b:Bool) : Subgroup (Sp F) :=
  if b then pointRadicalAmbient else planeRadicalAmbient
private theorem radicalPair_as_wing (b:Bool) :
    radicalPair (F:=F) b=(wing (!b)).map (unipotent (F:=F)).subtype := by
  let : Algebra (ZMod 2) F:=ZMod.algebra F 2
  cases b
  · exact SymplecticConjugatePair.planeRadical_eq_wing
  · exact SymplecticConjugatePair.pointRadical_eq_wing

theorem component_le_of_maxFamily_normalizers_of_sylow
    (S:Sylow 2 G) (K C M:Subgroup G) [K.Normal]
    (q:K→*Sp F) (hq:Function.Surjective q) (hk:IsPGroup 2 q.ker)
    {n:ℕ} (hn:1<n) (hF:Nat.card F=2^n)
    (hJ:Stellmacher.elementaryAbelianMaxJ (S:Subgroup G)=((S:Subgroup G)⊓K)⊔C)
    (hC:C≤centralizer (K:Set G)) [IsElementaryAbelian 2 C]
    (hker:((S:Subgroup G)⊓K)⊓C≤q.ker.map K.subtype)
    (hlift:∀W:Subgroup (Sp F),IsElementaryAbelian 2 W→IsElementaryAbelian 2 (W.comap q))
    (hM:∀A∈Stellmacher.elementaryAbelianMaxSubgroups (S:Subgroup G),normalizer (A:Set G)≤M) : K≤M := by
  let : Algebra (ZMod 2) F:=ZMod.algebra F 2
  obtain ⟨R,hR⟩:=S.exists_subgroupOf_eq_of_normal K
  let P:=R.mapSurjective (f:=q) hq
  obtain ⟨g,hg⟩:=MulAction.exists_smul_eq (Sp F) P (unipotentSylow hF (by omega))
  let q':K→*Sp F:=(MulAut.conj g).toMonoidHom.comp q
  have hq':Function.Surjective q':=(MulAut.conj g).surjective.comp hq
  have hk':q'.ker=q.ker:=MonoidHom.ker_comp_of_injective _ _ (MulAut.conj g).injective
  have himage:((S:Subgroup G).subgroupOf K).map q'=unipotent (F:=F):=by
    have hh:=congrArg Sylow.toSubgroup hg
    change ((R:Subgroup K).map q).map (MulAut.conj g).toMonoidHom=unipotent (F:=F) at hh
    rw [Subgroup.map_map,hR] at hh
    exact hh
  have hU:(unipotent (F:=F)).comap q'=(S:Subgroup G).subgroupOf K:=by
    rw [←himage]
    apply Subgroup.comap_map_eq_self
    exact hR ▸ (show IsPGroup 2 q'.ker from hk' ▸ hk).le_sylow_of_normal R
  have hDU (b:Bool):radicalPair (F:=F) b≤unipotent:=by
    rw [radicalPair_as_wing]
    exact map_subtype_le _
  have hDcover (A:Subgroup (Sp F)) (hA:IsElementaryAbelian 2 A) (hAU:A≤unipotent) :
      A≤radicalPair true ∨ A≤radicalPair false:=by
    let :=hA
    let : IsElementaryAbelian 2 (A.subgroupOf (unipotent (F:=F))):=IsElementaryAbelian.subgroupOf hAU
    have hstep (b:Bool) (ha:A.subgroupOf (unipotent (F:=F))≤wing (!b)) : A≤radicalPair b:=by
      rw [radicalPair_as_wing]
      intro a ha'
      exact ⟨⟨a,hAU ha'⟩,ha ha',rfl⟩
    exact (SymplecticConjugatePair.elementary_le_wing (A.subgroupOf unipotent)).imp (hstep true) (hstep false)
  have hDcard:Nat.card (radicalPair (F:=F) true)=Nat.card (radicalPair (F:=F) false):=by
    rw [radicalPair_as_wing,radicalPair_as_wing,
      card_map_of_injective (unipotent (F:=F)).subtype_injective,
      card_map_of_injective (unipotent (F:=F)).subtype_injective,card_wing,card_wing]
  have hDgen:normalizer (radicalPair (F:=F) true:Set (Sp F))⊔
      normalizer (radicalPair (F:=F) false:Set (Sp F))=⊤:=by
    change normalizer (pointRadicalAmbient (F:=F):Set (Sp F))⊔normalizer (planeRadicalAmbient (F:=F):Set (Sp F))=⊤
    rw [pointRadicalAmbient_normalizer hF hn,planeRadicalAmbient_normalizer hF hn,
      Theory.SpecificGroups.SymplecticFour.parabolics_sup_eq_top]
  have hD (b:Bool):IsElementaryAbelian 2 (radicalPair (F:=F) b):=by
    rw [radicalPair_as_wing]
    let :=wing_elementary (F:=F) (!b)
    exact IsElementaryAbelian.map _
  have hlift' (b:Bool):IsElementaryAbelian 2 ((radicalPair (F:=F) b).comap q'):=by
    change IsElementaryAbelian 2 (((radicalPair (F:=F) b).comap (MulAut.conj g).toMonoidHom).comap q)
    apply hlift
    rw [comap_equiv_eq_map_symm']
    let :=hD b
    exact IsElementaryAbelian.map _
  exact Stellmacher.component_le_of_two_plane_normalizers (S:Subgroup G) K C M q' hq'
    unipotent radicalPair hDU hDcover hDcard hDgen hU hJ hC (hk'.symm ▸ hker) hlift' hM
end Theory.SpecificGroups.SymplecticFour.ThompsonInner
