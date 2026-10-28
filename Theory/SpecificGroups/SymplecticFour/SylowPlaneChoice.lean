module
public import Theory.SpecificGroups.SymplecticFour.ThompsonNormalizerGeneration
public import Stellmacher.ElementaryAbelianMaxPair.PlaneChoice
/-! # An escaping wing normalizer on the actual symplectic Sylow
The point and plane radical normalizers are the generating parabolics.
Sylow alignment and their elementary cover select an intrinsic maximum wing
whose component normalizer escapes M. Source: Aschbacher--Smith 2.5.7, p.556.
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

theorem exists_maximum_escaping_normalizer_of_sylow
    (K M:Subgroup G) (hKM:¬K≤M) (q:K→*Sp F) (hq:Function.Surjective q)
    (hk:IsPGroup 2 q.ker) (P:Sylow 2 K)
    {n:ℕ} (hn:1<n) (hF:Nat.card F=2^n)
    (hlift:∀W:Subgroup (Sp F),IsElementaryAbelian 2 W→IsElementaryAbelian 2 (W.comap q)) :
    ∃V∈Stellmacher.elementaryAbelianMaxSubgroups ((P:Subgroup K).map K.subtype),
      ¬K⊓normalizer (V:Set G)≤M := by
  let : Algebra (ZMod 2) F:=ZMod.algebra F 2
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
  let :=hD true
  let :=hD false
  exact Stellmacher.exists_maximum_escaping_normalizer_of_sylow_planes K M hKM q hq hk P
    (unipotentSylow hF (by omega)) (radicalPair true) (radicalPair false)
    (hDU true) (hDU false) hlift hDcard hDcover hDgen
end Theory.SpecificGroups.SymplecticFour.ThompsonInner
