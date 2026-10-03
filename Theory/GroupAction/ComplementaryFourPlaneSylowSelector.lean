module
public import Theory.GroupAction.ComplementaryFourWreathAction
public import Theory.GroupAction.Lemmas
public import Theory.GroupAction.SubgroupConjugation
public import Theory.GroupAction.WreathComplementaryPlaneSylow

/-!
# Complementary plane and generating Sylow for an actual wreath action

A faithful group of order seventy-two acts on an elementary abelian two-group
and permutes two complementary subgroups of order four. Given an invariant
plane of order four for a supplied Sylow two-subgroup and an involution with
order-two displacement, one actor moves the plane disjointly while its
conjugate Sylow together with that involution generates the whole group.
The supplied action, Sylow, involution and plane are retained.

The complementary-support coordinate theorem identifies this action with the
natural SL₂(2) wreath C₂ action. Compatible actor and module equivalences
transport displacement, invariant planes and Sylow subgroups. Apply the finite
natural-action selector and pull both conclusions back with the same actor.
Both named natural action instances are installed once and used by recognition
and selection alike. This is the source-neutral action step behind the good
neighbor in Stellmacher (9.10), printed p.58, statement (**).
-/

namespace ComplementaryFourWreathAction
open scoped IsMulCommutative

private theorem equiv_commutatorAction
    {K L V W : Type*} [Group K] [Group L] [Group V] [Group W]
    [MulDistribMulAction K V] [MulDistribMulAction L W]
    (eK : K ≃* L) (eV : V ≃* W)
    (hcomp : ∀ k v, eV (k • v) = eK k • eV v)
    (A : Subgroup K) :
    (commutatorAction A V).map eV.toMonoidHom =
      commutatorAction (A.map eK.toMonoidHom) W := by
  rw [commutatorAction_eq_closure, commutatorAction_eq_closure, MonoidHom.map_closure]
  congr 1
  ext w
  constructor
  · rintro ⟨v, ⟨a, x, rfl⟩, rfl⟩
    refine ⟨⟨eK a, Subgroup.mem_map_of_mem eK.toMonoidHom a.property⟩, eV x, ?_⟩
    change eV (x⁻¹ * ((a:K) • x)) = (eV x)⁻¹ * (eK (a:K) • eV x)
    rw [map_mul, map_inv, hcomp]
  · rintro ⟨b, y, rfl⟩
    obtain ⟨a, ha, hba⟩ := b.property
    change eK a = (b:L) at hba
    refine ⟨(eV.symm y)⁻¹ * (a • eV.symm y), ⟨⟨a, ha⟩, eV.symm y, rfl⟩, ?_⟩
    change eV ((eV.symm y)⁻¹ * (a • eV.symm y)) = y⁻¹ * ((b:L) • y)
    rw [map_mul, map_inv, hcomp, eV.apply_symm_apply, hba]

private theorem equiv_map_smul_subgroup
    {K L V W : Type*} [Group K] [Group L] [Group V] [Group W]
    [MulDistribMulAction K V] [MulDistribMulAction L W]
    (eK : K ≃* L) (eV : V ≃* W)
    (hcomp : ∀ k v, eV (k • v) = eK k • eV v)
    (I : Subgroup V) (k : K) :
    (I.map (MulDistribMulAction.toMulAut K V k).toMonoidHom).map eV.toMonoidHom =
      (I.map eV.toMonoidHom).map
        (MulDistribMulAction.toMulAut L W (eK k)).toMonoidHom := by
  rw [Subgroup.map_map, Subgroup.map_map]
  congr 1
  ext v
  exact hcomp k v

private theorem equiv_map_conj_subgroup
    {K L : Type*} [Group K] [Group L]
    (eK : K ≃* L) (S : Subgroup K) (k : K) :
    (S.conjBy k).map eK.toMonoidHom = (S.map eK.toMonoidHom).conjBy (eK k) := by
  rw [Subgroup.conjBy, Subgroup.conjBy, Subgroup.map_map, Subgroup.map_map]
  congr 1
  ext x
  simp

private theorem pullback_plane_sylow_selector
    {K L V W : Type*} [Group K] [Group L] [Group V] [Group W]
    [MulDistribMulAction K V] [MulDistribMulAction L W]
    (eK : K ≃* L) (eV : V ≃* W)
    (hcomp : ∀ k v, eV (k • v) = eK k • eV v)
    (S : Subgroup K) (t : K) (I : Subgroup V)
    (hselected : ∃ g : L,
      Disjoint (I.map eV.toMonoidHom)
        ((I.map eV.toMonoidHom).map (MulDistribMulAction.toMulAut L W g).toMonoidHom) ∧
      (S.map eK.toMonoidHom).conjBy g ⊔ Subgroup.zpowers (eK t) = ⊤) :
    ∃ g : K,
      Disjoint I (I.map (MulDistribMulAction.toMulAut K V g).toMonoidHom) ∧
      S.conjBy g ⊔ Subgroup.zpowers t = ⊤ := by
  obtain ⟨g, hdisjoint, hgenerate⟩ := hselected
  refine ⟨eK.symm g, ?_, ?_⟩
  · rw [Subgroup.disjoint_def]
    intro v hv hvmoved
    have hmap := equiv_map_smul_subgroup eK eV hcomp I (eK.symm g)
    rw [eK.apply_symm_apply] at hmap
    have hmoved : eV v ∈ (I.map eV.toMonoidHom).map
        (MulDistribMulAction.toMulAut L W g).toMonoidHom :=
      hmap ▸ Subgroup.mem_map_of_mem eV.toMonoidHom hvmoved
    have hone := Subgroup.disjoint_def.mp hdisjoint
      (Subgroup.mem_map_of_mem eV.toMonoidHom hv) hmoved
    exact eV.injective (hone.trans (map_one eV).symm)
  · apply Subgroup.map_injective (f := eK.toMonoidHom) eK.injective
    rw [Subgroup.map_sup, equiv_map_conj_subgroup, MonoidHom.map_zpowers,
      Subgroup.map_top_of_surjective _ eK.surjective, eK.apply_symm_apply]
    exact hgenerate

private abbrev StandardD := Matrix.SpecialLinearGroup (Fin 2) (ZMod 2)
private abbrev StandardQ := Multiplicative (ZMod 2)
private abbrev StandardF := Multiplicative (Fin 2 → ZMod 2)
private abbrev StandardG := RegularWreathProduct StandardD StandardQ
private abbrev StandardV := StandardQ → StandardF

public theorem exists_complementary_plane_generating_sylow
    {K V : Type*} [Group K] [Group V] [Finite K] [Finite V]
    [IsElementaryAbelian 2 V] [MulDistribMulAction K V]
    (first second : Subgroup V) (hcompl : IsCompl first second)
    (hfirst : Nat.card first = 4) (hsecond : Nat.card second = 4)
    (hfaith : fixingSubgroup K (Set.univ : Set V) = ⊥)
    (hcard : Nat.card K = 72)
    (hperm : ∀ element : K,
      (first.map (MulDistribMulAction.toMulAut K V element).toMonoidHom = first ∧
       second.map (MulDistribMulAction.toMulAut K V element).toMonoidHom = second) ∨
      (first.map (MulDistribMulAction.toMulAut K V element).toMonoidHom = second ∧
       second.map (MulDistribMulAction.toMulAut K V element).toMonoidHom = first))
    (S : Sylow 2 K) (t : K) (ht : t^2 = 1)
    (hrank : Nat.card (commutatorAction (Subgroup.zpowers t) V) = 2)
    (I : Subgroup V) (hI : Nat.card I = 4)
    (hInv : ∀ s:S, ∀ v∈I, (s:K) • v∈I) :
    ∃ g:K, Disjoint I (I.map (MulDistribMulAction.toMulAut K V g).toMonoidHom) ∧
      (S:Subgroup K).conjBy g ⊔ Subgroup.zpowers t = ⊤ := by
  let _ := FourGroupMatrixCoordinates.naturalAction
  let _ := RegularWreathProduct.functionModule StandardD StandardQ StandardF
  obtain ⟨eK,eV,hcompatible⟩ :=
    ComplementaryFourWreathAction.equiv_natural_wreath_of_complementary_four
      first second hcompl hfirst hsecond hfaith hcard hperm
  have hcomp : ∀ k v, eV (k • v) = eK k • eV v := by
    intro k v
    funext i
    exact hcompatible k v i
  let S' := S.mapSurjective (f := eK.toMonoidHom) eK.surjective
  let I' := I.map eV.toMonoidHom
  have hS : (S':Subgroup StandardG) = (S:Subgroup K).map eK.toMonoidHom :=
    Sylow.coe_mapSurjective (f := eK.toMonoidHom) eK.surjective S
  have hcardI : Nat.card I' = 4 :=
    (Subgroup.card_map_of_injective eV.injective).trans hI
  have hInv' : ∀ s:S', ∀ v∈I', (s:StandardG) • v∈I' := by
    intro s v hv
    obtain ⟨w,hw,rfl⟩ := hv
    have hs : (s:StandardG) ∈ (S:Subgroup K).map eK.toMonoidHom := hS ▸ s.property
    obtain ⟨k,hk,heq⟩ := hs
    change eK k = (s:StandardG) at heq
    rw [← heq]
    change eK k • eV w ∈ I'
    rw [← hcomp]
    exact Subgroup.mem_map_of_mem eV.toMonoidHom (hInv ⟨k,hk⟩ w hw)
  have hrank' : Nat.card (commutatorAction (Subgroup.zpowers (eK t)) StandardV) = 2 := by
    change Nat.card (commutatorAction (Subgroup.zpowers (eK.toMonoidHom t)) StandardV) = 2
    rw [← MonoidHom.map_zpowers eK.toMonoidHom,
      ← equiv_commutatorAction eK eV hcomp,
      Subgroup.card_map_of_injective eV.injective]
    exact hrank
  have ht' : (eK t)^2 = 1 := by rw [← map_pow, ht, map_one]
  obtain ⟨g,hd,hg⟩ := RegularWreathProduct.exists_complementary_plane_generating_sylow S' (eK t) ht' hrank' I' hcardI hInv'
  rw [hS] at hg
  exact pullback_plane_sylow_selector eK eV hcomp (S:Subgroup K) t I ⟨g,hd,hg⟩

end ComplementaryFourWreathAction
