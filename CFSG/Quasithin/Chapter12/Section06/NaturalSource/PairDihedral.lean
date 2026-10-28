module
public import CFSG.Quasithin.Chapter12.Section06.NaturalSource.PairFixed
public import Theory.LinearAlgebra.BinaryOrthogonalPair
public import Theory.GroupTheory.InvolutionPairDihedral

/-!
# The dihedral alternatives for the original non-two pair

The original pair seed has complementary singular four-spaces, which are
exactly the fixed and displacement spaces of its marked generators. Apply
the structural binary orthogonal pair theorem to these same generators.
Their product has order three, five or six, so the faithful pair image is
isomorphic to the dihedral group of order six, ten or twelve.

The existing compatible action equivalence transports the rotation order
back through the literal map H → H/O₂(H), retaining the chosen v and its
specified conjugate by g. Extraspeciality, plus type and the fixed spaces
are supplied by the checked original pair constructions. The earlier point,
fixed-space, intersection and nonsingular-centralizer premises remain
explicit. Odd-core and component exclusions, abelianness of the point span,
and the universal NaturalReduction still require their source arguments.
Source: Aschbacher--Smith F.9.5(6.ii), pp.319--320, and 12.6.26, p.831.
-/

public section
namespace CFSG.Quasithin.Chapter12.Section06
open Subgroup Theory.GroupTheory
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V : Subgroup G} [IsElementaryAbelian 2 V]
  (S : SourceHypothesis KnownSimple.IsKnownSimple T L V)
  (D : OrthogonalMarking L V S.chosen.normalizes) (hZ : ZV L V = ⊥) (z : V)

/-- The original non-two pair image is dihedral of order six, ten or twelve.
The rotation order is proved for the images of one original element of V
and its specified conjugate, under the literal H → H/O₂(H) projection. -/
theorem SourceHypothesis.original_non_two_pair_dihedral
    (hz : z ≠ 1)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
    (hTz : (T : Subgroup G) ≤ normalizer ((D.fullSetup hZ T z).V₁ : Set G))
    (hbound : ∀ g : G, g ∉ normalizer (V : Set G) →
      Nat.card (V ⊓ V.map (MulAut.conj g).toMonoidHom : Subgroup G) ≤ 2 ^ 3)
    (hns : ∀ w : V, D.Nonsingular w → Gv w.val ≤ M L)
    {H : Subgroup G} (hH : H ∈ (D.fullSetup hZ T z).Hz)
    (g : G) (hg : g ∈ H)
    (hn : ¬ IsPGroup 2 (V ⊔ V.map (MulAut.conj g).toMonoidHom : Subgroup G)) :
    let I := V ⊔ V.map (MulAut.conj g).toMonoidHom
    ∃ (hIH : I ≤ H) (v : V) (m : ℕ), v.val ∉ (D.fullSetup hZ T z).V₅ ∧
      (m=3 ∨ m=5 ∨ m=6) ∧
      Nonempty (Nonabelian.Setup.star H I ≃* DihedralGroup m) ∧
      orderOf (QuotientGroup.mk' (pCore 2 H) (inclusion hIH ⟨v.val,mem_sup_left v.property⟩) *
        QuotientGroup.mk' (pCore 2 H) (inclusion hIH ⟨(MulAut.conj g) v.val,
          mem_sup_right (mem_map_of_mem (MulAut.conj g).toMonoidHom v.property)⟩))=m := by
  let E := D.fullSetup hZ T z
  let I := V ⊔ V.map (MulAut.conj g).toMonoidHom
  let P := E.V₅ ⊔ E.V₅.map (MulAut.conj g).toMonoidHom
  obtain ⟨_,hs,haction,hspaces⟩ :=
    S.original_non_two_pair_marked_orthogonal D hZ z hz hTV hTz hbound hns hH g hg hn
  let : IsExtraspecial 2 P := hs
  obtain ⟨hIH,n,α,e,hα,_,hproj,a,b,ha2,hb2,_,_,hgen,v,hv,hav,hbv⟩ := haction
  obtain ⟨hka,hra,_,hkb,hrb,_⟩ := hspaces n v hv
  have hka' : LinearMap.ker (a.val.toLinearMap-LinearMap.id)=
      ExtraspecialSquare.imageSpace P (E.V₅.subgroupOf P) := by simpa only [hav,hα] using hka
  have hra' : LinearMap.range (a.val.toLinearMap-LinearMap.id)=
      ExtraspecialSquare.imageSpace P (E.V₅.subgroupOf P) := by simpa only [hav,hα] using hra
  have hkb' : LinearMap.ker (b.val.toLinearMap-LinearMap.id)=
      ExtraspecialSquare.imageSpace P ((E.V₅.map (MulAut.conj g).toMonoidHom).subgroupOf P) := by
    simpa only [hbv,hα] using hkb
  have hrb' : LinearMap.range (b.val.toLinearMap-LinearMap.id)=
      ExtraspecialSquare.imageSpace P ((E.V₅.map (MulAut.conj g).toMonoidHom).subgroupOf P) := by
    simpa only [hbv,hα] using hrb
  obtain ⟨_,_,hND,_,hAd,hAs,hBd,hBs,hcompl⟩ :=
    S.original_non_two_pair_plus D hZ z hz hTV hTz hbound hns hH g hg hn
  have hp := BinaryOrthogonalPair.product_order (ExtraspecialSquare.form P) hND a.val b.val
    ((QuadraticMap.mem_isometrySubgroup _ _).mp a.property)
    ((QuadraticMap.mem_isometrySubgroup _ _).mp b.property) _ _ hcompl hAd hBd hAs hBs hka' hra' hkb' hrb'
  have hp' : orderOf (a*b)=3 ∨ orderOf (a*b)=5 ∨ orderOf (a*b)=6 := by
    change orderOf ((a*b : (ExtraspecialSquare.form P).isometrySubgroup).val)=3 ∨
      orderOf ((a*b : (ExtraspecialSquare.form P).isometrySubgroup).val)=5 ∨
      orderOf ((a*b : (ExtraspecialSquare.form P).isometrySubgroup).val)=6 at hp
    simpa only [Subgroup.orderOf_coe] using hp
  obtain ⟨m,hm,horder⟩ : ∃ m : ℕ, (m=3 ∨ m=5 ∨ m=6) ∧ orderOf (a*b)=m := by
    rcases hp' with h | h | h
    · exact ⟨3,Or.inl rfl,h⟩
    · exact ⟨5,Or.inr (Or.inl rfl),h⟩
    · exact ⟨6,Or.inr (Or.inr rfl),h⟩
  obtain ⟨d⟩ := involution_pair_dihedral a b ha2 hb2 (by rcases hm with rfl|rfl|rfl <;> decide) horder
  refine ⟨hIH,v,m,hv,hm,⟨e.trans ((MulEquiv.subgroupCongr hgen).trans d)⟩,?_⟩
  let x : I := ⟨v.val,mem_sup_left v.property⟩
  let y : I := ⟨(MulAut.conj g) v.val,
    mem_sup_right (mem_map_of_mem (MulAut.conj g).toMonoidHom v.property)⟩
  let q : I →* (H ⧸ pCore 2 H) := (QuotientGroup.mk' (pCore 2 H)).comp (inclusion hIH)
  let r : Nonabelian.Setup.star H I := ⟨q (x*y),mem_map_of_mem _ (x*y).property⟩
  have he : (e r).val=a*b := by
    change (e ⟨QuotientGroup.mk' (pCore 2 H) (inclusion hIH (x*y)),_⟩).val=_
    rw [hproj,map_mul,←hav,←hbv]
  calc
    orderOf (q x*q y) = orderOf r := by rw [←map_mul];exact Subgroup.orderOf_coe r
    _ = orderOf (e r) := (e.orderOf_eq r).symm
    _ = orderOf (a*b) := (Subgroup.orderOf_coe (e r)).symm.trans (congrArg orderOf he)
    _ = m := horder
end CFSG.Quasithin.Chapter12.Section06
