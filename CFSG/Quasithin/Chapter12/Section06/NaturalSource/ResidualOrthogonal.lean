module
public import Theory.LinearAlgebra.BinaryOrthogonalResidualNine
public import CFSG.Quasithin.Chapter12.Section06.NaturalSource.ResidualTwoCore

/-!
# The original residual-centralizer two-core bound

The simultaneous orthogonal action of the original pair and L₁ restricts
faithfully on each singular four-space to a Sylow E₉ of L₁. The residual-nine
pencil theorem forces the same pair rotation to have sixth power one. The
three-rank argument has already excluded the D₆ and D₁₂ alternatives, while
the remaining D₁₀ rotation has order five under the literal H → H/O₂(H)
projection. Thus every original pair with conjugator normalizing L₁ is a
two-group.

Apply this to the retained Baer--Suzuki witness in the literal section
centralizer C_H(L₁/O₂(L₁)). This proves V ≤ O₂(C_H(L₁/O₂(L₁))), with the
intrinsic quotient kernel O₂(L₁) kept distinct from L₁ intersect O₂(L).
The earlier point/fixed-space, intersection and nonsingular-centralizer
inputs remain explicit. Five-core centralization, the component analysis,
12.6.26 abelianness and the universal NaturalReduction remain obligations.

Source: Aschbacher--Smith, proof of 12.6.26, printed pp.831--832.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section06
open ChapterF.Section09.Setup.Hypothesis
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V : Subgroup G} [IsElementaryAbelian 2 V]
  (S : SourceHypothesis KnownSimple.IsKnownSimple T L V)
  (D : OrthogonalMarking L V S.chosen.normalizes) (hZ : ZV L V = ⊥) (z : V)

/-- The original non-two pair is impossible when its conjugator normalizes
L₁. The proof retains the marked generators and their quotient product order. -/
theorem SourceHypothesis.original_normalizing_pair_isTwoGroup
    (hz : z ≠ 1)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
    (hTz : (T : Subgroup G) ≤ normalizer ((D.fullSetup hZ T z).V₁ : Set G))
    (hbound : ∀ g : G, g ∉ normalizer (V : Set G) →
      Nat.card (V ⊓ V.map (MulAut.conj g).toMonoidHom : Subgroup G) ≤ 2 ^ 3)
    (hns : ∀ w : V, D.Nonsingular w → Gv w.val ≤ M L)
    {H : Subgroup G} (hH : H ∈ (D.fullSetup hZ T z).Hz)
    (hnH : ¬ IsMulCommutative ((D.fullSetup hZ T z).VH H))
    (g : G) (hg : g ∈ H)
    (hgL : g ∈ normalizer ((D.fullSetup hZ T z).L₁ : Set G)) :
    IsPGroup 2 (V ⊔ V.map (MulAut.conj g).toMonoidHom : Subgroup G) := by
  classical
  by_contra hn
  let E := D.fullSetup hZ T z
  let I := V ⊔ V.map (MulAut.conj g).toMonoidHom
  let J := I ⊔ E.L₁
  let P := E.V₅ ⊔ E.V₅.map (MulAut.conj g).toMonoidHom
  obtain ⟨hIH,v,hv,_,hfive⟩ :=
    S.original_normalizing_pair_dihedral_five D hZ z hz hTV hTz hbound hns hH hnH g hg hgL hn
  obtain ⟨hs,n,_,horder,hcomm,hpres,hSyl⟩ :=
    S.original_pair_residual_orthogonal_action D hZ z hz hTV hTz hbound hns hH hnH g hg hgL hn
  let : IsExtraspecial 2 P := hs
  let α := (ExtraspecialSquare.isometryAction P).comp (seedConjugation J P n)
  let nI : I ≤ normalizer (P : Set G) := le_sup_left.trans n
  let x : I := ⟨v.val,mem_sup_left v.property⟩
  let y : I := ⟨(MulAut.conj g) v.val,
    mem_sup_right (mem_map_of_mem (MulAut.conj g).toMonoidHom v.property)⟩
  let a := (α (inclusion le_sup_left x)).val
  let b := (α (inclusion le_sup_left y)).val
  let W := ExtraspecialSquare.imageSpace P (E.V₅.subgroupOf P)
  let W' := ExtraspecialSquare.imageSpace P
    ((E.V₅.map (MulAut.conj g).toMonoidHom).subgroupOf P)
  have hspaces := S.original_non_two_pair_seed_spaces D hZ z hz hTV hTz hbound hns hH g hg hn hs nI v hv
  obtain ⟨hka,hra,_,hkb,hrb,_⟩ := hspaces
  change LinearMap.ker (a.toLinearMap-LinearMap.id)=W at hka
  change LinearMap.range (a.toLinearMap-LinearMap.id)=W at hra
  change LinearMap.ker (b.toLinearMap-LinearMap.id)=W' at hkb
  change LinearMap.range (b.toLinearMap-LinearMap.id)=W' at hrb
  obtain ⟨_,_,hND,_,hWd,hWs,hW'd,hW's,hcompl⟩ :=
    S.original_non_two_pair_plus D hZ z hz hTV hTz hbound hns hH g hg hn
  let A : Sylow 3 E.L₁ := Classical.choice inferInstance
  obtain ⟨hA,hAc,_,hAf⟩ := hSyl A
  let := hA
  let ρ : A →* (ExtraspecialSquare.Space P ≃ₗ[ZMod 2] ExtraspecialSquare.Space P) :=
    (ExtraspecialSquare.form P).isometrySubgroup.subtype.comp
      (α.comp ((inclusion le_sup_right).comp A.toSubgroup.subtype))
  have hρq (r : A) (u) : ExtraspecialSquare.form P (ρ r u)=ExtraspecialSquare.form P u :=
    (QuadraticMap.mem_isometrySubgroup _ _).mp (α (inclusion le_sup_right r.val)).property u
  have hρa (r : A) : Commute (ρ r) a :=
    ((hcomm x r.val).map (ExtraspecialSquare.form P).isometrySubgroup.subtype).symm
  have hρb (r : A) : Commute (ρ r) b :=
    ((hcomm y r.val).map (ExtraspecialSquare.form P).isometrySubgroup.subtype).symm
  have hsix : (a*b)^6=1 := BinaryOrthogonalPair.product_six_of_nine
    (ExtraspecialSquare.form P) hND a b
    ((QuadraticMap.mem_isometrySubgroup _ _).mp (α (inclusion le_sup_left x)).property)
    ((QuadraticMap.mem_isometrySubgroup _ _).mp (α (inclusion le_sup_left y)).property)
    W W' hcompl (hWd.trans hW'd.symm) hWs hW's hka hra hkb hrb hAc ρ hρq
    (fun r => (hpres r.val).2) hAf hρa hρb hW'd
  have hrot : orderOf (a*b)=5 := by
    have hh := horder hIH (x*y)
    change orderOf (α (inclusion le_sup_left (x*y)))=_ at hh
    rw [map_mul,map_mul] at hh
    have hh' : orderOf (a*b)=orderOf
        (QuotientGroup.mk' (pCore 2 H) (inclusion hIH x) *
         QuotientGroup.mk' (pCore 2 H) (inclusion hIH y)) :=
      (Subgroup.orderOf_coe (α (inclusion le_sup_left x)*α (inclusion le_sup_left y))).trans hh
    exact hh'.trans hfive
  have hd := orderOf_dvd_of_pow_eq_one hsix
  rw [hrot] at hd
  exact (by decide : ¬ (5:ℕ) ∣ 6) hd

/-- The literal relative two-core assertion in the first paragraph of the
12.6.26 contradiction, under the retained earlier geometry. -/
theorem SourceHypothesis.original_module_le_residualCentralizer_twoCore
    (hz : z ≠ 1)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
    (hTz : (T : Subgroup G) ≤ normalizer ((D.fullSetup hZ T z).V₁ : Set G))
    (hbound : ∀ g : G, g ∉ normalizer (V : Set G) →
      Nat.card (V ⊓ V.map (MulAut.conj g).toMonoidHom : Subgroup G) ≤ 2 ^ 3)
    (hns : ∀ w : V, D.Nonsingular w → Gv w.val ≤ M L)
    {H : Subgroup G} (hH : H ∈ (D.fullSetup hZ T z).Hz)
    (hnH : ¬ IsMulCommutative ((D.fullSetup hZ T z).VH H)) :
    V ≤ ((D.fullSetup hZ T z).residualCentralizer H).pCoreIn 2 := by
  classical
  by_contra hn
  obtain ⟨g,hg,hpair,_⟩ := S.original_residualCentralizer_obstruction D hZ z hz hTV hTz hbound hns hH hnH hn
  obtain ⟨hgH,hgL,_⟩ := ((D.fullSetup hZ T z).mem_residualCentralizer H g).mp hg
  exact hpair (S.original_normalizing_pair_isTwoGroup D hZ z hz hTV hTz hbound hns hH hnH g hgH hgL)
end CFSG.Quasithin.Chapter12.Section06
