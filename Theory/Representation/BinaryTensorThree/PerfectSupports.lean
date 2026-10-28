module
public import Theory.Representation.BinaryOffender.CommutingPerfectSupports
public import Theory.Representation.BinaryTensorThree.Recognition
public import Theory.GroupTheory.GeneralizedFitting.ComponentSwapNormSylow
public import Theory.GroupTheory.ComponentPairRankDescent

/-!
# Full supports from the marked single-factor constituents

The actual product coordinates identify the normal component pair and its
permutation by the ambient group. Clifford theory makes each irreducible
ambient section semisimple on that pair. Single-factor constituents therefore
annihilate its mixed displacement. Commuting perfect support extraction lifts
this identity through every extension in the original module.

Every distinct component in the normal pair is the second coordinate factor,
so the conclusion applies to the original companion without choosing new
coordinates or assuming the original module is semisimple.
Source: Aschbacher--Smith F.9.18(5iii.b),14.6.22(2), printed pp.326,1038.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped MonoidAlgebra
namespace BinaryTensorThree
variable {G V : Type*} [_root_.Group G] [Finite G]
  [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V) (N K : Subgroup G) [N.Normal]
  (p : N ≃* (K × K)) (t : G)
  (hl : ∀ k : K, (p.symm (k,1)).val = k.val)
  (hr : ∀ k : K, (p.symm (1,k)).val = t*k.val*t⁻¹)

include hl hr
private theorem marked_pair_geometry (hK : IsComponent G K) :
    let C := K.map (MulAut.conj t).toMonoidHom
    K ≤ N ∧ C ≤ N ∧ K ⊔ C = N ∧ K ≠ C ∧
    (∀ k ∈ K, ∀ c ∈ C, Commute k c) ∧
    ∀ g : G,
      (K.map (MulAut.conj g).toMonoidHom = K ∧ C.map (MulAut.conj g).toMonoidHom = C) ∨
      (K.map (MulAut.conj g).toMonoidHom = C ∧ C.map (MulAut.conj g).toMonoidHom = K) := by
  let C := K.map (MulAut.conj t).toMonoidHom
  have hKN : K ≤ N := by
    intro k hk
    simpa only [hl] using (p.symm (⟨k,hk⟩,1)).property
  have hCN : C ≤ N := by
    rintro _ ⟨k,hk,rfl⟩
    change t*k*t⁻¹ ∈ N
    simpa only [hr] using (p.symm (1,⟨k,hk⟩)).property
  have hsup : K ⊔ C = N := by
    apply le_antisymm (sup_le hKN hCN)
    intro n hn
    let x := p ⟨n,hn⟩
    have he : (p.symm (x.1,1)) * (p.symm (1,x.2)) = (⟨n,hn⟩ : N) := by
      rw [←map_mul]
      simpa only [Prod.mk_mul_mk,mul_one,one_mul,Prod.mk.eta] using p.symm_apply_apply (⟨n,hn⟩ : N)
    have hv := congrArg Subtype.val he
    rw [Subgroup.coe_mul,hl,hr] at hv
    change (x.1:G)*(t*(x.2:G)*t⁻¹)=n at hv
    rw [←hv]
    exact (K ⊔ C).mul_mem (mem_sup_left x.1.property)
      (mem_sup_right (mem_map_of_mem (MulAut.conj t).toMonoidHom x.2.property))
  have hne : K ≠ C := by
    intro he
    let : IsQuasisimple K := hK.2
    let : IsSimpleGroup (K ⧸ center K) := IsQuasisimple.simple
    let : Nontrivial K := (QuotientGroup.mk'_surjective (center K)).nontrivial
    obtain ⟨k,hk⟩ := exists_ne (1 : K)
    have hc : t*(k:G)*t⁻¹ ∈ K := by
      exact he.ge (mem_map_of_mem (MulAut.conj t).toMonoidHom k.property)
    let j : K := ⟨t*(k:G)*t⁻¹,hc⟩
    have hh : p.symm (j,1) = p.symm (1,k) := Subtype.ext ((hl j).trans (hr k).symm)
    have hx := congrArg Prod.snd (p.symm.injective hh)
    exact hk hx.symm
  have hcomm (k : G) (hk : k ∈ K) (c : G) (hc : c ∈ C) : Commute k c := by
    obtain ⟨j,hj,rfl⟩ := hc
    have he : Commute ((⟨k,hk⟩ : K), (1 : K)) ((1 : K), (⟨j,hj⟩ : K)) := by
      show ((⟨k,hk⟩ : K), (1 : K)) * ((1 : K), (⟨j,hj⟩ : K)) = _
      simp
    have hh := congrArg Subtype.val (he.map p.symm.toMonoidHom).eq
    simpa only [Subgroup.coe_mul,MulEquiv.coe_toMonoidHom,hl,hr,Commute,SemiconjBy,MulAut.conj_apply] using hh
  let : (K ⊔ C).Normal := hsup ▸ inferInstance
  let : (K ⊔ K.conjBy t).Normal := by
    change (K ⊔ C).Normal
    infer_instance
  have hi := ComponentPairRankDescent.component_normalizer_index_two_of_normal_pair K hK t hne
  have hpair (g : G) : K.map (MulAut.conj g).toMonoidHom = K ∨
      K.map (MulAut.conj g).toMonoidHom = C :=
    NormPair.conjugate_eq_or_eq_of_normalizer_index_two hi hne.symm g
  have hpairC (g : G) : C.map (MulAut.conj g).toMonoidHom = K ∨
      C.map (MulAut.conj g).toMonoidHom = C := by
    have he : C.map (MulAut.conj g).toMonoidHom = K.map (MulAut.conj (g*t)).toMonoidHom := by
      rw [show C = K.map (MulAut.conj t).toMonoidHom from rfl,map_map]
      congr 1
      ext x
      change g*(t*x*t⁻¹)*g⁻¹ = (g*t)*x*(g*t)⁻¹
      group
    rw [he]
    exact hpair (g*t)
  refine ⟨hKN,hCN,hsup,hne,hcomm,?_⟩
  intro g
  have hinj := map_injective (f := (MulAut.conj g).toMonoidHom) (MulAut.conj g).injective
  rcases hpair g with ha | ha <;> rcases hpairC g with hb | hb
  · exact (hne (hinj (ha.trans hb.symm))).elim
  · exact Or.inl ⟨ha,hb⟩
  · exact Or.inr ⟨ha,hb⟩
  · exact (hne (hinj (ha.trans hb.symm))).elim

/-- Single-factor constituents force cross-centralization of the actual full
supports, even when the original representation has nonsplit extensions. -/
theorem HasSingleFactorConstituents.full_supports_centralize
    (hK : IsComponent G K) (hs : HasSingleFactorConstituents ρ N K p) :
    subspaceCommutator ρ ⊤ K ≤ fixedSpace ρ (K.map (MulAut.conj t).toMonoidHom) := by
  let C := K.map (MulAut.conj t).toMonoidHom
  obtain ⟨hKN,hCN,_,_,hcomm,hperm⟩ := marked_pair_geometry N K p t hl hr hK
  let : IsQuasisimple K := hK.2
  let : Group.IsPerfect C := Group.IsPerfect.map _
  apply (subspaceCommutator_eq_bot_iff ρ _ C).mp
  apply mixed_commutator_eq_bot_of_irreducible_sections ρ K C hcomm hperm
  intro S L hL
  let σ := L.quotientRepresentation
  let : IsSemisimpleModule (ZMod 2)[N] (Representation.asModule (σ.comp N.subtype)) :=
    NormalConstituentDisplacement.restriction_semisimple σ hL N
  apply mixed_commutator_eq_bot_of_semisimple_restriction σ N K C hKN hCN
  intro U hU
  rcases hs S L hL U hU with hleft | hright
  · left
    intro k hk
    have he := congrArg (fun f : Representation (ZMod 2) K U.toSubmodule => f ⟨k,hk⟩) hleft
    change U.toRepresentation (p.symm (⟨k,hk⟩,1)) = 1 at he
    have hh : p.symm (⟨k,hk⟩,1) = k := Subtype.ext (hl ⟨k,hk⟩)
    rwa [hh] at he
  · right
    rintro ⟨c,hcN⟩ ⟨k,hk,rfl⟩
    have he := congrArg (fun f : Representation (ZMod 2) K U.toSubmodule => f ⟨k,hk⟩) hright
    change U.toRepresentation (p.symm (1,⟨k,hk⟩)) = 1 at he
    have hh : p.symm (1,⟨k,hk⟩) = (⟨t*k*t⁻¹,hcN⟩ : N) := Subtype.ext (hr ⟨k,hk⟩)
    rwa [hh] at he

/-- Every other component in the marked normal pair centralizes the first
component's full support. No companion coordinate choice is imposed on the caller. -/
theorem HasSingleFactorConstituents.full_support_centralizes_component
    (hK : IsComponent G K) (hs : HasSingleFactorConstituents ρ N K p)
    (C : Subgroup G) (hC : IsComponent G C) (hCN : C ≤ N) (hne : C ≠ K) :
    subspaceCommutator ρ ⊤ K ≤ fixedSpace ρ C := by
  obtain ⟨_,_,hsup,_,_,_⟩ := marked_pair_geometry N K p t hl hr hK
  have he : C = K.map (MulAut.conj t).toMonoidHom := by
    by_contra hn
    have hcent : C ≤ centralizer (N : Set G) := by
      rw [←hsup]
      apply le_centralizer_iff.mpr
      exact sup_le
        (commutator_eq_bot_iff_le_centralizer.mp (hK.commutator_eq_bot_of_ne hC hne.symm))
        (commutator_eq_bot_iff_le_centralizer.mp
          ((hK.map_conj t).commutator_eq_bot_of_ne hC (Ne.symm hn)))
    have hCC := hcent.trans (centralizer_le hCN)
    let : IsQuasisimple C := hC.2
    let : IsSimpleGroup (C ⧸ center C) := IsQuasisimple.simple
    let : Nontrivial C := (QuotientGroup.mk'_surjective (center C)).nontrivial
    exact Group.IsPerfect.not_isMulCommutative C
      ⟨⟨fun x y => Subtype.ext ((hCC x.property y y.property).symm)⟩⟩
  rw [he]
  exact hs.full_supports_centralize ρ N K p t hl hr hK

end BinaryTensorThree
