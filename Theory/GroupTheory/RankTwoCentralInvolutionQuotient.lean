module

public import Theory.GroupTheory.OddPrimeSectionCentralizers.FullCentralizer
public import Theory.GroupTheory.CoprimeQuotientNormalizer
public import Theory.GroupTheory.CoprimeCentralizerDecomposition
public import Theory.GroupTheory.CharacteristicCentralizerFusion

/-!
# Abelian cubic quotients and a central involution modulo a normal three-group

Suppose an involution t moves a normal three-subgroup Q but is central modulo
Q. Coprime normalizer lifting gives G = Q C_G(t). Coprime action gives
Q = [Q,t] C_Q(t), so every abelian quotient is covered by C_G(t).
When G is covered by a group of three-rank at most two, every three-subgroup
of that centralizer is cyclic by A.1.31. Consequently every abelian
three-group quotient of G is cyclic.

The rank hypothesis stays on the original cover. No splitting of the
three-group kernel, bound on its generator rank, or quotient rank monotonicity
is used. Source: Aschbacher--Smith, A.1.31(1), printed pp.27--28, together
with the coprime-action and Frattini arguments of A.1.
-/

public noncomputable section
open Subgroup
open scoped IsMulCommutative commutatorElement
namespace Theory.GroupTheory

variable {B A D : Type*} [Group B] [Finite B] [Group A] [Finite A]
  [Group D] [IsMulCommutative D]

private theorem centralizer_sup_of_central_involution_mod_three
    (Q : Subgroup A) [Q.Normal] (hQ : IsPGroup 3 Q)
    (t : A) (ht : orderOf t = 2)
    (hz : QuotientGroup.mk' Q t ∈ center (A ⧸ Q)) :
    centralizer ({t} : Set A) ⊔ Q = ⊤ := by
  let q := QuotientGroup.mk' Q
  let T := zpowers t
  let Z := zpowers (q t)
  have hZc : Z ≤ center (A ⧸ Q) := zpowers_le.mpr hz
  let : Z.Normal := by
    refine ⟨fun x hx g => ?_⟩
    have hc := mem_center_iff.mp (hZc hx) g
    simpa only [hc,mul_inv_cancel_right] using hx
  let : Fact (IsPGroup 2 T) := ⟨IsPGroup.of_card (n := 1) (by
    change Nat.card (zpowers t) = 2 ^ 1
    rw [Nat.card_zpowers,ht,pow_one])⟩
  have hcop : Nat.Coprime 2 (Nat.card Q) := by
    obtain ⟨n,hn⟩ := hQ.exists_card_eq
    rw [hn]
    exact (by decide : Nat.Coprime 2 3).pow_right n
  have hm : (normalizer (T : Set A)).map q = ⊤ := by
    rw [← normalizer_map_quotient_eq_map_normalizer 2 T Q inferInstance hcop]
    change normalizer ((zpowers t).map q : Set (A ⧸ Q)) = ⊤
    rw [MonoidHom.map_zpowers]
    exact normalizer_eq_top (H := Z)
  have hh := congrArg (Subgroup.comap q) hm
  rw [comap_map_eq,QuotientGroup.ker_mk',comap_top,
    normalizer_zpowers_eq_centralizer_of_order_two t ht] at hh
  exact hh

private theorem centralizer_surjects_abelian_of_central_involution_mod_three
    (q : A →* D) (hq : Function.Surjective q)
    (Q : Subgroup A) [Q.Normal] (hQ : IsPGroup 3 Q)
    (t : A) (ht : orderOf t = 2)
    (hz : QuotientGroup.mk' Q t ∈ center (A ⧸ Q)) :
    Function.Surjective (q.comp (centralizer ({t} : Set A)).subtype) := by
  let C := centralizer ({t} : Set A)
  let T := zpowers t
  have hcop : Nat.Coprime (Nat.card T) (Nat.card Q) := by
    obtain ⟨n,hn⟩ := hQ.exists_card_eq
    rw [Nat.card_zpowers,ht,hn]
    exact (by decide : Nat.Coprime 2 3).pow_right n
  let : Group.IsNilpotent Q := hQ.isNilpotent
  have hsplit := eq_commutator_sup_centralizer_of_solvable_coprime Q T
    le_normalizer_of_normal inferInstance hcop
  have hkill : ⁅Q,T⁆ ≤ q.ker := by
    apply commutator_le.mpr
    intro x _ y _
    change q ⁅x,y⁆ = 1
    rw [map_commutatorElement,commutatorElement_eq_one_iff_mul_comm]
    exact mul_comm' _ _
  have hcent : Q ⊓ centralizer (T : Set A) ≤ C := by
    intro x hx
    exact mem_centralizer_singleton_iff.mpr (hx.2 t (mem_zpowers t)).symm
  have hQimage : Q.map q ≤ C.map q := by
    conv_lhs => rw [hsplit]
    rw [Subgroup.map_sup]
    exact sup_le ((map_mono hkill).trans (by rw [map_ker_self]; exact bot_le))
      (map_mono hcent)
  have hgen := centralizer_sup_of_central_involution_mod_three Q hQ t ht hz
  have himage : C.map q = ⊤ := by
    have hh := congrArg (Subgroup.map q) hgen
    rw [Subgroup.map_sup,map_top_of_surjective q hq,sup_eq_left.mpr hQimage] at hh
    exact hh
  apply MonoidHom.range_eq_top.mp
  rw [MonoidHom.range_comp,range_subtype,himage]

/-- A moved normal three-group with a central involution modulo it forces
every abelian three-group quotient to be cyclic, retaining rank on the cover. -/
theorem cyclic_abelian_three_quotient_of_central_involution
    (cover : B →* A) (hcover : Function.Surjective cover) (hrank : primeRank 3 B ≤ 2)
    (q : A →* D) (hq : Function.Surjective q) (hD : IsPGroup 3 D)
    (Q : Subgroup A) [Q.Normal] (hQ : IsPGroup 3 Q)
    (t : A) (ht : orderOf t = 2)
    (hz : QuotientGroup.mk' Q t ∈ center (A ⧸ Q))
    (hmove : t ∉ centralizer (Q : Set A)) : IsCyclic D := by
  let : Finite D := Finite.of_surjective q hq
  let C := centralizer ({t} : Set A)
  let f := q.comp C.subtype
  have hf : Function.Surjective f :=
    centralizer_surjects_abelian_of_central_involution_mod_three q hq Q hQ t ht hz
  let S : Sylow 3 C := Classical.choice inferInstance
  let R := (S : Subgroup C).map C.subtype
  have hcyc : IsCyclic R :=
    cyclic_pSubgroup_in_involution_centralizer_of_surjective_rank_two
      (by decide : Odd 3) cover hcover hrank Q hQ t ht hmove R
      (S.isPGroup'.map C.subtype) (map_subtype_le _)
  let : IsCyclic S := ((S : Subgroup C).equivMapOfInjective
    C.subtype C.subtype_injective).isCyclic.mpr hcyc
  have htop : (S : Subgroup C).map f = ⊤ :=
    ((S.mapSurjective hf).is_maximal' (hD.to_subgroup ⊤) le_top).symm
  apply isCyclic_of_surjective (f.comp (S : Subgroup C).subtype)
  apply MonoidHom.range_eq_top.mp
  rw [MonoidHom.range_comp,range_subtype,htop]

end Theory.GroupTheory
