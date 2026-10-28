module
public import CFSG.Quasithin.Chapter7.NormalizedSource.DoubledBinaryPureAction
public import CFSG.Quasithin.Chapter7.NormalizedSource.DoubledBinarySylowFixed
-- Keep the canonical inner-group/central-quotient transport from its owner.
import all CFSG.Quasithin.Chapter7.NormalizedSource.DoubledBinaryComponentSylow

/-!
# The original H1 component Sylow and its noncyclic center

The line Z centralizes K, so commutators in Z vanish in K's actual inner
action. The invariant join Z ∨ V₋ therefore gives a normalized elementary
sixteen in the canonical image of the original component Sylow, with
centralizer index at most two. The involution fixed-point bound supplies
at least four central elements and excludes a cyclic Sylow center.

All maps agree with K → K/Z(K). The chosen-module application keeps
H ≤ C_G(Z), the original pure line, and the same component; it does not
replace H by a paired-plane centralizer.
Source: Aschbacher–Smith, the H1 argument in 7.7.3, printed p.706,
refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter7.NormalizedSource.DoubledBinaryPureComponentSylow

private theorem inner_sylow_modulo
    {G : Type*} [_root_.Group G] [Finite G] (K Z A S : Subgroup G)
    (hAS : A ≤ S) (hpS : IsPGroup 2 S)
    (hAN : A ≤ normalizer (K : Set G)) (hZK : Z ≤ centralizer (K : Set G))
    (hSB : S ≤ normalizer ((Z ⊔ A : Subgroup G) : Set G))
    (N : Subgroup S) (hN : N.index ≤ 2) (hcomm : ⁅N.map S.subtype,Z ⊔ A⁆ ≤ Z)
    (P : Sylow 2 K) (hPS : (P : Subgroup K).map K.subtype ≤ S)
    (i : A →* MulAut.innerSubgroup K)
    (hact : ∀ a : A, (i a : MulAut K) = K.normalizerMonoidHom (inclusion hAN a)) :
    let PI := P.mapSurjective (f := (MulAut.conj : K →* MulAut K).rangeRestrict)
      MulAut.conj.rangeRestrict_surjective
    i.range ≤ (PI : Subgroup _) ∧
      (PI : Subgroup _) ≤ normalizer (i.range : Set (MulAut.innerSubgroup K)) ∧
      ((centralizer (i.range : Set (MulAut.innerSubgroup K))).subgroupOf (PI : Subgroup _)).index ≤ 2 := by
  let I := MulAut.innerSubgroup K
  let u : K →* I := MulAut.conj.rangeRestrict
  let PI := P.mapSurjective (f := u) MulAut.conj.rangeRestrict_surjective
  let E := i.range
  let NK := normalizer (K : Set G)
  let f := K.normalizerMonoidHom
  have hfk (k : K) : f ⟨k,K.le_normalizer k.property⟩ = (u k : MulAut K) := by
    ext x
    rfl
  let J := ((S.subgroupOf NK).map f).subgroupOf I
  have hpJ : IsPGroup 2 J := (hpS.comap_subtype.map f).comap_subtype
  have hPJ : (PI : Subgroup I) ≤ J := by
    rintro _ ⟨k,hk,rfl⟩
    refine ⟨⟨k,K.le_normalizer k.property⟩,hPS (mem_map_of_mem K.subtype hk),?_⟩
    ext x
    rfl
  have hEJ : E ≤ J := by
    rintro _ ⟨a,rfl⟩
    exact ⟨inclusion hAN a,hAS a.property,(hact a).symm⟩
  have hEP : E ≤ (PI : Subgroup I) := hEJ.trans (PI.is_maximal' hpJ hPJ).le
  have hZN : Z ≤ NK := hZK.trans (Subgroup.centralizer_le_normalizer _)
  have hF : ((Z ⊔ A).subgroupOf NK).map f = E.map I.subtype := by
    rw [subgroupOf_sup hZN hAN,Subgroup.map_sup]
    have hz : (Z.subgroupOf NK).map f = ⊥ := by
      rw [Subgroup.map_eq_bot_iff]
      intro z hz
      rw [normalizerMonoidHom_ker]
      exact hZK hz
    rw [hz,bot_sup_eq]
    apply le_antisymm
    · rintro _ ⟨a,ha,rfl⟩
      exact ⟨i ⟨a,ha⟩,⟨⟨a,ha⟩,rfl⟩,hact ⟨a,ha⟩⟩
    · rintro _ ⟨b,⟨a,rfl⟩,rfl⟩
      exact ⟨inclusion hAN a,a.property,(hact a).symm⟩
  have hnorm : (PI : Subgroup I) ≤ normalizer (E : Set I) := by
    rintro _ ⟨k,hk,rfl⟩
    have hn : (⟨k,K.le_normalizer k.property⟩ : NK) ∈
        normalizer ((Z ⊔ A).subgroupOf NK : Set NK) :=
      le_normalizer_comap NK.subtype (hSB (hPS (mem_map_of_mem K.subtype hk)))
    have hh := le_normalizer_map f (mem_map_of_mem f hn)
    rw [hF,hfk] at hh
    have hhh : u k ∈ normalizer ((E.map I.subtype).comap I.subtype : Set I) :=
      le_normalizer_comap I.subtype (show (u k : MulAut K) ∈ normalizer (E.map I.subtype : Set _) from hh)
    rwa [comap_map_eq_self_of_injective I.subtype_injective] at hhh
  let C := (centralizer (E : Set I)).subgroupOf (PI : Subgroup I)
  let r : P →* PI := u.subgroupMap (P : Subgroup K)
  have hr : Function.Surjective r := u.subgroupMap_surjective _
  let s : P →* S := ((K.subtype.comp (P : Subgroup K).subtype).codRestrict S
    (fun k => hPS (mem_map_of_mem K.subtype k.property)))
  have hNC : N.comap s ≤ C.comap r := by
    intro k hk
    change u k.val ∈ centralizer (E : Set I)
    rintro _ ⟨a,rfl⟩
    have hz := hZK (hcomm (commutator_mem_commutator
      (mem_map_of_mem S.subtype hk) (mem_sup_right a.property)))
    let n : NK := ⟨k.val,K.le_normalizer k.val.property⟩
    let b := inclusion hAN a
    have hker : ⁅n,b⁆ ∈ f.ker := by
      rw [normalizerMonoidHom_ker]
      exact hz
    have he : ⁅f n,f b⁆ = 1 := by
      rw [← map_commutatorElement]
      exact hker
    apply Subtype.ext
    have hc := (commutatorElement_eq_one_iff_mul_comm.mp he).symm
    change (i a : MulAut K) * (u k.val : MulAut K) =
      (u k.val : MulAut K) * (i a : MulAut K)
    rw [hact]
    rw [show f n = (u k.val : MulAut K) from hfk k.val] at hc
    exact hc
  have hi : C.index ≤ 2 := by
    rw [← C.index_comap_of_surjective hr]
    apply (Nat.le_of_dvd (Nat.pos_of_ne_zero (N.comap s).index_ne_zero_of_finite)
      (index_dvd_of_le hNC)).trans
    apply le_trans _ hN
    rw [N.index_comap]
    exact (relIndex_le_of_le_right (H := N) (le_top : s.range ≤ ⊤)
      (by simpa using N.index_ne_zero_of_finite)).trans_eq N.relIndex_top_right
  exact ⟨hEP,hnorm,hi⟩

/-- The original component Sylow contains and normalizes the projected
rank-four actor, and centralizes it with index at most two. The modulo-line
commutators vanish under the actual action on K, since K centralizes Z. -/
theorem projected_sylow_modulo
    {G : Type*} [_root_.Group G] [Finite G] (K Z A S : Subgroup G)
    (hAS : A ≤ S) (hpS : IsPGroup 2 S)
    (hAN : A ≤ normalizer (K : Set G)) (hZK : Z ≤ centralizer (K : Set G))
    (hSB : S ≤ normalizer ((Z ⊔ A : Subgroup G) : Set G))
    (N : Subgroup S) (hN : N.index ≤ 2) (hcomm : ⁅N.map S.subtype,Z ⊔ A⁆ ≤ Z)
    (P : Sylow 2 K) (hPS : (P : Subgroup K).map K.subtype ≤ S)
    (j : A →* K ⧸ center K)
    (hact : ∀ a : A, (innerEquivCentralQuotient.symm (j a) : MulAut K) =
      K.normalizerMonoidHom (inclusion hAN a)) :
    let Q := P.mapSurjective (QuotientGroup.mk'_surjective (center K))
    j.range ≤ (Q : Subgroup _) ∧
      (Q : Subgroup _) ≤ normalizer (j.range : Set (K ⧸ center K)) ∧
      ((centralizer (j.range : Set (K ⧸ center K))).subgroupOf (Q : Subgroup _)).index ≤ 2 := by
  let e := innerEquivCentralQuotient (H := K)
  let i : A →* MulAut.innerSubgroup K := e.symm.toMonoidHom.comp j
  obtain ⟨hEP,hPN,hi⟩ := inner_sylow_modulo K Z A S hAS hpS hAN hZK hSB N hN hcomm P hPS i hact
  obtain ⟨Q,hQI,hQ,hC⟩ := DoubledBinaryComponentSylow.transport_sylow e _ i.range hEP hi
  have hj : i.range.map e.toMonoidHom = j.range := by
    rw [←MonoidHom.range_comp]
    congr 1
    ext a
    exact e.apply_symm_apply (j a)
  have hmap : e.toMonoidHom.comp (MulAut.conj : K →* MulAut K).rangeRestrict =
      QuotientGroup.mk' (center K) := by
    ext k
    exact DoubledBinaryComponentSylow.inner_conj k
  have hQQ : (Q : Subgroup (K ⧸ center K)) =
      (P : Subgroup K).map (QuotientGroup.mk' (center K)) := by
    rw [hQI]
    change ((P : Subgroup K).map (MulAut.conj : K →* MulAut K).rangeRestrict).map
      e.toMonoidHom = _
    rw [map_map,hmap]
  have hn : (Q : Subgroup (K ⧸ center K)) ≤ normalizer (j.range : Set _) := by
    rw [hQI,←hj,←map_equiv_normalizer_eq]
    exact map_mono hPN
  rw [hj,hQQ] at hQ hC
  rw [hQQ] at hn
  exact ⟨hQ,hn,hC⟩

/-- A normalized elementary sixteen with centralizer index at most two
forces the center of this very Sylow subgroup to be noncyclic. -/
theorem projected_center_not_cyclic
    {X : Type*} [_root_.Group X] [Finite X]
    (P : Sylow 2 X) (A : Subgroup X) [IsElementaryAbelian 2 A]
    (hA : Nat.card A = 16) (hAP : A ≤ (P : Subgroup X))
    (hPN : (P : Subgroup X) ≤ normalizer (A : Set X))
    (hi : ((centralizer (A : Set X)).subgroupOf (P : Subgroup X)).index ≤ 2) :
    ¬ IsCyclic (center P) := by
  have hfour := DoubledBinarySylowFixed.four_le_fixed_card A A (P : Subgroup X) le_rfl hPN hA hi
  let C := (centralizer (P : Set X)).subgroupOf A
  change 4 ≤ Nat.card C at hfour
  let r : C →* P := (inclusion hAP).comp C.subtype
  have hc (c : C) : r c ∈ center P := by
    apply mem_center_iff.mpr
    intro p
    exact Subtype.ext (c.property p p.property)
  let f : C →* center P := r.codRestrict _ hc
  have hf : Function.Injective f := by
    intro a b he
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun z : center P => (z.val : X)) he
  intro hcyc
  let := hcyc
  let : IsCyclic C := isCyclic_of_injective f hf
  let : IsElementaryAbelian 2 C := IsElementaryAbelian.of_injective C.subtype C.subtype_injective
  have hd := IsElementaryAbelian.exponent_dvd_p 2 C
  rw [IsCyclic.exponent_eq_card] at hd
  have hh := Nat.le_of_dvd (by decide : 0 < 2) hd
  omega

end CFSG.Quasithin.Chapter7.NormalizedSource.DoubledBinaryPureComponentSylow
