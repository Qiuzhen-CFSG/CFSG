module
public import CFSG.Quasithin.Chapter13.Section05.NormalBranch.SourceCoreIntersection
public import CFSG.Quasithin.Chapter13.Section05.NormalBranch.SourcePairNormal
public import Theory.GroupTheory.SylowNormalRestriction

/-!
# The original starred group in the A₆ normal branch

The supplied Sylow subgroup meets L in a group of order 128, whose kernel
in H* is the original U_H of order 32. Thus four divides |H*|. The actual
cubic and the selected symmetric-three pair already give an order-eighteen
subgroup. Together with the proved bound |H*| dividing 36, this forces
|H*|=36. The original faithful orthogonal action is therefore onto its
marked cubic normalizer, giving H* isomorphic to S₃×S₃.

Source: Aschbacher–Smith 13.5.15(9), printed pp.920–921.
-/

public section
open Subgroup
namespace CFSG.Quasithin.Chapter13.Section05.NormalBranch.SourceStarFull
open Section08.SourceCompletion
open SourceOrthogonal SourceOrthogonalWitness SourceStarBound
open ChapterF.Section09.Setup.Hypothesis
variable {G : Type*} [Group G] [Finite G] {D : ChapterF.Section09.Setup G}
  {V₂ M : Subgroup G}
  (d : NaturalSetup D.T D.L D.V D.V₁ V₂ D.Vplus M D.Gz)
  (h : D.Hypothesis) (e : (D.L ⧸ pCore 2 D.L) ≃* alternatingGroup (Fin 6))
  (hseed : D.Vplus = ⁅D.V,D.L₁⁆) (hn : (D.L₁.subgroupOf D.H).Normal)
  (hU : ¬IsMulCommutative D.UH)
include d h e hseed hn hU

theorem local_sylow_card (hQ : D.LT.pCoreIn 2 = D.V) :
    Nat.card ((D.T : Subgroup G) ⊓ D.L : Subgroup G) = 128 := by
  have hc : Nat.card (pCore 2 D.L) = 16 := by
    have he : Nat.card (D.L.pCoreIn 2) = Nat.card (pCore 2 D.L) :=
      card_map_of_injective D.L.subtype_injective
    rw [SourceCoreIntersection.local_core_eq_module d h e hseed hn hU hQ,
      ReturningPlane.module_card d] at he
    exact he.symm
  have hL : Nat.card D.L = 5760 := by
    rw [card_eq_card_quotient_mul_card_subgroup (pCore 2 D.L),hc,
      Nat.card_congr e.toEquiv,nat_card_alternatingGroup]
    norm_num
  obtain ⟨R,hR⟩ := (D.T.subtype d.normalizes_L).exists_subgroupOf_eq_of_normal
    (D.L.subgroupOf (normalizer (D.L : Set G)))
  let a := subgroupOfEquivOfLe D.L.le_normalizer
  let P := R.mapSurjective (f := a.toMonoidHom) a.surjective
  have hP : (P : Subgroup D.L) = (D.T : Subgroup G).subgroupOf D.L := by
    change (R : Subgroup _).map a.toMonoidHom = _
    rw [hR]
    ext x
    constructor
    · rintro ⟨y,hy,rfl⟩; exact hy
    · intro hx
      exact ⟨⟨⟨x,D.L.le_normalizer x.property⟩,x.property⟩,hx,rfl⟩
  have hp : Nat.card P = 128 := by
    rw [P.card_eq_multiplicity,hL]
    decide +kernel
  rw [←subgroupOf_map_subtype (D.T : Subgroup G) D.L,
    card_map_of_injective D.L.subtype_injective,←hP]
  exact hp

theorem four_dvd_original_star (hQ : D.LT.pCoreIn 2 = D.V) :
    4 ∣ Nat.card (Section08.Source.Hstar D.H) := by
  let R : Subgroup G := (D.T : Subgroup G) ⊓ D.L
  have hRH : R ≤ D.H := inf_le_left.trans h.T_le_H
  have hUR : D.UH ≤ R := le_inf (h.UH_le_QH.trans h.QH_le_T)
    ((closure_reduction h hseed hn).2.2)
  let f := pairProjection R hRH
  have hk : f.ker = D.UH.subgroupOf R := by
    rw [pairProjection_ker]
    ext x
    change (x : G) ∈ D.QH ↔ (x : G) ∈ D.UH
    constructor
    · intro hx
      exact (SourceCoreIntersection.core_inf_local d h e hseed hn hU hQ).le
        ⟨hx,x.property.2⟩
    · intro hx
      exact h.UH_le_QH hx
  have hkc : Nat.card f.ker = 32 := by
    rw [hk,Nat.card_congr (subgroupOfEquivOfLe hUR).toEquiv]
    exact (SourceQuaternion.source13_5_15_five d h e hseed hn hU).2.1
  have hc := f.ker.card_mul_index
  rw [index_ker,hkc,show Nat.card R = 128 from local_sylow_card d h e hseed hn hU hQ] at hc
  have hi : Nat.card f.range = 4 := by omega
  rw [←hi]
  exact f.range.card_subgroup_dvd_card

theorem eighteen_dvd_original_star : 18 ∣ Nat.card (Section08.Source.Hstar D.H) := by
  obtain ⟨r,hr,_,_,hj⟩ := SourcePairExact.exists_original_pair_core d h e hseed hn hU
  let f := starEmbedding d h e hseed hn hU
  let A := localCubic d h e hseed hn hU
  let J := ((D.V ⊔ D.V.map (MulAut.conj r).toMonoidHom).subgroupOf D.H).map
    (SourcePairNormal.actor d h e hseed hn hU)
  have hle : A ⊔ J ≤ f.range := by
    apply sup_le
    · exact (Section08.Source.starImage D.H D.L₁).map_le_range f
    · change ((D.V ⊔ D.V.map (MulAut.conj r).toMonoidHom).subgroupOf D.H).map
        (f.comp (QuotientGroup.mk' (pCore 2 D.H))) ≤ f.range
      rw [←map_map]
      exact Subgroup.map_le_range _ _
  have hc : Nat.card (A ⊔ J : Subgroup _) = 18 :=
    (SourcePairNormal.pair_image_structure d h e hseed hn hU r hr hj).2.2.2
  have hd := card_dvd_of_le hle
  rw [hc] at hd
  have he : Nat.card f.range = Nat.card (Section08.Source.Hstar D.H) :=
    (Nat.card_congr (MonoidHom.ofInjective (starEmbedding_injective d h e hseed hn hU)).toEquiv).symm
  rwa [he] at hd

theorem original_star_card (hQ : D.LT.pCoreIn 2 = D.V) :
    Nat.card (Section08.Source.Hstar D.H) = 36 := by
  apply Nat.dvd_antisymm (original_star_card_dvd d h e hseed hn hU)
  have hh := Nat.lcm_dvd (four_dvd_original_star d h e hseed hn hU hQ)
    (eighteen_dvd_original_star d h e hseed hn hU)
  norm_num at hh
  exact hh

theorem original_star_model (hQ : D.LT.pCoreIn 2 = D.V) :
    Nonempty (Section08.Source.Hstar D.H ≃* OmegaPlusFour) := by
  let f := starEmbedding d h e hseed hn hU
  let A := localCubic d h e hseed hn hU
  have hr : f.range ≤ normalizer (A : Set BinaryFourPlus.Wreath) :=
    range_normalizes_local d h e hseed hn hU
  let j : Section08.Source.Hstar D.H →* normalizer (A : Set BinaryFourPlus.Wreath) :=
    f.codRestrict _ (fun x => hr ⟨x,rfl⟩)
  have hj : Function.Injective j := fun x y he =>
    (starEmbedding_injective d h e hseed hn hU) (congrArg (fun z => (z.val : BinaryFourPlus.Wreath)) he)
  have hb : Function.Bijective j := hj.bijective_of_nat_card_le (by
    rw [(original_normalizer_card d h e hseed hn hU).1,
      original_star_card d h e hseed hn hU hQ])
  obtain ⟨a⟩ := (original_normalizer_models d h e hseed hn hU).1
  exact ⟨(MulEquiv.ofBijective j hb).trans a⟩

end CFSG.Quasithin.Chapter13.Section05.NormalBranch.SourceStarFull
