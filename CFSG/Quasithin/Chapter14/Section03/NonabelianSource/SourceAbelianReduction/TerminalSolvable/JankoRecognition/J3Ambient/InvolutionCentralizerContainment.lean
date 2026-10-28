module
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable.JankoRecognition.J3Ambient.TriangleGeneration
public import Theory.SpecificGroups.MinusExtraspecial.TriangleMaximal

/-!
# The full involution centralizer in the original completion join

The literal triangle supplements the full extraspecial core and meets it in
the central involution. It is maximal in the full involution centralizer.
The local cubic normalizer has order 48 and lies in the join of the actual
completion and cubic normalizer, so that join cannot meet the centralizer
only in its order-120 triangle. Thus it contains the entire centralizer.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable.J3Ambient
open Janko23.J3Recognition.LocalSixteen Janko23.J3Recognition.Ambient
open Janko23.J3Recognition.Ambient.Seventeen
open Representation.CentralCubicNaturalFour
open Sporadic.Janko3.SourceRecognition
open Sporadic.Janko3.SourceRecognition.BaumeisterParabolics

variable {G : Type*} [Group G] [Finite G] {D : Seed G}

private theorem local_cubic_normalizer_card_of_fusion
    {D : Seed G}
    (hc : Janko23.OneInvolutionClass G) (f : G) (hf : orderOf f = 2)
    (s : Janko23.involutionCentralizer f) (hs : orderOf s = 3) :
    Nat.card (normalizer (zpowers s : Set (Janko23.involutionCentralizer f))) = 48 := by
  obtain ⟨g,hg⟩ := isConj_iff.mp (hc.isConj D.localType.involution hf)
  let a := MulAut.conj g
  have haf : a f = D.z := hg
  let e : Janko23.involutionCentralizer f ≃* Janko23.involutionCentralizer D.z :=
    (CentralizerSmallKernelTransport.centralizerEquiv a f).trans
      (MulEquiv.subgroupCongr (by rw [haf]))
  have hm : (normalizer (zpowers s : Set (Janko23.involutionCentralizer f))).map
      e.toMonoidHom = normalizer (zpowers (e s) : Set (Janko23.involutionCentralizer D.z)) := by
    rw [map_equiv_normalizer_eq,MonoidHom.map_zpowers]
    rfl
  rw [←card_map_of_injective (f := e.toMonoidHom) e.injective,hm]
  exact cubic_local_normalizer_card D.localType (e s) ((e.orderOf_eq s).trans hs)

/-- The original completion and the normalizer of its literal cubic together
contain the full centralizer of the same field involution. -/
theorem literal_involution_centralizer_le_completion_sup_cubic_normalizer
    (P : ReturningPair D) (hc : Janko23.OneInvolutionClass G)
    (A : Subgroup G) (C : Subgroup (normalizer (A : Set G)))
    (a : A ≃* Plane) (j : SingerField.Model →* G)
    (hj : PlaneTransport.FieldEmbedding A C a j) :
    Janko23.involutionCentralizer (j SingerField.fieldElement) ≤
      completion j.range (overlap j) ⊔ normalizer (zpowers (j cubic) : Set G) := by
  let f := j SingerField.fieldElement
  let s := j cubic
  let H := Janko23.involutionCentralizer f
  let Q := Janko23.localCore f
  let R := third j.range (overlap j) f
  let J := completion j.range (overlap j) ⊔ normalizer (zpowers s : Set G)
  let K := J.subgroupOf H
  have hf : orderOf f = 2 := image_involution_order j hj.1
  obtain ⟨⟨eQ⟩,_,⟨eA⟩⟩ := literal_involution_core_and_quotient (D := D) hc f hf
  obtain ⟨hRH,hQR,hgen,hRcard⟩ := literal_triangle_generation P hc A C a j hj
  obtain ⟨hZmap,_⟩ := literal_triangle_quotient_splitting P hc A C a j hj
  have hRmap : (R.subgroupOf H).map H.subtype = R := map_subgroupOf_eq_of_le hRH
  have hinf : Q ⊓ R.subgroupOf H = center H := by
    apply map_injective (f := H.subtype) H.subtype_injective
    rw [map_inf _ _ _ H.subtype_injective,hRmap,hZmap]
    exact hQR
  have hsup : Q ⊔ R.subgroupOf H = ⊤ := by
    apply map_injective (f := H.subtype) H.subtype_injective
    rw [Subgroup.map_sup,hRmap,←MonoidHom.range_eq_map,H.range_subtype]
    exact hgen
  have hRK : R.subgroupOf H ≤ K := by
    intro x hx
    change (x : G) ∈ J
    exact mem_sup_left (third_le j.range (overlap j) f hx)
  have hsH : s ∈ H := mem_centralizer_singleton_iff.mpr
    ((cubic_commutes_complement
      ⟨SingerField.fieldElement,(mem_pointComplement _).mpr rfl⟩).map j).eq
  let sH : H := ⟨s,hsH⟩
  have hs : orderOf sH = 3 :=
    (orderOf_coe sH).symm.trans ((orderOf_injective j hj.1 _).trans cubic_order)
  have hNcard : Nat.card (normalizer (zpowers sH : Set H)) = 48 :=
    local_cubic_normalizer_card_of_fusion (D := D) hc f hf sH hs
  have hNK : normalizer (zpowers sH : Set H) ≤ K := by
    intro x hx
    change (x : G) ∈ J
    apply mem_sup_right
    have hm := (zpowers sH).le_normalizer_map H.subtype (mem_map_of_mem H.subtype hx)
    have hline : (zpowers sH).map H.subtype = zpowers s := by
      rw [MonoidHom.map_zpowers]
      rfl
    rw [hline] at hm
    exact hm
  rcases MinusExtraspecial.triangle_overgroup_eq_or_top Q (R.subgroupOf H) K eQ
      (centralizer_generalizedFitting_le H) eA hinf hsup hRK with hK | hK
  · have hd := card_dvd_of_le (hNK.trans_eq hK)
    rw [hNcard,Nat.card_congr (subgroupOfEquivOfLe hRH).toEquiv,hRcard] at hd
    norm_num at hd
  · exact subgroupOf_eq_top.mp hK

end CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable.J3Ambient
