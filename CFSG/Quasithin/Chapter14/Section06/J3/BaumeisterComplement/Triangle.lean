module
public import CFSG.Quasithin.Chapter14.Section06.J3.BaumeisterComplement.TriangleQuotient
public import Theory.GroupTheory.Gaschutz

/-!
# Central splitting after the literal third-core intersection

A central two-cover of A₅ containing A₄ × C₂ splits: the central kernel
has a complement in that subgroup, whose index is five, and Gaschütz
extends the complement to the whole cover. The resulting direct product
uses the given epimorphism and its actual central kernel.

Applied to the original third parabolic, the preceding quotient theorem
discharges surjectivity. Thus only L₃ ∩ Q_f = ⟨f⟩ remains before constructing
the A₅ × C₂ map and OriginalMarking. The known intersection for C_{L₁}(f)
alone does not prove this generated-group intersection. In particular this
module does not assume or infer an A₅ complement from HTypeAt, and does
not claim completion of Baumeister 2.6.

Source: Baumeister (2007), Lemma 2.6, pp.496–497. Gaschütz supplies the
central-cover splitting once the source's complement alignment controls
the kernel; the alignment itself remains explicit.
-/

open Subgroup
namespace CFSG.Quasithin.Janko23.J3Recognition.Ambient.BaumeisterComplement
public noncomputable section
open Sporadic.Janko3.SourceRecognition
open Sporadic.Janko3.SourceRecognition.SingerField hiding normalizer
open Sporadic.Janko3.SourceRecognition.BaumeisterParabolics
variable {G : Type*} [Group G] [Finite G]

private theorem four_central_detection
    (x : alternatingGroup (Fin 4) × Multiplicative (ZMod 2))
    (hx : x ∈ center _) (h2 : x.2=1) : x=1 := by
  revert x
  decide +kernel

private theorem central_two_split_in_four {H : Type*} [Group H] [Finite H]
    (V : Subgroup H) (hV : V ≤ center H) (hcard : Nat.card V=2)
    (e : H ≃* (alternatingGroup (Fin 4) × Multiplicative (ZMod 2))) :
    ∃ K : Subgroup H, V.IsComplement' K := by
  let f : alternatingGroup (Fin 4) →* H := e.symm.toMonoidHom.comp (MonoidHom.inl _ _)
  have hf : Function.Injective f := e.symm.injective.comp (fun _ _ hh => congrArg Prod.fst hh)
  refine ⟨f.range,isComplement'_of_card_mul_and_disjoint ?_ ?_⟩
  · rw [hcard,←Nat.card_congr (MonoidHom.ofInjective hf).toEquiv,
      Nat.card_congr e.toEquiv,Nat.card_prod,nat_card_alternatingGroup]
    norm_num [Nat.factorial]
  · apply disjoint_def.mpr
    rintro x hx ⟨a,rfl⟩
    apply e.injective
    rw [map_one]
    apply four_central_detection _ ((MulEquivClass.apply_mem_center_iff e).mpr (hV hx))
    change (e (e.symm (a,1))).2=1
    rw [e.apply_symm_apply]

/-- A central two-cover of A₅ containing the actual A₄ × C₂ overgroup splits.
Gaschütz applies at its odd index five; no splitting of a larger group is used. -/
theorem alternating_central_cover_of_four {H : Type*} [Group H] [Finite H]
    (q : H →* alternatingGroup (Fin 5)) (hq : Function.Surjective q)
    (hcentral : q.ker ≤ center H) (hk : Nat.card q.ker=2)
    (X : Subgroup H) (hX : q.ker ≤ X)
    (eX : X ≃* (alternatingGroup (Fin 4) × Multiplicative (ZMod 2))) :
    Nonempty (H ≃* (alternatingGroup (Fin 5) × Multiplicative (ZMod 2))) := by
  let : IsMulCommutative q.ker := ⟨⟨fun x y => Subtype.ext
    (mem_center_iff.mp (hcentral y.property) x)⟩⟩
  have hH : Nat.card H=120 := by
    have hh := q.ker.index_mul_card
    rw [index_ker,q.range_eq_top_of_surjective hq,card_top,nat_card_alternatingGroup,hk] at hh
    norm_num [Nat.factorial] at hh
    exact hh.symm
  have hXC : Nat.card X=24 := by
    rw [Nat.card_congr eX.toEquiv,Nat.card_prod,nat_card_alternatingGroup]
    norm_num [Nat.factorial]
  have hXi : X.index=5 := by
    have hh := X.card_mul_index
    rw [hXC,hH] at hh
    omega
  obtain ⟨K,hK⟩ := exists_complement_of_coprime_overgroup q.ker X hX
    (by rw [hk,hXi]; decide) (central_two_split_in_four (q.ker.subgroupOf X)
      (fun x hx => mem_center_iff.mpr (fun y => Subtype.ext (mem_center_iff.mp (hcentral hx) y)))
      ((Nat.card_congr (subgroupOfEquivOfLe hX).toEquiv).trans hk) eX)
  let eK : K ≃* alternatingGroup (Fin 5) :=
    hK.symm.QuotientMulEquiv.symm.trans (QuotientGroup.quotientKerEquivOfSurjective q hq)
  let : IsCyclic q.ker := isCyclic_of_prime_card hk
  let eZ : q.ker ≃* Multiplicative (ZMod 2) := mulEquivOfCyclicCardEq (by
    rw [hk]; simp only [Nat.card_eq_fintype_card,Fintype.card_multiplicative,ZMod.card])
  obtain ⟨eProd,_⟩ := exists_mulEquiv_prod_sup_of_disjoint_of_commuting K q.ker
    hK.disjoint.symm (fun x _ y hy => (mem_center_iff.mp (hcentral hy) x).symm)
  exact ⟨(Subgroup.topEquiv.symm.trans (MulEquiv.subgroupCongr hK.symm.sup_eq_top.symm)).trans
    (eProd.symm.trans (eK.prodCongr eZ))⟩


/-- The remaining Baumeister 2.6 obligation is the intersection of the
GENERATED third group with Q_f. Its A₅ image and central splitting are proved
here. The known intersection for C_{L₁}(f) alone does not supply this premise. -/
theorem field_triangle_of_core_intersection {D : LocalSixteen.Seed G}
    (P : LocalSixteen.ReturningPair D) (hc : OneInvolutionClass G)
    (A : Subgroup G) [IsElementaryAbelian 2 A] (hA : Nat.card A = 16) (hAR : A ≤ P.R)
    (j : Model →* G) (hj : Function.Injective j)
    (hcore : Seventeen.third j.range (overlap j) (j fieldElement) ⊓
      (pCore 2 (involutionCentralizer (j fieldElement))).map
        (involutionCentralizer (j fieldElement)).subtype = zpowers (j fieldElement)) :
    Nonempty (Seventeen.third j.range (overlap j) (j fieldElement) ≃*
      Seventeen.TriangleGroup) := by
  let f := j fieldElement
  let C := involutionCentralizer f
  let L := Seventeen.third j.range (overlap j) f
  let X := j.range ⊓ C
  have hXL : X ≤ L := le_sup_left
  have hLC : L ≤ C := BaumeisterParabolics.third_le_centralizer _ _ _
  have hf : orderOf f=2 := image_involution_order j hj
  have hfX : f ∈ X := ⟨⟨fieldElement,rfl⟩,mem_centralizer_singleton_iff.mpr rfl⟩
  have hzL : zpowers f ≤ L := zpowers_le.mpr (hXL hfX)
  have hzX : zpowers f ≤ X := zpowers_le.mpr hfX
  obtain ⟨eQ⟩ := involution_twoCore_quotient D.localType hc f hf
  let qC := QuotientGroup.mk' (pCore 2 C)
  let q : L →* alternatingGroup (Fin 5) := eQ.toMonoidHom.comp (qC.comp (inclusion hLC))
  have hq : Function.Surjective q := by
    intro a
    have hm : eQ.symm a ∈ (L.subgroupOf C).map qC :=
      (field_third_quotient P hc A hA hAR j hj).symm ▸ mem_top _
    obtain ⟨x,hx,he⟩ := hm
    refine ⟨⟨x,hx⟩,?_⟩
    change eQ (qC x)=a
    rw [he,eQ.apply_symm_apply]
  have hk : q.ker = (zpowers f).subgroupOf L := by
    ext x
    change eQ (qC (inclusion hLC x))=1 ↔ (x : G) ∈ zpowers f
    rw [←eQ.map_one,eQ.injective.eq_iff]
    change ((inclusion hLC x : C) : C ⧸ pCore 2 C)=1 ↔ _
    rw [QuotientGroup.eq_one_iff]
    constructor
    · intro hx
      exact hcore ▸ (show (x : G) ∈ L ⊓ (pCore 2 C).map C.subtype from
        ⟨x.property,⟨inclusion hLC x,hx,rfl⟩⟩)
    · intro hx
      have hm : (x : G) ∈ (pCore 2 C).map C.subtype :=
        (show (x : G) ∈ L ⊓ (pCore 2 C).map C.subtype from hcore.symm ▸ hx).2
      obtain ⟨u,hu,he⟩ := hm
      have heu : u = inclusion hLC x := Subtype.ext he
      rwa [heu] at hu
  have hcentral : q.ker ≤ center L := by
    intro x hx
    have hxZ : (x : G) ∈ zpowers f := by
      change x ∈ (zpowers f).subgroupOf L
      rwa [←hk]
    obtain ⟨n,hn⟩ := mem_zpowers_iff.mp hxZ
    apply mem_center_iff.mpr
    intro y
    apply Subtype.ext
    change (y : G) * (x : G) = (x : G) * (y : G)
    rw [←hn]
    have hy : Commute (y : G) f := mem_centralizer_singleton_iff.mp (hLC y.property)
    exact (hy.zpow_right n).eq
  have hk2 : Nat.card q.ker=2 := by
    rw [hk,←card_map_of_injective L.subtype_injective,subgroupOf_map_subtype,
      inf_eq_left.mpr hzL,Nat.card_zpowers,hf]
  have hkerX : q.ker ≤ X.subgroupOf L := by
    intro x hx
    apply hzX
    change x ∈ (zpowers f).subgroupOf L
    rwa [←hk]
  exact alternating_central_cover_of_four q hq hcentral hk2 (X.subgroupOf L) hkerX
    ((subgroupOfEquivOfLe hXL).trans (PointCentralizer.imagePointCentralizerEquiv j hj))

/-- All model and overlap fields of OriginalMarking follow once the same
literal L₃ has central intersection with Q_f. This retains that unproved
alignment premise explicitly. -/
noncomputable def field_original_marking_of_core_intersection {D : LocalSixteen.Seed G}
    (P : LocalSixteen.ReturningPair D) (hc : OneInvolutionClass G)
    (A : Subgroup G) [IsElementaryAbelian 2 A] (hA : Nat.card A = 16) (hAR : A ≤ P.R)
    (j : Model →* G) (hj : Function.Injective j)
    (hcore : Seventeen.third j.range (overlap j) (j fieldElement) ⊓
      (pCore 2 (involutionCentralizer (j fieldElement))).map
        (involutionCentralizer (j fieldElement)).subtype = zpowers (j fieldElement)) :
    Seventeen.OriginalMarking j.range (overlap j) (j fieldElement) :=
  field_original_marking_of_triangle P hc A hA hAR j hj
    (Classical.choice (field_triangle_of_core_intersection P hc A hA hAR j hj hcore))

end
end CFSG.Quasithin.Janko23.J3Recognition.Ambient.BaumeisterComplement
