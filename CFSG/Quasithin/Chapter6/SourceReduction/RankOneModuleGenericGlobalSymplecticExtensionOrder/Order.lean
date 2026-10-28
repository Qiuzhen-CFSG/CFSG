module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalSymplecticExtensionOrder.ClassPairs
public import CFSG.Quasithin.Chapter5.Section03SymplecticSource.ClassSeparation
public import Theory.GroupTheory.InvolutionClassOrderComparison

/-!
# Ambient order of the prepared symplectic full extension

The three pinned native involutions remain distinct in the full extension.
The original center-fusion theorem transports any alleged fusion between
source representatives through a full normalizer, proving source
irredundance. Conjugating an arbitrary endpoint involution into the original
Sylow gives compatible source and extension class paths. Irredundance then
proves preservation and reflection of every class predicate on each full
endpoint and on the whole middle.

For each representative, the established root-or-square alternatives select
its full marked centralizer comparison. These comparisons retain the marked
involution and the two distinct class predicates required by Thompson's
counting theorem. The complete three-class families therefore give equality
of the original group order with the SAME full extension carrier order.
No ambient generation or recognition theorem enters this order argument.

Source: Aschbacher--Smith F.4.27,30,35,38--43, printed pp.288--296, through
5.3.2--3, pp.658--659 of refs/quasithin.pdf. The original Preparation,
perfect whole residual, both orientations and n=2 are retained.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Theory.SpecificGroups.SymplecticFour
open Representation.OneCohomology.SymplecticFour
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
open Theory.SpecificGroups.SymplecticFour.SourceFusionOrder
open CFSG.Quasithin.ChapterF.SourceCompletion.SymplecticFour
variable {G : Type*} [Group G] [Finite G]

private theorem local_class_pair {J I : Type*} [Group J]
    (T : Sylow 2 G) (S M : Subgroup G) (hST : S=(T : Subgroup G)) (hSM : S≤M)
    (φ : M→*J) (ψ : S→*J) (hmark : ∀ x, φ (inclusion hSM x)=ψ x)
    (u : I→S) (w : I→J)
    (hpairs : ∀ x : S, orderOf x=2 → ∃ i, IsConj (u i).val x.val ∧ IsConj (w i) (ψ x))
    (x : M) (hx : orderOf x=2) :
    ∃ i, IsConj (u i).val x.val ∧ IsConj (w i) (φ x) := by
  have hTM : (T : Subgroup G)≤M := hST ▸ hSM
  let R := T.subtype hTM
  obtain ⟨y,hxy⟩ := R.exists_isConj_of_orderOf_eq_prime_pow
    (x := x) (n := 1) (by simpa using hx)
  let s : S := ⟨y.val.val,hST ▸ y.property⟩
  have hys : inclusion hSM s=y.val := rfl
  have hy2 : orderOf s=2 := by
    rw [←Subgroup.orderOf_coe]
    change orderOf y.val.val=2
    rw [Subgroup.orderOf_coe]
    obtain ⟨c,hc⟩ := isConj_iff.mp hxy
    rw [←hc]
    exact ((MulAut.conj c).orderOf_eq x).trans hx
  obtain ⟨i,hi,hj⟩ := hpairs s hy2
  refine ⟨i,hi.trans (M.subtype.map_isConj hxy.symm),?_⟩
  rw [←hmark s,hys] at hj
  exact hj.trans (φ.map_isConj hxy.symm)

private theorem local_class_predicate {J I : Type*} [Group J]
    (T : Sylow 2 G) (S M : Subgroup G) (hST : S=(T : Subgroup G)) (hSM : S≤M)
    (φ : M→*J) (hφ : Function.Injective φ) (ψ : S→*J)
    (hmark : ∀ x, φ (inclusion hSM x)=ψ x)
    (u : I→S) (w : I→J) (hu : ∀ i, orderOf (u i).val=2) (hw : ∀ i, orderOf (w i)=2)
    (hpairs : ∀ x : S, orderOf x=2 → ∃ i, IsConj (u i).val x.val ∧ IsConj (w i) (ψ x))
    (hirred : ∀ i j, IsConj (u i).val (u j).val → i=j)
    (hirred' : ∀ i j, IsConj (w i) (w j) → i=j)
    (i : I) (x : M) : IsConj (u i).val x.val ↔ IsConj (w i) (φ x) := by
  have hc (hx : orderOf x=2) := local_class_pair T S M hST hSM φ ψ hmark u w hpairs x hx
  constructor
  · intro hi
    have hx : orderOf x=2 := by
      rw [←Subgroup.orderOf_coe]
      obtain ⟨c,hc⟩ := isConj_iff.mp hi
      rw [←hc]
      exact ((MulAut.conj c).orderOf_eq _).trans (hu i)
    obtain ⟨j,hj,hj'⟩ := hc hx
    exact (hirred i j (hi.trans hj.symm)).symm ▸ hj'
  · intro hi
    have hx : orderOf x=2 := by
      rw [←orderOf_injective φ hφ]
      obtain ⟨c,hc⟩ := isConj_iff.mp hi
      rw [←hc]
      exact ((MulAut.conj c).orderOf_eq _).trans (hw i)
    obtain ⟨j,hj,hj'⟩ := hc hx
    exact (hirred' i j (hi.trans hj'.symm)).symm ▸ hj

private theorem marked_class_card_eq {J : Type*} [Group J] [Finite J]
    (T : Sylow 2 G) (S : Subgroup G) (hST : S=(T : Subgroup G))
    (ψ : S→*J) (u : Fin 3→S) (w : Fin 3→J)
    (hu : ∀ i, orderOf (u i).val=2) (hw : ∀ i, orderOf (w i)=2)
    (hψu : ∀ i, ψ (u i)=w i)
    (hpairs : ∀ x : S, orderOf x=2 → ∃ i, IsConj (u i).val x.val ∧ IsConj (w i) (ψ x))
    (hcomplete' : ∀ x : J, orderOf x=2 → ∃ i, IsConj (w i) x)
    (hirred' : ∀ i j, IsConj (w i) (w j) → i=j)
    (hcontrol : ∀ i j, IsConj (u i).val (u j).val → IsConj (w i) (w j))
    (hcomparisons : ∀ k, ∃ (M : Subgroup G) (hSM : S≤M) (φ : M→*J),
      Function.Injective φ ∧ (∀ x, φ (inclusion hSM x)=ψ x) ∧
        MarkedCentralizerComparison M φ (inclusion hSM (u k))) : Nat.card G=Nat.card J := by
  have hirred (i j) (hij : IsConj (u i).val (u j).val) : i=j := hirred' i j (hcontrol i j hij)
  have hcomplete (x : G) (hx : orderOf x=2) : ∃ i, IsConj (u i).val x := by
    obtain ⟨y,hxy⟩ := T.exists_isConj_of_orderOf_eq_prime_pow
      (x := x) (n := 1) (by simpa using hx)
    let s : S := ⟨y.val,hST ▸ y.property⟩
    have hs : orderOf s=2 := by
      rw [←Subgroup.orderOf_coe]
      change orderOf y.val=2
      obtain ⟨c,hc⟩ := isConj_iff.mp hxy
      rw [←hc]
      exact ((MulAut.conj c).orderOf_eq x).trans hx
    obtain ⟨i,hi,_⟩ := hpairs s hs
    exact ⟨i,hi.trans hxy.symm⟩
  have heach (k : Fin 3) : ∃ e : centralizer ({(u k).val} : Set G)≃*
      centralizer ({w k} : Set J),
      e (InvolutionClassOrderComparison.centralizerPoint (u k).val)=
        InvolutionClassOrderComparison.centralizerPoint (w k) ∧
      ∀ i (x : centralizer ({(u k).val} : Set G)),
        IsConj (u i).val x.val ↔ IsConj (w i) (e x).val := by
    obtain ⟨M,hSM,φ,hφ,hm,hC⟩ := hcomparisons k
    change ∃ hz : centralizer ({(u k).val} : Set G)≤M,
      ∃ e : centralizer ({(u k).val} : Set G)≃*
        centralizer ({φ (inclusion hSM (u k))} : Set J),
          ∀ x, (e x).val=φ (inclusion hz x) at hC
    obtain ⟨hz,hC⟩ := hC
    have hpoint : φ (inclusion hSM (u k))=w k := (hm (u k)).trans (hψu k)
    rw [hpoint] at hC
    obtain ⟨e,he⟩ := hC
    refine ⟨e,?_,?_⟩
    · apply Subtype.ext
      have hv : inclusion hz (InvolutionClassOrderComparison.centralizerPoint (u k).val)=
          inclusion hSM (u k) := Subtype.ext (InvolutionClassOrderComparison.centralizerPoint_coe _)
      simpa only [InvolutionClassOrderComparison.centralizerPoint_coe] using
        (he _).trans ((congrArg φ hv).trans hpoint)
    · intro i x
      rw [he x]
      exact local_class_predicate T S M hST hSM φ hφ ψ hm u w hu hw hpairs hirred hirred' i (inclusion hz x)
  choose e he hf using heach
  exact InvolutionClassOrderComparison.card_eq_of_centralizer_equivs
    (fun i => (u i).val) w hu hw hcomplete hcomplete' hirred hirred' 0 1 (by decide)
      e he (hf · 0) (hf · 1)

variable {T : Sylow 2 G} {L W H A B : Subgroup G} {n : ℕ}
    (d : Preparation T L H A B (residual H))
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hp : Group.IsPerfect (residual H))
    (F : Type) [Field F] [Finite F] [CharP F 2]
    {m : ℕ} (hm : 0<m) (hF : Nat.card F=2^m)
    (he : Nonempty (RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H))
      (ChapterF.GreenBook.LieModels.SymplecticFour.amalgam F)) ∨
      Nonempty (RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H))
      (ChapterF.GreenBook.LieModels.SymplecticFour.amalgam F).reverse))
include d h hH hp hm hF he

private theorem Preparation.symplectic_card_eq_of_sylow_marking
    (a : SymplecticNormalizerMarking L (residual H) (sourceS L H) F)
    (b : sourceS L H≃*unipotent (F := F))
    (hpair : ∀ x : sourceS L H, orderOf x=2 → ∃ i : Fin 3,
      IsConj (b.symm (centralRepresentative i)).val x.val ∧
        IsConj (centralRepresentative i).val (b x).val)
    (hS1 : sourceS L H≤normalizer (L : Set G))
    (hS2 : sourceS L H≤normalizer (residual H : Set G))
    (φ : normalizer (L : Set G)→*a.extension.carrier)
    (χ : normalizer (residual H : Set G)→*a.extension.carrier)
    (δ : (normalizer (L : Set G)⊓normalizer (residual H : Set G) : Subgroup G)→*a.extension.carrier)
    (hφ : Function.Injective φ) (hχ : Function.Injective χ) (hδ : Function.Injective δ)
    (hmφ : ∀ x, φ (inclusion hS1 x)=a.extension.innerMap (b x).val)
    (hmχ : ∀ x, χ (inclusion hS2 x)=a.extension.innerMap (b x).val)
    (hmδ : ∀ x, δ (inclusion (le_inf hS1 hS2) x)=a.extension.innerMap (b x).val)
    (hcφ : SymplecticRootComparisons L (normalizer (L : Set G)) φ)
    (hcχ : SymplecticRootComparisons (residual H) (normalizer (residual H : Set G)) χ)
    (hcδ : SymplecticSquareComparisons (sourceS L H)
      (normalizer (L : Set G)⊓normalizer (residual H : Set G)) δ (le_inf hS1 hS2)) :
    Nat.card G=Nat.card a.extension.carrier := by
  let S := sourceS L H
  let ψ : S→*a.extension.carrier := a.extension.innerMap.comp (unipotent.subtype.comp b.toMonoidHom)
  let u (i : Fin 3) : S := b.symm (centralRepresentative i)
  let w (i : Fin 3) := a.extension.innerMap (centralRepresentative i).val
  have hu (i) : orderOf (u i).val=2 := (Subgroup.orderOf_coe _).trans
    ((b.symm.orderOf_eq _).trans (centralRepresentative_order i))
  have huc (i) : u i∈center S :=
    (centerCongr b.symm ⟨_,centralRepresentative_center i⟩).property
  have hw (i) : orderOf (w i)=2 :=
    (orderOf_injective a.extension.innerMap a.extension.innerMap_injective _).trans
      ((Subgroup.orderOf_coe _).trans (centralRepresentative_order i))
  have hψu (i) : ψ (u i)=w i := by simp [ψ,u,w]
  apply marked_class_card_eq T S (d.symplectic_sourceS_eq_sylow h hH hp F hm hF he)
    ψ u w hu hw hψu
  · intro x hx
    obtain ⟨i,hi,hj⟩ := hpair x hx
    exact ⟨i,hi,a.extension.innerMap.map_isConj hj⟩
  · exact d.symplectic_extension_three_class_cover h hH hp F hm hF he a
  · exact Chapter5.Section03SymplecticSource.extension_centralRepresentative_irredundant hm hF a.extension
  · intro i j hij
    obtain ⟨g,hg,hgij⟩ := d.symplectic_center_fusion_control h hH hp F hm hF he
      0 (u i) (u j) (huc i) (huc j) hij
    have hh : IsConj (inclusion hS1 (u i)) (inclusion hS1 (u j)) :=
      isConj_iff.mpr ⟨⟨g,hg⟩,Subtype.ext hgij⟩
    have hh' := φ.map_isConj hh
    rw [hmφ,hmφ] at hh'
    simpa only [u,b.apply_symm_apply] using hh'
  · intro k
    rcases d.symplectic_center_local_or_square h hH.1.1.2 hp F hm hF he (u k) (huc k) with hl | hr | hs
    · exact ⟨_,hS1,φ,hφ,hmφ,hcφ (inclusion hS1 (u k)) hl (hu k)⟩
    · exact ⟨_,hS2,χ,hχ,hmχ,hcχ (inclusion hS2 (u k)) hr (hu k)⟩
    · exact ⟨_,le_inf hS1 hS2,δ,hδ,hmδ,hcδ (u k) ((Subgroup.orderOf_coe _).symm.trans (hu k)) hs⟩

/-- The original ambient group and the same full symplectic extension have
identical orders. All three class centralizers and their ambient class
predicates are compared through the coherent marking, in either orientation. -/
theorem Preparation.symplectic_extension_card_eq
    (a : SymplecticNormalizerMarking L (residual H) (sourceS L H) F) :
    Nat.card G=Nat.card a.extension.carrier := by
  let P := ChapterF.Source.parabolic ![L,residual H] (sourceS L H)
  let C := P 0⊓P 1
  let D := normalizer (L : Set G)⊓normalizer (residual H : Set G)
  have hSC : sourceS L H≤C :=
    le_inf (le_sup_right.trans le_sup_left) (le_sup_right.trans le_sup_left)
  have hCD : C≤D := le_inf (inf_le_left.trans a.left_le) (inf_le_right.trans a.right_le)
  have hS1 : sourceS L H≤normalizer (L : Set G) := (hSC.trans inf_le_left).trans a.left_le
  have hS2 : sourceS L H≤normalizer (residual H : Set G) := (hSC.trans inf_le_right).trans a.right_le
  have hf := d.hypothesisF11 h hH.1.1.2
  have hs : Chapter1.IsSylowIn 2 (sourceS L H) C := by
    change Chapter1.IsSylowIn 2 (sourceS L H) (P 0⊓P 1)
    rw [show P 0⊓P 1=ChapterF.Source.commonBorel ![L,residual H] (sourceS L H) from
      ChapterF.Source.lemma_F_1_3_6 hf]
    exact hf.sylow_commonBorel
  rcases d.symplectic_marked_centralizers h hH hp F hm hF he a with
    ⟨e,f,hl,hr,hd,hcl,hcr,hcs⟩ | ⟨e,f,hl,hr,hd,hcl,hcr,hcs⟩
  · obtain ⟨b,hb,hpair⟩ := symplectic_amalgam_class_pairs hm hF hSC inf_le_left inf_le_right hs e
    let φ := (inclusion a.extension.left_le).comp f.left.toMonoidHom
    let χ := (inclusion a.extension.right_le).comp f.right.toMonoidHom
    let δ := (inclusion (inf_le_left.trans a.extension.left_le)).comp f.middle.toMonoidHom
    have hmδ (x) : δ (inclusion (le_inf hS1 hS2) x)=a.extension.innerMap (b x).val := by
      apply Subtype.ext
      exact (hd (inclusion hSC x)).trans (congrArg MulAut.conj (hb x))
    have hmφ (x) : φ (inclusion hS1 x)=a.extension.innerMap (b x).val := by
      rw [←hmδ x]
      apply Subtype.ext
      exact congrArg (fun y : a.extension.left => y.val) (f.left_commutes (inclusion (le_inf hS1 hS2) x))
    have hmχ (x) : χ (inclusion hS2 x)=a.extension.innerMap (b x).val := by
      rw [←hmδ x]
      apply Subtype.ext
      exact congrArg (fun y : a.extension.right => y.val) (f.right_commutes (inclusion (le_inf hS1 hS2) x))
    exact d.symplectic_card_eq_of_sylow_marking h hH hp F hm hF he a b hpair hS1 hS2
      φ χ δ ((inclusion_injective a.extension.left_le).comp f.left.injective)
      ((inclusion_injective a.extension.right_le).comp f.right.injective)
      ((inclusion_injective (inf_le_left.trans a.extension.left_le)).comp f.middle.injective)
      hmφ hmχ hmδ hcl hcr hcs
  · obtain ⟨b,hb,hpair⟩ := symplectic_amalgam_class_pairs hm hF hSC inf_le_right inf_le_left hs e.reverse
    let φ := (inclusion a.extension.right_le).comp f.left.toMonoidHom
    let χ := (inclusion a.extension.left_le).comp f.right.toMonoidHom
    let δ := (inclusion (inf_le_left.trans a.extension.left_le)).comp f.middle.toMonoidHom
    have hmδ (x) : δ (inclusion (le_inf hS1 hS2) x)=a.extension.innerMap (b x).val := by
      apply Subtype.ext
      exact (hd (inclusion hSC x)).trans (congrArg MulAut.conj (hb x))
    have hmφ (x) : φ (inclusion hS1 x)=a.extension.innerMap (b x).val := by
      rw [←hmδ x]
      apply Subtype.ext
      exact congrArg (fun y : a.extension.right => y.val) (f.left_commutes (inclusion (le_inf hS1 hS2) x))
    have hmχ (x) : χ (inclusion hS2 x)=a.extension.innerMap (b x).val := by
      rw [←hmδ x]
      apply Subtype.ext
      exact congrArg (fun y : a.extension.left => y.val) (f.right_commutes (inclusion (le_inf hS1 hS2) x))
    exact d.symplectic_card_eq_of_sylow_marking h hH hp F hm hF he a b hpair hS1 hS2
      φ χ δ ((inclusion_injective a.extension.right_le).comp f.left.injective)
      ((inclusion_injective a.extension.left_le).comp f.right.injective)
      ((inclusion_injective (inf_le_left.trans a.extension.left_le)).comp f.middle.injective)
      hmφ hmχ hmδ hcl hcr hcs
end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
