module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalM23.CorePlacement
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalM23.RecognitionFromVertex
public import Theory.GroupTheory.Recognition.QuasithinM23.CoreDetermination
/-!
# Determining the whole original intersection from its core

Restrict the vertex and heptad markings to the original H. Once they agree
pointwise on O₂(J), self-centralization of the native heptad kernel implies
that both markings have the same image of every core-overgroup in H. This
includes the entire Ix, so its image is a consequence of core agreement.

The existing core correction, edge rigidity and uniqueness-system recognition
then produce the actual ambient equivalence with M23. The source application
retains the constructed coset system, its fixed heptad marking, and the vertex
map carrying L, the full linear subgroup, the full core and H to their native
images. Pointwise agreement on that core remains explicit: this is a reduction,
not unconditional source 5.2.10.

Source: Aschbacher--Smith 5.2.20(5) and 5.2.10, printed pp.656--658.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped Pointwise
open Sporadic.Mathieu.M23Geometry GraphUniquenessSystem
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
variable {G : Type*} [Group G]

/-- Agreement on the full exceptional core determines every core-overgroup
inside the common normalizer, in particular the original Ix. -/
theorem heptad_marked_intersection_of_normalizer_core_comparison
    (J H R X : Subgroup G) (hHJ : H ≤ J) (hHX : H ≤ X)
    (hRH : R ≤ H) (hUR : J.pCoreIn 2 ≤ R)
    (ζ : J ≃* heptadStabilizer)
    (hcore : (pCore 2 J).map ζ.toMonoidHom = heptadKernel)
    (hmark : (R.subgroupOf J).map ζ.toMonoidHom =
      fourPairStabilizer.subgroupOf heptadStabilizer)
    (β : X ≃* pairStabilizer)
    (hβH : (H.subgroupOf X).map β.toMonoidHom =
      heptadStabilizer.subgroupOf pairStabilizer)
    (hβcore : ∀ u : J.pCoreIn 2,
      (β ⟨u,hHX (hRH (hUR u.property))⟩ : Sporadic.Mathieu.M23) =
        (ζ ⟨u,pCoreIn_le 2 J u.property⟩ : Sporadic.Mathieu.M23)) :
    (R.subgroupOf X).map β.toMonoidHom =
      fourPairStabilizer.subgroupOf pairStabilizer := by
  let N := (J.pCoreIn 2).subgroupOf H
  let : N.Normal := normal_subgroupOf_of_le_normalizer
    (hHJ.trans (J.le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image J (pCore 2 J))))
  let f₀ : H →* Sporadic.Mathieu.M23 := pairStabilizer.subtype.comp
    (β.toMonoidHom.comp (inclusion hHX))
  have hf₀ (a : H) : f₀ a ∈ heptadStabilizer := by
    have hh : β ⟨a,hHX a.property⟩ ∈ (H.subgroupOf X).map β.toMonoidHom :=
      mem_map_of_mem _ a.property
    rw [hβH] at hh
    exact hh
  let f : H →* heptadStabilizer := f₀.codRestrict heptadStabilizer hf₀
  let g : H →* heptadStabilizer := ζ.toMonoidHom.comp (inclusion hHJ)
  have hagree (u : N) : f u = g u := by
    apply Subtype.ext
    exact hβcore ⟨u.val.val,u.property⟩
  have hNg : N.map g = heptadKernel := by
    rw [←hcore]
    ext z
    constructor
    · rintro ⟨a,ha,rfl⟩
      refine ⟨⟨a,hHJ a.property⟩,?_,rfl⟩
      exact (mem_map_iff_mem (f := J.subtype) J.subtype_injective).mp ha
    · rintro ⟨a,ha,rfl⟩
      have hu : (a : G) ∈ J.pCoreIn 2 := mem_map_of_mem J.subtype ha
      refine ⟨⟨a,hRH (hUR hu)⟩,hu,?_⟩
      rfl
  have hNf : N.map f = heptadKernel := by
    rw [←hNg]
    ext z
    constructor
    · rintro ⟨u,hu,rfl⟩
      exact ⟨u,hu,(hagree ⟨u,hu⟩).symm⟩
    · rintro ⟨u,hu,rfl⟩
      exact ⟨u,hu,hagree ⟨u,hu⟩⟩
  have hm := QuasithinM23.map_eq_of_agree_on_selfCentralizing_normal N (R.subgroupOf H)
    (subgroupOf_mono H hUR) f g hagree (by rw [hNf]; exact heptadKernel_selfCentralizing)
  have hRf : (R.subgroupOf H).map f = fourPairStabilizer.subgroupOf heptadStabilizer := by
    rw [hm,←hmark]
    change (R.subgroupOf H).map (ζ.toMonoidHom.comp (inclusion hHJ)) = _
    rw [←map_map]
    congr 1
    apply map_injective J.subtype_injective
    rw [map_map]
    have hi : J.subtype.comp (inclusion hHJ) = H.subtype := rfl
    rw [hi,map_subgroupOf_eq_of_le hRH,
      map_subgroupOf_eq_of_le (hRH.trans hHJ)]
  apply map_injective pairStabilizer.subtype_injective
  rw [map_map,map_subgroupOf_eq_of_le (show fourPairStabilizer ≤ pairStabilizer from inf_le_right)]
  calc
    (R.subgroupOf X).map (pairStabilizer.subtype.comp β.toMonoidHom) =
        ((R.subgroupOf H).map f).map heptadStabilizer.subtype := by
      rw [map_map]
      have hi : heptadStabilizer.subtype.comp f =
          (pairStabilizer.subtype.comp β.toMonoidHom).comp (inclusion hHX) := rfl
      rw [hi,←Subgroup.map_map (K := R.subgroupOf H)
        (g := pairStabilizer.subtype.comp β.toMonoidHom) (f := inclusion hHX)]
      congr 1
      apply map_injective X.subtype_injective
      rw [map_map]
      have hj : X.subtype.comp (inclusion hHX) = H.subtype := rfl
      rw [hj,map_subgroupOf_eq_of_le hRH,
        map_subgroupOf_eq_of_le (hRH.trans hHX)]
    _ = fourPairStabilizer := by
      rw [hRf,map_subgroupOf_eq_of_le fourPairStabilizer_le_heptad]


/-- The normalizer image and pointwise agreement on the full core suffice for
ambient recognition; the image of Ix follows rather than being assumed. -/
theorem heptad_marked_recognition_of_normalizer_core_comparison
    {V : Type*} [MulAction G V] (U : System G V)
    (J H : Subgroup G) (hUJ : U.H ≤ J)
    (hXJ : U.vertexGroup ⊓ J = H)
    (ζ : J ≃* heptadStabilizer)
    (hcore : (pCore 2 J).map ζ.toMonoidHom = heptadKernel)
    (hUL : J.pCoreIn 2 ≤ U.H ⊓ U.edgeGroup)
    (hIm : (U.H.subgroupOf J).map ζ.toMonoidHom =
      fourStabilizer.subgroupOf heptadStabilizer)
    (hvM : ((U.H ⊓ U.vertexGroup).subgroupOf J).map ζ.toMonoidHom =
      fourPairStabilizer.subgroupOf heptadStabilizer)
    (hesM : ((U.H ⊓ U.edgeSetGroup).subgroupOf J).map ζ.toMonoidHom =
      fourEdgeStabilizer.subgroupOf heptadStabilizer)
    (hrigid : AutomorphismRigid (U.H.subgroupOf U.edgeGroup))
    (β : U.vertexGroup ≃* pairStabilizer)
    (hβH : (H.subgroupOf U.vertexGroup).map β.toMonoidHom =
      heptadStabilizer.subgroupOf pairStabilizer)
    (hβcore : ∀ (u : U.vertexGroup) (hu : (u : G) ∈ J.pCoreIn 2),
      (β u : Sporadic.Mathieu.M23) =
        (ζ ⟨u,pCoreIn_le 2 J hu⟩ : Sporadic.Mathieu.M23))
    (hβedge : ∀ a : U.vertexGroup, (a : G) ∈ U.edgeGroup ↔
      (β a : Sporadic.Mathieu.M23) ∈ standardSystem.edgeGroup) :
    ∃ e : G ≃* Sporadic.Mathieu.M23,
      U.vertexGroup.map e.toMonoidHom = pairStabilizer ∧
      U.edgeGroup.map e.toMonoidHom = standardSystem.edgeGroup ∧
      ∀ a : U.H, e a = (ζ ⟨a,hUJ a.property⟩ : Sporadic.Mathieu.M23) := by
  have hHJ : H ≤ J := by rw [←hXJ]; exact inf_le_right
  have hHX : H ≤ U.vertexGroup := by rw [←hXJ]; exact inf_le_left
  have hRH : U.H ⊓ U.vertexGroup ≤ H := by
    rw [←hXJ]
    exact le_inf inf_le_right (inf_le_left.trans hUJ)
  have hUR : J.pCoreIn 2 ≤ U.H ⊓ U.vertexGroup :=
    fun u hu => ⟨(hUL hu).1,(hUL hu).2.1⟩
  have hβR := heptad_marked_intersection_of_normalizer_core_comparison
    J H (U.H ⊓ U.vertexGroup) U.vertexGroup hHJ hHX hRH hUR ζ hcore hvM β hβH
    (fun u => hβcore ⟨u,hHX (hRH (hUR u.property))⟩ u.property)
  exact heptad_marked_recognition_of_core_comparison U J hUJ ζ hcore
    (hUL.trans inf_le_right) hIm hvM hesM hrigid β hβR
    (fun r hr => hβcore ⟨r,r.property.2⟩ hr) hβedge

variable [Finite G]

/-- The constructed original vertex coordinates preserve the edge, the core
and its relative normalizer. Pointwise core agreement remains explicit in the
final implication; it forces the entire Ix image and then ambient recognition. -/
theorem Preparation.linear_nonmaximal_coset_core_recognition_reduction
    {T : Sylow 2 G} {L W H A B : Subgroup G} {n : ℕ}
    (d : Preparation T L H A B (residual H))
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hp : Group.IsPerfect (residual H))
    (F : Type) [Field F] [Finite F] [CharP F 2]
    {m : ℕ} (hm : 0 < m) (hF : Nat.card F = 2^m)
    (he : Nonempty (RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H))
      (ChapterF.GreenBook.LieModels.LinearThree.amalgam F)) ∨
      Nonempty (RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H))
      (ChapterF.GreenBook.LieModels.LinearThree.amalgam F).reverse))
    (hnonmax : residual H ∉ Chapter1.LStar G (T : Subgroup G)) :
    ∃ J : Subgroup G, J ∈ Chapter1.LStar G (T : Subgroup G) ∧ residual H < J ∧
      ∃ (U : System G (G ⧸ (L ⊔ H : Subgroup G))) (ζ : J ≃* heptadStabilizer) (hUJ : U.H ≤ J)
        (β : U.vertexGroup ≃* pairStabilizer),
      U.x = ((1 : G) : G ⧸ (L ⊔ H : Subgroup G)) ∧
      U.vertexGroup = L ⊔ H ∧ U.edgeGroup = L ∧
      (pCore 2 J).map ζ.toMonoidHom = heptadKernel ∧
      ((residual H).subgroupOf J).map ζ.toMonoidHom =
        (fixingSubgroup (Equiv.Perm (Fin 7)) ({5,6} : Set (Fin 7))).comap heptadAction ∧
      (H.subgroupOf J).map ζ.toMonoidHom = pairStabilizer.subgroupOf heptadStabilizer ∧
      ((normalizer (L : Set G)).subgroupOf J).map ζ.toMonoidHom =
        (MulAction.stabilizer (Equiv.Perm (Fin 7)) ({4,5,6} : Set (Fin 7))).comap heptadAction ∧
      (U.H.subgroupOf J).map ζ.toMonoidHom = fourStabilizer.subgroupOf heptadStabilizer ∧
      ((U.H ⊓ U.vertexGroup).subgroupOf J).map ζ.toMonoidHom =
        fourPairStabilizer.subgroupOf heptadStabilizer ∧
      ((U.H ⊓ U.edgeGroup).subgroupOf J).map ζ.toMonoidHom =
        fourTwoPairStabilizer.subgroupOf heptadStabilizer ∧
      ((U.H ⊓ U.edgeSetGroup).subgroupOf J).map ζ.toMonoidHom =
        fourEdgeStabilizer.subgroupOf heptadStabilizer ∧
      (∀ a b : J, a • U.x = b • U.x ↔ ζ a • x.val = ζ b • x.val) ∧
      (∃ t : J, (t:G) ∈ U.H ∧ t • U.x = U.y ∧ ζ t • x.val = y.val) ∧
      AutomorphismRigid (U.H.subgroupOf U.edgeGroup) ∧
      J.pCoreIn 2 ≤ U.H ⊓ U.edgeGroup ∧
      (∀ a : U.vertexGroup, (a : G) ∈ U.edgeGroup ↔
        (β a : Sporadic.Mathieu.M23) ∈ standardSystem.edgeGroup) ∧
      ((L ⊔ residual H).subgroupOf U.vertexGroup).map β.toMonoidHom =
        pointwisePairStabilizer ∧
      ((J.pCoreIn 2).subgroupOf U.vertexGroup).map β.toMonoidHom =
        heptadKernelAmbient.subgroupOf pairStabilizer ∧
      (H.subgroupOf U.vertexGroup).map β.toMonoidHom =
        heptadStabilizer.subgroupOf pairStabilizer ∧
      ((∀ (u : U.vertexGroup) (hu : (u : G) ∈ J.pCoreIn 2),
        (β u : Sporadic.Mathieu.M23) =
          (ζ ⟨u,pCoreIn_le 2 J hu⟩ : Sporadic.Mathieu.M23)) →
        ∃ e : G ≃* Sporadic.Mathieu.M23,
          U.vertexGroup.map e.toMonoidHom = pairStabilizer ∧
          U.edgeGroup.map e.toMonoidHom = standardSystem.edgeGroup ∧
          ∀ a : U.H, e a = (ζ ⟨a,hUJ a.property⟩ : Sporadic.Mathieu.M23)) := by
  obtain ⟨J,hJ,hKJ,U,ζ,hUJ,β,hx,hv,he0,hcore,hK,hHm,hMm,hIm,hvM,hedgeM,hesM,
    horbit,ht,hrigid,hcoreEdge,hβedge,hβlinear,hβU,hβH⟩ :=
    d.linear_nonmaximal_coset_core_placement h hH hp F hm hF he hnonmax
  refine ⟨J,hJ,hKJ,U,ζ,hUJ,β,hx,hv,he0,hcore,hK,hHm,hMm,hIm,hvM,hedgeM,hesM,
    horbit,ht,hrigid,hcoreEdge,hβedge,hβlinear,hβU,hβH,?_⟩
  intro hagree
  have hXJ : U.vertexGroup ⊓ J = H := by
    rw [hv]
    exact d.linear_exceptional_pair_intersection h hH hp F hm hF he hJ hKJ
  exact heptad_marked_recognition_of_normalizer_core_comparison U J H hUJ hXJ ζ hcore
    hcoreEdge hIm hvM hesM hrigid β hβH hagree hβedge

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
