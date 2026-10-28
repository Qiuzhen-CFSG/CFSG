module
public import CFSG.Quasithin.ChapterJ.Section05.SourceAction.RankThree
public import Theory.SpecificGroups.Rudvalis.Model.MarkedStabilizer.First
public import Theory.SpecificGroups.Rudvalis.Model.MarkedStabilizer.Second
public import Theory.SpecificGroups.Rudvalis.Model.MarkedStabilizer.Swap
/-!
# The concrete Rudvalis model has the original J.5 rank-three datum

The actual point stabilizer at0 is marked as the full binary Ree group.
Its stabilizers at the certified first and second points have the native
first-parabolic and mixed PSL₂(25)⁺ markings. Transport through the canonical
coset-to-orbit equivalence retains the actual ATLAS action, and supplies all
fields of Definition J.5.1, together with an element exchanging the base
point and its first neighbor. No ambient or local recognition is assumed.

Source: Aschbacher–Smith J.5.1, J.5.4 and J.5.13–14, pp.445–450.
-/

@[expose] public section
noncomputable section
open Subgroup MulAction
namespace CFSG.Quasithin.ChapterJ.Section05.SourceModel
open Rudvalis Rudvalis.MarkedStabilizer

/-- The original coset action is the literal ATLAS action on 4060 letters. -/
def cosetEquiv : Cosets pointStabilizer ≃ Fin 4060 :=
  Equiv.ofBijective (ofQuotientStabilizer Model (0 : Fin 4060)) ⟨
    injective_ofQuotientStabilizer Model 0, by
      let _ := Rudvalis.model_isPretransitive
      intro x
      obtain ⟨g,hg⟩ := exists_smul_eq Model (0 : Fin 4060) x
      exact ⟨(g : Model ⧸ pointStabilizer),hg⟩⟩

theorem cosetEquiv_smul (g : Model) (x : Cosets pointStabilizer) :
    cosetEquiv (g • x)=g • cosetEquiv x := ofQuotientStabilizer_smul Model 0 g x

theorem cosetEquiv_base : cosetEquiv (basePoint pointStabilizer)=0 := by
  change (1 : Model) • (0 : Fin 4060)=0
  exact one_smul _ _

def firstCoset : Cosets pointStabilizer := cosetEquiv.symm firstPoint
def secondCoset : Cosets pointStabilizer := cosetEquiv.symm 6

private theorem orbit_iff (x y : Cosets pointStabilizer) :
    y∈orbit pointStabilizer x ↔ cosetEquiv y∈orbit pointStabilizer (cosetEquiv x) := by
  constructor
  · rintro ⟨g,hg⟩
    exact ⟨g, (cosetEquiv_smul (g : Model) x).symm.trans (congrArg cosetEquiv hg)⟩
  · rintro ⟨g,hg⟩
    exact ⟨g,cosetEquiv.injective ((cosetEquiv_smul (g : Model) x).trans hg)⟩

private theorem stabilizer_eq (x : Cosets pointStabilizer) :
    stabilizer pointStabilizer x=stabilizer pointStabilizer (cosetEquiv x) := by
  ext g
  change (g : Model) • x=x ↔ (g : Model) • cosetEquiv x=cosetEquiv x
  rw [← cosetEquiv_smul (g : Model) x,cosetEquiv.injective.eq_iff]

private def orbitEquiv (x : Cosets pointStabilizer) :
    orbit pointStabilizer x ≃ orbit pointStabilizer (cosetEquiv x) :=
  cosetEquiv.subtypeEquiv (orbit_iff x)

theorem partition : orbit pointStabilizer secondCoset=
    (({basePoint pointStabilizer}:Set (Cosets pointStabilizer))∪
      orbit pointStabilizer firstCoset)ᶜ := by
  ext x
  rw [orbit_iff]
  simp only [secondCoset,Equiv.apply_symm_apply]
  rw [MarkedStabilizer.orbit_partition]
  simp only [Set.mem_compl_iff,Set.mem_union,Set.mem_singleton_iff]
  rw [← cosetEquiv_base,cosetEquiv.injective.eq_iff,orbit_iff]
  simp only [firstCoset,Equiv.apply_symm_apply]

theorem base_not_first : basePoint pointStabilizer∉orbit pointStabilizer firstCoset := by
  rw [orbit_iff,cosetEquiv_base]
  simp only [firstCoset,Equiv.apply_symm_apply]
  rintro ⟨g,hg⟩
  have hz : (g:Model) • (0 : Fin 4060)=0 := g.property
  have hx : firstPoint=0 := smul_left_cancel (g:Model) (hg.trans hz.symm)
  exact (by decide : firstPoint≠0) hx

/-- The full concrete datum of Definition J.5.1, with both local markings. -/
def action : RudvalisAction pointStabilizer firstCoset secondCoset where
  marking := fullEquiv
  first_marked := by
    rw [stabilizer_eq]
    simpa only [firstCoset,Equiv.apply_symm_apply] using MarkedStabilizer.first_marked
  second_plus := by
    rw [stabilizer_eq]
    change Nonempty (stabilizer pointStabilizer (cosetEquiv (cosetEquiv.symm (6 : Fin 4060)))≃*Tits.Max4Outer.Mixed.Plus)
    rw [Equiv.apply_symm_apply]
    exact MarkedStabilizer.second_plus
  degree := (Nat.card_congr cosetEquiv).trans (by simp)
  first_length := by
    rw [Nat.card_congr (orbitEquiv firstCoset)]
    simpa only [firstCoset,Equiv.apply_symm_apply] using first_orbit_card
  second_length := by
    rw [Nat.card_congr (orbitEquiv secondCoset)]
    simpa only [secondCoset,Equiv.apply_symm_apply] using second_orbit_card
  partition := SourceModel.partition
  faithful := by
    constructor
    intro g h he
    apply Subtype.ext
    apply Equiv.ext
    intro x
    obtain ⟨y,rfl⟩ := cosetEquiv.surjective x
    exact (cosetEquiv_smul g y).symm.trans
      ((congrArg cosetEquiv (he y)).trans (cosetEquiv_smul h y))
  primitive := by
    let f : Cosets pointStabilizer →ₑ[fun g : Model => g] Fin 4060 :=
      ⟨cosetEquiv,cosetEquiv_smul⟩
    exact (isPreprimitive_congr (f:=f) Function.surjective_id cosetEquiv.bijective).mpr
      Rudvalis.model_isPreprimitive
  rank_three := ThreeSuborbits.rank_three _ _ _
    (basePoint_fixed pointStabilizer) SourceModel.base_not_first SourceModel.partition

/-- The concrete datum in the same source format used by the J.5 graph. -/
theorem exists_source_action : ∃q g:Model,
    q∉pointStabilizer ∧ g∉pointStabilizer ∧
    q • (q • basePoint pointStabilizer)=basePoint pointStabilizer ∧
    Nonempty (RudvalisAction pointStabilizer
      (q • basePoint pointStabilizer) (g • basePoint pointStabilizer)) := by
  obtain ⟨q,hq0,hq1⟩ := exists_swap_first
  let _ := Rudvalis.model_isPretransitive
  obtain ⟨g,hg⟩ := exists_smul_eq Model (0 : Fin 4060) (6 : Fin 4060)
  have hqF : q∉pointStabilizer := by
    intro hq
    have hh : q • (0 : Fin 4060)=0 := hq
    exact (by decide : firstPoint≠0) (hq0.symm.trans hh)
  have hgF : g∉pointStabilizer := by
    intro hgF
    have hh : g • (0 : Fin 4060)=0 := hgF
    have he : (6 : Fin 4060)=0 := hg.symm.trans hh
    exact (by decide : (6 : Fin 4060)≠0) he
  have hfirst : q • basePoint pointStabilizer=firstCoset := by
    apply cosetEquiv.injective
    rw [cosetEquiv_smul,cosetEquiv_base,hq0]
    exact (cosetEquiv.apply_symm_apply firstPoint).symm
  have hsecond : g • basePoint pointStabilizer=secondCoset := by
    apply cosetEquiv.injective
    rw [cosetEquiv_smul,cosetEquiv_base,hg]
    exact (cosetEquiv.apply_symm_apply (6 : Fin 4060)).symm
  refine ⟨q,g,hqF,hgF,?_,?_⟩
  · apply cosetEquiv.injective
    rw [cosetEquiv_smul,cosetEquiv_smul,cosetEquiv_base,hq0,hq1]
  · rw [hfirst,hsecond]
    exact ⟨action⟩

end CFSG.Quasithin.ChapterJ.Section05.SourceModel
