module
public import Theory.SpecificGroups.PSL3Two.Parabolics.MarkedAutomorphisms
public import Theory.GroupTheory.AutomorphismSquareRank
public import Theory.GroupTheory.WreathTwoElementaryRank
public import Theory.SpecificGroups.SymmetricFourWreath.ResidualQuotient

/-!
# The actor preserving the marked binary parabolic pair

An automorphism of SL₃(2)² permutes its two simple factors. Preserving the
paired line parabolic forces its coordinate automorphisms to be inner,
implemented by elements of the same parabolic. These actual formulas identify
the actor with S₄ wr C₂, whose two-core quotient is S₃ wr C₂. The source overlap
application uses the original conjugation action on L₀/O₂(L₀).
Source: Aschbacher--Smith 10.2.3(3), printed p.745.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Geometry.FixedSpaceTI.HStarParameter.QuotientGeometry.ParabolicModel
open Matrix.PSL3Two WreathTwoElementaryRank
abbrev P := lineParabolicSL
abbrev Pair := SL × SL
abbrev Actor := W P

def actorAut (w : Actor) : MulAut Pair :=
  if w.right = 1 then (MulAut.conj (w.left 1).val).prodCongr (MulAut.conj (w.left turn).val)
  else (MulAut.conj (w.left 1).val).prodCongr (MulAut.conj (w.left turn).val) * MulEquiv.prodComm

theorem actorAut_apply (w : Actor) (x : Pair) :
    actorAut w x = if w.right = 1 then
      ((w.left 1 : SL)*x.1*(w.left 1 : SL)⁻¹,
        (w.left turn : SL)*x.2*(w.left turn : SL)⁻¹)
    else ((w.left 1 : SL)*x.2*(w.left 1 : SL)⁻¹,
        (w.left turn : SL)*x.1*(w.left turn : SL)⁻¹) := by
  by_cases h : w.right = 1 <;> simp only [actorAut,h,ite_true,ite_false] <;> rfl

def actorHom : Actor →* MulAut Pair where
  toFun := actorAut
  map_one' := by ext x <;> simp [actorAut_apply]
  map_mul' a b := by
    apply MulEquiv.ext
    intro x
    change actorAut (a*b) x = actorAut a (actorAut b x)
    rcases index_cases a.right with ha | ha <;>
      rcases index_cases b.right with hb | hb <;>
      simp [actorAut_apply,ha,hb,turn_ne_one,mul_assoc]

theorem actorHom_injective : Function.Injective actorHom := by
  apply (injective_iff_map_eq_one actorHom).mpr
  intro w hw
  have hh (x : Pair) : actorAut w x = x := MulEquiv.congr_fun hw x
  rcases index_cases w.right with hr | hr
  · have ha : MulAut.conj (w.left 1 : SL) = 1 := by
      apply MulEquiv.ext
      intro x
      simpa [actorAut_apply,hr] using congrArg Prod.fst (hh (x,1))
    have hb : MulAut.conj (w.left turn : SL) = 1 := by
      apply MulEquiv.ext
      intro x
      simpa [actorAut_apply,hr] using congrArg Prod.snd (hh (1,x))
    have h1 : w.left 1 = 1 := Subtype.ext
      (MarkedAutomorphisms.conj_injective (ha.trans (map_one MulAut.conj).symm))
    have h2 : w.left turn = 1 := Subtype.ext
      (MarkedAutomorphisms.conj_injective (hb.trans (map_one MulAut.conj).symm))
    apply RegularWreathProduct.ext
    · funext i
      rcases index_cases i with rfl | rfl
      · exact h1
      · exact h2
    · exact hr
  · let : Nontrivial SL := Finite.one_lt_card_iff_nontrivial.mp (by rw [card_SL]; decide)
    obtain ⟨x,hx⟩ := exists_ne (1 : SL)
    have he := congrArg Prod.fst (hh (x,1))
    have hx1 : x = 1 := by simpa [actorAut_apply,hr,turn_ne_one] using he.symm
    exact (hx hx1).elim

theorem preserving_parabolic_is_conj (a : MulAut SL)
    (ha : P.map a.toMonoidHom = P) : ∃ g ∈ P, a = MulAut.conj g := by
  apply MarkedAutomorphisms.preserving_residual_is_conj P (Or.inr rfl)
  change ((pResidual 2 P).map P.subtype).map a.toMonoidHom = _
  rw [map_embedded_pResidual,ha]
  rfl

theorem preserving_pair_realization [IsQuasisimple SL] (a : MulAut Pair)
    (ha : (P.prod P).map a.toMonoidHom = P.prod P) : ∃ w : Actor, actorHom w = a := by
  have hin (x : Pair) (hx : x ∈ P.prod P) : a x ∈ P.prod P := by
    rw [←ha]
    exact mem_map_of_mem _ hx
  rcases AutomorphismSquare.normal_form center_eq_bot a with ⟨b,c,rfl⟩ | ⟨b,c,rfl⟩
  · have hb : P.map b.toMonoidHom = P := by
      apply eq_of_le_of_card_ge ?_ (le_of_eq (card_map_of_injective b.injective).symm)
      rintro _ ⟨x,hx,rfl⟩
      exact (hin (x,1) ⟨hx,one_mem _⟩).1
    have hc : P.map c.toMonoidHom = P := by
      apply eq_of_le_of_card_ge ?_ (le_of_eq (card_map_of_injective c.injective).symm)
      rintro _ ⟨x,hx,rfl⟩
      exact (hin (1,x) ⟨one_mem _,hx⟩).2
    obtain ⟨g,hg,rfl⟩ := preserving_parabolic_is_conj b hb
    obtain ⟨h,hh,rfl⟩ := preserving_parabolic_is_conj c hc
    refine ⟨baseHom (⟨g,hg⟩,⟨h,hh⟩),?_⟩
    ext x <;> simp [actorHom,actorAut,baseHom,turn_ne_one]
  · have hb : P.map b.toMonoidHom = P := by
      apply eq_of_le_of_card_ge ?_ (le_of_eq (card_map_of_injective b.injective).symm)
      rintro _ ⟨x,hx,rfl⟩
      exact (hin (1,x) ⟨one_mem _,hx⟩).1
    have hc : P.map c.toMonoidHom = P := by
      apply eq_of_le_of_card_ge ?_ (le_of_eq (card_map_of_injective c.injective).symm)
      rintro _ ⟨x,hx,rfl⟩
      exact (hin (x,1) ⟨hx,one_mem _⟩).2
    obtain ⟨g,hg,rfl⟩ := preserving_parabolic_is_conj b hb
    obtain ⟨h,hh,rfl⟩ := preserving_parabolic_is_conj c hc
    refine ⟨⟨fun i => if i=1 then ⟨g,hg⟩ else ⟨h,hh⟩,turn⟩,?_⟩
    ext x <;> simp [actorHom,actorAut,turn_ne_one]

theorem actorHom_base (x : P × P) :
    actorHom (baseHom x) = MulAut.conj ((x.1 : SL),(x.2 : SL)) := by
  apply MulEquiv.ext
  intro y
  change actorAut (baseHom x) y = _
  rw [actorAut_apply]
  simp only [baseHom]
  rfl

def quotientEquiv : (Actor ⧸ pCore 2 Actor) ≃* WreathTwoResidual.Actor :=
  let e := RegularWreathProduct.congr MarkedAutomorphisms.lineEquivSymmetric (MulEquiv.refl C2)
  (QuotientGroup.congr _ _ e (pCore_map_iso 2 e)).trans SymmetricFourWreath.quotientEquivActor

theorem actorHom_inner_of_base (w : Actor) (hw : w.right = 1) :
    actorHom w = MulAut.conj ((w.left 1 : SL),(w.left turn : SL)) := by
  apply MulEquiv.ext
  intro x
  change actorAut w x = _
  rw [actorAut_apply,if_pos hw]
  rfl

theorem onto_of_base_outside {X : Type*} [Group X] (f : X →* Actor)
    (hb : ∀ x : P × P, baseHom x ∈ f.range)
    (ho : ∃ x : X, (f x).right ≠ 1) : Function.Surjective f := by
  have hbase (w : Actor) (hw : w.right=1) : w ∈ f.range := by
    have he : baseHom (w.left 1,w.left turn) = w := by
      apply RegularWreathProduct.ext
      · funext i
        rcases index_cases i with rfl | rfl
        · simp [baseHom]
        · simp [baseHom,turn_ne_one]
      · exact hw.symm
    exact he ▸ hb _
  intro w
  by_cases hw : w.right = 1
  · exact hbase w hw
  obtain ⟨x,hx⟩ := ho
  have hwr := (index_cases w.right).resolve_left hw
  have hxr := (index_cases (f x).right).resolve_left hx
  obtain ⟨y,hy⟩ := hbase (w*(f x)⁻¹) (by simp [hwr,hxr])
  exact ⟨y*x,by rw [map_mul,hy,inv_mul_cancel_right]⟩

end CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Geometry.FixedSpaceTI.HStarParameter.QuotientGeometry.ParabolicModel
