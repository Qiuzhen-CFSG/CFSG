module
public import CFSG.Quasithin.ChapterB.Section06To07.FFClassification.LinearThree
public import Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms.InvariantParabolicPair
public import Theory.SpecificGroups.SymplecticFour.TwoConjugate.MovingPair

/-!
# The original nonbinary Sp4 minimal-parabolic diagram actor

Sylow conjugacy aligns the supplied normal Sp4 subgroup with the original
Sylow. If all its actors preserve the diagram, the point and plane parabolics
produce two proper Sylow overgroups. They generate the normal supplement,
contradicting the original unique-maximal-overgroup hypothesis. Thus the
actual original Sylow contains a diagram-moving actor on that same marking.

This proves the diagram part of E.2.2(2b), pp.215–216. The original maximal
subgroup's Borel intersection and V's inner placement are separate steps.
-/

@[expose] public section
noncomputable section
open Subgroup
namespace CFSG.Quasithin.ChapterE.Structure.SymplecticFour
open Theory.SpecificGroups.SymplecticFour
open DiagramAutomorphisms EvenBorelTorus
variable {G F:Type*} [Group G] [Finite G] [Field F] [Finite F] [CharP F 2]

omit [Finite G] [CharP F 2] in
/-- The original Sylow acts on its exact marked model Sylow. -/
theorem sylow_actor (T:Sylow 2 G) (L:Subgroup G) [L.Normal] (e:Sp F≃*L)
    (hmark:(T:Subgroup G).comap (L.subtype.comp e.toMonoidHom)=unipotent)
    (t:T) : unipotent.map (extensionAction L e t).toMonoidHom=unipotent := by
  apply eq_of_le_of_card_ge
  · rintro _ ⟨x,hx,rfl⟩
    rw [←hmark] at hx ⊢
    change (e (extensionAction L e t x)).val∈T
    rw [extensionAction_apply]
    exact T.mul_mem (T.mul_mem t.property hx) (T.inv_mem t.property)
  · rw [card_map_of_injective (extensionAction L e t).injective]

/-- Minimal parabolicity forces a genuine diagram-moving member of the
original Sylow, on the same model marking. -/
theorem exists_moving_sylow_actor {n:ℕ} (hF:Nat.card F=2^n) (hn:1<n)
    (T:Sylow 2 G) (hP:ChapterB.IsMinimalParabolicOver T ⊤)
    (L:Subgroup G) [L.Normal] (e:Sp F≃*L)
    (hmark:(T:Subgroup G).comap (L.subtype.comp e.toMonoidHom)=unipotent)
    (hgen:L⊔(T:Subgroup G)=⊤) : ∃t:T,¬PreservesDiagram (extensionAction L e t) := by
  by_contra! h
  let f:Sp F→*G:=L.subtype.comp e.toMonoidHom
  have hf:Function.Injective f:=L.subtype_injective.comp e.injective
  have hftop:(⊤:Subgroup (Sp F)).map f=L := by
    rw [show f=L.subtype.comp e.toMonoidHom from rfl,←map_map,
      map_top_of_surjective _ e.surjective,←MonoidHom.range_eq_map,range_subtype]
  let P:Subgroup G:=pointParabolic.map f
  let Q:Subgroup G:=planeParabolic.map f
  have hPQ:P⊔Q=L := by
    change pointParabolic.map f⊔planeParabolic.map f=L
    rw [←Subgroup.map_sup,parabolics_sup_eq_top,hftop]
  have hp:P≠L := by
    intro hh
    exact pointParabolic_ne_top (map_injective hf (hh.trans hftop.symm))
  have hq:Q≠L := by
    intro hh
    exact planeParabolic_ne_top (map_injective hf (hh.trans hftop.symm))
  have ha (t:T):pointParabolic.map (extensionAction L e t).toMonoidHom=pointParabolic ∧
      planeParabolic.map (extensionAction L e t).toMonoidHom=planeParabolic :=
    parabolic_pair_map_of_unipotent_map hF hn _ (h t) (sylow_actor T L e hmark t)
  have hnorm (D:Subgroup (Sp F))
      (hd:∀t:T,D.map (extensionAction L e t).toMonoidHom=D) :
      (T:Subgroup G)≤normalizer (D.map f:Set G) := by
    apply le_normalizer_iff.mpr
    intro t ht x hx
    obtain ⟨y,hy,rfl⟩:=hx
    let a:=extensionAction L e t
    have hay:a y∈D := by
      rw [←hd ⟨t,ht⟩]
      exact mem_map_of_mem _ hy
    exact ⟨a y,hay,extensionAction_apply L e t y⟩
  have hint (D:Subgroup (Sp F)) (hd:unipotent≤D) :
      L⊓(T:Subgroup G)≤D.map f := by
    rintro x ⟨hxL,hxT⟩
    have hx:e.symm ⟨x,hxL⟩∈unipotent := by
      rw [←hmark]
      change (e (e.symm ⟨x,hxL⟩)).val∈T
      rw [e.apply_symm_apply]
      exact hxT
    refine ⟨e.symm ⟨x,hxL⟩,hd hx,?_⟩
    change (e (e.symm ⟨x,hxL⟩)).val=x
    rw [e.apply_symm_apply]
  exact ChapterB.not_minimalParabolic_of_two_overgroups T L P Q hgen hPQ hp hq
    (hnorm _ fun t=>(ha t).1) (hnorm _ fun t=>(ha t).2)
    (hint _ (unipotent_le_borel.trans inf_le_left))
    (hint _ (unipotent_le_borel.trans inf_le_right)) hP

omit [CharP F 2] in
/-- Sylow conjugacy adjusts the supplied marking inside the same Sp4 carrier. -/
theorem exists_alignment {n:ℕ} (hF:Nat.card F=2^n) (hn:1≤n)
    (T:Sylow 2 G) (L:Subgroup G) [L.Normal] (e:L≃*Sp F) :
    ∃g:Sp F,(T:Subgroup G).comap
      (L.subtype.comp (e.trans (MulAut.conj g)).symm.toMonoidHom)=unipotent := by
  obtain ⟨P,hP⟩:=T.exists_subgroupOf_eq_of_normal L
  let Q:=P.mapSurjective (f:=e.toMonoidHom) e.surjective
  obtain ⟨g,hg⟩:=MulAction.exists_smul_eq (Sp F) Q (unipotentSylow hF hn)
  refine ⟨g,?_⟩
  have hm:=congrArg Sylow.toSubgroup hg
  change ((P:Subgroup L).map e.toMonoidHom).map (MulAut.conj g).toMonoidHom=unipotent at hm
  rw [hP,Subgroup.map_map] at hm
  change ((T:Subgroup G).subgroupOf L).map (e.trans (MulAut.conj g)).toMonoidHom=_ at hm
  rw [←hm]
  change (((T:Subgroup G).comap L.subtype).comap
    (e.trans (MulAut.conj g)).symm.toMonoidHom)=_
  exact comap_equiv_eq_map_symm (e.trans (MulAut.conj g)).symm _

/-- The genuine nonbinary E.2.2 diagram conclusion from original
minimal-parabolic and normal-supplement hypotheses. -/
theorem source_diagram_actor {n:ℕ} (hF:Nat.card F=2^n) (hn:1<n)
    (T:Sylow 2 G) (hP:ChapterB.IsMinimalParabolicOver T ⊤)
    (L:Subgroup G) [L.Normal] (e:L≃*Sp F) (hgen:L⊔(T:Subgroup G)=⊤) :
    ∃g:Sp F, let e':=(e.trans (MulAut.conj g)).symm
      (T:Subgroup G).comap (L.subtype.comp e'.toMonoidHom)=unipotent ∧
      ∃t:T,¬PreservesDiagram (extensionAction L e' t) := by
  obtain ⟨g,hg⟩:=exists_alignment hF hn.le T L e
  exact ⟨g,hg,exists_moving_sylow_actor hF hn T hP L _ hg hgen⟩

end CFSG.Quasithin.ChapterE.Structure.SymplecticFour
