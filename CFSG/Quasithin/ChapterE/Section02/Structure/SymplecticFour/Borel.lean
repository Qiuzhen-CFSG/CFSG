module
public import Theory.SpecificGroups.SymplecticFour.TwoConjugate.Borel
public import CFSG.Quasithin.ChapterE.Section02.Structure.SymplecticFour.SourceActor

/-!
# The original Sp4 maximal-subgroup intersection

The normalizer of the marked inner Sylow is proper and contains the original
Sylow, so unique maximality places its Borel inside M. The original moving
actor stabilizes M∩L. The actual parabolic overgroup geometry then identifies
that intersection with the marked Borel. Neither conclusion is assumed.

Source: Aschbacher–Smith E.2.2(2b), printed pp.215–216.
-/

@[expose] public section
noncomputable section
open Subgroup
namespace CFSG.Quasithin.ChapterE.Structure.SymplecticFour
open Theory.SpecificGroups.SymplecticFour DiagramAutomorphisms TwoConjugate
open ChapterB
variable {G F:Type*} [Group G] [Finite G] [Field F] [Finite F] [CharP F 2]

theorem source_borel_intersection {n:ℕ} (hF:Nat.card F=2^n) (hn:1<n)
   (T:Sylow 2 G) (hP:IsMinimalParabolicOver T ⊤)
   (L:Subgroup G) [L.Normal] (e:Sp F≃*L)
   (hmark:(T:Subgroup G).comap (L.subtype.comp e.toMonoidHom)=unipotent)
   (hgen:L⊔(T:Subgroup G)=⊤) :
   (minimalParabolicMax T hP).comap (L.subtype.comp e.toMonoidHom)=borel := by
 let M:=minimalParabolicMax T hP
 let f:Sp F→*G:=L.subtype.comp e.toMonoidHom
 have hf:Function.Injective f:=L.subtype_injective.comp e.injective
 have hfr:f.range=L := by
   rw [MonoidHom.range_comp,MonoidHom.range_eq_top.mpr e.surjective,
     ←MonoidHom.range_eq_map,range_subtype]
 have hTM:(T:Subgroup G)≤M:=(minimalParabolicMax_spec T hP).2
 have hM:IsCoatom M:=(minimalParabolicMax_spec T hP).1
 have hLnot:¬L≤M := by
   intro hh
   exact hM.ne_top (top_unique (hgen ▸ sup_le hh hTM))
 have hD:M.comap f≠⊤ := by
   intro hh
   apply hLnot
   rw [←hfr]
   rintro x ⟨y,rfl⟩
   exact show y∈M.comap f from hh ▸ mem_top y
 have hUmap:unipotent.map f=L⊓(T:Subgroup G) := by
   rw [←hmark,map_comap_eq,hfr]
 have hN:normalizer (unipotent.map f:Set G)≤M := by
   apply hP.1.le_maximal ⟨hTM,hM.covBy_top⟩
   · rw [hUmap]
     exact (le_inf (show (T:Subgroup G)≤normalizer (L:Set G) from le_normalizer_of_normal)
       T.le_normalizer).trans inf_normalizer_le_normalizer_inf
   · apply lt_top_iff_ne_top.mpr
     intro hh
     have he:=congrArg (comap f) hh
     rw [comap_normalizer_eq_of_le_range (unipotent.map_le_range f),
       comap_map_eq_self_of_injective hf,comap_top,←borel_eq_normalizer_unipotent] at he
     have hbp : borel (F:=F) ≤ pointParabolic := inf_le_left
     rw [he] at hbp
     exact pointParabolic_ne_top (top_unique hbp)
 have hBD:borel≤M.comap f := by
   apply map_le_iff_le_comap.mp
   have hh:borel.map f≤normalizer (unipotent.map f:Set G) := by
     rw [borel_eq_normalizer_unipotent]
     exact unipotent.le_normalizer_map f
   exact hh.trans hN
 obtain ⟨t,ht⟩:=exists_moving_sylow_actor hF hn T hP L e hmark hgen
 have hm:(M.comap f).map (extensionAction L e t).toMonoidHom=M.comap f := by
   apply eq_of_le_of_card_ge
   · rintro x ⟨y,hy,rfl⟩
     change (e (extensionAction L e t y)).val∈M
     rw [extensionAction_apply]
     exact M.mul_mem (M.mul_mem (hTM t.property) hy) (M.inv_mem (hTM t.property))
   · rw [card_map_of_injective (extensionAction L e t).injective]
 exact eq_borel_of_moving_actor hF hn _ (sylow_actor T L e hmark t) ht _ hBD hD hm

/-- Original nonbinary E.2.2 source marks, including both the actual Borel
intersection and a diagram-moving element of the original Sylow. -/
theorem source_diagram_and_borel {n:ℕ} (hF:Nat.card F=2^n) (hn:1<n)
   (T:Sylow 2 G) (hP:IsMinimalParabolicOver T ⊤)
   (L:Subgroup G) [L.Normal] (e:L≃*Sp F) (hgen:L⊔(T:Subgroup G)=⊤) :
   ∃g:Sp F, let e':=(e.trans (MulAut.conj g)).symm
     (T:Subgroup G).comap (L.subtype.comp e'.toMonoidHom)=unipotent ∧
     (∃t:T,¬PreservesDiagram (extensionAction L e' t)) ∧
     (minimalParabolicMax T hP).comap (L.subtype.comp e'.toMonoidHom)=borel := by
 obtain ⟨g,hg,ht⟩:=source_diagram_actor hF hn T hP L e hgen
 exact ⟨g,hg,ht,source_borel_intersection hF hn T hP L _ hg hgen⟩

end CFSG.Quasithin.ChapterE.Structure.SymplecticFour
