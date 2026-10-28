module
public import CFSG.Quasithin.ChapterE.Section02.Structure.SymplecticFour.SourceGeometry
public import Theory.SpecificGroups.SymplecticFour.TwoConjugate.RootRecognition.InternalOpposition
/-!
# An internal conjugator for the root-containing original E.2.7 pair

The minimal-parabolic source supplies a genuine diagram-moving actor. A
nonzero long-root element of the original module then yields a nonzero short
root. Diagonal torus normalization makes the opposition word internal in the
literal two-conjugate subgroup. Mapping through the original component
marking retains the same V and the same internal conjugator in the ambient
group. This discharges only internality; coefficient-field recognition,
Sylow alignment and the marked core remain separate source obligations.

Source: Aschbacher--Smith E.2.7, printed pp.219--220.
-/

public section
noncomputable section
open Subgroup
namespace CFSG.Quasithin.ChapterE.Witnesses.SymplecticFour
open Theory.SpecificGroups.SymplecticFour TwoConjugate DiagramAutomorphisms EvenBorelTorus
open ChapterB Representation.OneCohomology.SymplecticFour
variable {G F : Type*} [Group G] [Finite G] [Field F] [Finite F] [CharP F 2]

/-- Internal opposition for the original source module, assuming only its
nontrivial long-root intersection in the aligned model. -/
theorem source_long_root_internal_conjugator {n : ℕ} (hF : Nat.card F = 2^n) (hn : 1<n)
    (T : Sylow 2 G) (hP : IsMinimalParabolicOver T ⊤)
    (hJ : minimalParabolicCore T hP = ⊥)
    (L : Subgroup G) [L.Normal] [IsSimpleGroup L] (e : Sp F ≃* L)
    (hmark : (T : Subgroup G).comap (L.subtype.comp e.toMonoidHom) = unipotent)
    (hgen : L ⊔ (T : Subgroup G) = ⊤)
    (V : Subgroup G) [IsElementaryAbelian 2 V] (hVT : V ≤ T)
    (hVM : V ≤ (minimalParabolicMax T hP).pCoreIn 2)
    (hVN : (T : Subgroup G) ≤ normalizer (V : Set G))
    {s : F} (hs : s ≠ 0)
    (hroot : rootElement 0 s ∈ V.comap (L.subtype.comp e.toMonoidHom)) :
    ∃ b : Sp F, b ∈ normalizer (unipotent (F := F) : Set (Sp F)) ∧
      let g : G := L.subtype (e (b⁻¹ * opposition * b))
      g ∈ V ⊔ V.map (MulAut.conj g).toMonoidHom := by
  let f := L.subtype.comp e.toMonoidHom
  let W := V.comap f
  have hVL := Structure.SymplecticFour.source_inner_placement hF hn T hP hJ L e hmark hgen V hVT hVM
  have hfr : f.range = L := by
    rw [MonoidHom.range_comp,MonoidHom.range_eq_top.mpr e.surjective,
      ←MonoidHom.range_eq_map,range_subtype]
  have hmap : W.map f = V := by rw [map_comap_eq,hfr,inf_eq_right.mpr hVL]
  obtain ⟨t,ht⟩ := Structure.SymplecticFour.exists_moving_sylow_actor hF hn T hP L e hmark hgen
  let a : ActorReduction.stabilizer (F := F) :=
    ⟨extensionAction L e t, Structure.SymplecticFour.sylow_actor T L e hmark t⟩
  have hWa : W.map a.val.toMonoidHom = W := by
    apply eq_of_le_of_card_ge
    · rintro _ ⟨x,hx,rfl⟩
      change f (a.val x) ∈ V
      rw [show f (a.val x) = t.val*f x*t.val⁻¹ from extensionAction_apply L e t x]
      exact (mem_normalizer_iff.mp (hVN t.property) (f x)).mp hx
    · rw [card_map_of_injective a.val.injective]
  have hq : 2 < Nat.card F := by
    rw [hF]
    exact (by norm_num : 2=2^1) ▸ Nat.pow_lt_pow_right (by decide) hn
  obtain ⟨b,hb,hg⟩ := exists_internal_conjugator_of_moving_root hq a ht W hWa hs hroot
  refine ⟨b,hb,?_⟩
  let g : Sp F := b⁻¹ * opposition * b
  have hm := mem_map_of_mem f hg
  have he : (MulAut.conj (f g)).toMonoidHom.comp f =
      f.comp (MulAut.conj g).toMonoidHom := by
    ext x
    simp only [MonoidHom.comp_apply,MulEquiv.coe_toMonoidHom,MulAut.conj_apply,map_mul,map_inv]
  have hpair : (W ⊔ W.map (MulAut.conj g).toMonoidHom).map f =
      V ⊔ V.map (MulAut.conj (f g)).toMonoidHom := by
    rw [Subgroup.map_sup,←hmap,Subgroup.map_map,Subgroup.map_map,he]
  change f g ∈ V ⊔ V.map (MulAut.conj (f g)).toMonoidHom
  exact hpair ▸ hm

end CFSG.Quasithin.ChapterE.Witnesses.SymplecticFour
