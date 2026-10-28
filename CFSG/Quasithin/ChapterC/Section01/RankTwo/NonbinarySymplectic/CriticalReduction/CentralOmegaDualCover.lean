module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.CentralOmegaQuotient
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.InnerAction
public import Theory.Representation.DualCoverFromConjugationSection
public import Theory.Representation.SymplecticFourOrthogonalCover.FixedIndex
public import Theory.Representation.BinaryOffender.EmbeddedFixedIndex

/-!
# The natural dual cover in the whole central omega quotient

The original moving cover and the whole X fixed quotient have the same
kernel on U. Their coordinate maps identify the natural module with the
image of U. The equality [X,L]=U and perfectness give a dual cover.
The whole vertex quotient and all natural fixed indices use the same
marking, so the small-mover exclusion applies to this precise section.
Source: MS93 (5.3), printed p.915, using the natural module from (3.2).
-/
public noncomputable section
open scoped IsMulCommutative
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open Representation.OneCohomology Representation.SymplecticFourOrthogonalCover
open Theory.SpecificGroups.SymplecticFour
open Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
namespace CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
open ChapterB.QuasisimpleSource MSCentralOrbit
private theorem map_marked_component
    {G J D : Type*} [Group G] [Group J] [Group D]
    (C : Subgroup J) (q : G →* J) (hq : ∀ x, q x ∈ C)
    (e : C ≃* D) (A : Subgroup G) (hA : A.map q = C) :
    A.map (e.toMonoidHom.comp (q.codRestrict C hq)) = ⊤ := by
  apply top_unique
  intro g _
  obtain ⟨x,hx,he⟩ := (hA.symm ▸ (e.symm g).property : (e.symm g).val ∈ A.map q)
  refine ⟨x,hx,?_⟩
  change e ⟨q x,hq x⟩ = g
  rw [show (⟨q x,hq x⟩ : C) = e.symm g from Subtype.ext he,e.apply_symm_apply]

universe u w
variable {H : Type u} {F : Type w} [Group H] [Finite H] [Field F] [Finite F] [CharP F 2]
variable {K R : Subgroup H} {n : ℕ} (h : Input K R n F)
variable (d : CharacteristicReduction K R)
include h

private theorem centralOmegaDualCover_of_marked_cover
    {a : Vertex d.radical} (ha : color d.radical a = false)
    {E V : Type*} [Field E] [Finite E] [CharP E 2] [Algebra (ZMod 2) E]
    [AddCommGroup V] [Module (ZMod 2) V]
    (σ : Representation (ZMod 2) (L (K := E)) V)
    (p : σ.IntertwiningMap (binaryNatural (K := E))) (hp : IsCover p)
    (j : Multiplicative V →* FreeAmalgam d.radical) (hjr : j.range = U d.radical a)
    (s : CentralOmegaQuotient d.radical a (L (K := E)))
    (hmap : ((Ltilde d.radical a).subgroupOf (stabilizer d.radical a)).map s.quotient = ⊤)
    (hact : ∀ (g : stabilizer d.radical a) (v : V),
      j (Multiplicative.ofAdd (σ (s.quotient g) v)) =
        (g : FreeAmalgam d.radical)*j (Multiplicative.ofAdd v)*(g : FreeAmalgam d.radical)⁻¹)
    (hker : ∀ v : V, p v = 0 ↔
      j (Multiplicative.ofAdd v) ∈ centralizer (Ltilde d.radical a : Set (FreeAmalgam d.radical)))
    (hUX : U d.radical a ≤ X d.radical a) :
    ∃ i : (binaryNatural (K := E)).IntertwiningMap s.action,
      Function.Injective i ∧ IsDualCover i.range ∧
      ∀ w, w ∈ i.toLinearMap.range ↔
        ∃ x : X d.radical a, (x : FreeAmalgam d.radical) ∈ U d.radical a ∧
          (s.sectionData.coordinates x).toAdd = w := by
  let S := stabilizer d.radical a
  let f := s.quotient.comp (inclusion (Ltilde_le_stabilizer a))
  have hf : Function.Surjective f := by
    intro g
    obtain ⟨l,hl,he⟩ := (hmap.symm ▸ mem_top g :
      g ∈ ((Ltilde d.radical a).subgroupOf S).map s.quotient)
    exact ⟨⟨l.val,hl⟩,he⟩
  let π := s.sectionData.coordinates
  have hfixed : OneCohomology.fixed s.action = ⊥ := by
    apply bot_unique
    intro v hv
    exact s.fixed_eq_bot.le (fun g => hv g.val)
  have hkernel (v : V) : p v = 0 ↔
      π ⟨j (Multiplicative.ofAdd v),hUX (hjr ▸ ⟨_,rfl⟩)⟩ = 1 := by
    rw [hker,s.sectionData.coordinates_eq_one_iff]
    have hvX : j (Multiplicative.ofAdd v) ∈ X d.radical a := hUX (hjr ▸ ⟨_,rfl⟩)
    exact ⟨fun hc => ⟨hvX,omegaCenter_le _ hvX,hc⟩,fun hc => hc.2.2⟩
  obtain ⟨i,hi,hdual,_,hrange⟩ := exists_dualCover_of_conjugation_section
    (X d.radical a) (U d.radical a) (Ltilde d.radical a) hUX
    ((Ltilde_le_stabilizer a).trans (X_normalized _ _))
    (h.replacement_X_commutator_eq_U d ha).le σ s.action (binaryNatural (K := E))
    p hp.1 j hjr π s.sectionData.onto f hf
    (fun l v => hact (inclusion (Ltilde_le_stabilizer a) l) v)
    (fun l x => s.sectionData.equivariant (inclusion (Ltilde_le_stabilizer a) l) x)
    hkernel hfixed
  exact ⟨i,hi,hdual,hrange⟩

omit h [Finite H] in
private theorem marked_cover_indices
    {a : Vertex d.radical}
    {E V : Type*} [Field E] [Finite E] [CharP E 2] [Algebra (ZMod 2) E]
    [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V]
    (σ : Representation (ZMod 2) (L (K := E)) V)
    (p : σ.IntertwiningMap (binaryNatural (K := E))) (hp : IsCover p)
    (j : Multiplicative V →* FreeAmalgam d.radical) (hj : Function.Injective j)
    (hjr : j.range = U d.radical a)
    (f : stabilizer d.radical a →* L (K := E))
    (haction : ∀ (g : stabilizer d.radical a) (v : V),
      j (Multiplicative.ofAdd (σ (f g) v)) =
        (g : FreeAmalgam d.radical)*j (Multiplicative.ofAdd v)*(g : FreeAmalgam d.radical)⁻¹) :
    ∀ A : Subgroup (stabilizer d.radical a),
      (centralizer (A : Set (stabilizer d.radical a))).relIndex
        ((U d.radical a).subgroupOf (stabilizer d.radical a)) =
        2 ^ fixedCodim (binaryNatural (K := E)) (A.map f) := by
  let S := stabilizer d.radical a
  have hUS : U d.radical a ≤ S := (U_le_Z a).trans (Z_le_stabilizer d.radical a)
  let jS := j.codRestrict S (fun w => hUS (hjr ▸ (show j w ∈ j.range from ⟨w,rfl⟩)))
  have hjS : Function.Injective jS := fun v w he => hj (congrArg Subtype.val he)
  have hjSr : jS.range = (U d.radical a).subgroupOf S := by
    ext x
    constructor
    · rintro ⟨w,rfl⟩
      exact hjr ▸ (show j w ∈ j.range from ⟨w,rfl⟩)
    · intro hx
      obtain ⟨w,hw⟩ := (show x.val ∈ j.range from hjr.symm ▸ hx)
      exact ⟨w,Subtype.ext hw⟩
  intro A
  have hi := embedded_centralizer_index σ ((U d.radical a).subgroupOf S) A jS hjS hjSr
    (f.comp A.subtype) (fun x w => Subtype.ext (haction x.val w))
  rw [fixedCodim_of_binaryCover p hp,
    MonoidHom.range_comp,range_subtype] at hi
  exact hi


/-- The full X fixed quotient has a natural dual cover and exact small-mover
indices for its own literal vertex marking. -/
theorem Input.exists_replacement_centralOmegaDualCover
    (geometry : Geometry d.radical) (hb : 4 ≤ geometry.b d.radical)
    {a : Vertex d.radical} (ha : color d.radical a = false) :
    ∃ E : BinaryField, E.degree = n ∧
      ∃ s : CentralOmegaQuotient d.radical a (L (K := E.Carrier)),
      ∃ i : (binaryNatural (K := E.Carrier)).IntertwiningMap s.action,
        Function.Injective i ∧ IsDualCover i.range ∧
        (∀ w, w ∈ i.toLinearMap.range ↔
          ∃ x : X d.radical a, (x : FreeAmalgam d.radical) ∈ U d.radical a ∧
            (s.sectionData.coordinates x).toAdd = w) ∧
        ∀ A : Subgroup (stabilizer d.radical a),
          (centralizer (A : Set (stabilizer d.radical a))).relIndex
            ((U d.radical a).subgroupOf (stabilizer d.radical a)) =
            2 ^ fixedCodim (binaryNatural (K := E.Carrier)) (A.map s.quotient) := by
  let q := QuotientGroup.mk' (pCore 2 d.overgroup)
  let C₀ := (K.subgroupOf d.overgroup).map q
  let : C₀.Normal := (h.replacement_component_image_structure d).2.1
  let : IsElementaryAbelian 2 (omegaCenterIn (pCore 2 d.overgroup)) := omegaCenterIn_elementary _
  let s₀ := MovedSection.ofNormal (NormalElementaryQuotient.representation
    (omegaCenterIn (pCore 2 d.overgroup)) q (QuotientGroup.mk'_surjective _)
    ((QuotientGroup.ker_mk' _).trans (h.replacement_centralOmega_centralizer d).symm)) C₀
  obtain ⟨E,hE,e,he,j,hj,hjr,κ,hκ,hκQ,hκC,hκL,hψ,hsemi,hconj,hproj,hker⟩ :=
    h.replacement_ambient_initial_cover_at_vertex d ha
  change ActionEquiv (s₀.action.comp C₀.subtype) (binaryNatural (K := E.Carrier)) at e
  change IsCover (MovedSection.coverProjection s₀ e) at he
  change Multiplicative s₀.space.toSubmodule →* FreeAmalgam d.radical at j
  have hCtop : C₀ = ⊤ := by
    have hpre : C₀.comap q = ⊤ := by
      rw [show C₀ = (K.subgroupOf d.overgroup).map q from rfl,
        comap_map_eq,QuotientGroup.ker_mk']
      exact h.replacement_inner_of_four_le d geometry hb
    rw [←map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _) C₀,hpre,
      ←MonoidHom.range_eq_map]
    exact MonoidHom.range_eq_top_of_surjective _ (QuotientGroup.mk'_surjective _)
  let κC := κ.codRestrict C₀ (fun x => hCtop ▸ mem_top (κ x))
  let f := e.groupEquiv.toMonoidHom.comp κC
  have hκC : Function.Surjective κC := by
    intro x
    obtain ⟨g,hg⟩ := hκ x
    exact ⟨g,Subtype.ext hg⟩
  have hf : Function.Surjective f := e.groupEquiv.surjective.comp hκC
  have hfker : f.ker = κ.ker := by
    ext x
    change e.groupEquiv (κC x) = 1 ↔ κ x = 1
    rw [e.groupEquiv.map_eq_one_iff]
    exact Subtype.ext_iff
  obtain ⟨s,hs⟩ := h.exists_replacement_centralOmegaQuotient_over d ha f hf
    (by rw [hfker]; exact hκQ)
  let σ := MovedSection.coverAction s₀ e
  have haction (x : stabilizer d.radical a) (v : s₀.space.toSubmodule) :
      j (Multiplicative.ofAdd (σ (f x) v)) =
        (x : FreeAmalgam d.radical)*j (Multiplicative.ofAdd v)*(x : FreeAmalgam d.radical)⁻¹ := by
    change j (Multiplicative.ofAdd (s₀.space.toRepresentation
      (e.groupEquiv.symm (e.groupEquiv (κC x))) v)) = _
    rw [e.groupEquiv.symm_apply_apply]
    exact hconj x v
  have hmap : ((Ltilde d.radical a).subgroupOf (stabilizer d.radical a)).map s.quotient = ⊤ := by
    rw [hs]
    exact map_marked_component C₀ κ _ e.groupEquiv _ hκL
  have hUX : U d.radical a ≤ X d.radical a := (U_le_Z a).trans
    (geometry.omega_bound a ha (by rw [geometry.distance_constant a ha]; change 0 < geometry.b d.radical; omega))
  obtain ⟨i,hi,hdual,hrange⟩ := centralOmegaDualCover_of_marked_cover h d ha σ
    (MovedSection.coverProjection s₀ e) he j hjr s hmap
    (by intro g v; rw [hs]; exact haction g v) hker hUX
  refine ⟨E,hE,s,i,hi,hdual,hrange,?_⟩
  rw [hs]
  exact marked_cover_indices d σ (MovedSection.coverProjection s₀ e) he j hj hjr f haction

end CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
