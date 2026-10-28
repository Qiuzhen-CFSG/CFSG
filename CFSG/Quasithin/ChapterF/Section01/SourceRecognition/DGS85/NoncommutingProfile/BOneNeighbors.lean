module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.NoncommutingProfile.BOneCenters

/-!
# Arbitrary turns in the noncommuting b=1 graph

The actual local actor is transitive on neighbors. Its marked SL₂ Sylow
normalizer is exactly the stabilizer of the original neighbor, so distinct
neighbors give distinct Sylow images. Their trivial intersection forces a
two-subgroup fixing a turn into the middle vertex core. Since Q=Z is
abelian, the two neighbor cores then generate the actor modulo its core,
and their literal intersection is its full center.

This extends the chosen-opposite calculation to every turn of the source
graph. It uses the earlier marked Chapter 7 actions and Borel normalization;
it assumes neither path transitivity nor the order of a path stabilizer.
The graph is not assumed to be a tree.

Source: DGS, *Groups and Graphs* (1985), 10.4 and the path-stabilizer
argument in 10.5(c,d), printed pp.155–156, using 3.1(f) and 7.1.
-/

@[expose] public noncomputable section
open Subgroup
open scoped MatrixGroups Pointwise
namespace CFSG.Quasithin.ChapterF.Source.DGS85.NoncommutingProfile
open Subgroup.CosetGeometry.RankTwo
open Theory.GroupTheory.AmalgamGraph
variable {G : Type*} [Group G] {P : Fin 2 → Subgroup G} {B : Subgroup G}
variable {k W : Type*} [Field k] [Finite k] [CharP k 2]
  [AddCommGroup W] [Module (ZMod 2) W]
variable (h : LocallyRankOneTriple P B) (i : Bool)
    (c : BOneActionData (family P) (base (family P) i) (base (family P) (!i)) k W)
    (hn : B ≤ normalizer (c.actor : Set G))

include h

private theorem base_edge_eq :
    stabilizer (family P) (base (family P) i) ⊓
      stabilizer (family P) (base (family P) (!i)) = B := by
  cases i <;> simpa only [stabilizer,Subgroup.CosetGeometry.stabilizer_base,family,
    Bool.not_false,Bool.not_true,inf_comm (P 1) (P 0)] using h.intersection

include hn

/-- The earlier Borel normalization and supplement give normality in the full vertex group. -/
theorem base_actor_normalized :
    stabilizer (family P) (base (family P) i) ≤ normalizer (c.actor : Set G) := by
  rw [←c.supplement,base_edge_eq h i]
  exact sup_le c.actor.le_normalizer hn

/-- The actual actor is transitive on the neighbors of its marked vertex. -/
theorem base_actor_neighbor_transitive (u : Vertex (family P))
    (hu : (graph (family P)).Adj (base (family P) i) u) :
    ∃ g : c.actor, (g : G) • base (family P) (!i) = u := by
  have hn' : family P i ≤ normalizer (c.actor : Set G) := by
    simpa only [stabilizer,Subgroup.CosetGeometry.stabilizer_base] using
      base_actor_normalized h i c hn
  have hs : c.actor ⊔ B = family P i := by
    have hs0 := c.supplement
    rw [base_edge_eq h i] at hs0
    simpa only [stabilizer,Subgroup.CosetGeometry.stabilizer_base] using hs0
  obtain ⟨g,hg,he⟩ := neighbor_transitive_of_borel_cover h i c.actor hn' hs u hu
  exact ⟨⟨g,hg⟩,he⟩

/-- The marked SL₂ Sylow normalizer is exactly the stabilizer of the marked neighbor. -/
theorem base_actor_fixes_neighbor_iff
    (hcore : Q (family P) (base (family P) (!i)) = Z (family P) (base (family P) (!i)))
    (g : c.actor) :
    c.quotient g ∈ normalizer (c.imageSylow : Set SL(2,k)) ↔
      (g : G) • base (family P) (!i) = base (family P) (!i) := by
  constructor
  · intro hg
    obtain ⟨a,ha,he⟩ := base_borel_lifts_sylow_normalizer h i c hcore hn _ hg
    have hk : g*a⁻¹ ∈ c.quotient.ker := by
      change c.quotient (g*a⁻¹) = 1
      rw [map_mul,map_inv,he,mul_inv_cancel]
    have hq : ((g*a⁻¹ : c.actor) : G) ∈ Q (family P) (base (family P) i) := by
      change g*a⁻¹ ∈ (Q (family P) (base (family P) i)).subgroupOf c.actor
      rw [←c.kernel]
      exact hk
    have hfix : ((g*a⁻¹ : c.actor) : G) • base (family P) (!i) = base (family P) (!i) :=
      ((source_Z_Q_U h _).2.trans
        ((ballKernel_one_le_edge _ c.adjacent).trans inf_le_right)) hq
    have ha' : (a : G) • base (family P) (!i) = base (family P) (!i) := by
      have hab : (a : G) ∈ B := ha
      have hab' : (a : G) ∈ stabilizer (family P) (base (family P) (!i)) :=
        (base_edge_eq h i ▸ hab).2
      exact hab'
    have heq : (g : G) = ((g*a⁻¹ : c.actor) : G) * (a : G) := by simp
    rw [heq,mul_smul,ha',hfix]
  · intro hg
    let T := Q (family P) (base (family P) (!i)) ⊔ Q (family P) (base (family P) i)
    have hT : T ≤ c.actor := sup_le c.neighbor_core_le c.core_le
    have hpre := neighbor_core_product_preimage c hcore
    have hgv : (g : G) • base (family P) i = base (family P) i := c.actor_le g.property
    have hconj : T.map (MulAut.conj (g : G)).toMonoidHom = T := by
      rw [Subgroup.map_sup,←Q_translate,←Q_translate,hg,hgv]
    have hnorm : (g : G) ∈ normalizer (T : Set G) := mem_normalizer_iff_map_conj_eq.mpr hconj
    have hgn : g ∈ normalizer (T.subgroupOf c.actor : Set c.actor) := by
      rw [←subgroupOf_normalizer_eq hT]
      exact hnorm
    have hh := comap_normalizer_eq_of_surjective (c.imageSylow : Subgroup SL(2,k)) c.onto
    rw [hpre] at hh
    exact (show g ∈ (normalizer (c.imageSylow : Set SL(2,k))).comap c.quotient from hh ▸ hgn)

/-- Distinct graph neighbors give distinct marked Sylows. -/
theorem base_neighbor_sylows_ne
    (hcore : Q (family P) (base (family P) (!i)) = Z (family P) (base (family P) (!i)))
    (g t : c.actor)
    (hne : (g : G) • base (family P) (!i) ≠ (t : G) • base (family P) (!i)) :
    c.quotient g • c.imageSylow ≠ c.quotient t • c.imageSylow := by
  intro he
  have hnorm : c.quotient (t⁻¹*g) ∈ normalizer (c.imageSylow : Set SL(2,k)) := by
    apply Sylow.smul_eq_iff_mem_normalizer.mp
    rw [map_mul,map_inv,mul_smul,he,inv_smul_smul]
  have hfix := (base_actor_fixes_neighbor_iff h i c hn hcore (t⁻¹*g)).mp hnorm
  apply hne
  have hh := congrArg (fun x : Vertex (family P) => (t : G) • x) hfix
  simpa only [Subgroup.coe_mul,Subgroup.coe_inv,mul_smul,smul_inv_smul] using hh


omit h hn in
private theorem conjugate_le (L A : Subgroup G) (hA : A ≤ L) (g : L) :
    A.map (MulAut.conj (g : G)).toMonoidHom ≤ L := by
  rintro _ ⟨a,ha,rfl⟩
  exact L.mul_mem (L.mul_mem g.property (hA ha)) (L.inv_mem g.property)

omit h hn in
private theorem quotient_conjugate (L A : Subgroup G) (hA : A ≤ L)
    {J : Type*} [Group J] (π : L →* J) (g : L) :
    ((A.map (MulAut.conj (g : G)).toMonoidHom).subgroupOf L).map π =
      ((A.subgroupOf L).map π).map (MulAut.conj (π g)).toMonoidHom := by
  have hc : (A.map (MulAut.conj (g : G)).toMonoidHom).subgroupOf L =
      (A.subgroupOf L).map (MulAut.conj g).toMonoidHom := by
    apply map_injective L.subtype_injective
    rw [map_subgroupOf_eq_of_le (conjugate_le L A hA g),map_map]
    have he : L.subtype.comp (MulAut.conj g).toMonoidHom =
        (MulAut.conj (g : G)).toMonoidHom.comp L.subtype := by ext a; rfl
    rw [he,←map_map,map_subgroupOf_eq_of_le hA]
  rw [hc,map_map,map_map]
  congr 1
  ext a
  simp only [MonoidHom.comp_apply,MulEquiv.coe_toMonoidHom,MulAut.conj_apply,map_mul,map_inv]

omit h hn in
/-- Neighbor-core images are the actual conjugate Sylows, with their transporters retained. -/
theorem base_neighbor_core_image
    (hcore : Q (family P) (base (family P) (!i)) = Z (family P) (base (family P) (!i)))
    (g : c.actor) :
    ((Q (family P) ((g : G) • base (family P) (!i))).subgroupOf c.actor).map c.quotient =
      (c.quotient g • c.imageSylow : Sylow 2 SL(2,k)) := by
  rw [Q_translate,quotient_conjugate _ _ c.neighbor_core_le,hcore,c.neighbor_image]
  rfl

omit h hn in
private theorem sylow_disjoint_of_ne (S T : Sylow 2 SL(2,k)) (hne : S ≠ T) :
    Disjoint (S : Subgroup SL(2,k)) (T : Subgroup SL(2,k)) := by
  apply disjoint_def.mpr
  intro x hxS hxT
  by_contra hx
  have hgen := Representation.SL2SylowFixedRecognition.sylow_sup_zpowers_eq_top T S hne.symm hxT hx
  have htop : (S : Subgroup SL(2,k)) = ⊤ := by
    simpa only [sup_eq_left.mpr (zpowers_le.mpr hxS)] using hgen
  apply Matrix.SpecialLinearGroup.sylow_normalizer_ne_top S
  change normalizer ((S : Subgroup SL(2,k)) : Set SL(2,k)) = ⊤
  rw [htop]
  exact top_unique (⊤ : Subgroup SL(2,k)).le_normalizer

omit h hn in
private theorem sylow_sup_eq_top (S T : Sylow 2 SL(2,k)) (hne : S ≠ T) :
    (S : Subgroup SL(2,k)) ⊔ T = ⊤ := by
  by_contra he
  have hT := (le_sup_right : (T : Subgroup SL(2,k)) ≤ (S : Subgroup SL(2,k)) ⊔ T).trans
    (Matrix.SpecialLinearGroup.proper_overgroup_le_sylow_normalizer S _ le_sup_left he)
  have hle : (T : Subgroup SL(2,k)) ≤ S := by
    have hh := T.isPGroup'.inf_normalizer_sylow S
    rw [inf_eq_left.mpr hT] at hh
    exact hh.le.trans inf_le_right
  exact hne (Sylow.ext (T.is_maximal' S.isPGroup' hle))

omit hn in
private theorem conjugate_core_product_sylow
    (hcore : Q (family P) (base (family P) (!i)) = Z (family P) (base (family P) (!i)))
    (g : c.actor) :
    Stellmacher.IsSylowSubgroupIn
      (Q (family P) ((g : G) • base (family P) (!i)) ⊔ Q (family P) (base (family P) i))
      (stabilizer (family P) (base (family P) i)) := by
  let := finite_endpoints h
  have hs := sylow_witness_map (MulAut.conj (g : G)).toMonoidHom (MulAut.conj (g : G)).injective
    _ _ (core_product_sylow c h hcore)
  have hgv : (g : G) • base (family P) i = base (family P) i := c.actor_le g.property
  rwa [Subgroup.map_sup,←Q_translate,←Q_translate,←stabilizer_translate,hgv] at hs

omit h hn in
private theorem pGroup_le_normal_sylowIn (T E A : Subgroup G) [Finite E]
    (hT : Stellmacher.IsSylowSubgroupIn T E) (hA : IsPGroup 2 A)
    (hAE : A ≤ E) (hnT : A ≤ normalizer (T : Set G)) : A ≤ T := by
  obtain ⟨R,hR⟩ := hT
  have hTE : T ≤ E := hR ▸ map_subtype_le _
  have he : (R : Subgroup E) = T.subgroupOf E := by
    apply map_injective E.subtype_injective
    rw [hR,map_subgroupOf_eq_of_le hTE]
  have hnorm : A.subgroupOf E ≤ normalizer ((R : Subgroup E) : Set E) := by
    rw [he,←subgroupOf_normalizer_eq hTE]
    exact comap_mono hnT
  have hh := hA.comap_subtype.inf_normalizer_sylow R
  have hleR : A.subgroupOf E ≤ (R : Subgroup E) := by
    calc
      A.subgroupOf E = A.subgroupOf E ⊓ normalizer (R : Set E) := (inf_eq_left.mpr hnorm).symm
      _ = A.subgroupOf E ⊓ (R : Subgroup E) := hh
      _ ≤ R := inf_le_right
  have hl : A.subgroupOf E ≤ T.subgroupOf E := by simpa only [he] using hleR
  have hm := map_mono (f := E.subtype) hl
  rwa [map_subgroupOf_eq_of_le hAE,map_subgroupOf_eq_of_le hTE] at hm

omit h hn in
private theorem core_normalized (F : Bool → Subgroup G) (v : Vertex F) :
    stabilizer F v ≤ normalizer (Q F v : Set G) := by
  simpa only [Q,pCoreIn,normalizer_eq_top,←MonoidHom.range_eq_map,range_subtype]
    using (pCore 2 (stabilizer F v)).le_normalizer_map (stabilizer F v).subtype

/-- A two-subgroup fixing two distinct neighbors lies in the actual middle core. -/
theorem base_two_group_fixes_turn
    (hcore : Q (family P) (base (family P) (!i)) = Z (family P) (base (family P) (!i)))
    {u z : Vertex (family P)}
    (hu : (graph (family P)).Adj (base (family P) i) u)
    (hz : (graph (family P)).Adj (base (family P) i) z) (hne : u ≠ z)
    (A : Subgroup G) (hA : IsPGroup 2 A)
    (hAv : A ≤ stabilizer (family P) (base (family P) i))
    (hAu : A ≤ stabilizer (family P) u) (hAz : A ≤ stabilizer (family P) z) :
    A ≤ Q (family P) (base (family P) i) := by
  let := finite_endpoints h
  obtain ⟨g,rfl⟩ := base_actor_neighbor_transitive h i c hn u hu
  obtain ⟨t,rfl⟩ := base_actor_neighbor_transitive h i c hn z hz
  let v := base (family P) i
  let w := base (family P) (!i)
  have hprod (a : c.actor) (ha : A ≤ stabilizer (family P) ((a : G) • w)) :
      A ≤ Q (family P) ((a : G) • w) ⊔ Q (family P) v := by
    apply pGroup_le_normal_sylowIn _ (stabilizer (family P) v) A
      (conjugate_core_product_sylow h i c hcore a) hA hAv
    exact (le_inf (ha.trans (core_normalized _ _))
      (hAv.trans (core_normalized _ _))).trans (normalizer_inf_normalizer_le_normalizer_sup _ _)
  have hle (a : c.actor) : Q (family P) ((a : G) • w) ≤ c.actor := by
    rw [Q_translate]
    exact conjugate_le _ _ c.neighbor_core_le a
  have hAL : A ≤ c.actor := (hprod g hAu).trans (sup_le (hle g) c.core_le)
  have him (a : c.actor) (ha : A ≤ stabilizer (family P) ((a : G) • w)) :
      (A.subgroupOf c.actor).map c.quotient ≤ (c.quotient a • c.imageSylow : Sylow 2 SL(2,k)) := by
    have hA' : A.subgroupOf c.actor ≤
        (Q (family P) ((a : G) • w) ⊔ Q (family P) v).subgroupOf c.actor := subgroupOf_mono c.actor (hprod a ha)
    have hm := map_mono (f := c.quotient) hA'
    rw [subgroupOf_sup (hle a) c.core_le,Subgroup.map_sup,←c.kernel,
      Subgroup.map_ker_self, sup_bot_eq,base_neighbor_core_image i c hcore a] at hm
    exact hm
  have hd := sylow_disjoint_of_ne _ _ (base_neighbor_sylows_ne h i c hn hcore g t hne)
  intro x hx
  let xL : c.actor := ⟨x,hAL hx⟩
  have hxI : c.quotient xL ∈ (A.subgroupOf c.actor).map c.quotient := mem_map_of_mem _ hx
  have hxker : xL ∈ c.quotient.ker := disjoint_def.mp hd (him g hAu hxI) (him t hAz hxI)
  exact (show xL ∈ (Q (family P) v).subgroupOf c.actor from c.kernel ▸ hxker)

/-- The literal intersection of the cores at any two distinct neighbors is the full actor center. -/
theorem base_two_neighbor_core_intersection
    (hv : Q (family P) (base (family P) i) = Z (family P) (base (family P) i))
    (hw : Q (family P) (base (family P) (!i)) = Z (family P) (base (family P) (!i)))
    {u z : Vertex (family P)}
    (hu : (graph (family P)).Adj (base (family P) i) u)
    (hz : (graph (family P)).Adj (base (family P) i) z) (hne : u ≠ z) :
    Q (family P) u ⊓ Q (family P) z = centerIn c.actor := by
  let := finite_endpoints h
  obtain ⟨g,rfl⟩ := base_actor_neighbor_transitive h i c hn u hu
  obtain ⟨t,rfl⟩ := base_actor_neighbor_transitive h i c hn z hz
  let v := base (family P) i
  let w := base (family P) (!i)
  let u := (g : G) • w
  let z := (t : G) • w
  let D := Q (family P) u ⊓ Q (family P) z
  have hle (a : c.actor) : Q (family P) ((a : G) • w) ≤ c.actor := by
    rw [Q_translate]
    exact conjugate_le _ _ c.neighbor_core_le a
  have hdistinct := base_neighbor_sylows_ne h i c hn hw g t hne
  have hsep : D ≤ Q (family P) v := by
    intro x hx
    let xL : c.actor := ⟨x,hle g hx.1⟩
    have hxg : c.quotient xL ∈ (c.quotient g • c.imageSylow : Sylow 2 SL(2,k)) := by
      change c.quotient xL ∈ ((c.quotient g • c.imageSylow : Sylow 2 SL(2,k)) : Subgroup SL(2,k))
      rw [←base_neighbor_core_image i c hw g]
      exact mem_map_of_mem _ hx.1
    have hxt : c.quotient xL ∈ (c.quotient t • c.imageSylow : Sylow 2 SL(2,k)) := by
      change c.quotient xL ∈ ((c.quotient t • c.imageSylow : Sylow 2 SL(2,k)) : Subgroup SL(2,k))
      rw [←base_neighbor_core_image i c hw t]
      exact mem_map_of_mem _ hx.2
    have hk : xL ∈ c.quotient.ker := disjoint_def.mp (sylow_disjoint_of_ne _ _ hdistinct) hxg hxt
    exact (show xL ∈ (Q (family P) v).subgroupOf c.actor from c.kernel ▸ hk)
  have hgen : (Q (family P) u ⊔ Q (family P) z) ⊔ Q (family P) v = c.actor := by
    let R := (Q (family P) u ⊔ Q (family P) z) ⊔ Q (family P) v
    have hRL : R ≤ c.actor := sup_le (sup_le (hle g) (hle t)) c.core_le
    have hm : (R.subgroupOf c.actor).map c.quotient = ⊤ := by
      rw [subgroupOf_sup (sup_le (hle g) (hle t)) c.core_le,subgroupOf_sup (hle g) (hle t),
        Subgroup.map_sup,Subgroup.map_sup,base_neighbor_core_image i c hw g,
        base_neighbor_core_image i c hw t,sylow_sup_eq_top _ _ hdistinct,top_sup_eq]
    have he : R.subgroupOf c.actor = ⊤ := map_injective_of_ker_le c.quotient
      (by rw [c.kernel]; exact comap_mono le_sup_right) le_top
      (hm.trans (map_top_of_surjective c.quotient c.onto).symm)
    have he' := congrArg (map c.actor.subtype) he
    rwa [map_subgroupOf_eq_of_le hRL,←MonoidHom.range_eq_map,range_subtype] at he'
  have hab (a : c.actor) : IsElementaryAbelian 2 (Q (family P) ((a : G) • w)) := by
    rw [Q_translate]
    let : IsElementaryAbelian 2 (Q (family P) w) := core_elementary h hw
    exact IsElementaryAbelian.map _
  let : IsElementaryAbelian 2 (Q (family P) u) := hab g
  let : IsElementaryAbelian 2 (Q (family P) z) := hab t
  let : IsElementaryAbelian 2 (Q (family P) v) := core_elementary h hv
  apply le_antisymm
  · refine le_inf (inf_le_left.trans (hle g)) ?_
    apply le_centralizer_iff.mp
    have hcen : (Q (family P) u ⊔ Q (family P) z) ⊔ Q (family P) v ≤
        centralizer (D : Set G) := sup_le (sup_le
      ((Q (family P) u).le_centralizer.trans (centralizer_le inf_le_left))
      ((Q (family P) z).le_centralizer.trans (centralizer_le inf_le_right)))
      ((Q (family P) v).le_centralizer.trans (centralizer_le hsep))
    rw [hgen] at hcen
    exact hcen
  · have hc := (actor_center_le_cores c h hv).trans inf_le_right
    have hcentral (a : c.actor) : centerIn c.actor ≤ Q (family P) ((a : G) • w) := by
      intro x hx
      rw [Q_translate]
      refine ⟨x,hc hx,?_⟩
      change (a : G)*x*(a : G)⁻¹ = x
      rw [hx.2 a a.property,mul_inv_cancel_right]
    exact le_inf (hcentral g) (hcentral t)

end CFSG.Quasithin.ChapterF.Source.DGS85.NoncommutingProfile
