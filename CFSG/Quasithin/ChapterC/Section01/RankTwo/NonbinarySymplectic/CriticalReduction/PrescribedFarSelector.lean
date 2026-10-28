module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.SmallerPrescribedSelection
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.DistanceFourNeighbor
import all CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.DistanceFourPrescribedFixedEscape
import all CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.RootSelectedPaths

/-!
# The same far selector with both prescribed root actors

The maximizing plane contains the original own-index mover and both full
endpoint roots. Of the same two positioned selector candidates, one has the
required nonnormal endpoint action. Radius fixedness excludes trapping and
supplies an actual backward critical path. Its mover is transported at the
original vertex, retaining both prescribed root actors and both plane positions.
-/

public noncomputable section
open Subgroup Representation Theory.GroupTheory Theory.SpecificGroups.SymplecticFour
open Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
open CFSG.Quasithin.ChapterC.Sp4Four.DistanceReduction
open CFSG.Quasithin.ChapterC.Sp4Four.DistanceReduction.LargeDistance
namespace CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
open ChapterB.QuasisimpleSource MSCentralOrbit

private theorem prescribed_conjugate_le {G : Type*} [Group G]
    {S D : Subgroup G} (hD : D ≤ S) {g : G} (hg : g ∈ S) :
    D.map (MulAut.conj g).toMonoidHom ≤ S := by
  rintro _ ⟨z,hz,rfl⟩
  exact S.mul_mem (S.mul_mem hg (hD hz)) (S.inv_mem hg)

private theorem prescribed_subgroupOf_conjugate {G : Type*} [Group G]
    {S : Subgroup G} (D : Subgroup G) (hDS : D ≤ S) (g : S) :
    (D.map (MulAut.conj g.val).toMonoidHom).subgroupOf S =
      (D.subgroupOf S).map (MulAut.conj g).toMonoidHom := by
  apply Subgroup.map_injective S.subtype_injective
  rw [Subgroup.image_conjugate,map_subgroupOf_eq_of_le hDS]
  exact map_subgroupOf_eq_of_le (prescribed_conjugate_le hDS g.property)

private theorem prescribed_map_conj_mul {G : Type*} [Group G]
    (A : Subgroup G) (g k : G) :
    (A.map (MulAut.conj k).toMonoidHom).map (MulAut.conj g).toMonoidHom =
      A.map (MulAut.conj (g*k)).toMonoidHom := by
  rw [Subgroup.map_map]
  congr 1
  ext z
  simp [MulAut.conj_apply,mul_assoc]

private theorem prescribed_second_coordinate
    {G E : Type*} [Group G] [Group E]
    (S D : Subgroup G) (hDS : D ≤ S) (f : S →* E)
    (g x : S) (hxD : x.val ∈ normalizer (D : Set G)) (c : E) :
    (((D.subgroupOf S).map f).map (MulAut.conj (c*f x)).toMonoidHom =
      ((D.subgroupOf S).map f).map (MulAut.conj c).toMonoidHom) ∧
    (((((D.map (MulAut.conj g.val).toMonoidHom).map
        (MulAut.conj x.val⁻¹).toMonoidHom).subgroupOf S).map f).map
          (MulAut.conj (c*f x)).toMonoidHom =
      (((D.map (MulAut.conj g.val).toMonoidHom).subgroupOf S).map f).map
        (MulAut.conj c).toMonoidHom) := by
  have hxn : (D.subgroupOf S).map (MulAut.conj x).toMonoidHom = D.subgroupOf S := by
    have hn : D.map (MulAut.conj x.val).toMonoidHom = D :=
      mem_normalizer_iff_map_conj_eq.mp hxD
    rw [←prescribed_subgroupOf_conjugate D hDS x,hn]
  constructor
  · rw [←prescribed_map_conj_mul,←Subgroup.image_conjugate,hxn]
  · have hsub : ((D.map (MulAut.conj g.val).toMonoidHom).map
        (MulAut.conj x.val⁻¹).toMonoidHom).subgroupOf S =
        ((D.map (MulAut.conj g.val).toMonoidHom).subgroupOf S).map
          (MulAut.conj x⁻¹).toMonoidHom :=
      prescribed_subgroupOf_conjugate _ (prescribed_conjugate_le hDS g.property) x⁻¹
    rw [hsub,Subgroup.image_conjugate,prescribed_map_conj_mul,map_inv,
      show (c*f x)*(f x)⁻¹=c by group]

variable {H F : Type*} [Group H] [Finite H] [Field F] [Finite F] [CharP F 2]
variable {K R : Subgroup H} {n : ℕ} (h : Input K R n F)
variable (d : CharacteristicReduction K R)
include h

private theorem prescribed_far_backward
    {geometry : Geometry d.radical} {v e a' s : Vertex d.radical}
    (p : CriticalPath d.radical geometry v e) (hb : geometry.b d.radical=4)
    (hvs : Adjacent d.radical v s) (has : Adjacent d.radical a' s)
    (r : FreeAmalgam d.radical) (hr : r ∈ Ltilde d.radical v)
    (hra : act d.radical r (p.walk.getVert 2)=a')
    (hfixed : ⁅V d.radical v,Q d.radical v⁆ ≤ fixedCore d.radical v)
    (hn : ¬ Z d.radical e ≤ normalizer
      ((Z d.radical a' ⊔ Z d.radical v : Subgroup (FreeAmalgam d.radical)) : Set _)) :
    ∃ back : CriticalPath d.radical geometry a' (p.walk.getVert 2),
      back.walk.getVert 1=s ∧
      ∀ i ≤ p.walk.length-2, back.walk.getVert (i+2)=p.walk.getVert i := by
  have hnot := prescribed_selector_not_trapped h d p hb hvs has r hr hra hfixed hn
  have hpen : p.walk.getVert (p.walk.length-2)=p.walk.getVert 2 := by
    rw [p.length_eq_b,hb]
  obtain ⟨back,hfirst,hover⟩ := exists_backward_path_of_not_le geometry (by omega) p hvs has
    (by rwa [hpen])
  let back' : CriticalPath d.radical geometry a' (p.walk.getVert 2) := {
    start_color := back.start_color
    walk := back.walk.copy rfl hpen
    shortest := by rw [SimpleGraph.Walk.length_copy,←hpen]; exact back.shortest
    critical := by simpa only [hpen] using back.critical }
  refine ⟨back',?_,?_⟩
  · change (back.walk.copy rfl hpen).getVert 1=s
    simpa only [SimpleGraph.Walk.getVert_copy] using hfirst
  · intro i hi
    change (back.walk.copy rfl hpen).getVert (i+2)=_
    simpa only [SimpleGraph.Walk.getVert_copy] using hover i hi


/-- The original own-index mover selects an actual far path and generates
with both retained full endpoint roots, in the same opposite-plane position. -/
theorem Input.replacement_prescribed_far_selector
    {geometry : Geometry d.radical} {v e₁ e₂ w : Vertex d.radical}
    (p : CriticalPath d.radical geometry v e₁)
    (companion : CriticalPath d.radical geometry v e₂)
    (hb : geometry.b d.radical=4)
    (hfirst : p.walk.getVert 1=w) (hcfirst : companion.walk.getVert 1=w)
    (hfixed : ⁅V d.radical v,Q d.radical v⁆ ≤ fixedCore d.radical v)
    (hJm : (centralizer (Subgroup.SmallMover.join (U d.radical v) (Q d.radical v)
      (Q d.radical w) (Nat.card F^2) : Set (FreeAmalgam d.radical))).relIndex
        (U d.radical v) ≤ Nat.card F^2)
    (hJlarge : Nat.card F^2 < (Q d.radical v).relIndex
      (Subgroup.SmallMover.join (U d.radical v) (Q d.radical v)
        (Q d.radical w) (Nat.card F^2)))
    (hne : Z d.radical v ⊓ centralizer (Z d.radical e₁ : Set (FreeAmalgam d.radical)) ≠
      Z d.radical v ⊓ centralizer (Z d.radical e₂ : Set (FreeAmalgam d.radical))) :
    ∃ B : BinaryField, B.degree=n ∧
      ∃ f : stabilizer d.radical v →* Sp B.Carrier,
        Function.Surjective f ∧ f.ker.map (stabilizer d.radical v).subtype=Q d.radical v ∧
        ((Q d.radical w).subgroupOf (stabilizer d.radical v)).map f ≤ unipotent ∧
        (∀ A : Subgroup (stabilizer d.radical v),
          (centralizer (A : Set (stabilizer d.radical v))).relIndex
            ((U d.radical v).subgroupOf (stabilizer d.radical v)) =
            2 ^ BinaryOffender.fixedCodim (restrictScalars (k := ZMod 2)
              (symplecticNatural (k := B.Carrier) 2)) (A.map f)) ∧
    let P := (CentralRootGeometry.wing (F := B.Carrier) true).map unipotent.subtype
    let D := (P.comap f).map (stabilizer d.radical v).subtype
    let J := Subgroup.SmallMover.join (U d.radical v) (Q d.radical v)
      (Q d.radical w) (Nat.card F^2)
    J ≤ D ∧ Z d.radical e₁ ≤ D ∧ Z d.radical e₂ ≤ D ∧
    ∃ g ∈ Ltilde d.radical v, ∃ x ∈ Ltilde d.radical v, ∃ c : Sp B.Carrier,
      ((J.map (MulAut.conj g).toMonoidHom ⊔ Z d.radical e₁) ⊔
        (Z d.radical e₁).map (MulAut.conj x).toMonoidHom = stabilizer d.radical v) ∧
      (D.map (MulAut.conj g).toMonoidHom ⊔
        (D.map (MulAut.conj g).toMonoidHom).map (MulAut.conj x⁻¹).toMonoidHom = stabilizer d.radical v) ∧
      ((Z d.radical v ⊓ centralizer (J.map (MulAut.conj g).toMonoidHom : Set (FreeAmalgam d.radical))) ⊓
        centralizer ((J.map (MulAut.conj g).toMonoidHom).map
          (MulAut.conj x⁻¹).toMonoidHom : Set (FreeAmalgam d.radical)) =
          Z d.radical v ⊓ centralizer (stabilizer d.radical v : Set (FreeAmalgam d.radical))) ∧
      x ∈ normalizer (D : Set (FreeAmalgam d.radical)) ∧
      x ∈ (planeParabolic.comap f).map (stabilizer d.radical v).subtype ∧
      ((J.map (MulAut.conj g).toMonoidHom ⊔ Z d.radical e₁) ⊔ Z d.radical e₂ =
        stabilizer d.radical v) ∧
      (((J.map (MulAut.conj g).toMonoidHom).map (MulAut.conj x⁻¹).toMonoidHom ⊔
        Z d.radical e₁) ⊔ Z d.radical e₂ = stabilizer d.radical v) ∧
      (((D.subgroupOf (stabilizer d.radical v)).map f).map (MulAut.conj c).toMonoidHom =
        P.map (MulAut.conj (TwoConjugate.opposition (F := B.Carrier))).toMonoidHom) ∧
      ((((D.map (MulAut.conj g).toMonoidHom).subgroupOf (stabilizer d.radical v)).map f).map
        (MulAut.conj c).toMonoidHom = P) ∧
      ((((Z d.radical e₁).subgroupOf (stabilizer d.radical v)).map f).map
        (MulAut.conj c).toMonoidHom = RootSubgroup.group 1) ∧
      (((((Z d.radical e₁).map (MulAut.conj x).toMonoidHom).subgroupOf
        (stabilizer d.radical v)).map f).map (MulAut.conj c).toMonoidHom = RootSubgroup.group 3) ∧
      ∃ r ∈ Ltilde d.radical v, ∃ c' : Sp B.Carrier,
        ((r=g⁻¹ ∧ c'=c) ∨ ∃ xs : stabilizer d.radical v,
          xs.val=x ∧ r=g⁻¹*x ∧ c'=c*f xs) ∧
        let a' := act d.radical r (p.walk.getVert 2)
        let s := act d.radical r w
        Adjacent d.radical v s ∧ Adjacent d.radical a' s ∧
        (¬ Z d.radical e₁ ≤ normalizer
          ((Z d.radical a' ⊔ Z d.radical v : Subgroup (FreeAmalgam d.radical)) : Set _)) ∧
        ((Subgroup.SmallMover.join (U d.radical v) (Q d.radical v)
          (Q d.radical s) (Nat.card F^2) ⊔ Z d.radical e₁) ⊔ Z d.radical e₂ = stabilizer d.radical v) ∧
        (((D.subgroupOf (stabilizer d.radical v)).map f).map (MulAut.conj c').toMonoidHom =
          P.map (MulAut.conj (TwoConjugate.opposition (F := B.Carrier))).toMonoidHom) ∧
        ((((D.map (MulAut.conj r⁻¹).toMonoidHom).subgroupOf (stabilizer d.radical v)).map f).map
          (MulAut.conj c').toMonoidHom = P) ∧
        ((((Z d.radical e₁).subgroupOf (stabilizer d.radical v)).map f).map
          (MulAut.conj c').toMonoidHom ≤ P.map
            (MulAut.conj (TwoConjugate.opposition (F := B.Carrier))).toMonoidHom) ∧
        ((((Z d.radical e₂).subgroupOf (stabilizer d.radical v)).map f).map
          (MulAut.conj c').toMonoidHom ≤ P.map
            (MulAut.conj (TwoConjugate.opposition (F := B.Carrier))).toMonoidHom) ∧
        ∃ back : CriticalPath d.radical geometry a' (p.walk.getVert 2),
          back.walk.getVert 1=s ∧
          ∀ i ≤ p.walk.length-2, back.walk.getVert (i+2)=p.walk.getVert i := by
  classical
  have hb4 : 4 ≤ geometry.b d.radical := by omega
  have hl : p.walk.length=4 := p.length_eq_b.trans hb
  have hvw : Adjacent d.radical v w := by
    rw [←hfirst]
    simpa only [SimpleGraph.Walk.getVert_zero] using (cosetGraph_adj d.radical _ _).mp
      (p.walk.adj_getVert_succ (by omega : 0<p.walk.length))
  have hmw : Adjacent d.radical (p.walk.getVert 2) w := by
    rw [←hfirst]
    exact adjacent_symm d.radical ((cosetGraph_adj d.radical _ _).mp
      (p.walk.adj_getVert_succ (by omega : 1<p.walk.length)))
  have hsmall₁ : (Q d.radical v).relIndex (Z d.radical e₁) < Nat.card F^2 := by
    rw [(h.replacement_distance_four_fixed_critical_indices d hb p.start_color hfixed p).2]
    have hq : 1<Nat.card F := Finite.one_lt_card
    nlinarith
  have hsmall₂ : (Q d.radical v).relIndex (Z d.radical e₂) < Nat.card F^2 := by
    rw [(h.replacement_distance_four_fixed_critical_indices d hb p.start_color hfixed companion).2]
    have hq : 1<Nat.card F := Finite.one_lt_card
    nlinarith
  obtain ⟨B,hB,f,hf,hfQ,hTf,hindex,hcore,hTP,hquad,hmax⟩ :=
    h.replacement_maximizing_parabolic d geometry hb4 p.start_color hvw
  have hJplane := h.replacement_small_mover_le_maximizing_plane_of_index_le d
    geometry hb4 p.start_color hvw B hB f hfQ hTf hindex hmax hJm
  let S := stabilizer d.radical v
  let P := (CentralRootGeometry.wing (F := B.Carrier) true).map unipotent.subtype
  let D := (P.comap f).map S.subtype
  let J := Subgroup.SmallMover.join (U d.radical v) (Q d.radical v)
    (Q d.radical w) (Nat.card F^2)
  have hJS : J ≤ S := (Subgroup.SmallMover.join_le _ _ _ _).trans
    (fun _ hx => hx.2 v (adjacent_symm d.radical hvw))
  have hDS : D ≤ S := (map_le_range _ _).trans_eq (range_subtype _)
  have hJD : J ≤ D := by
    have hh := map_mono (f := S.subtype) hJplane
    rwa [map_subgroupOf_eq_of_le hJS] at hh
  have hE₁D : Z d.radical e₁ ≤ D :=
    (h.replacement_root_endpoint_le_small_mover d p hb4 hvw hfirst hsmall₁
      B hB f hf hTf hindex hJplane).trans hJD
  have hE₂D : Z d.radical e₂ ≤ D :=
    (h.replacement_root_endpoint_le_small_mover d companion hb4 hvw hcfirst hsmall₂
      B hB f hf hTf hindex hJplane).trans hJD
  obtain ⟨g,hg,x,hx,hgen,hpair,hfix,hxn,hxp,hprescribed₁,hprescribed₂,c,hDc,hDgc,hEc,hExc⟩ :=
    h.replacement_smaller_prescribed_root_selection d p companion hb4 hvw hfirst hcfirst
      hsmall₁ hsmall₂ B hB f hf hfQ hTf hindex hJplane hJlarge hne
  refine ⟨B,hB,f,hf,hfQ,hTf,hindex,hJD,hE₁D,hE₂D,g,hg,x,hx,c,hgen,hpair,hfix,
    hxn,hxp,hprescribed₁,hprescribed₂,hDc,hDgc,hEc,hExc,?_⟩
  let m := p.walk.getVert 2
  let s₁ := act d.radical g⁻¹ w
  let a₁ := act d.radical g⁻¹ m
  let s₂ := act d.radical x s₁
  let a₂ := act d.radical x a₁
  have hgS : g ∈ S := Ltilde_le_stabilizer v hg
  have hxS : x ∈ S := Ltilde_le_stabilizer v hx
  have hgv : act d.radical g⁻¹ v=v := S.inv_mem hgS
  have hxv : act d.radical x v=v := hxS
  have hv₁ : Adjacent d.radical v s₁ := by
    rw [←hgv]
    exact (adjacent_act_iff d.radical g⁻¹ _ _).mpr hvw
  have ha₁ : Adjacent d.radical a₁ s₁ := (adjacent_act_iff d.radical g⁻¹ _ _).mpr hmw
  have hv₂ : Adjacent d.radical v s₂ := by
    rw [←hxv]
    exact (adjacent_act_iff d.radical x _ _).mpr hv₁
  have ha₂ : Adjacent d.radical a₂ s₂ := (adjacent_act_iff d.radical x _ _).mpr ha₁
  have hn₁ : ¬ S ≤ normalizer
      ((Z d.radical a₁ ⊔ Z d.radical v : Subgroup (FreeAmalgam d.radical)) : Set _) := by
    have hh := nonnormal_map_conj S (Z d.radical m ⊔ Z d.radical v)
      (h.replacement_path_neighbor_join_not_normal_of_four_le d p hb4) hgS
    have hZv : (Z d.radical v).map (MulAut.conj g).toMonoidHom=Z d.radical v := by
      simpa only [hgv,inv_inv] using (Z_act d.radical g⁻¹ v).symm
    rwa [Subgroup.map_sup,hZv,←show Z d.radical a₁ =
      (Z d.radical m).map (MulAut.conj g).toMonoidHom by simp only [a₁,Z_act,inv_inv]] at hh
  have complete (r : FreeAmalgam d.radical) (hr : r ∈ Ltilde d.radical v)
      (c' : Sp B.Carrier)
      (hchoice : (r=g⁻¹ ∧ c'=c) ∨ ∃ xs : S, xs.val=x ∧ r=g⁻¹*x ∧ c'=c*f xs)
      (hn : ¬ Z d.radical e₁ ≤ normalizer
        ((Z d.radical (act d.radical r m) ⊔ Z d.radical v : Subgroup (FreeAmalgam d.radical)) : Set _))
      (hpres : (J.map (MulAut.conj r⁻¹).toMonoidHom ⊔ Z d.radical e₁) ⊔ Z d.radical e₂=S)
      (hDpos : ((D.subgroupOf S).map f).map (MulAut.conj c').toMonoidHom =
        P.map (MulAut.conj (TwoConjugate.opposition (F := B.Carrier))).toMonoidHom)
      (hDrpos : (((D.map (MulAut.conj r⁻¹).toMonoidHom).subgroupOf S).map f).map
        (MulAut.conj c').toMonoidHom=P) :
      ∃ r ∈ Ltilde d.radical v, ∃ c' : Sp B.Carrier,
        ((r=g⁻¹ ∧ c'=c) ∨ ∃ xs : S, xs.val=x ∧ r=g⁻¹*x ∧ c'=c*f xs) ∧
        let a' := act d.radical r m
        let s := act d.radical r w
        Adjacent d.radical v s ∧ Adjacent d.radical a' s ∧
        (¬ Z d.radical e₁ ≤ normalizer
          ((Z d.radical a' ⊔ Z d.radical v : Subgroup (FreeAmalgam d.radical)) : Set _)) ∧
        ((Subgroup.SmallMover.join (U d.radical v) (Q d.radical v)
          (Q d.radical s) (Nat.card F^2) ⊔ Z d.radical e₁) ⊔ Z d.radical e₂=S) ∧
        (((D.subgroupOf S).map f).map (MulAut.conj c').toMonoidHom =
          P.map (MulAut.conj (TwoConjugate.opposition (F := B.Carrier))).toMonoidHom) ∧
        ((((D.map (MulAut.conj r⁻¹).toMonoidHom).subgroupOf S).map f).map
          (MulAut.conj c').toMonoidHom=P) ∧
        ((((Z d.radical e₁).subgroupOf S).map f).map (MulAut.conj c').toMonoidHom ≤
          P.map (MulAut.conj (TwoConjugate.opposition (F := B.Carrier))).toMonoidHom) ∧
        ((((Z d.radical e₂).subgroupOf S).map f).map (MulAut.conj c').toMonoidHom ≤
          P.map (MulAut.conj (TwoConjugate.opposition (F := B.Carrier))).toMonoidHom) ∧
        ∃ back : CriticalPath d.radical geometry a' m,
          back.walk.getVert 1=s ∧
          ∀ i ≤ p.walk.length-2, back.walk.getVert (i+2)=p.walk.getVert i := by
    have hrv : act d.radical r v=v := Ltilde_le_stabilizer v hr
    have hvs : Adjacent d.radical v (act d.radical r w) := by
      rw [←hrv]
      exact (adjacent_act_iff d.radical r _ _).mpr hvw
    have has : Adjacent d.radical (act d.radical r m) (act d.radical r w) :=
      (adjacent_act_iff d.radical r _ _).mpr hmw
    have hJr : Subgroup.SmallMover.join (U d.radical v) (Q d.radical v)
        (Q d.radical (act d.radical r w)) (Nat.card F^2) = J.map (MulAut.conj r⁻¹).toMonoidHom := by
      simpa only [hrv] using mover_act d.radical r v w (Nat.card F^2)
    refine ⟨r,hr,c',hchoice,hvs,has,hn,?_,hDpos,hDrpos,?_,?_,?_⟩
    · rwa [hJr]
    · exact hDpos ▸ map_mono (map_mono (comap_mono hE₁D))
    · exact hDpos ▸ map_mono (map_mono (comap_mono hE₂D))
    · exact prescribed_far_backward h d p hb hvs has r hr rfl hfixed hn
  by_cases hn : Z d.radical e₁ ≤ normalizer
      ((Z d.radical a₁ ⊔ Z d.radical v : Subgroup (FreeAmalgam d.radical)) : Set _)
  · have hn₂ : ¬ Z d.radical e₁ ≤ normalizer
        ((Z d.radical a₂ ⊔ Z d.radical v : Subgroup (FreeAmalgam d.radical)) : Set _) := by
      intro hh
      have he := paired_endpoint_normalizes_first_join x hxS hh
      have hJedge : J.map (MulAut.conj g).toMonoidHom ≤ Q d.radical s₁ := by
        simpa only [s₁,Q_act,inv_inv] using map_mono (f := (MulAut.conj g).toMonoidHom)
          (Subgroup.SmallMover.join_le (U d.radical v) (Q d.radical v) (Q d.radical w) (Nat.card F^2))
      apply hn₁
      change stabilizer d.radical v ≤ _
      rw [←hgen]
      refine sup_le (sup_le (hJedge.trans (edge_normalizes_neighbor_seed_join hv₁ ha₁)) hn) ?_
      simpa only [Z_act,inv_inv] using he
    let xs : S := ⟨x,hxS⟩
    let gs : S := ⟨g,hgS⟩
    have hcoords := prescribed_second_coordinate S D hDS f gs xs hxn c
    refine complete (g⁻¹*x) ((Ltilde d.radical v).mul_mem ((Ltilde d.radical v).inv_mem hg) hx)
      (c*f xs) (Or.inr ⟨xs,rfl,rfl,rfl⟩) ?_ ?_ (hcoords.1.trans hDc) ?_
    · simpa only [act_mul] using hn₂
    · simpa only [_root_.mul_inv_rev,inv_inv,←prescribed_map_conj_mul] using hprescribed₂
    · simpa only [_root_.mul_inv_rev,inv_inv,←prescribed_map_conj_mul] using hcoords.2.trans hDgc
  · exact complete g⁻¹ ((Ltilde d.radical v).inv_mem hg) c (Or.inl ⟨rfl,rfl⟩) hn
      (by simpa only [inv_inv] using hprescribed₁) hDc (by simpa only [inv_inv] using hDgc)

end CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
