module
public import Theory.GroupTheory.SylowNormalizerCommutingFamily
public import Mathlib.Logic.Equiv.Fin.Basic
public import Mathlib.Data.Finite.Perm
public import Theory.GroupTheory.Recognition.JankoFour.SourceComparison.ToddCorrection
public import Theory.GroupTheory.Recognition.JankoFour.SourceIncidence.LineClosure

/-!
# The original pointwise edge fixer and its cubic normalizer

The unique source line places the whole edge fixer in N_G(Z). The actual
five-point action has kernel K and is already induced by S=C_G(Z). Restricting
to S∩M gives the full permutation action on the other four points, with kernel
R. A constructed Sylow three-subgroup has normalizer equal to the selected
point stabilizer in S₄. Surjectivity on Sylow normalizers lifts this equality
through R. Combining it with N_G(Z)=KS gives B=K N_(S∩M)(Y), with every
subgroup embedded in the original ambient group and the original edge tM.

Source: Aschbacher–Segev, Invent. Math. 105 (1991), (5.1)(2) and the
normalizer argument in (8.2), pp.599–600,606. This supplies the subgroup
identification used to choose the Todd correction; full edge reversal and
global recognition require further comparison arguments.
-/

public section

open Subgroup
namespace Theory.GroupTheory.Recognition.JankoFour.SourceComparison
private def fourCycle : Equiv.Perm (Fin 4) := Equiv.swap 1 2 * Equiv.swap 2 3

private theorem fourCycle_order : orderOf fourCycle = 3 :=
  orderOf_eq_prime (by decide) (by decide)

private theorem four_normalizer :
    normalizer (zpowers fourCycle : Set (Equiv.Perm (Fin 4))) =
      MulAction.stabilizer (Equiv.Perm (Fin 4)) (0 : Fin 4) := by
  have forward : ∀ g : Equiv.Perm (Fin 4),
      (g*fourCycle*g⁻¹=1 ∨ g*fourCycle*g⁻¹=fourCycle ∨ g*fourCycle*g⁻¹=fourCycle^2) → g 0=0 := by
    decide +kernel
  have backward : ∀ g : Equiv.Perm (Fin 4), g 0=0 →
      g*fourCycle*g⁻¹=fourCycle ∨ g*fourCycle*g⁻¹=fourCycle⁻¹ := by
    decide +kernel
  ext g
  constructor
  · intro hg
    have hh := (mem_normalizer_iff.mp hg fourCycle).mp (mem_zpowers fourCycle)
    rw [mem_zpowers_iff_mem_range_orderOf,fourCycle_order] at hh
    obtain ⟨i,hi,he⟩ := Finset.mem_image.mp hh
    have hi' := Finset.mem_range.mp hi
    apply forward g
    interval_cases i
    · exact Or.inl (by simpa using he.symm)
    · exact Or.inr (Or.inl (by simpa using he.symm))
    · exact Or.inr (Or.inr he.symm)
  · intro hg
    apply mem_normalizer_iff_map_conj_eq.mpr
    rw [MonoidHom.map_zpowers]
    change zpowers (g*fourCycle*g⁻¹)=_
    rcases backward g hg with he | he
    · rw [he]
    · rw [he,zpowers_inv]

private noncomputable def fourSylow : Sylow 3 (Equiv.Perm (Fin 4)) := by
  have hc : Nat.card (zpowers fourCycle)=3 := (Nat.card_zpowers _).trans fourCycle_order
  apply (IsPGroup.of_card (G := zpowers fourCycle) (p := 3) (n := 1) hc).toSylow
  have hi := (zpowers fourCycle).card_mul_index
  rw [hc,Nat.card_perm,Nat.card_fin] at hi
  norm_num [Nat.factorial] at hi
  have he : (zpowers fourCycle).index=8 := by omega
  rw [he]
  decide

private theorem fourSylow_coe : (fourSylow : Subgroup (Equiv.Perm (Fin 4)))=zpowers fourCycle := rfl

/-- A Sylow three-normalizer in the full four-point action is the prescribed
point stabilizer. The Sylow is constructed, not supplied as a comparison input. -/
theorem fourPoint_sylow_normalizer {β : Type*} [Finite β] (hc : Nat.card β=4) (y : β) :
    ∃ P : Sylow 3 (Equiv.Perm β), normalizer (P : Set (Equiv.Perm β)) =
      MulAction.stabilizer (Equiv.Perm β) y := by
  classical
  let := Fintype.ofFinite β
  let e₀ : β ≃ Fin 4 := Fintype.equivFinOfCardEq (by rwa [←Nat.card_eq_fintype_card])
  let e := e₀.trans (Equiv.swap (e₀ y) 0)
  have hey : e y=0 := Equiv.swap_apply_left _ _
  let f : Equiv.Perm (Fin 4) →* Equiv.Perm β := e.symm.permCongrHom
  let P := fourSylow.mapSurjective (f := f) e.symm.permCongr.surjective
  refine ⟨P,?_⟩
  change normalizer (↑((fourSylow : Subgroup (Equiv.Perm (Fin 4))).map f) : Set (Equiv.Perm β))=_
  rw [←fourSylow.normalizer_map_surjective f e.symm.permCongr.surjective]
  change (normalizer (↑(fourSylow : Subgroup (Equiv.Perm (Fin 4))) : Set (Equiv.Perm (Fin 4)))).map f=_
  rw [fourSylow_coe,four_normalizer]
  ext g
  constructor
  · rintro ⟨k,hk,rfl⟩
    change e.symm (k (e y))=y
    rw [hey,show k 0=0 from hk,←hey,e.symm_apply_apply]
  · intro hg
    refine ⟨e.permCongr g,?_,?_⟩
    · change e (g (e.symm 0))=0
      rw [←hey,e.symm_apply_apply,show g y=y from hg,hey]
    · apply Equiv.ext
      intro x
      change e.symm (e (g (e.symm (e x))))=g x
      simp only [e.symm_apply_apply]

/-- Pull the four-point normalizer back through the literal action. -/
theorem fourPoint_normalizer_preimage {A β : Type*} [Group A] [Finite A] [Finite β]
    (hc : Nat.card β=4) (f : A →* Equiv.Perm β) (hf : Function.Surjective f) (y : β) :
    ∃ Y : Sylow 3 A, (MulAction.stabilizer (Equiv.Perm β) y).comap f =
      f.ker ⊔ normalizer (Y : Set A) := by
  obtain ⟨P,hP⟩ := fourPoint_sylow_normalizer hc y
  obtain ⟨Y,hY⟩ := Sylow.mapSurjective_surjective hf 3 P
  refine ⟨Y,?_⟩
  have he : (Y : Subgroup A).map f = (P : Subgroup (Equiv.Perm β)) := congrArg Sylow.toSubgroup hY
  rw [←hP]
  change (normalizer (↑(P : Subgroup (Equiv.Perm β)) : Set (Equiv.Perm β))).comap f=_
  rw [←he,←Y.normalizer_map_surjective f hf,comap_map_eq,sup_comm]

end Theory.GroupTheory.Recognition.JankoFour.SourceComparison

namespace Theory.GroupTheory.Recognition.JankoFour.SourceComparison
open Subgroup SourceRecognition LocalGeometry LocalGeometry.LocalSubgroups SourceCycleBase GraphUniquenessSystem
open scoped Pointwise
variable {G : Type*} [Group G] [Finite G] {z : G} {h : IsTypeJ4 z}
variable (a : SourceIncidence.LocalData h)

/-- The literal pointwise edge fixer, with the inverse required by left cosets. -/
@[expose] def lineEdgeGroup (t : G) : Subgroup G :=
  a.P.M ⊓ a.P.M.comap (MulAut.conj t⁻¹).toMonoidHom

/-- The centralizer factor at the original point of the original line. -/
@[expose] def lineCentralPoint : Subgroup G := a.d.S ⊓ a.P.M

@[expose] def lineBase : a.LinePoints := ⟨Cosets.vertex a.P.M 1,⟨1,rfl,rfl⟩⟩

/-- The other four points, still ambient left cosets on the same line. -/
abbrev OtherLinePoints := {y : a.LinePoints // y ≠ lineBase a}

private theorem S_le_line : a.d.S ≤ a.L.G₂ := by
  rw [a.line_normalizer]
  exact Subgroup.centralizer_le_normalizer _

private def centralPointInLine : lineCentralPoint a →* a.L.G₂ where
  toFun s := ⟨s,S_le_line a s.property.1⟩
  map_one' := rfl
  map_mul' _ _ := rfl

private theorem centralPoint_fixes_base (s : lineCentralPoint a) :
    a.linePointAction (centralPointInLine a s) (lineBase a)=lineBase a := by
  apply Subtype.ext
  rw [a.linePointAction_apply]
  change (s : G) • Cosets.vertex a.P.M 1=Cosets.vertex a.P.M 1
  rw [Cosets.smul_vertex,mul_one]
  exact (Cosets.vertex_eq_base _ _).mpr s.property.2

/-- Restriction of the actual five-point action to the four points other than M. -/
noncomputable def centralPointAction : lineCentralPoint a →* Equiv.Perm (OtherLinePoints a) where
  toFun s := (a.linePointAction (centralPointInLine a s)).subtypePerm (fun y => by
    calc
      a.linePointAction (centralPointInLine a s) y ≠ lineBase a ↔
          a.linePointAction (centralPointInLine a s) y ≠
            a.linePointAction (centralPointInLine a s) (lineBase a) := by
              rw [centralPoint_fixes_base]
      _ ↔ y ≠ lineBase a := (a.linePointAction (centralPointInLine a s)).injective.ne_iff)
  map_one' := Equiv.ext fun y => Subtype.ext (by
    change a.linePointAction (centralPointInLine a 1) y.val=y.val
    rw [map_one,map_one]; rfl)
  map_mul' s r := Equiv.ext fun y => Subtype.ext (by
    change a.linePointAction (centralPointInLine a (s*r)) y.val =
      a.linePointAction (centralPointInLine a s) (a.linePointAction (centralPointInLine a r) y.val)
    rw [map_mul,map_mul]; rfl)

theorem centralPointAction_apply (s : lineCentralPoint a) (y : OtherLinePoints a) :
    (centralPointAction a s y).val.val=(s : G) • y.val.val :=
  a.linePointAction_apply (centralPointInLine a s) y.val

theorem otherLinePoints_card : Nat.card (OtherLinePoints a)=4 := by
  classical
  let := Fintype.ofFinite a.LinePoints
  rw [Nat.card_eq_fintype_card,Fintype.card_subtype_compl]
  have hc : Fintype.card a.LinePoints=5 := by rw [←Nat.card_eq_fintype_card]; exact a.line_card _
  simp only [hc,Fintype.card_unique]

/-- S∩M induces the entire permutation group on the other four actual points. -/
theorem centralPointAction_surjective : Function.Surjective (centralPointAction a) := by
  classical
  intro p
  let q : Equiv.Perm a.LinePoints := Equiv.Perm.ofSubtype p
  obtain ⟨s,n,hs,hn⟩ := a.exists_S_linePointAction q
  have hfix : a.linePointAction n (lineBase a)=lineBase a := by
    rw [hn]
    exact Equiv.Perm.ofSubtype_apply_of_not_mem p (by simp)
  have hsm : (s : G) ∈ a.P.M := by
    have hh := congrArg Subtype.val hfix
    rw [a.linePointAction_apply] at hh
    change (n : G) • Cosets.vertex a.P.M 1=Cosets.vertex a.P.M 1 at hh
    rw [Cosets.smul_vertex,mul_one,hs] at hh
    exact (Cosets.vertex_eq_base _ _).mp hh
  let s' : lineCentralPoint a := ⟨s,s.property,hsm⟩
  refine ⟨s',?_⟩
  apply Equiv.ext
  intro y
  apply Subtype.ext
  change a.linePointAction (centralPointInLine a s') y.val = _
  have he : centralPointInLine a s'=n := Subtype.ext hs.symm
  rw [he,hn]
  exact Equiv.Perm.ofSubtype_apply_of_mem p y.property

/-- The four-point action retains precisely the original special radical R. -/
theorem centralPointAction_ker : (centralPointAction a).ker=a.d.R.subgroupOf (lineCentralPoint a) := by
  ext s
  change centralPointAction a s=1 ↔ (s : G) ∈ a.d.R
  constructor
  · intro hs
    have he : a.linePointAction (centralPointInLine a s)=1 := by
      apply Equiv.ext
      intro y
      by_cases hy : y=lineBase a
      · subst y; exact centralPoint_fixes_base a s
      · exact congrArg Subtype.val (Equiv.congr_fun hs (⟨y,hy⟩ : OtherLinePoints a))
    have hk : (s : G) ∈ a.d.K := by
      have hh := MonoidHom.mem_ker.mpr he
      rw [a.linePointAction_ker] at hh
      exact hh
    exact ⟨hk,s.property.1⟩
  · intro hs
    have he : a.linePointAction (centralPointInLine a s)=1 := by
      apply MonoidHom.mem_ker.mp
      rw [a.linePointAction_ker]
      exact hs.1
    apply Equiv.ext
    intro y
    apply Subtype.ext
    change a.linePointAction (centralPointInLine a s) y.val=y.val
    rw [he]; rfl

/-- Every edge fixer preserves its unique original line. -/
theorem lineEdgeGroup_le_line (t : G) (ht : t ∈ a.L.G₂) (hnt : t ∉ a.P.M) :
    lineEdgeGroup a t ≤ a.L.G₂ := by
  let x := Cosets.vertex a.P.M 1
  let y := Cosets.vertex a.P.M t
  let l := Cosets.vertex a.L.G₂ 1
  have hx : OnLine a.L x l := ⟨1,rfl,rfl⟩
  have hy : OnLine a.L y l := ⟨t,rfl,(Cosets.vertex_eq_base _ _).mpr ht⟩
  have hxy : x ≠ y := fun he => hnt ((Cosets.vertex_eq_base _ _).mp he.symm)
  obtain ⟨k,hk,huniq⟩ := a.unique_line x y ⟨hxy,l,hx,hy⟩
  have hlk := huniq l ⟨hx,hy⟩
  intro b hb
  have hbx : b • x=x := by
    change b • Cosets.vertex a.P.M 1=Cosets.vertex a.P.M 1
    rw [Cosets.smul_vertex,mul_one]
    exact (Cosets.vertex_eq_base _ _).mpr hb.1
  have hby : b • y=y := by
    have hh : b ∈ MulAction.stabilizer G (Cosets.vertex a.P.M t) := by
      rw [Cosets.stabilizer_vertex]; exact hb.2
    exact hh
  have he : b • l=l := (huniq (b • l) ⟨by
    simpa only [OnLine,hbx] using incident_smul b hx,by
    simpa only [OnLine,hby] using incident_smul b hy⟩).trans hlk.symm
  apply (Cosets.vertex_eq_base _ _).mp
  simpa only [l,Cosets.smul_vertex,mul_one] using he

/-- The line kernel fixes both ends of the actual edge. -/
theorem K_le_lineEdgeGroup (t : G) (ht : t ∈ a.L.G₂) : a.d.K ≤ lineEdgeGroup a t := by
  intro k hk
  have hn : k ∈ a.L.G₂ := a.line_normalizer.symm ▸ a.d.K_le_normalizer hk
  have hfix := (a.point_action_kernel ⟨k,hn⟩).mpr hk
  refine ⟨a.K_le_point hk,?_⟩
  rw [←Cosets.stabilizer_vertex]
  exact hfix _ ⟨t,rfl,(Cosets.vertex_eq_base _ _).mpr ht⟩

/-- The whole edge fixer is generated by K and its actual intersection with S. -/
theorem lineEdgeGroup_factorization (t : G) (ht : t ∈ a.L.G₂) (hnt : t ∉ a.P.M) :
    lineEdgeGroup a t=a.d.K ⊔ (a.d.S ⊓ lineEdgeGroup a t) := by
  apply le_antisymm
  · intro b hb
    obtain ⟨k,hk,s,hs,he⟩ := a.d.normalizer_product h b
      (a.line_normalizer ▸ lineEdgeGroup_le_line a t ht hnt hb)
    have hsB : s ∈ lineEdgeGroup a t := by
      have hh := (lineEdgeGroup a t).mul_mem
        ((lineEdgeGroup a t).inv_mem (K_le_lineEdgeGroup a t ht hk)) hb
      rw [←he,inv_mul_cancel_left] at hh
      exact hh
    rw [←he]
    exact mul_mem_sup hk ⟨hs,hsB⟩
  · exact sup_le (K_le_lineEdgeGroup a t ht) inf_le_right


private theorem R_le_centralPoint : a.d.R ≤ lineCentralPoint a :=
  fun _ hr => ⟨hr.2,a.K_le_point hr.1⟩

/-- The cubic is chosen in the original S∩M. Its ambient normalizer remains
relative to that same subgroup, rather than an unrelated copy of S₄. -/
theorem exists_lineEdge_normalizer (t : G) (ht : t ∈ a.L.G₂) (hnt : t ∉ a.P.M) :
    ∃ Y : Sylow 3 (lineCentralPoint a),
      lineEdgeGroup a t = a.d.K ⊔ (normalizer (Y : Set (lineCentralPoint a))).map
        (lineCentralPoint a).subtype := by
  let y : OtherLinePoints a := ⟨⟨Cosets.vertex a.P.M t,
    ⟨t,rfl,(Cosets.vertex_eq_base _ _).mpr ht⟩⟩,
    fun he => hnt ((Cosets.vertex_eq_base _ _).mp (congrArg Subtype.val he))⟩
  obtain ⟨Y,hY⟩ := fourPoint_normalizer_preimage (otherLinePoints_card a)
    (centralPointAction a) (centralPointAction_surjective a) y
  have hpre : (MulAction.stabilizer (Equiv.Perm (OtherLinePoints a)) y).comap
      (centralPointAction a) = (lineEdgeGroup a t).subgroupOf (lineCentralPoint a) := by
    ext s
    change centralPointAction a s y=y ↔ (s : G) ∈ lineEdgeGroup a t
    have he : centralPointAction a s y=y ↔
        (s : G) • Cosets.vertex a.P.M t=Cosets.vertex a.P.M t := by
      constructor
      · intro he
        exact (centralPointAction_apply a s y).symm.trans (congrArg (fun v => v.val.val) he)
      · intro he
        apply Subtype.ext
        apply Subtype.ext
        exact (centralPointAction_apply a s y).trans he
    rw [he]
    change _ ↔ (s : G) ∈ a.P.M ∧ (s : G) ∈ a.P.M.comap (MulAut.conj t⁻¹).toMonoidHom
    rw [←Cosets.stabilizer_vertex]
    exact (and_iff_right s.property.2).symm
  rw [hpre,centralPointAction_ker] at hY
  have he := congrArg (Subgroup.map (lineCentralPoint a).subtype) hY
  rw [subgroupOf_map_subtype,Subgroup.map_sup,map_subgroupOf_eq_of_le (R_le_centralPoint a)] at he
  have hleft : lineEdgeGroup a t ⊓ lineCentralPoint a=a.d.S ⊓ lineEdgeGroup a t := by
    ext g
    constructor
    · rintro ⟨hb,hs,hm⟩; exact ⟨hs,hb⟩
    · rintro ⟨hs,hb⟩; exact ⟨hb,hs,hb.1⟩
  rw [hleft] at he
  refine ⟨Y,?_⟩
  calc
    lineEdgeGroup a t = a.d.K ⊔ (a.d.S ⊓ lineEdgeGroup a t) :=
      lineEdgeGroup_factorization a t ht hnt
    _ = a.d.K ⊔ (a.d.R ⊔ (normalizer (Y : Set (lineCentralPoint a))).map
        (lineCentralPoint a).subtype) := by rw [he]
    _ = _ := by rw [←sup_assoc,sup_of_le_left (show a.d.R ≤ a.d.K from inf_le_left)]

/-- Mapping a relative normalizer into G gives the literal intersection with
the ambient normalizer of the same mapped cubic. -/
theorem lineCubic_normalizer_image (Y : Sylow 3 (lineCentralPoint a)) :
    (normalizer (Y : Set (lineCentralPoint a))).map (lineCentralPoint a).subtype =
      lineCentralPoint a ⊓ normalizer (↑((Y : Subgroup (lineCentralPoint a)).map
        (lineCentralPoint a).subtype) : Set G) := by
  let U := (Y : Subgroup (lineCentralPoint a)).map (lineCentralPoint a).subtype
  have hU : U ≤ lineCentralPoint a := map_subtype_le _
  have he : U.subgroupOf (lineCentralPoint a)=(Y : Subgroup (lineCentralPoint a)) :=
    Subgroup.comap_map_eq_self_of_injective (lineCentralPoint a).subtype_injective _
  change (normalizer (↑(Y : Subgroup (lineCentralPoint a)) : Set (lineCentralPoint a))).map _=
    lineCentralPoint a ⊓ normalizer (U : Set G)
  rw [←he,←subgroupOf_normalizer_eq hU,subgroupOf_map_subtype,inf_comm]

/-- The source formula B=K N_(S∩M)(Y), on the actual ambient embeddings. -/
theorem exists_lineEdge_ambient_normalizer (t : G) (ht : t ∈ a.L.G₂) (hnt : t ∉ a.P.M) :
    ∃ Y : Sylow 3 (lineCentralPoint a),
      lineEdgeGroup a t = a.d.K ⊔ (lineCentralPoint a ⊓ normalizer
        (↑((Y : Subgroup (lineCentralPoint a)).map (lineCentralPoint a).subtype) : Set G)) := by
  obtain ⟨Y,hY⟩ := exists_lineEdge_normalizer a t ht hnt
  exact ⟨Y,hY.trans (congrArg (a.d.K ⊔ ·) (lineCubic_normalizer_image a Y))⟩

end Theory.GroupTheory.Recognition.JankoFour.SourceComparison
