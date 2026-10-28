module
public import CFSG.Quasithin.ChapterJ.Section05.SourceAction.Faithful
public import Theory.GroupAction.ThreeSuborbits

/-!
# The actual Rudvalis rank-three action

The preceding source orbit theorem gives exactly three F-orbits on G/F.
The unchanged element q has first stabilizer F₁ and exchanges the edge;
the second stabilizer is the native mixed PSL₂(25)⁺. The action is faithful
by the derived-Tits kernel argument and primitive by the three subdegrees.
Only genuine preceding marked J.4.7 recognition remains as an input.

Source: Aschbacher–Smith Definition J.5.1 and J.5.4(3), pp.445–446.
-/

@[expose] public section
noncomputable section
open Subgroup MulAction
namespace CFSG.Quasithin.ChapterJ.Section05
open RuSubgroup Centralizers.Choices Tits.ExceptionalParabolics.FullRee
variable {G:Type*} [Group G] [Finite G]

/-- Definition J.5.1 on the unchanged original coset space. -/
structure RudvalisAction (F:Subgroup G) (δ γ:Cosets F) where
  marking : F≃*ReeF4.Model 0
  first_marked : (stabilizer F δ).map marking.toMonoidHom=first
  second_plus : Nonempty (stabilizer F γ≃*Tits.Max4Outer.Mixed.Plus)
  degree : Nat.card (Cosets F)=4060
  first_length : Nat.card (orbit F δ)=1755
  second_length : Nat.card (orbit F γ)=2304
  partition : orbit F γ=(({basePoint F}:Set (Cosets F))∪orbit F δ)ᶜ
  faithful : FaithfulSMul G (Cosets F)
  primitive : IsPreprimitive G (Cosets F)
  rank_three : Nat.card (orbitRel.Quotient F (Cosets F))=3

omit [Finite G] in
theorem basePoint_not_mem_orbit {F:Subgroup G} {q:G} (hq:q∉F) :
    basePoint F∉orbit F (q•basePoint F) := by
  rintro ⟨a,ha⟩
  have haf:(a:G)•basePoint F=basePoint F:=
    (show (a:G)∈stabilizer G (basePoint F) from (stabilizer_quotient F).symm ▸ a.property)
  have he:q•basePoint F=basePoint F:=smul_left_cancel a (ha.trans haf.symm)
  exact hq ((stabilizer_quotient F) ▸ he)

omit [Finite G] in
theorem basePoint_fixed (F:Subgroup G) (a:F) : a•basePoint F=basePoint F :=
  (show (a:G)∈stabilizer G (basePoint F) from (stabilizer_quotient F).symm ▸ a.property)

omit [Finite G] in
theorem orbit_stabilizer_base (F:Subgroup G) (x:Cosets F) :
    orbit (stabilizer G (basePoint F)) x=orbit F x := by
  have he:stabilizer G (basePoint F)=F:=stabilizer_quotient F
  ext y
  constructor
  · rintro ⟨g,hg⟩; exact ⟨⟨g,he.le g.property⟩,hg⟩
  · rintro ⟨g,hg⟩; exact ⟨⟨g,he.ge g.property⟩,hg⟩

/-- The original element q has the marked parabolic stabilizer and exchanges the edge. -/
theorem SourceChoice.first_point_data {d:LocalSetup G} (p:Plane d) (s:SourceChoice p)
    (B5:Sylow 5 d.toTypeRuSetup.H) (hi:∀a∈B5Image B5,s.v*a*s.v⁻¹=a⁻¹)
    (X:Sylow 3 p.parabolic) (e:p.F B5 X≃*ReeF4.Model 0) {q:G} (hq:q∈d.toTypeRuSetup.Q)
    (ho:Nat.card (orbit (p.F B5 X) (q•basePoint (p.F B5 X)))=1755) :
    stabilizer (p.F B5 X) (q•basePoint (p.F B5 X))=
      (p.F₁ B5).subgroupOf (p.F B5 X) ∧
      q•(q•basePoint (p.F B5 X))=basePoint (p.F B5 X) := by
  let F:=p.F B5 X
  let M:=p.F₁ B5
  let J:=M⊔d.toTypeRuSetup.Q
  have hMF:M≤F:=le_sup_left
  have hMJ:M≤J:=le_sup_left
  have hj:q∈J:=(show d.toTypeRuSetup.Q≤J from le_sup_right) hq
  have hindex:M.relIndex J=2:=s.F₁_relIndex_sup_Q p B5 hi
  let :(M.subgroupOf J).Normal:=normal_of_index_eq_two hindex
  have hnorm:q∈normalizer (M:Set G):=le_normalizer_of_normal_subgroupOf hMJ hj
  have hMmap:M.map (MulAut.conj q).toMonoidHom=M:=mem_normalizer_iff_map_conj_eq.mp hnorm
  have hle:M.subgroupOf F≤stabilizer F (q•basePoint F):=by
    intro m hm
    change (m:G)∈stabilizer G (q•basePoint F)
    rw [stabilizer_smul_eq_stabilizer_map_conj,stabilizer_quotient]
    exact (hMmap ▸ map_mono hMF) hm
  have hcard:Nat.card (M.subgroupOf F)=20480:=by
    rw [Nat.card_congr (subgroupOfEquivOfLe hMF).toEquiv]
    exact s.card_F₁ p B5 hi
  have hs:Nat.card (stabilizer F (q•basePoint F))=20480:=by
    have hh:=Nat.card_congr (orbitProdStabilizerEquivGroup F (q•basePoint F))
    rw [Nat.card_prod,ho] at hh
    have hF:Nat.card F=35942400:=
      (Nat.card_congr e.toEquiv).trans group_card
    rw [hF] at hh
    omega
  have hsq:q^2∈M:=(M.subgroupOf J).sq_mem_of_index_two hindex (⟨q,hj⟩:J)
  refine ⟨(eq_of_le_of_card_ge hle (by rw [hcard,hs])).symm,?_⟩
  rw [← mul_smul,← pow_two]
  exact (show q^2∈stabilizer G (basePoint F) from (stabilizer_quotient F).symm ▸ hMF hsq)

/-- J.5.4(3), with the same original q and g and no rank-three premise. -/
theorem SourceChoice.source_rank_three {d:LocalSetup G} (p:Plane d) (s:SourceChoice p)
    (B5:Sylow 5 d.toTypeRuSetup.H) (hi:∀a∈B5Image B5,s.v*a*s.v⁻¹=a⁻¹)
    (X:Sylow 3 p.parabolic) (e:p.F B5 X≃*ReeF4.Model 0)
    (hmark:((p.F₁ B5).subgroupOf (p.F B5 X)).map e.toMonoidHom=first)
    (P:Sylow 5 (p.F B5 X)) :
    ∃q g:G,q∈d.toTypeRuSetup.Q ∧ q∉p.F B5 X ∧
      g∈normalizer (((P:Subgroup (p.F B5 X)).map (p.F B5 X).subtype):Set G) ∧
      g∉p.F B5 X ∧ q•(q•basePoint (p.F B5 X))=basePoint (p.F B5 X) ∧
      Nonempty (RudvalisAction (p.F B5 X)
        (q•basePoint (p.F B5 X)) (g•basePoint (p.F B5 X))) := by
  obtain ⟨q,g,hq,hqF,hg,hgF,hcos,hfirst,hstab,hsecond,hrem,hplus,hSyl⟩:=
    SourceChoice.source_second_orbit_plus p s B5 hi X e hmark P
  have hdata:=SourceChoice.first_point_data p s B5 hi X e hq hfirst
  let F:=p.F B5 X
  have hbase:stabilizer G (basePoint F)=F:=stabilizer_quotient F
  have hab:=basePoint_not_mem_orbit hqF
  have hrank:Nat.card (orbitRel.Quotient F (Cosets F))=3:=
    ThreeSuborbits.rank_three (basePoint F) (q•basePoint F) (g•basePoint F)
      (basePoint_fixed F) hab hrem
  have hprim:IsPreprimitive G (Cosets F):=by
    let sizes:Fin 3→ℕ:=![1,1755,2304]
    apply Atlas.GroupTheory.primitive_of_rankThree_nondivisibility (basePoint F)
      (ThreeSuborbits.family (K:=F) (basePoint F) (q•basePoint F))
      ((ThreeSuborbits.family_zero _ _ _).mpr rfl) ?_ sizes rfl ?_ ?_ ?_ ?_
    · intro x y hh
      obtain ⟨f,hf⟩:=ThreeSuborbits.transitive (basePoint F) (q•basePoint F)
        (g•basePoint F) hab hrem hh
      exact ⟨⟨f,hbase.ge f.property⟩,hf⟩
    · intro i
      simpa only [F,hfirst,hsecond,sizes] using
        ThreeSuborbits.fiber_card (basePoint F) (q•basePoint F) (g•basePoint F) hab hrem i
    · change Nat.card (Cosets F)=4060; exact hcos
    · rw [hcos]; change ¬1756∣4060; decide
    · rw [hcos]; change ¬2305∣4060; decide
  refine ⟨q,g,hq,hqF,hg,hgF,hdata.2,⟨?_⟩⟩
  exact ⟨e,hdata.1 ▸ hmark,hplus,hcos,hfirst,hsecond,hrem,
    source_cosets_faithful d B5 F
      (le_sup_right.trans (le_sup_left.trans le_sup_left))
      (le_sup_right.trans le_sup_left) e hqF,hprim,hrank⟩

end CFSG.Quasithin.ChapterJ.Section05
