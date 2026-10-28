module

public import Theory.GroupTheory.Recognition.UnitaryFourThree.CubicGeometry.Irreducible

/-!
# The ten original cubic lines and their tangent hyperplane

The actual normalizer orbit of W has ten members and spans V. For any other
line L the stabilizer in D is exactly V∩D: the original TI Sylow intersection
and the common normalizer identify it without a chosen quotient action.
Thus D is transitive on the other nine lines. Since V is irreducible, these
nine cannot lie in the invariant hyperplane V∩D. Consequently W is the only
line in the orbit which lies in D. No orthogonal-module marking is assumed.
Source: Aschbacher, Sporadic Groups (1994),45.9–45.10,pp247–248.
-/

public section
open Subgroup
open scoped Pointwise
namespace Theory.GroupTheory.Recognition.UnitaryFourThree.CubicGeometry
variable {G:Type*} [Group G] [Finite G] {z:G} {h:IsType z} {P:Sylow 3 (centralizer z)}
namespace SourceConfiguration
variable (c:SourceConfiguration h P)
def kernelLines : Set (Subgroup G):=
  {L|∃g∈normalizer (c.toSourceData.V:Set G),L=c.toSourceData.W.map (MulAut.conj g).toMonoidHom}
omit [Finite G] in
theorem mem_kernelLines_iff (L : Subgroup G) : L ∈ c.kernelLines ↔
    ∃ g ∈ normalizer (c.V : Set G), L = c.W.map (MulAut.conj g).toMonoidHom := Iff.rfl
omit [Finite G] in
theorem line_mem_kernelLines : c.toSourceData.W∈c.kernelLines := by
  refine ⟨1,one_mem _,?_⟩
  simp

theorem kernelLines_le {L:Subgroup G} (hL:L∈c.kernelLines) : L≤c.toSourceData.V := by
  obtain ⟨g,hg,rfl⟩:=hL
  exact (map_mono c.line_le_kernel).trans_eq (mem_normalizer_iff_map_conj_eq.mp hg)

theorem kernelLines_card : Nat.card c.kernelLines=10 := by
  classical
  let V:=c.toSourceData.V
  let W:=c.toSourceData.W
  let M:=normalizer (V:Set G)
  let :MulAction G (Subgroup G):=MulAction.compHom (Subgroup G) MulAut.conj
  have he:c.kernelLines=MulAction.orbit M W:=by
    ext L
    constructor
    · rintro ⟨g,hg,he⟩
      exact ⟨⟨g,hg⟩,he.symm⟩
    · rintro ⟨g,hg⟩
      exact ⟨g,g.property,hg.symm⟩
  have hs:MulAction.stabilizer M W=(normalizer (W:Set G)).subgroupOf M:=by
    ext g
    exact mem_normalizer_iff_map_conj_eq.symm
  have hNM:normalizer (c.sylow:Set G)≤M:=c.common_normalizer.le.trans inf_le_left
  have hc:Nat.card (MulAction.stabilizer M W)=2916:=by
    rw[hs]
    have hh:(normalizer (W:Set G)).subgroupOf M=(normalizer (c.sylow:Set G)).subgroupOf M:=by
      rw[c.common_normalizer]
      ext x
      change (x:G)∈normalizer (W:Set G) ↔ (x:G)∈M∧(x:G)∈normalizer (W:Set G)
      exact ⟨fun hx=>⟨x.property,hx⟩,And.right⟩
    rw[hh,Nat.card_congr (subgroupOfEquivOfLe hNM).toEquiv]
    exact c.normalizer_card
  have hM:Nat.card M=29160:=by rw[c.quotient_card_mul_kernel,c.quotient_card]
  have hh:=(MulAction.stabilizer M W).index_mul_card
  rw[hc,hM] at hh
  rw[he,Nat.card_congr (MulAction.orbitEquivQuotientStabilizer M W)]
  change (MulAction.stabilizer M W).index=10
  omega

omit [Finite G] in
theorem kernelLines_invariant {L:Subgroup G} (hL:L∈c.kernelLines) (g:G)
    (hg:g∈normalizer (c.toSourceData.V:Set G)) :
    L.map (MulAut.conj g).toMonoidHom∈c.kernelLines := by
  obtain ⟨k,hk,rfl⟩:=hL
  refine ⟨g*k,mul_mem hg hk,?_⟩
  exact conjBy_conjBy _ k g

theorem kernelLines_span : sSup c.kernelLines=c.toSourceData.V := by
  let R:=sSup c.kernelLines
  have hRV:R≤c.toSourceData.V:=sSup_le fun L hL=>c.kernelLines_le hL
  have hMR:normalizer (c.toSourceData.V:Set G)≤normalizer (R:Set G):=by
    apply le_normalizer_iff.mpr
    intro g hg x hx
    have hr:R.map (MulAut.conj g).toMonoidHom≤R:=by
      apply map_le_iff_le_comap.mpr
      apply sSup_le
      intro L hL
      exact map_le_iff_le_comap.mp (le_sSup (c.kernelLines_invariant hL g hg))
    exact hr (mem_map_of_mem _ hx)
  rcases c.kernel_irreducible R hRV hMR with hb|he
  · have hh:=card_le_of_le (le_sSup c.line_mem_kernelLines)
    change Nat.card c.toSourceData.W≤Nat.card R at hh
    rw[c.line_card,hb,card_bot] at hh
    omega
  · exact he

theorem other_kernelLine_odd_stabilizer {L:Subgroup G} (hL:L∈c.kernelLines)
    (hne:L≠c.toSourceData.W) :
    c.toSourceData.D⊓normalizer (L:Set G)=c.toSourceData.V⊓c.toSourceData.D := by
  let V:=c.toSourceData.V
  let D:=c.toSourceData.D
  let Q:=c.toSourceData.Q
  let M:=normalizer (V:Set G)
  have hLV:L≤V:=c.kernelLines_le hL
  let :IsElementaryAbelian 3 V:=c.kernel_elementary
  have hQM:Q≤M:=(h.cubic_kernel_outside_fixed_planes P c.actors c.actors_eq
    c.odd_split c.odd_card c.odd_extraspecial).1
  have hDM:D≤M:=le_sup_right.trans hQM
  obtain ⟨g,hg,rfl⟩:=hL
  let T:Sylow 3 G:=g • c.sylow
  have hNQ:normalizer (Q:Set G)=M⊓normalizer (c.toSourceData.W:Set G):=by
    have hh:=c.common_normalizer
    change normalizer ((c.sylow:Subgroup G):Set G)=_ at hh
    rwa[c.sylow_eq] at hh
  have hNT:normalizer (T:Set G)=M⊓normalizer (c.toSourceData.W.map (MulAut.conj g).toMonoidHom:Set G):=by
    change normalizer (((c.sylow:Subgroup G).map (MulAut.conj g).toMonoidHom):Set G)=_
    rw[c.sylow_eq,←map_equiv_normalizer_eq Q (MulAut.conj g),hNQ,Subgroup.map_inf _ _ _ (MulAut.conj g).injective]
    have hm:M.map (MulAut.conj g).toMonoidHom=M:=mem_normalizer_iff_map_conj_eq.mp (M.le_normalizer hg)
    rw[hm,map_equiv_normalizer_eq]
  have hgN:g∉normalizer (Q:Set G):=by
    intro hn
    exact hne (mem_normalizer_iff_map_conj_eq.mp (hNQ.le hn).2)
  apply le_antisymm
  · intro x hx
    have hxT:x∈Q⊓(T:Subgroup G):=by
      have hh:=c.sylow.isPGroup'.inf_normalizer_sylow T
      rw[c.sylow_eq] at hh
      apply hh.le
      exact ⟨mem_sup_right hx.1,hNT.ge ⟨hDM hx.1,hx.2⟩⟩
    have hxV:x∈V:=by
      have hh:=c.sylow_intersection_eq_kernel g hg hgN
      apply hh.le
      change x∈Q⊓(c.sylow:Subgroup G).map (MulAut.conj g).toMonoidHom at hxT
      rwa[c.sylow_eq] at hxT
    exact ⟨hxV,hx.1⟩
  · intro x hx
    exact ⟨hx.2,centralizer_le_normalizer _ ((centralizer_le hLV) (V.le_centralizer hx.1))⟩

theorem other_kernelLine_orbit {L:Subgroup G} (hL:L∈c.kernelLines) (hne:L≠c.toSourceData.W) :
    ∀K∈c.kernelLines,K≠c.toSourceData.W→∃d∈c.toSourceData.D,K=L.map (MulAut.conj d).toMonoidHom := by
  classical
  let D:=c.toSourceData.D
  let V:=c.toSourceData.V
  let W:=c.toSourceData.W
  let A:=V⊓D
  let :MulAction G (Subgroup G):=MulAction.compHom (Subgroup G) MulAut.conj
  have hQM:c.toSourceData.Q≤normalizer (V:Set G):=(h.cubic_kernel_outside_fixed_planes P c.actors c.actors_eq
    c.odd_split c.odd_card c.odd_extraspecial).1
  have hDM:D≤normalizer (V:Set G):=le_sup_right.trans hQM
  have hDW:D≤normalizer (W:Set G):=by rw[c.odd_split];exact le_sup_left
  have hs:MulAction.stabilizer D L=A.subgroupOf D:=by
    ext d
    change L.map (MulAut.conj (d:G)).toMonoidHom=L ↔ (d:G)∈A
    have hm:(L.map (MulAut.conj (d:G)).toMonoidHom=L) ↔ (d:G)∈normalizer (L:Set G):=mem_normalizer_iff_map_conj_eq.symm
    rw[hm]
    have hh:=c.other_kernelLine_odd_stabilizer hL hne
    exact ⟨fun hd=>hh.le ⟨d.property,hd⟩,fun hd=>(hh.ge hd).2⟩
  have hc:Nat.card (MulAction.stabilizer D L)=27:=by
    rw[hs,Nat.card_congr (subgroupOfEquivOfLe (show A≤D from inf_le_right)).toEquiv]
    exact c.intersection_card
  have ho:Nat.card (MulAction.orbit D L)=9:=by
    have hh:=(MulAction.stabilizer D L).index_mul_card
    rw[hc,c.odd_card] at hh
    rw[Nat.card_congr (MulAction.orbitEquivQuotientStabilizer D L)]
    change (MulAction.stabilizer D L).index=9
    omega
  have hsub:MulAction.orbit D L⊆c.kernelLines\{W}:=by
    rintro K ⟨d,rfl⟩
    refine ⟨c.kernelLines_invariant hL d (hDM d.property),?_⟩
    intro he
    change (d:G) • L=W at he
    have hh:=congrArg (fun R:Subgroup G=>(d:G)⁻¹ • R) he
    rw[inv_smul_smul] at hh
    have hf:(d:G)⁻¹ • W=W:=mem_normalizer_iff_map_conj_eq.mp (hDW (inv_mem d.property))
    exact hne (hh.trans hf)
  have he:MulAction.orbit D L=c.kernelLines\{W}:=by
    apply Set.eq_of_subset_of_ncard_le hsub
    rw[Set.ncard_sdiff_singleton_of_mem c.line_mem_kernelLines]
    change Nat.card c.kernelLines-1≤Nat.card (MulAction.orbit D L)
    rw[c.kernelLines_card,ho]
  intro K hK hKW
  obtain ⟨d,hd⟩:=he.ge ⟨hK,hKW⟩
  exact ⟨d,d.property,hd.symm⟩

theorem kernelLines_le_odd_iff {L:Subgroup G} (hL:L∈c.kernelLines) :
    L≤c.toSourceData.D ↔ L=c.toSourceData.W := by
  let V:=c.toSourceData.V
  let D:=c.toSourceData.D
  let W:=c.toSourceData.W
  have hWD:W≤D:=c.odd_fixed.ge.trans inf_le_left
  refine ⟨?_,fun he=>he ▸ hWD⟩
  intro hLD
  by_contra hne
  have hQM:c.toSourceData.Q≤normalizer (V:Set G):=(h.cubic_kernel_outside_fixed_planes P c.actors c.actors_eq
    c.odd_split c.odd_card c.odd_extraspecial).1
  have hDA:D≤normalizer ((V⊓D:Subgroup G):Set G):=by
    apply le_normalizer_iff.mpr
    intro d hd x hx
    exact ⟨(mem_normalizer_iff.mp (hQM (mem_sup_right hd)) x).mp hx.1,
      (mem_normalizer_iff.mp (D.le_normalizer hd) x).mp hx.2⟩
  have hLA:L≤V⊓D:=le_inf (c.kernelLines_le hL) hLD
  have hall:∀K∈c.kernelLines,K≤V⊓D:=by
    intro K hK
    by_cases he:K=W
    · rw[he];exact le_inf c.line_le_kernel hWD
    · obtain ⟨d,hd,rfl⟩:=c.other_kernelLine_orbit hL hne K hK he
      exact (map_mono hLA).trans_eq (mem_normalizer_iff_map_conj_eq.mp (hDA hd))
  have hVA:V≤V⊓D:=calc
    V=sSup c.kernelLines:=c.kernelLines_span.symm
    _≤V⊓D:=sSup_le hall
  have hh:=card_le_of_le hVA
  rw[c.kernel_card,c.intersection_card] at hh
  omega
end SourceConfiguration
end Theory.GroupTheory.Recognition.UnitaryFourThree.CubicGeometry

namespace Theory.GroupTheory.Recognition.UnitaryFourThree.IsType
variable {G:Type*} [Group G] [Finite G] {z:G}
theorem original_cubic_line_geometry (h:IsType z) (P:Sylow 3 (centralizer z)) :
    ∃c:CubicGeometry.SourceConfiguration h P,
      Nat.card c.kernelLines=10 ∧ sSup c.kernelLines=c.toSourceData.V ∧
      (∀L∈c.kernelLines,L≤c.toSourceData.D ↔ L=c.toSourceData.W) ∧
      ∀L∈c.kernelLines,L≠c.toSourceData.W→∀K∈c.kernelLines,K≠c.toSourceData.W→
        ∃d∈c.toSourceData.D,K=L.map (MulAut.conj d).toMonoidHom := by
  obtain ⟨c⟩:=h.original_cubic_source_configuration P
  exact ⟨c,c.kernelLines_card,c.kernelLines_span,fun _ hL=>c.kernelLines_le_odd_iff hL,
    fun _ hL hne=>c.other_kernelLine_orbit hL hne⟩
end Theory.GroupTheory.Recognition.UnitaryFourThree.IsType
