module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.NoncommutingProfile.BTwoFieldFourTerminalCubic
public import Theory.SpecificGroups.SL2.SylowNormalizerCard
public import Theory.SpecificGroups.SL2.OddSylowCentralizer

/-!
# The terminal cubic on the actual core sections

At a binary alpha vertex, the intrinsic local group meets the full
radius-one kernel in precisely the two-core. This follows from the
literal edge Sylow normalizer in SL₂(2), together with the source Sylow
property of the two-core in that kernel. Hence the intrinsic actor
commutes with the full kernel modulo the two-core.

An order-three element in this kernel which belongs to one neighboring
linear local group consequently belongs to every neighboring local group.
In each literal neighbor quotient, its image is a nontrivial odd element,
so it centralizes no nonidentity root element. Applying this at two
neighbors proves that its action on the alpha core modulo the intersection
of their cores has no nontrivial fixed coset. The commutator formulation
retains the actual quotient representatives.

The original terminal application uses the previously constructed cubic,
with both centralizing root factors, the residual, and the original
completion inclusion unchanged. The actor remains in the full alpha
kernel; it is not identified with an element of the alpha two-core or
intrinsic local group. Placing the tested residual element in this new
alpha core and constructing the third centralizing root are still needed
for the terminal contradiction.

Source: Delgado--Goldschmidt--Stellmacher, Groups and Graphs (1985),
(10.7)--(10.8), printed pp.159--161, especially the field-four paragraph
on p.161.
-/

public noncomputable section
open Subgroup
open scoped Pointwise MatrixGroups commutatorElement
namespace CFSG.Quasithin.ChapterF.Source.DGS85.NoncommutingProfile
open Theory.GroupTheory.AmalgamGraph Subgroup.CosetGeometry.RankTwo Noncommuting
variable {G : Type*} [Group G] {P : Fin 2 → Subgroup G} {B : Subgroup G}
local notation "F" => family P
variable {k : Type*} [Field k] [Finite k] [CharP k 2]

private theorem binary_kernel_intersection
    (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T:Subgroup B)=pCore 2 B)
    (hS : ∀ i, ∃ T : Sylow 2 (P i), (T:Subgroup (P i)).map (P i).subtype≤B)
    {v w : Vertex F} (hw : (graph F).Adj v w)
    (e : (graphLocalGroup F v⧸pCore 2 (graphLocalGroup F v))≃*SL(2,k))
    (hk : Nat.card k=2) :
    graphLocalGroup F v⊓ballKernel F v 1=Q F v := by
  let _ := finite_endpoints h
  let M := graphLocalGroup F v
  let : Finite M := Finite.of_injective (inclusion (sylowGenerated_le _)) (inclusion_injective _)
  obtain ⟨T,hT⟩ := source_edge_vertex_sylow h hS hw
  obtain ⟨R,hR⟩ := T.exists_map_subtype_eq_of_le (H:=M) (sylowGenerated_le _)
    (sylow_le_sylowGenerated _ T)
  have hR := hR.trans (sylow_image_eq_edge_core _ _ inf_le_left
    (source_edge_core_sylow h hB hw) T hT)
  let q := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 M))
  have hq : Function.Surjective q := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hker : q.ker=pCore 2 M := by
    rw [MonoidHom.ker_comp_of_injective _ _ e.injective,QuotientGroup.ker_mk']
  let T := R.mapSurjective (f:=q) hq
  have hc : Nat.card (normalizer (T:Set SL(2,k)))=Nat.card T := by
    have hncard : Nat.card (normalizer (T:Set SL(2,k)))=Nat.card k*(Nat.card k-1) :=
      Matrix.SpecialLinearGroup.card_sylow_normalizer_even T
    rw [hncard]
    have ht : Nat.card T=Nat.card k :=
      (Nat.card_congr (Matrix.SpecialLinearGroup.sylowEquivAdditive k 2 T).toEquiv).symm
    rw [ht,hk]
  have hn : normalizer (T:Set SL(2,k))=(T:Subgroup SL(2,k)) :=
    (eq_of_le_of_card_ge T.le_normalizer hc.le).symm
  have hnR : normalizer (R:Set M)=(R:Subgroup M) := by
    apply map_injective_of_ker_le q
      ((hker ▸ pCore_isPGroup.le_sylow_of_normal R).trans R.le_normalizer)
      (hker ▸ pCore_isPGroup.le_sylow_of_normal R)
    rw [R.normalizer_map_surjective q hq]
    exact hn
  have hle : graphLocalGroup F v⊓ballKernel F v 1≤
      (stabilizer F v⊓stabilizer F w).pCoreIn 2 := by
    intro x hx
    have hxw := (ballKernel_one_le_edge F hw hx.2).2
    have hxR : (⟨x,hx.1⟩:M)∈(R:Subgroup M) := by
      rw [←hnR,←graph_intrinsic_edge_sylow_normalizer h hB hw R hR]
      exact hxw
    exact hR ▸ mem_map_of_mem M.subtype hxR
  apply le_antisymm
  · exact CommutingNontrivial.pSubgroup_le_Q_of_le_U F v _ ((isPGroup_pCoreIn 2 _).to_le hle)
      inf_le_right (source_kernel_sylow h hB hS v)
  · exact le_inf (pGroup_le_sylowGenerated _ _ (Q_le_stabilizer F v)
      (isPGroup_pCoreIn 2 _)) (source_Z_Q_U h v).2

private theorem kernel_actor_propagates
    (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T:Subgroup B)=pCore 2 B)
    (hS : ∀ i, ∃ T : Sylow 2 (P i), (T:Subgroup (P i)).map (P i).subtype≤B)
    {v w z : Vertex F} (hw : (graph F).Adj v w) (hz : (graph F).Adj v z)
    (hker : graphLocalGroup F v⊓ballKernel F v 1=Q F v)
    (a : G) (ha : a∈graphLocalGroup F w) (hak : a∈ballKernel F v 1) :
    a∈graphLocalGroup F z := by
  let _ := finite_endpoints h
  obtain ⟨g,hg,hgz⟩ := graphLocalGroup_transitive h hB hS v ⟨w,hw⟩ ⟨z,hz⟩
  change g • w=z at hgz
  have hcomm : ⁅graphLocalGroup F v,ballKernel F v 1⁆≤Q F v := by
    rw [←hker]
    exact le_inf
      (le_normalizer_iff_commutator_le_left.mp
        ((ballKernel_le_stabilizer F v 1).trans (sylowGenerated_normalized _)))
      (le_normalizer_iff_commutator_le_right.mp
        ((sylowGenerated_le _).trans (stabilizer_le_normalizer_ballKernel F v 1)))
  have hga : g*a*g⁻¹∈graphLocalGroup F z := by
    rw [←hgz,graphLocalGroup_conjugate h]
    exact mem_map_of_mem (MulAut.conj g).toMonoidHom ha
  have hcg : ⁅g,a⁆∈graphLocalGroup F z :=
    (pGroup_le_sylowGenerated _ _ ((source_Z_Q_U h v).2.trans
      ((ballKernel_one_le_edge F hz).trans inf_le_right)) (isPGroup_pCoreIn 2 _))
      (hcomm (commutator_mem_commutator hg hak))
  have he : a=⁅g,a⁆⁻¹*(g*a*g⁻¹) := by simp only [commutatorElement_def]; group
  rw [he]
  exact (graphLocalGroup F z).mul_mem ((graphLocalGroup F z).inv_mem hcg) hga

private theorem cubic_neighbor_core_fixed
    (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T:Subgroup B)=pCore 2 B)
    (hS : ∀ i, ∃ T : Sylow 2 (P i), (T:Subgroup (P i)).map (P i).subtype≤B)
    {v w : Vertex F} (hw : (graph F).Adj v w)
    (e : (graphLocalGroup F w⧸pCore 2 (graphLocalGroup F w))≃*SL(2,k))
    (a : G) (ha : a∈graphLocalGroup F w) (hao : orderOf a=3)
    (x : G) (hx : x∈Q F v) (hxa : ⁅x,a⁆∈Q F w) : x∈Q F w := by
  let _ := finite_endpoints h
  let M := graphLocalGroup F w
  let : Finite M := Finite.of_injective (inclusion (sylowGenerated_le _)) (inclusion_injective _)
  obtain ⟨T,hT⟩ := source_edge_vertex_sylow h hS hw.symm
  obtain ⟨R,hR⟩ := T.exists_map_subtype_eq_of_le (H:=M) (sylowGenerated_le _)
    (sylow_le_sylowGenerated _ T)
  have hR := hR.trans (sylow_image_eq_edge_core _ _ inf_le_left
    (source_edge_core_sylow h hB hw.symm) T hT)
  have hQR : Q F v≤(R:Subgroup M).map M.subtype := by
    rw [hR]
    simpa only [inf_comm] using graph_Q_le_edgeCore h hw
  have hxM : x∈M := map_subtype_le _ (hQR hx)
  let aM : M := ⟨a,ha⟩
  let xM : M := ⟨x,hxM⟩
  let q := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 M))
  have hq : Function.Surjective q := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hk : q.ker=pCore 2 M := by
    rw [MonoidHom.ker_comp_of_injective _ _ e.injective,QuotientGroup.ker_mk']
  have han : q aM≠1 := by
    intro he
    have haQ : aM∈pCore 2 M := hk ▸ he
    have hco := (pCore_isPGroup (p:=2) (G:=M)).orderOf_coprime
      (show Nat.Coprime 2 3 from by decide) (⟨aM,haQ⟩:pCore 2 M)
    rw [Subgroup.orderOf_mk,Subgroup.orderOf_mk,hao] at hco
    norm_num at hco
  have hxp : q xM∈R.mapSurjective (f:=q) hq := by
    obtain ⟨y,hy,he⟩ := hQR hx
    have he' : y=xM := Subtype.ext he
    exact mem_map_of_mem q (he' ▸ hy)
  have hpow : (q aM)^3=1 := by
    rw [←map_pow]
    have he : aM^3=1 := Subtype.ext (hao ▸ pow_orderOf_eq_one a)
    rw [he,map_one]
  have hcomm : Commute (q xM) (q aM) := by
    apply commutatorElement_eq_one_iff_mul_comm.mp
    rw [←map_commutatorElement]
    have hxc : ⁅xM,aM⁆∈q.ker := by
      rw [hk,←graph_intrinsic_core h w]
      exact hxa
    exact hxc
  have he := Matrix.SpecialLinearGroup.eq_one_of_sylow_commutes_nontrivial_odd
    (R.mapSurjective (f:=q) hq) (q xM) (q aM) hxp han (by decide : Odd 3) hpow
    hcomm
  have hxQ : xM∈pCore 2 M := hk ▸ he
  exact (sylowGenerated_core (stabilizer F w)).le (mem_map_of_mem M.subtype hxQ)

omit [Finite k] [CharP k 2] in
private theorem quotient_at_translate
    (h : LocallyRankOneTriple P B) {v w : Vertex F}
    (g : G) (hg : g • v=w)
    (e : (graphLocalGroup F v⧸pCore 2 (graphLocalGroup F v))≃*SL(2,k)) :
    Nonempty ((graphLocalGroup F w⧸pCore 2 (graphLocalGroup F w))≃*SL(2,k)) := by
  have he : (graphLocalGroup F v).map (MulAut.conj g).toMonoidHom=graphLocalGroup F w := by
    rw [←hg,graphLocalGroup_conjugate h]
  let E := ((graphLocalGroup F v).equivMapOfInjective (MulAut.conj g).toMonoidHom
    (MulAut.conj g).injective).trans (MulEquiv.subgroupCongr he)
  exact ⟨(QuotientGroup.congr _ _ E (pCore_map_iso 2 E)).symm.trans e⟩

/-- A cubic in a binary vertex's full kernel propagates to every neighboring
linear actor and has no fixed nontrivial coset on the literal two-core section.
The actor is not required to belong to the binary vertex's local group. -/
theorem binary_kernel_cubic_core_section
    {K : Type*} [Field K] [Finite K] [CharP K 2]
    (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T:Subgroup B)=pCore 2 B)
    (hS : ∀ i, ∃ T : Sylow 2 (P i), (T:Subgroup (P i)).map (P i).subtype≤B)
    {v w z : Vertex F} (hw : (graph F).Adj v w) (hz : (graph F).Adj v z)
    (ev : (graphLocalGroup F v⧸pCore 2 (graphLocalGroup F v))≃*SL(2,k))
    (hk : Nat.card k=2)
    (ew : (graphLocalGroup F w⧸pCore 2 (graphLocalGroup F w))≃*SL(2,K))
    (a : G) (ha : a∈graphLocalGroup F w) (hao : orderOf a=3)
    (hak : a∈ballKernel F v 1) :
    a∈graphLocalGroup F z ∧
      ∀ x∈Q F v, ⁅x,a⁆∈Q F w⊓Q F z → x∈Q F w⊓Q F z := by
  have hker := binary_kernel_intersection h hB hS hw ev hk
  have haz := kernel_actor_propagates h hB hS hw hz hker a ha hak
  obtain ⟨g,_,hgz⟩ := locally_transitive F hw hz
  obtain ⟨ez⟩ := quotient_at_translate h g hgz ew
  exact ⟨haz,fun x hx hxa => ⟨cubic_neighbor_core_fixed h hB hS hw ew a ha hao x hx hxa.1,
    cubic_neighbor_core_fixed h hB hS hz ez a haz hao x hx hxa.2⟩⟩

namespace Reduction
open DGS85.Reduction
variable {L : Fin 2 → Subgroup G} {S : Subgroup G}
local notation "F₀" => reducedFamily L S
variable {K : Type*} [Field K] [Finite K] [CharP K 2]

/-- The actual terminal cubic acts without fixed nontrivial cosets on every
new alpha core section, using the original completion inclusion. -/
theorem original_bTwo_field_four_terminal_cubic_action
    {K₀ : Type*} [Field K₀] [Finite K₀] [CharP K₀ 2]
    (h : HypothesisF11 L S) {u t : Vertex F₀}
    (hc : IsCriticalPair F₀ (base F₀ false) u)
    (hne : ⁅Z F₀ (base F₀ false),Z F₀ u⁆≠⊥)
    (hb : b F₀=2) (hβu : (graph F₀).Adj (base F₀ true) u)
    (ht : (graph F₀).Adj (base F₀ false) t) (htne : t≠base F₀ true)
    (e₀ : (L 0⧸pCore 2 (L 0))≃*PSL(2,K₀)) (hK₀ : Nat.card K₀=2)
    (e : (L 1⧸pCore 2 (L 1))≃*PSL(2,K))
    (hK : Nat.card K=4)
    (hD : (parabolic L S 1).pCoreIn 2⊓(Q F₀ t).map (G₀ L S).subtype≠
      (Z F₀ (base F₀ false)).map (G₀ L S).subtype) :
    ∃ g∈graphLocalGroup F₀ (base F₀ false), g • base F₀ true=t ∧
      let ι := (G₀ L S).subtype
      let Q₀ := (parabolic L S 0).pCoreIn 2
      let Q₁ := (parabolic L S 1).pCoreIn 2
      let D₀ := Q₁⊓(Q F₀ t).map ι
      let W₀ := (Z F₀ u).map ι⊔(Z F₀ (g • u)).map ι
      let R₀ := D₀⊓centralizer (W₀:Set G)
      W₀⊔Q₀=enlargedEndpoint L S 0 ∧
      R₀=(D₀⊓(Q F₀ u).map ι)⊓(Q F₀ (g • u)).map ι ∧ R₀≠⊥ ∧
      ∀ y : Vertex F₀, (graph F₀).Adj u y → y≠base F₀ true →
        ∀ x∈R₀⊓(Q F₀ y).map ι, x≠1 →
          ∃ d∈graphLocalGroup F₀ (base F₀ true), orderOf d=3 ∧ orderOf (ι d)=3 ∧
            ι d∈(((V F₀ t 1).map ι⊓Q₀)⊓centralizer ({x}:Set G))⊔
              (((V F₀ y 1).map ι⊓(Q F₀ u).map ι)⊓centralizer ({x}:Set G)) ∧
            ι d∈centralizer ({x}:Set G) ∧
            ∃ δ : Vertex F₀, (graph F₀).Adj (base F₀ true) δ ∧
              δ≠base F₀ false ∧ d∈ballKernel F₀ δ 1 ∧
              ∀ ρ : Vertex F₀, (graph F₀).Adj δ ρ →
                d∈graphLocalGroup F₀ ρ ∧
                  ∀ z∈(Q F₀ δ).map ι, ⁅z,ι d⁆∈Q₁⊓(Q F₀ ρ).map ι →
                    z∈Q₁⊓(Q F₀ ρ).map ι := by
  obtain ⟨g,hg,hgt,hW,hfour,hRne,hcubic⟩ :=
    original_bTwo_field_four_terminal_cubic h hc hne hb hβu ht htne e₀ hK₀ e hK hD
  refine ⟨g,hg,hgt,hW,hfour,hRne,?_⟩
  intro y hy hyne x hx hx1
  obtain ⟨d,hd,hdo,hdorig,hdroots,hdcentral,δ,hδ,hδne,hdk⟩ :=
    hcubic y hy hyne x hx hx1
  refine ⟨d,hd,hdo,hdorig,hdroots,hdcentral,δ,hδ,hδne,hdk,?_⟩
  let H := reduced_triple h
  let ι := (G₀ L S).subtype
  let α := base F₀ false
  let β := base F₀ true
  have hδtype : δ.type=false := by
    have ht := hδ.1
    change true≠δ.type at ht
    cases hdtype : δ.type with
    | false => rfl
    | true => exact (ht hdtype.symm).elim
  let eα := (reduced_graphLinearQuotient h false e₀).trans
    (MulEquiv.ofBijective (BenderSuzuki.Converse.pi K₀)
      ⟨BenderSuzuki.Converse.pi_injective,BenderSuzuki.Converse.pi_surjective⟩).symm
  let eβ := (reduced_graphLinearQuotient h true e).trans
    (MulEquiv.ofBijective (BenderSuzuki.Converse.pi K)
      ⟨BenderSuzuki.Converse.pi_injective,BenderSuzuki.Converse.pi_surjective⟩).symm
  obtain ⟨a,ha⟩ := Subgroup.CosetGeometry.exists_smul_base F₀ δ
  have haδ : a • α=δ := by simpa only [hδtype] using ha
  obtain ⟨eδ⟩ := quotient_at_translate H a haδ eα
  intro ρ hρ
  obtain ⟨hdρ,hfixed⟩ := binary_kernel_cubic_core_section H (reduced_borel_core_sylow h)
    (reduced_vertex_sylow h) hδ.symm hρ eδ hK₀ eβ d hd hdo hdk
  refine ⟨hdρ,?_⟩
  intro z hz hzc
  obtain ⟨r,hr,rfl⟩ := hz
  have hmap : (Q F₀ β⊓Q F₀ ρ).map ι=
      (parabolic L S 1).pCoreIn 2⊓(Q F₀ ρ).map ι := by
    rw [map_inf _ _ _ (G₀ L S).subtype_injective,reduced_base_Q_map h true]
    rfl
  have hrc : ⁅r,d⁆∈Q F₀ β⊓Q F₀ ρ := by
    have hm : ι ⁅r,d⁆∈(Q F₀ β⊓Q F₀ ρ).map ι := by
      rw [hmap,map_commutatorElement]
      exact hzc
    obtain ⟨s,hs,he⟩ := hm
    exact (G₀ L S).subtype_injective he ▸ hs
  exact hmap ▸ mem_map_of_mem ι (hfixed r hr hrc)

end Reduction
end CFSG.Quasithin.ChapterF.Source.DGS85.NoncommutingProfile
