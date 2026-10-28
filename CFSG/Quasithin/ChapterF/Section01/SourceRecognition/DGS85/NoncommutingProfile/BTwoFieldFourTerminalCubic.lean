module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.NoncommutingProfile.BTwoBinaryAlphaCentralizers
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.LocalStructure.IntrinsicEdgeGeneration
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingNontrivial.LocalGeneration
public import Theory.SpecificGroups.SL2.FieldFourCubicSubgroups

/-!
# The actual field-four cubic in the terminal centralizer

In DGS (10.8), binary alpha and field-four beta give two half-sized root
images centralizing a contrary terminal element x. The incident Sylow
images are distinct, and their join is nontransitive on the five beta
neighbors. The field-four root theorem therefore constructs an actual
order-three element in this same generated centralizer.

Orbit counting supplies another alpha-type neighbor fixed by the cubic.
Its three-element neighbor set already has the fixed beta vertex, so the
cubic fixes that entire set and lies in the full radius-one kernel.
This is the full permutation kernel, not an identification with its
two-core or with the Sylow-generated local group.

The original-source application retains one opposite-center conjugator,
the literal residual, both root factors, and the reduced-to-original
inclusion. Controlling the cubic on the new core section and obtaining
the third centralizing root remain necessary for terminal separation.

Source: Delgado--Goldschmidt--Stellmacher, Groups and Graphs (1985),
(10.8), printed p.161, the binary-alpha/nonbinary-beta paragraph.
-/

public noncomputable section
open Subgroup
open scoped Pointwise MatrixGroups commutatorElement
namespace CFSG.Quasithin.ChapterF.Source.DGS85.NoncommutingProfile
open Theory.GroupTheory.AmalgamGraph Subgroup.CosetGeometry.RankTwo Noncommuting
namespace Reduction
open DGS85.Reduction
universe u
variable {G : Type u} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}
local notation "F" => reducedFamily L S
variable {K : Type*} [Field K] [Finite K] [CharP K 2]

private theorem cubic_other_fixed
    {H X : Type*} [Group H] [MulAction H X] [Finite X]
    (hX : Nat.card X=5) (d : H) (hd : orderOf d=3) (x : X) :
    ∃ y : X, d • y=y ∧ y≠x := by
  let : Fact (Nat.Prime 3) := ⟨by decide⟩
  have hp : IsPGroup 3 (zpowers d) := IsPGroup.of_card (n:=1)
    (by rw [Nat.card_zpowers,hd,pow_one])
  have hh := hp.card_modEq_card_fixedPoints X
  rw [hX] at hh
  have ht : 1<Nat.card (MulAction.fixedPoints (zpowers d) X) := by
    change 5%3=Nat.card (MulAction.fixedPoints (zpowers d) X)%3 at hh
    omega
  obtain ⟨y,hy,hne⟩ := Set.exists_ne_of_one_lt_ncard ht x
  exact ⟨y,hy ⟨d,mem_zpowers d⟩,hne⟩

private theorem cubic_fixes_three
    {H X : Type*} [Group H] [MulAction H X] [Finite X]
    (hX : Nat.card X=3) (d : H) (hd : orderOf d=3)
    (x : X) (hx : d • x=x) : ∀ y : X, d • y=y := by
  let : Fact (Nat.Prime 3) := ⟨by decide⟩
  have hp : IsPGroup 3 (zpowers d) := IsPGroup.of_card (n:=1)
    (by rw [Nat.card_zpowers,hd,pow_one])
  have hfix : x∈MulAction.fixedPoints (zpowers d) X :=
    fun a => (zpowers_le.mpr (show d∈MulAction.stabilizer H x from hx)) a.property
  have hpos : 0<Nat.card (MulAction.fixedPoints (zpowers d) X) :=
    Finite.card_pos_iff.mpr ⟨⟨x,hfix⟩⟩
  have hle : Nat.card (MulAction.fixedPoints (zpowers d) X)≤3 := hX ▸
    Nat.card_le_card_of_injective Subtype.val Subtype.val_injective
  have hh := hp.card_modEq_card_fixedPoints X
  rw [hX] at hh
  have he : (MulAction.fixedPoints (zpowers d) X).ncard=Nat.card X := by
    change Nat.card (MulAction.fixedPoints (zpowers d) X)=Nat.card X
    change 3%3=Nat.card (MulAction.fixedPoints (zpowers d) X)%3 at hh
    omega
  have hfull := (Set.eq_univ_iff_ncard _).mpr he
  intro y
  have hy : y∈MulAction.fixedPoints (zpowers d) X := hfull ▸ Set.mem_univ y
  exact hy ⟨d,mem_zpowers d⟩

private theorem half_roots_cubic
    (h : HypothesisF11 L S) {v a b : Vertex F}
    (ha : (graph F).Adj v a) (hb : (graph F).Adj v b) (hab : a≠b)
    (e : (graphLocalGroup F v⧸pCore 2 (graphLocalGroup F v))≃*SL(2,K))
    (hK : Nat.card K=4) (hval : Nat.card ((graph F).neighborSet v)=5)
    (A B : Subgroup (G₀ L S)) (hA : A≤Q F a) (hB : B≤Q F b)
    (hAc : Nat.card K≤2*(Q F v).relIndex A)
    (hBc : Nat.card K≤2*(Q F v).relIndex B)
    (hnt : ¬∀ z : Vertex F, (graph F).Adj v z →
      ∃ g∈graphLocalGroup F v, g∈A⊔B ∧ g • a=z) :
    ∃ d∈graphLocalGroup F v, d∈A⊔B ∧ orderOf d=3 := by
  let H := reduced_triple h
  let _ : ∀ i, Finite (F i) := finite_endpoints H
  let M := graphLocalGroup F v
  let : Finite M := Finite.of_injective (inclusion (sylowGenerated_le _)) (inclusion_injective _)
  let q : M →* SL(2,K) := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 M))
  have hq : Function.Surjective q := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hk : q.ker=(Q F v).subgroupOf M := by
    have hc : (Q F v).subgroupOf M=pCore 2 M := graph_intrinsic_core H v
    rw [hc]
    ext x
    change e (QuotientGroup.mk' (pCore 2 M) x)=1 ↔ x∈pCore 2 M
    rw [e.map_eq_one_iff]
    exact QuotientGroup.eq_one_iff x
  let d := reducedFullEarlierLocalTheorems h
  obtain ⟨R,hR⟩ := CommutingNontrivial.source_edge_core_local_sylow H
    (reduced_borel_core_sylow h) d ha
  obtain ⟨T,hT⟩ := CommutingNontrivial.source_edge_core_local_sylow H
    (reduced_borel_core_sylow h) d hb
  change Sylow 2 M at R T
  change (R:Subgroup M).map M.subtype=_ at hR
  change (T:Subgroup M).map M.subtype=_ at hT
  have hAR : A≤(R:Subgroup M).map M.subtype := by
    rw [hR]
    exact hA.trans (by simpa only [inf_comm,reducedFamily] using graph_Q_le_edgeCore H ha.symm)
  have hBT : B≤(T:Subgroup M).map M.subtype := by
    rw [hT]
    exact hB.trans (by simpa only [inf_comm,reducedFamily] using graph_Q_le_edgeCore H hb.symm)
  have hAM : A≤M := hAR.trans (map_subtype_le _)
  have hBM : B≤M := hBT.trans (map_subtype_le _)
  have hAi : A.subgroupOf M≤R := by
    intro x hx
    obtain ⟨y,hy,he⟩ := hAR hx
    exact (Subtype.ext he : y=x) ▸ hy
  have hBi : B.subgroupOf M≤T := by
    intro x hx
    obtain ⟨y,hy,he⟩ := hBT hx
    exact (Subtype.ext he : y=x) ▸ hy
  let R' := R.mapSurjective (f:=q) hq
  let T' := T.mapSurjective (f:=q) hq
  have hne : R'≠T' := by
    intro he
    have hh := congrArg (fun U : Sylow 2 SL(2,K) => (U:Subgroup SL(2,K)).comap q) he
    change ((R:Subgroup M).map q).comap q=((T:Subgroup M).map q).comap q at hh
    have hkR : q.ker≤(R:Subgroup M) := by
      rw [hk]
      have hc : (Q F v).subgroupOf M=pCore 2 M := graph_intrinsic_core H v
      rw [hc]
      exact pCore_isPGroup.le_sylow_of_normal R
    have hkT : q.ker≤(T:Subgroup M) := by
      rw [hk]
      have hc : (Q F v).subgroupOf M=pCore 2 M := graph_intrinsic_core H v
      rw [hc]
      exact pCore_isPGroup.le_sylow_of_normal T
    rw [comap_map_eq_self hkR,comap_map_eq_self hkT] at hh
    have hec := congrArg (map M.subtype) hh
    rw [hR,hT] at hec
    exact hab (graph_intrinsic_edgeCore_unique_neighbor H (reduced_borel_core_sylow h)
      ha hb (hec ▸ (pCoreIn_le 2 _).trans inf_le_right))
  let A' := (A.subgroupOf M).map q
  let B' := (B.subgroupOf M).map q
  have hca : Nat.card A'=(Q F v).relIndex A :=
    Representation.BinaryConjugationSection.actor_image_card_eq_relIndex M (Q F v) A q hk hAM
  have hcb : Nat.card B'=(Q F v).relIndex B :=
    Representation.BinaryConjugationSection.actor_image_card_eq_relIndex M (Q F v) B q hk hBM
  let Ω := (graph F).neighborSet v
  let act : M →* Equiv.Perm Ω := (localAction F v).comp (inclusion (sylowGenerated_le _))
  let : MulAction M Ω := MulAction.compHom _ act
  let : Finite Ω := finite_neighbors F v
  let : MulAction.IsPretransitive M Ω := ⟨by
    intro x y
    obtain ⟨g,hg,hge⟩ := graphLocalGroup_transitive H (reduced_borel_core_sylow h)
      (reduced_vertex_sylow h) v x y
    exact ⟨⟨g,hg⟩,Subtype.ext hge⟩⟩
  have hkfix (k : M) (hk' : k∈q.ker) (x : Ω) : k • x=x := by
    apply Subtype.ext
    change (k:G₀ L S) • x.val=x.val
    have hr : (k:G₀ L S)∈Q F v := by
      change k∈(Q F v).subgroupOf M
      rw [←hk]
      exact hk'
    exact (source_Z_Q_U H v).2 hr x.val
      ((mem_ball_one F v x.val).mpr (Or.inl x.property))
  let C := (A⊔B).subgroupOf M
  have hnt' : ¬MulAction.IsPretransitive C Ω := by
    intro hp
    let := hp
    apply hnt
    intro z hz
    obtain ⟨d,hd⟩ := MulAction.exists_smul_eq C (⟨a,ha⟩:Ω) ⟨z,hz⟩
    exact ⟨d.val.val,d.val.property,d.property,congrArg Subtype.val hd⟩
  have hmap : C.map q=A'⊔B' := by
    rw [show C=(A⊔B).subgroupOf M from rfl,subgroupOf_sup hAM hBM,Subgroup.map_sup]
  have hAne : A'≠⊥ := by
    intro he
    rw [←hca,he,card_bot,hK] at hAc
    omega
  have hBne : B'≠⊥ := by
    intro he
    rw [←hcb,he,card_bot,hK] at hBc
    omega
  obtain ⟨d,hd,hdo⟩ := Matrix.SpecialLinearGroup.exists_cubic_of_nontransitive_roots
    hK hval q hq hkfix C hnt' R' T' hne A' B' (map_mono hAi) (map_mono hBi)
    (hmap.symm ▸ le_sup_left) (hmap.symm ▸ le_sup_right) hAne hBne
  exact ⟨d,d.property,hd,(orderOf_injective M.subtype M.subtype_injective d).trans hdo⟩

/-- A contrary terminal element in the binary-alpha, field-four-beta case
produces a cubic in the literal two-root centralizer. The same cubic has
order three in the original completion and fixes the full radius-one ball
at another alpha-type neighbor. -/
theorem original_bTwo_field_four_terminal_cubic
    {K₀ : Type*} [Field K₀] [Finite K₀] [CharP K₀ 2]
    (h : HypothesisF11 L S) {u t : Vertex F}
    (hc : IsCriticalPair F (base F false) u)
    (hne : ⁅Z F (base F false),Z F u⁆≠⊥)
    (hb : b F=2) (hβu : (graph F).Adj (base F true) u)
    (ht : (graph F).Adj (base F false) t) (htne : t≠base F true)
    (e₀ : (L 0⧸pCore 2 (L 0))≃*PSL(2,K₀)) (hK₀ : Nat.card K₀=2)
    (e : (L 1⧸pCore 2 (L 1))≃*PSL(2,K))
    (hK : Nat.card K=4)
    (hD : (parabolic L S 1).pCoreIn 2⊓(Q F t).map (G₀ L S).subtype≠
      (Z F (base F false)).map (G₀ L S).subtype) :
    ∃ g∈graphLocalGroup F (base F false), g • base F true=t ∧
      let ι := (G₀ L S).subtype
      let Q₀ := (parabolic L S 0).pCoreIn 2
      let Q₁ := (parabolic L S 1).pCoreIn 2
      let D₀ := Q₁⊓(Q F t).map ι
      let W₀ := (Z F u).map ι⊔(Z F (g • u)).map ι
      let R₀ := D₀⊓centralizer (W₀:Set G)
      W₀⊔Q₀=enlargedEndpoint L S 0 ∧
      R₀=(D₀⊓(Q F u).map ι)⊓(Q F (g • u)).map ι ∧ R₀≠⊥ ∧
      ∀ y : Vertex F, (graph F).Adj u y → y≠base F true →
        ∀ x∈R₀⊓(Q F y).map ι, x≠1 →
          ∃ d∈graphLocalGroup F (base F true), orderOf d=3 ∧ orderOf (ι d)=3 ∧
            ι d∈(((V F t 1).map ι⊓Q₀)⊓centralizer ({x}:Set G))⊔
              (((V F y 1).map ι⊓(Q F u).map ι)⊓centralizer ({x}:Set G)) ∧
            ι d∈centralizer ({x}:Set G) ∧
            ∃ δ : Vertex F, (graph F).Adj (base F true) δ ∧
              δ≠base F false ∧ d∈ballKernel F δ 1 := by
  obtain ⟨g,hg,hgt,hW,hfour,hRne,hroots⟩ :=
    original_bTwo_alpha_binary_terminal_half_roots h hc hne hb hβu ht htne e₀ hK₀ e hD
  refine ⟨g,hg,hgt,hW,hfour,hRne,?_⟩
  intro y hy hyne x hx hx1
  obtain ⟨hA,hB,hspan,hnt⟩ := hroots y hy hyne x hx hx1
  let ι := (G₀ L S).subtype
  let α := base F false
  let β := base F true
  let C := (centralizer ({x}:Set G)).comap ι
  let A := (V F t 1⊓Q F α)⊓C
  let B := (V F y 1⊓Q F u)⊓C
  have hmap (T : Subgroup (G₀ L S)) :
      (T⊓C).map ι=T.map ι⊓centralizer ({x}:Set G) := by
    ext z
    constructor
    · rintro ⟨a,ha,rfl⟩
      exact ⟨mem_map_of_mem ι ha.1,ha.2⟩
    · rintro ⟨⟨a,ha,rfl⟩,hcx⟩
      exact mem_map.mpr ⟨a,⟨ha,hcx⟩,rfl⟩
  have hAm : A.map ι=((V F t 1).map ι⊓(parabolic L S 0).pCoreIn 2)⊓
      centralizer ({x}:Set G) := by
    rw [show A=(V F t 1⊓Q F α)⊓C from rfl,hmap,
      map_inf _ _ _ (G₀ L S).subtype_injective,reduced_base_Q_map h false]
    rfl
  have hBm : B.map ι=((V F y 1).map ι⊓(Q F u).map ι)⊓
      centralizer ({x}:Set G) := by
    rw [show B=(V F y 1⊓Q F u)⊓C from rfl,hmap,
      map_inf _ _ _ (G₀ L S).subtype_injective]
  have hAc : Nat.card K≤2*(Q F β).relIndex A := by
    rw [←relIndex_map_map_of_injective (f:=ι) (Q F β) A (G₀ L S).subtype_injective,
      reduced_base_Q_map h true,hAm]
    exact hA
  have hBc : Nat.card K≤2*(Q F β).relIndex B := by
    rw [←relIndex_map_map_of_injective (f:=ι) (Q F β) B (G₀ L S).subtype_injective,
      reduced_base_Q_map h true,hBm]
    exact hB
  let eβ := (reduced_graphLinearQuotient h true e).trans
    (MulEquiv.ofBijective (BenderSuzuki.Converse.pi K)
      ⟨BenderSuzuki.Converse.pi_injective,BenderSuzuki.Converse.pi_surjective⟩).symm
  have hab : (graph F).Adj β α :=
    (show (graph F).Adj α β from
      ⟨by change false≠true; decide,Subgroup.CosetGeometry.incident_base _ _ _⟩).symm
  have hau : α≠u := by
    intro he
    have hd := hc.1
    rw [←he,SimpleGraph.dist_self,hb] at hd
    contradiction
  let H := reduced_triple h
  have hval : Nat.card ((graph F).neighborSet β)=5 := by
    have hi := source_linear_edge_index_of_quotient H (reduced_borel_core_sylow h)
      (reduced_vertex_sylow h) hab eβ
    rw [card_neighbor_base]
    change (F false).relIndex (F true)=5
    change (stabilizer F α).relIndex (stabilizer F β)=Nat.card K+1 at hi
    simpa only [α,β,stabilizer,Subgroup.CosetGeometry.stabilizer_base,hK] using hi
  have hnt' : ¬∀ z : Vertex F, (graph F).Adj β z →
      ∃ a∈graphLocalGroup F β, a∈A⊔B ∧ a • α=z := by
    intro hh
    apply hnt
    intro z hz
    obtain ⟨a,ha,haAB,haz⟩ := hh z hz
    refine ⟨a,ha,?_,haz⟩
    have hm := mem_map_of_mem ι haAB
    rwa [Subgroup.map_sup,hAm,hBm] at hm
  obtain ⟨d,hd,hdAB,hdo⟩ := half_roots_cubic h hab hβu hau eβ hK hval A B
    (inf_le_left.trans inf_le_right) (inf_le_left.trans inf_le_right) hAc hBc hnt'
  have hdm : ι d∈(((V F t 1).map ι⊓(parabolic L S 0).pCoreIn 2)⊓
      centralizer ({x}:Set G))⊔(((V F y 1).map ι⊓(Q F u).map ι)⊓
      centralizer ({x}:Set G)) := by
    have hm := mem_map_of_mem ι hdAB
    rwa [Subgroup.map_sup,hAm,hBm] at hm
  have hdc : ι d∈centralizer ({x}:Set G) := (hspan hdm).2
  let _ : ∀ i, Finite (F i) := finite_endpoints H
  let Ω := (graph F).neighborSet β
  let : Finite Ω := finite_neighbors F β
  let : MulAction (stabilizer F β) Ω := MulAction.compHom _ (localAction F β)
  let dβ : stabilizer F β := ⟨d,sylowGenerated_le _ hd⟩
  have hdβ : orderOf dβ=3 :=
    (orderOf_injective (stabilizer F β).subtype (stabilizer F β).subtype_injective dβ).symm.trans hdo
  obtain ⟨⟨δ,hδ⟩,hdδ,hδα⟩ := cubic_other_fixed hval dβ hdβ (⟨α,hab⟩:Ω)
  have hδfix : d • δ=δ := congrArg Subtype.val hdδ
  have hδne : δ≠α := fun he => hδα (Subtype.ext he)
  have hδtype : δ.type=false := by
    have ht := hδ.1
    change true≠δ.type at ht
    cases hdtype : δ.type with
    | false => rfl
    | true => exact (ht hdtype.symm).elim
  let eα := (reduced_graphLinearQuotient h false e₀).trans
    (MulEquiv.ofBijective (BenderSuzuki.Converse.pi K₀)
      ⟨BenderSuzuki.Converse.pi_injective,BenderSuzuki.Converse.pi_surjective⟩).symm
  have hvalα : Nat.card ((graph F).neighborSet α)=3 := by
    have hi := source_linear_edge_index_of_quotient H (reduced_borel_core_sylow h)
      (reduced_vertex_sylow h) hab.symm eα
    rw [card_neighbor_base]
    change (F true).relIndex (F false)=3
    change (stabilizer F β).relIndex (stabilizer F α)=Nat.card K₀+1 at hi
    simpa only [α,β,stabilizer,Subgroup.CosetGeometry.stabilizer_base,hK₀] using hi
  have hvalδ : Nat.card ((graph F).neighborSet δ)=3 := by
    obtain ⟨a,ha⟩ := Subgroup.CosetGeometry.exists_smul_base F δ
    have ha' : a • α=δ := by simpa only [hδtype] using ha
    have hh := Nat.card_congr ((Subgroup.CosetGeometry.translationGraphIso F a).mapNeighborSet α)
    change Nat.card ((graph F).neighborSet α)=Nat.card ((graph F).neighborSet (a • α)) at hh
    rw [ha'] at hh
    exact hh.symm.trans hvalα
  let Ωδ := (graph F).neighborSet δ
  let : Finite Ωδ := finite_neighbors F δ
  let : MulAction (stabilizer F δ) Ωδ := MulAction.compHom _ (localAction F δ)
  let dδ : stabilizer F δ := ⟨d,hδfix⟩
  have hdoδ : orderOf dδ=3 :=
    (orderOf_injective (stabilizer F δ).subtype (stabilizer F δ).subtype_injective dδ).symm.trans hdo
  have hδβ : (graph F).Adj δ β := (show (graph F).Adj β δ from hδ).symm
  have hβfix : dδ • (⟨β,hδβ⟩:Ωδ)=(⟨β,hδβ⟩:Ωδ) :=
    Subtype.ext (sylowGenerated_le _ hd)
  have hall := cubic_fixes_three hvalδ dδ hdoδ (⟨β,hδβ⟩:Ωδ) hβfix
  refine ⟨d,hd,hdo,(orderOf_injective ι (G₀ L S).subtype_injective d).trans hdo,
    hdm,hdc,δ,hδ,hδne,?_⟩
  intro z hz
  rcases (mem_ball_one F δ z).mp hz with hz|rfl
  · exact congrArg Subtype.val (hall ⟨z,hz⟩)
  · exact hδfix

end Reduction
end CFSG.Quasithin.ChapterF.Source.DGS85.NoncommutingProfile
