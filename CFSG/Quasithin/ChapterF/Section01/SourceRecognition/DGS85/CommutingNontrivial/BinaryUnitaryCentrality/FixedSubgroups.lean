module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingNontrivial.BinaryUnitaryCentrality.SmallTerminal
public import Theory.GroupTheory.CentralizerDisplacementNormalization

/-!
# Binary unitary fixed subgroups on the original critical graph

Every escaping elementary actor on a moving SU₃(2) or PSU₃(2) center has
fixed index at least four. The actual quotient has two-rank one and Sylow
order at least eight; the Sylow-faithful center representation and fixed-space
generation give the bound. Graph conjugation transports it to every center
of the same type, preserving the original actor and centralizer indices.

The opposite core index is two by `SmallTerminal`. Consequently an elementary
subgroup of Q_beta fixing A = V_beta intersect Q_alpha' fixes all of V_beta.
Apply this to the literal moving-center fixed subgroup C when C lies in Q_beta.
The edge two-core normalizes C, and generation by that edge core and V_beta
makes C normal in L_alpha'. Thus C is exactly the intersection of the centers
at all terminal neighbors. The core fixed-subgroup identity is unconditional;
the trapped-center conclusions retain their trapping premise.

The same bound four excludes commuting opposite core intersections. Applying
the exact 8.6 equivalences, with nonzero H derived from the retained moving
commutator, gives noncentrality and a nonnatural starting center. Therefore
completion of 8.7 in this binary unitary branch requires exclusion of the
entire configuration. These reductions do not prove that exclusion or claim
centrality from omega fixedness.

Source: Delgado--Goldschmidt--Stellmacher, *Groups and Graphs* (1985),
8.1 and 8.6--8.7, printed pp.132--140. The lower bound uses the corrected
Sylow-faithful rank-one argument in `RankOneSquare`; the fixed-subgroup
argument is the binary counterpart of `UnitaryFixedCore`.
-/

@[expose] public noncomputable section
open Subgroup BenderSuzuki.MatrixGroups
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingNontrivial.BinaryUnitaryCentrality
open Subgroup.CosetGeometry.RankTwo Theory.GroupTheory.AmalgamGraph
variable {G : Type*} [Group G] {J : Fin 2 → Subgroup G} {S₀ : Subgroup G}
local notation "Γ" => Reduction.reducedFamily J S₀

private theorem centralizer_map_equiv (A : Subgroup G) (e : G ≃* G) :
    (centralizer (A : Set G)).map e.toMonoidHom = centralizer (A.map e.toMonoidHom : Set G) := by
  apply le_antisymm
  · exact map_centralizer_le_centralizer_image _ _
  · intro x hx
    refine ⟨e.symm x,?_,e.apply_symm_apply x⟩
    intro a ha
    apply e.injective
    simpa only [map_mul,e.apply_symm_apply] using hx (e a) (mem_map_of_mem _ ha)

/-- The actual small-unitary Sylow geometry forces fixed index at least four
for every escaping elementary actor on the unchanged moving center. -/
theorem reduced_moving_binary_square
    (h : HypothesisF11 J S₀)
    {a beta a' : Vertex Γ} (hc : IsCriticalPair Γ a a')
    (hab : (graph Γ).Adj a beta)
    (hd : (graph Γ).dist beta a' + 1 = b Γ) (hb : 1 < b Γ)
    (hcomm : ⁅Z Γ a,Z Γ a'⁆ = ⊥)
    (w : (graph Γ).neighborSet a')
    (hm : ⁅V Γ beta 1 ⊓ Q Γ a',Z Γ w.val⁆ ≠ ⊥)
    (hu : ClassicalGroup.IsPSU (graphLocalGroup Γ w.val ⧸
      pCore 2 (graphLocalGroup Γ w.val)) 3 2 ∨
      IsSU (graphLocalGroup Γ w.val ⧸ pCore 2 (graphLocalGroup Γ w.val)) 3 2)
    (E : Subgroup (Reduction.G₀ J S₀)) [IsElementaryAbelian 2 E]
    (hEL : E ≤ graphLocalGroup Γ w.val) (hEQ : ¬ E ≤ Q Γ w.val) :
    4 ≤ (centralizer (E : Set (Reduction.G₀ J S₀))).relIndex (Z Γ w.val) := by
  let ht := Reduction.reduced_triple h
  let d := Reduction.reducedFullEarlierLocalTheorems h
  rcases hu with hu | hu
  · obtain ⟨K,_,_,F,hK,hconj,⟨e⟩⟩ := hu
    let : Finite (ProjectiveSpecialUnitaryMatrixGroup F) :=
      Finite.of_surjective F.specialToProjective F.specialToProjective_surjective
    apply source_moving_rank_one_square_bound ht d hc hab hd hb hcomm w hm e
      (HermitianForm.EvenTwoRank.two_rank F (n := 1) (by decide) hK hconj).le ?_ E hEL hEQ
    intro S
    have hh := HermitianForm.BinarySylowOrder.cube_le_sylow_card F
      (n := 1) (by decide) hK hconj S
    norm_num at hh
    omega
  · obtain ⟨K,_,_,F,hK,hconj,⟨e⟩⟩ := hu
    let : Finite (ProjectiveSpecialUnitaryMatrixGroup F) :=
      Finite.of_surjective F.specialToProjective F.specialToProjective_surjective
    apply source_moving_rank_one_square_bound ht d hc hab hd hb hcomm w hm e ?_ ?_ E hEL hEQ
    · rw [primeRank_eq_of_surjective_of_coprime 2 F.specialToProjective
        F.specialToProjective_surjective F.odd_card_specialToProjective_ker.coprime_two_left]
      exact (HermitianForm.EvenTwoRank.two_rank F (n := 1) (by decide) hK hconj).le
    · intro S
      let T := S.mapSurjective (f := F.specialToProjective) F.specialToProjective_surjective
      have hh := HermitianForm.BinarySylowOrder.cube_le_sylow_card F
        (n := 1) (by decide) hK hconj T
      have hle : Nat.card T ≤ Nat.card S := Nat.card_le_card_of_surjective
        (fun s : S => (⟨F.specialToProjective s,mem_map_of_mem _ s.property⟩ : T)) (by
          rintro ⟨_,s,hs,rfl⟩
          exact ⟨⟨s,hs⟩,rfl⟩)
      norm_num at hh
      omega

/-- Graph conjugation carries the bound to every center of the same type,
including its literal centralizer and core denominator. -/
theorem reduced_moving_binary_orbit_square
    (h : HypothesisF11 J S₀)
    {a beta a' : Vertex Γ} (hc : IsCriticalPair Γ a a')
    (hab : (graph Γ).Adj a beta)
    (hd : (graph Γ).dist beta a' + 1 = b Γ) (hb : 1 < b Γ)
    (hcomm : ⁅Z Γ a,Z Γ a'⁆ = ⊥)
    (w : (graph Γ).neighborSet a')
    (hm : ⁅V Γ beta 1 ⊓ Q Γ a',Z Γ w.val⁆ ≠ ⊥)
    (hu : ClassicalGroup.IsPSU (graphLocalGroup Γ w.val ⧸
      pCore 2 (graphLocalGroup Γ w.val)) 3 2 ∨
      IsSU (graphLocalGroup Γ w.val ⧸ pCore 2 (graphLocalGroup Γ w.val)) 3 2)
    {v : Vertex Γ} (hvw : v.type = w.val.type)
    (E : Subgroup (Reduction.G₀ J S₀)) [IsElementaryAbelian 2 E]
    (hEL : E ≤ graphLocalGroup Γ v) (hEQ : ¬ E ≤ Q Γ v) :
    4 ≤ (centralizer (E : Set (Reduction.G₀ J S₀))).relIndex (Z Γ v) := by
  let ht := Reduction.reduced_triple h
  let d := Reduction.reducedFullEarlierLocalTheorems h
  let : ∀ i, Finite (Γ i) := finite_endpoints ht
  obtain ⟨g,hg⟩ := (same_orbit_iff Γ v w.val).mpr hvw
  let f := MulAut.conj g
  let E' := E.map f.toMonoidHom
  let : IsElementaryAbelian 2 E' := IsElementaryAbelian.map _
  have hEL' : E' ≤ graphLocalGroup Γ w.val := by
    change E' ≤ d.localGroup w.val
    rw [←hg,d.conjugate]
    exact map_mono hEL
  have hEQ' : ¬ E' ≤ Q Γ w.val := by
    rw [←hg,Q_translate]
    exact fun he => hEQ ((map_le_map_iff_of_injective f.injective).mp he)
  have hh := reduced_moving_binary_square h hc hab hd hb hcomm w hm hu E' hEL' hEQ'
  rw [←hg,Z_translate,←centralizer_map_equiv E f,
    relIndex_map_map_of_injective _ _ f.injective] at hh
  exact hh

/-- An elementary beta-core actor fixing the opposite core intersection
fixes the entire beta span: a nonzero action would have index at least four,
whereas the source core index bounds it by two. -/
theorem reduced_core_actor_fixed
    (h : HypothesisF11 J S₀)
    (models : ∀ v : Vertex Γ,
      IsRankOneModel (graphLocalGroup Γ v ⧸ pCore 2 (graphLocalGroup Γ v)))
    {a beta a' : Vertex Γ} (hc : IsCriticalPair Γ a a')
    (hab : (graph Γ).Adj a beta)
    (hd : (graph Γ).dist beta a' + 1 = b Γ) (hb : 1 < b Γ)
    (hcomm : ⁅Z Γ a,Z Γ a'⁆ = ⊥)
    (w : (graph Γ).neighborSet a')
    (hm : ⁅V Γ beta 1 ⊓ Q Γ a',Z Γ w.val⁆ ≠ ⊥)
    (hu : ClassicalGroup.IsPSU (graphLocalGroup Γ w.val ⧸
      pCore 2 (graphLocalGroup Γ w.val)) 3 2 ∨
      IsSU (graphLocalGroup Γ w.val ⧸ pCore 2 (graphLocalGroup Γ w.val)) 3 2)
    (E : Subgroup (Reduction.G₀ J S₀)) [IsElementaryAbelian 2 E]
    (hEQ : E ≤ Q Γ beta)
    (hEA : E ≤ centralizer ((V Γ beta 1 ⊓ Q Γ a' : Subgroup (Reduction.G₀ J S₀)) :
      Set (Reduction.G₀ J S₀))) :
    E ≤ centralizer (V Γ beta 1 : Set (Reduction.G₀ J S₀)) := by
  let ht := Reduction.reduced_triple h
  let d := Reduction.reducedFullEarlierLocalTheorems h
  let : ∀ i, Finite (Γ i) := finite_endpoints ht
  let F := Γ
  let A := V F beta 1 ⊓ Q F a'
  have hVL : V F beta 1 ≤ stabilizer F beta :=
    V_le_stabilizer_of_dist_add_le_b F ht.generate beta beta 1
      (by simpa only [SimpleGraph.dist_self,zero_add] using hb.le)
  let : Finite (V F beta 1) := Finite.of_injective (inclusion hVL) (inclusion_injective _)
  have hupper : (centralizer (E : Set (Reduction.G₀ J S₀))).relIndex (V F beta 1) ≤
      (Q F a').relIndex (V F beta 1) := by
    have hAC : A ≤ centralizer (E : Set (Reduction.G₀ J S₀)) := le_centralizer_iff.mp hEA
    have hh := relIndex_le_of_le_left hAC (A.subgroupOf (V F beta 1)).index_ne_zero_of_finite
    simpa only [A,inf_relIndex_left] using hh
  have heven : Even ((graph F).dist beta a') := by
    have hodd : Odd (b Γ) := (source_critical_geometry ht d hc hab hd hb hcomm).1
    obtain ⟨k,hk⟩ := hodd
    refine ⟨k,?_⟩
    change (graph Γ).dist beta a' = k+k
    omega
  have htype := (even_dist_iff F ht.generate beta a').mp heven
  apply le_centralizer_iff.mp
  rw [V_one_eq_sup_neighbors]
  apply sup_le
  · exact (Z_centralizes_Q F beta (source_Z_Q_U ht beta).1).trans (centralizer_le hEQ)
  · apply iSup_le
    intro z
    by_contra hz
    have hzt : z.val.type = w.val.type := by
      have hz' := z.property.1
      have hw' := w.property.1
      cases hzt : z.val.type <;> cases hwt : w.val.type <;>
        cases hbt : beta.type <;> cases het : a'.type <;> simp_all
    have hEL : E ≤ d.localGroup z.val := pGroup_le_localGroup F d z.val E
      (IsElementaryAbelian.isPGroup 2 E)
      (hEQ.trans ((source_Z_Q_U ht beta).2.trans
        ((ballKernel_one_le_edge F z.property).trans inf_le_right)))
    have hEQz : ¬ E ≤ Q F z.val := by
      intro he
      exact hz ((Z_centralizes_Q F z.val (source_Z_Q_U ht z.val).1).trans (centralizer_le he))
    have hl := reduced_moving_binary_orbit_square h hc hab hd hb hcomm w hm hu hzt E hEL hEQz
    have hi := relIndex_le_of_le_right (Z_neighbor_le_V F z.property)
      (((centralizer (E : Set (Reduction.G₀ J S₀))).subgroupOf (V F beta 1)).index_ne_zero_of_finite)
    have hi2 := (reduced_binary_indices h models hc hab hd hb hcomm w hm hu).1
    have hh := hl.trans (hi.trans hupper)
    change (Q Γ a').relIndex (V Γ beta 1) = 2 at hi2
    change 4 ≤ (Q Γ a').relIndex (V Γ beta 1) at hh
    omega

/-- The literal beta-core fixed subgroup is unchanged when the actor is
extended from the terminal-core intersection to the full beta span. -/
theorem reduced_core_fixed_subgroup_eq
    (h : HypothesisF11 J S₀)
    (models : ∀ v : Vertex Γ,
      IsRankOneModel (graphLocalGroup Γ v ⧸ pCore 2 (graphLocalGroup Γ v)))
    {a beta a' : Vertex Γ} (hc : IsCriticalPair Γ a a')
    (hab : (graph Γ).Adj a beta)
    (hd : (graph Γ).dist beta a' + 1 = b Γ) (hb : 1 < b Γ)
    (hcomm : ⁅Z Γ a,Z Γ a'⁆ = ⊥)
    (w : (graph Γ).neighborSet a')
    (hm : ⁅V Γ beta 1 ⊓ Q Γ a',Z Γ w.val⁆ ≠ ⊥)
    (hu : ClassicalGroup.IsPSU (graphLocalGroup Γ w.val ⧸
      pCore 2 (graphLocalGroup Γ w.val)) 3 2 ∨
      IsSU (graphLocalGroup Γ w.val ⧸ pCore 2 (graphLocalGroup Γ w.val)) 3 2)
    : (V Γ a' 1 ⊓ Q Γ beta) ⊓ centralizer
        ((V Γ beta 1 ⊓ Q Γ a' : Subgroup (Reduction.G₀ J S₀)) : Set (Reduction.G₀ J S₀)) =
      (V Γ a' 1 ⊓ Q Γ beta) ⊓ centralizer (V Γ beta 1 : Set (Reduction.G₀ J S₀)) := by
  let ht := Reduction.reduced_triple h
  let d := Reduction.reducedFullEarlierLocalTheorems h
  let : ∀ i, Finite (Γ i) := finite_endpoints ht
  have hb3 : 3 ≤ b Γ := (source_critical_geometry ht d hc hab hd hb hcomm).2.1
  let : IsElementaryAbelian 2 (V Γ a' 1) := CommutingThreeProfile.V_elementary Γ ht.generate
    (fun v => (source_Z_Q_U ht v).1) d.kernel_sylow (by omega) a'
  let C := (V Γ a' 1 ⊓ Q Γ beta) ⊓ centralizer
    ((V Γ beta 1 ⊓ Q Γ a' : Subgroup (Reduction.G₀ J S₀)) : Set (Reduction.G₀ J S₀))
  let : IsElementaryAbelian 2 C := IsElementaryAbelian.of_le (inf_le_left.trans inf_le_left)
  apply le_antisymm
  · exact le_inf inf_le_left (reduced_core_actor_fixed h models hc hab hd hb hcomm w hm hu C
      (inf_le_left.trans inf_le_right) inf_le_right)
  · exact inf_le_inf_left _ (centralizer_le inf_le_left)

/-- If the chosen fixed subgroup is trapped in the beta core, it fixes
all of the beta span. The trapping premise remains explicit. -/
theorem reduced_trapped_fixed_centralizer
    (h : HypothesisF11 J S₀)
    (models : ∀ v : Vertex Γ,
      IsRankOneModel (graphLocalGroup Γ v ⧸ pCore 2 (graphLocalGroup Γ v)))
    {a beta a' : Vertex Γ} (hc : IsCriticalPair Γ a a')
    (hab : (graph Γ).Adj a beta)
    (hd : (graph Γ).dist beta a' + 1 = b Γ) (hb : 1 < b Γ)
    (hcomm : ⁅Z Γ a,Z Γ a'⁆ = ⊥)
    (w : (graph Γ).neighborSet a')
    (hm : ⁅V Γ beta 1 ⊓ Q Γ a',Z Γ w.val⁆ ≠ ⊥)
    (hu : ClassicalGroup.IsPSU (graphLocalGroup Γ w.val ⧸
      pCore 2 (graphLocalGroup Γ w.val)) 3 2 ∨
      IsSU (graphLocalGroup Γ w.val ⧸ pCore 2 (graphLocalGroup Γ w.val)) 3 2)
    (htrap : Z Γ w.val ⊓ centralizer
      ((V Γ beta 1 ⊓ Q Γ a' : Subgroup (Reduction.G₀ J S₀)) : Set (Reduction.G₀ J S₀)) ≤ Q Γ beta) :
    Z Γ w.val ⊓ centralizer
      ((V Γ beta 1 ⊓ Q Γ a' : Subgroup (Reduction.G₀ J S₀)) : Set (Reduction.G₀ J S₀)) ≤
        centralizer (V Γ beta 1 : Set (Reduction.G₀ J S₀)) := by
  let : IsElementaryAbelian 2 (Z Γ w.val) :=
    CommutingOneProfile.source_center_elementary (Reduction.reduced_triple h) w.val
  let C := Z Γ w.val ⊓ centralizer
    ((V Γ beta 1 ⊓ Q Γ a' : Subgroup (Reduction.G₀ J S₀)) : Set (Reduction.G₀ J S₀))
  let : IsElementaryAbelian 2 C := IsElementaryAbelian.of_le inf_le_left
  exact reduced_core_actor_fixed h models hc hab hd hb hcomm w hm hu C htrap inf_le_right

/-- A trapped binary moving-center fixed subgroup is exactly the common
intersection of the terminal neighboring centers, with literal relative normality. -/
theorem reduced_trapped_fixed_intersection
    (h : HypothesisF11 J S₀)
    (models : ∀ v : Vertex Γ,
      IsRankOneModel (graphLocalGroup Γ v ⧸ pCore 2 (graphLocalGroup Γ v)))
    {a beta a' : Vertex Γ} (hc : IsCriticalPair Γ a a')
    (hab : (graph Γ).Adj a beta)
    (hd : (graph Γ).dist beta a' + 1 = b Γ) (hb : 1 < b Γ)
    (hcomm : ⁅Z Γ a,Z Γ a'⁆ = ⊥)
    (w : (graph Γ).neighborSet a')
    (hm : ⁅V Γ beta 1 ⊓ Q Γ a',Z Γ w.val⁆ ≠ ⊥)
    (hu : ClassicalGroup.IsPSU (graphLocalGroup Γ w.val ⧸
      pCore 2 (graphLocalGroup Γ w.val)) 3 2 ∨
      IsSU (graphLocalGroup Γ w.val ⧸ pCore 2 (graphLocalGroup Γ w.val)) 3 2)
    (htrap : Z Γ w.val ⊓ centralizer
      ((V Γ beta 1 ⊓ Q Γ a' : Subgroup (Reduction.G₀ J S₀)) : Set (Reduction.G₀ J S₀)) ≤ Q Γ beta) :
    let A := V Γ beta 1 ⊓ Q Γ a'
    let C := Z Γ w.val ⊓ centralizer (A : Set (Reduction.G₀ J S₀))
    graphLocalGroup Γ a' ≤ normalizer (C : Set (Reduction.G₀ J S₀)) ∧
      C = neighborCenterIntersection Γ a' ∧
      ∀ z : (graph Γ).neighborSet a', A ≤ Q Γ z.val → C = Z Γ w.val ⊓ Z Γ z.val := by
  let ht := Reduction.reduced_triple h
  let d := Reduction.reducedFullEarlierLocalTheorems h
  let hB := Reduction.reduced_borel_core_sylow h
  let : ∀ i, Finite (Γ i) := finite_endpoints ht
  let F := Γ
  let A := V F beta 1 ⊓ Q F a'
  let C := Z F w.val ⊓ centralizer (A : Set (Reduction.G₀ J S₀))
  change d.localGroup a' ≤ normalizer (C : Set (Reduction.G₀ J S₀)) ∧
    C = neighborCenterIntersection F a' ∧
    ∀ z : (graph F).neighborSet a', A ≤ Q F z.val → C = Z F w.val ⊓ Z F z.val
  have hCV : C ≤ centralizer (V F beta 1 : Set (Reduction.G₀ J S₀)) :=
    reduced_trapped_fixed_centralizer h models hc hab hd hb hcomm w hm hu htrap
  obtain ⟨T,hT⟩ := source_moving_edge_generation ht hB d hc hab hd hb hcomm (models a') w hm
  let T₀ := T.toSubgroup.map
    (stabilizer F a' ⊓ stabilizer F w.val).subtype
  change V F beta 1 ⊔ T₀ = d.localGroup a' at hT
  have hTw : T₀ ≤ stabilizer F w.val := (map_subtype_le _).trans inf_le_right
  have hTA : ⁅T₀,A⁆ ≤ Q F w.val :=
    source_moving_actor_displacement ht d hc hab hd hb hcomm w (models w.val) T
  have hTC : T₀ ≤ normalizer (C : Set (Reduction.G₀ J S₀)) :=
    normalizes_inf_centralizer_of_displacement T₀ (Z F w.val) A (Q F w.val)
      (hTw.trans (stabilizer_normalizes_Z F w.val))
      (hTw.trans (stabilizer_normalizes_Q F w.val))
      (Z_centralizes_Q F w.val (source_Z_Q_U ht w.val).1)
      (by rw [commutator_comm]; exact hTA)
  have hMC : d.localGroup a' ≤ normalizer (C : Set (Reduction.G₀ J S₀)) := by
    rw [←hT]
    exact sup_le ((le_centralizer_iff.mp hCV).trans (Subgroup.centralizer_le_normalizer _)) hTC
  have hCZ (z : (graph F).neighborSet a') : C ≤ Z F z.val := by
    obtain ⟨g,hg,hgz⟩ := d.transitive a' w z
    have he : (Z F w.val).map (MulAut.conj g).toMonoidHom = Z F z.val :=
      (Z_translate F g w.val).symm.trans (congrArg (Z F) hgz)
    rw [←he]
    exact normal_subgroup_le_conjugate (d.localGroup a') C (Z F w.val) hMC inf_le_left hg
  have hCX : C ≤ neighborCenterIntersection F a' :=
    le_iInf (fun z : (graph F).neighborSet a' => hCZ z)
  have hpair (z : (graph F).neighborSet a') (hAz : A ≤ Q F z.val) :
      C = Z F w.val ⊓ Z F z.val := by
    apply le_antisymm (le_inf inf_le_left (hCZ z))
    exact le_inf inf_le_left (inf_le_right.trans
      ((Z_centralizes_Q F z.val (source_Z_Q_U ht z.val).1).trans (centralizer_le hAz)))
  obtain ⟨_,_,_,_,prev,hp,_,hVP,_⟩ := source_critical_geometry ht d hc hab hd hb hcomm
  have hXpair : neighborCenterIntersection F a' ≤ Z F w.val ⊓ Z F prev :=
    le_inf (iInf_le (fun z : (graph F).neighborSet a' => Z F z.val) w)
      (iInf_le (fun z : (graph F).neighborSet a' => Z F z.val) ⟨prev,hp⟩)
  refine ⟨hMC,le_antisymm hCX ?_,hpair⟩
  rw [hpair ⟨prev,hp⟩ (inf_le_left.trans hVP)]
  exact hXpair

/-- In the binary unitary branch the intersection commutator is nonzero:
otherwise the index-two opposite core would contradict the unitary bound four. -/
theorem reduced_intersection_nontrivial
    (h : HypothesisF11 J S₀)
    (models : ∀ v : Vertex Γ,
      IsRankOneModel (graphLocalGroup Γ v ⧸ pCore 2 (graphLocalGroup Γ v)))
    {a beta a' : Vertex Γ} (hc : IsCriticalPair Γ a a')
    (hab : (graph Γ).Adj a beta)
    (hd : (graph Γ).dist beta a' + 1 = b Γ) (hb : 1 < b Γ)
    (hcomm : ⁅Z Γ a,Z Γ a'⁆ = ⊥)
    (w : (graph Γ).neighborSet a')
    (hm : ⁅V Γ beta 1 ⊓ Q Γ a',Z Γ w.val⁆ ≠ ⊥)
    (hu : ClassicalGroup.IsPSU (graphLocalGroup Γ w.val ⧸
      pCore 2 (graphLocalGroup Γ w.val)) 3 2 ∨
      IsSU (graphLocalGroup Γ w.val ⧸ pCore 2 (graphLocalGroup Γ w.val)) 3 2)
    : ⁅V Γ beta 1 ⊓ Q Γ a',V Γ a' 1 ⊓ Q Γ beta⁆ ≠ ⊥ := by
  let ht := Reduction.reduced_triple h
  let d := Reduction.reducedFullEarlierLocalTheorems h
  let : ∀ i, Finite (Γ i) := finite_endpoints ht
  have hb3 : 3 ≤ b Γ := (source_critical_geometry ht d hc hab hd hb hcomm).2.1
  let : IsElementaryAbelian 2 (V Γ beta 1) := CommutingThreeProfile.V_elementary Γ ht.generate
    (fun v => (source_Z_Q_U ht v).1) d.kernel_sylow (by omega) beta
  let A := V Γ beta 1 ⊓ Q Γ a'
  let : IsElementaryAbelian 2 A := IsElementaryAbelian.of_le inf_le_left
  obtain ⟨_,hAL,_,hAQ,_⟩ := source_moving_actor ht d hc hab hd hb hcomm w hm
  have hl := reduced_moving_binary_square h hc hab hd hb hcomm w hm hu A hAL hAQ
  intro hi
  have hh := hl.trans (source_commuting_intersection_fixed_index_le ht hb w hi)
  have he := (reduced_binary_indices h models hc hab hd hb hcomm w hm hu).2.1
  change 4 ≤ (Q Γ beta).relIndex (V Γ a' 1) at hh
  omega

/-- The retained binary moving hypothesis places the original source
configuration in the noncentral and nonnatural case of 8.6. The source 8.7
assembly must therefore exclude this configuration, not infer naturality
from its omega-center action alone. -/
theorem reduced_noncentral_and_nonnatural
    (h : HypothesisF11 J S₀)
    (models : ∀ v : Vertex Γ,
      IsRankOneModel (graphLocalGroup Γ v ⧸ pCore 2 (graphLocalGroup Γ v)))
    {a beta a' : Vertex Γ} (hc : IsCriticalPair Γ a a')
    (hab : (graph Γ).Adj a beta)
    (hd : (graph Γ).dist beta a' + 1 = b Γ) (hb : 1 < b Γ)
    (hcomm : ⁅Z Γ a,Z Γ a'⁆ = ⊥)
    (w : (graph Γ).neighborSet a')
    (hm : ⁅V Γ beta 1 ⊓ Q Γ a',Z Γ w.val⁆ ≠ ⊥)
    (hu : ClassicalGroup.IsPSU (graphLocalGroup Γ w.val ⧸
      pCore 2 (graphLocalGroup Γ w.val)) 3 2 ∨
      IsSU (graphLocalGroup Γ w.val ⧸ pCore 2 (graphLocalGroup Γ w.val)) 3 2)
    : (¬ ⁅V Γ beta 1 ⊓ Q Γ a',V Γ a' 1⁆ ≤ Z Γ a') ∧
      ¬ Noncommuting.HasNaturalCenter (graphLocalGroup Γ a) (Z Γ a) (Q Γ a) := by
  have hne : ⁅V Γ beta 1 ⊓ Q Γ a',V Γ a' 1⁆ ≠ ⊥ := by
    intro hz
    exact hm (bot_unique ((commutator_mono le_rfl (Z_neighbor_le_V Γ w.property)).trans hz.le))
  obtain ⟨_,_,_,_,hAD,hDI,hIN,_⟩ :=
    reduced_critical_central_equivalences h models hc hab hd hb hcomm hne
  have hi := reduced_intersection_nontrivial h models hc hab hd hb hcomm w hm hu
  exact ⟨fun hH => hi (hDI.mp (hAD.mp hH)),fun hn => hi (hIN.mpr hn)⟩

end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingNontrivial.BinaryUnitaryCentrality
