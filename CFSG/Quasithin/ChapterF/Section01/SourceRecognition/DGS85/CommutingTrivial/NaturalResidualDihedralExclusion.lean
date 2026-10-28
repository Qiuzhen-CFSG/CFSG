module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingTrivial.TorusOmegaBound
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.Noncommuting.TerminalDihedral
public import Theory.GroupAction.SmallQuotientCentralization
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.LocalStructure.FullGraphObstruction

/-!
# Natural residual sections exclude the adjacent dihedral quotient

The beta torus normalizes the alpha Sylow quotient. If that quotient has
order two, its torus action is trivial. The source fixed subgroup on the
alpha center and coprime decomposition then force the beta torus to be
trivial, so the beta field has order two. The resulting fixed-space index
at alpha is at most two, contradicting the dihedral quintic displacement
bound. This uses the literal residual section and does not assume zero
critical displacement or a binary model witness at alpha.

This removes the dihedral exception when applying the natural-residual
recognition argument to the full source catalogue in DGS, *Groups and
Graphs* (1985), 8.5 and 9.4, printed pp.139,143.
-/

@[expose] public noncomputable section
open Subgroup Representation Representation.BinaryOffender
open Representation.RankOne.QuadraticRecognition
open Subgroup.CosetGeometry.RankTwo Theory.GroupTheory.AmalgamGraph
open scoped MatrixGroups IsMulCommutative commutatorElement
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingTrivial
variable {G : Type*} [Group G]

private theorem small_quotient_commutator (P U Z : Subgroup G) [Finite U]
    (hPU : P ≤ normalizer (U : Set G)) (hPZ : P ≤ normalizer (Z : Set G))
    (hN : (Z.subgroupOf U).Normal) :
    let := hN
    Nat.card (U ⧸ Z.subgroupOf U) = 2 → ⁅U,P⁆ ≤ Z := by
  let := hN
  dsimp only
  intro hc
  obtain ⟨action,hact⟩ := exists_quotient_conjugation_action P U Z hPU hPZ hN
  have hfix (p : P) (x : U ⧸ Z.subgroupOf U) : action p x = x := by
    obtain ⟨z,_,hz⟩ := (Nat.card_eq_two_iff' (1 : U ⧸ Z.subgroupOf U)).mp hc
    by_cases hx : x = 1
    · simp only [hx,map_one]
    · exact (hz _ (fun he => hx ((action p).injective (he.trans (map_one _).symm)))).trans
        (hz _ hx).symm
  rw [commutator_comm]
  apply commutator_le.mpr
  intro p hp u hu
  have he := hact ⟨p,hp⟩ ⟨u,hu⟩
  rw [hfix] at he
  have hm := QuotientGroup.eq_iff_div_mem.mp he.symm
  change p*u*p⁻¹/u ∈ Z at hm
  simpa only [div_eq_mul_inv,commutatorElement_def] using hm

private theorem dihedral_sylow_omega (D : Type*) [Group D] [Finite D]
    (e : D ≃* DihedralGroup 5) (T : Sylow 2 D) :
    Nat.card T = 2 ∧ omegaCenterIn (T : Subgroup D) = T := by
  have hc : Nat.card D = 10 := by rw [Nat.card_congr e.toEquiv,DihedralGroup.nat_card]
  have hT : Nat.card T = 2 := by
    rw [T.card_eq_multiplicity,hc]
    rw [show 10 = 2*5 from rfl,Nat.factorization_mul (by decide) (by decide),
      Nat.prime_two.factorization,Nat.prime_five.factorization]
    norm_num
  let : IsCyclic T := isCyclic_of_prime_card hT
  refine ⟨hT,le_antisymm (map_subtype_le _) ?_⟩
  intro t ht
  apply (mem_omegaCenterIn_iff _ _).mpr
  refine ⟨ht,?_,?_⟩
  · intro s hs
    exact congrArg Subtype.val (mul_comm' (⟨s,hs⟩ : (T : Subgroup D)) ⟨t,ht⟩)
  · have he := pow_card_eq_one' (x := (⟨t,ht⟩ : T))
    change (⟨t,ht⟩ : (T : Subgroup D)) ^ Nat.card (T : Subgroup D) = 1 at he
    rw [hT] at he
    exact congrArg Subtype.val he

variable {L : Fin 2 → Subgroup G} {S₀ : Subgroup G}

private theorem reduced_dihedral_natural_residual_field_two (h : HypothesisF11 L S₀)
    (hob : ∀ v w : Vertex (Reduction.reducedFamily L S₀),
      (graph (Reduction.reducedFamily L S₀)).Adj v w →
      ¬ stabilizer (Reduction.reducedFamily L S₀) v ≤ normalizer
        ((Q (Reduction.reducedFamily L S₀) w ⊓ Q (Reduction.reducedFamily L S₀) v :
          Subgroup (Reduction.G₀ L S₀)) : Set (Reduction.G₀ L S₀)))
    {a beta a' : Vertex (Reduction.reducedFamily L S₀)}
    (hc : IsCriticalPair (Reduction.reducedFamily L S₀) a a')
    (hab : (graph (Reduction.reducedFamily L S₀)).Adj a beta)
    (hd : (graph (Reduction.reducedFamily L S₀)).dist beta a' + 1 = b (Reduction.reducedFamily L S₀))
    (hb : 1 < b (Reduction.reducedFamily L S₀))
    (hcomm : ⁅Z (Reduction.reducedFamily L S₀) a, Z (Reduction.reducedFamily L S₀) a'⁆ = ⊥)
    (M : IsRankOneModel (graphLocalGroup (Reduction.reducedFamily L S₀) a ⧸
      pCore 2 (graphLocalGroup (Reduction.reducedFamily L S₀) a)))
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    {n : ℕ} (hn : 0 < n) (hF : Nat.card F = 2^n)
    (e : (graphLocalGroup (Reduction.reducedFamily L S₀) beta ⧸
      pCore 2 (graphLocalGroup (Reduction.reducedFamily L S₀) beta)) ≃* SL(2,F))
    (hres : NaturalResidualSection h beta e n)
    (ed : (graphLocalGroup (Reduction.reducedFamily L S₀) a ⧸
      pCore 2 (graphLocalGroup (Reduction.reducedFamily L S₀) a)) ≃* DihedralGroup 5) : Nat.card F = 2 := by
  let ht := Reduction.reduced_triple h
  let d := Reduction.reducedEarlierLocalTheorems h hob
  let Γ := Reduction.reducedFamily L S₀
  let H := graphLocalGroup Γ a
  let Hβ := graphLocalGroup Γ beta
  let E := (stabilizer Γ a ⊓ stabilizer Γ beta).pCoreIn 2
  let W := conjugateSpanBy (Q Γ a) (stabilizer Γ beta)
  let Z₀ := Z Γ a ⊓ (Subgroup.center W).map W.subtype
  let q := QuotientGroup.mk' (pCore 2 H)
  let : ∀ i, Finite (Γ i) := finite_endpoints ht
  let : Finite H := Finite.of_injective (inclusion (sylowGenerated_le _)) (inclusion_injective _)
  let : Finite Hβ := Finite.of_injective (inclusion (sylowGenerated_le _)) (inclusion_injective _)
  let : Finite (Z Γ a) := Finite.of_injective (inclusion (Z_le_stabilizer Γ a)) (inclusion_injective _)
  let := Z_elementary Γ (fun v => (source_Z_Q_U ht v).1) a
  obtain ⟨R,hR,hYW,hYZ,hZY,hquad,hindex⟩ :=
    reduced_natural_residual_omega_quadratic h hob hc hab hd hb hcomm M hn hF e hres
  let T : Sylow 2 (H ⧸ pCore 2 H) := R.mapSurjective (QuotientGroup.mk'_surjective _)
  let A := omegaCenterIn ((R : Subgroup H).map q)
  let Y := (A.comap q).map H.subtype
  change (R : Subgroup H).map H.subtype = E at hR
  have hER : E.subgroupOf H = (R : Subgroup H) := by
    rw [←hR]
    exact comap_map_eq_self_of_injective H.subtype_injective _
  have hYH : Y ≤ H := map_subtype_le _
  let : Finite Y := Finite.of_injective (inclusion hYH) (inclusion_injective hYH)
  have hYq : (Y.subgroupOf H).map q = A := by
    change ((A.comap q).map H.subtype |>.comap H.subtype).map q = A
    rw [comap_map_eq_self_of_injective H.subtype_injective,
      map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _)]
  have hYE : Y ≤ E := by
    rw [←hR]
    apply map_mono
    have hh := comap_mono (f := q) (map_subtype_le
      ((omega₁ (center ((R : Subgroup H).map q)) (p := 2)).map
        (center ((R : Subgroup H).map q)).subtype))
    have hk : q.ker ≤ (R : Subgroup H) := by
      rw [QuotientGroup.ker_mk']
      exact pCore_isPGroup.le_sylow_of_normal R
    exact hh.trans (comap_map_eq_self hk).le
  have hYP : Y ≤ stabilizer Γ a := hYH.trans (sylowGenerated_le _)
  have hYtwo : IsPGroup 2 Y := (isPGroup_pCoreIn 2 _).to_le hYE
  have hYC := Reduction.reduced_critical_inf_centralizer h hc Y hYtwo hYP
  have hqker : q.ker = (Q Γ a).subgroupOf H :=
    CommutingNontrivial.local_quotient_kernel Γ d a (MulEquiv.refl _)
  have hi : (Q Γ a).relIndex Y = Nat.card A := by
    rw [←Representation.BinaryConjugationSection.actor_image_card_eq_relIndex
      H (Q Γ a) Y q hqker hYH,hYq]
  have hiC : (centralizer (Z Γ a : Set (Reduction.G₀ L S₀))).relIndex Y = Nat.card A := by
    calc
      _ = (Y ⊓ centralizer (Z Γ a : Set (Reduction.G₀ L S₀))).relIndex Y :=
        (inf_relIndex_left _ _).symm
      _ = (Y ⊓ Q Γ a).relIndex Y := congrArg (fun U => U.relIndex Y) hYC
      _ = (Q Γ a).relIndex Y := inf_relIndex_left _ _
      _ = Nat.card A := hi
  have hTne : (T : Subgroup (H ⧸ pCore 2 H)) ≠ ⊥ := by
    intro he
    have hh := (M.rankOneSylowFacts T).proper
    change normalizer (↑(T : Subgroup (H ⧸ pCore 2 H)) : Set (H ⧸ pCore 2 H)) < ⊤ at hh
    rw [he,normalizer_eq_top] at hh
    exact (lt_irrefl _ hh)
  let : Nontrivial T := (nontrivial_iff_ne_bot _).mpr hTne
  have hAne : A ≠ ⊥ := by
    have hh := omega_center_ne_bot T.isPGroup'
    intro he
    apply hh
    apply (Subgroup.map_eq_bot_iff_of_injective _ (T : Subgroup (H ⧸ pCore 2 H)).subtype_injective).mp
    exact he
  have hYnc : ¬ Y ≤ centralizer (Z Γ a : Set (Reduction.G₀ L S₀)) := by
    intro hh
    have hcard : Nat.card A = 1 := by rw [←hiC,relIndex_eq_one.mpr hh]
    exact hAne (card_eq_one.mp hcard)
  obtain ⟨hTc,hω⟩ := dihedral_sylow_omega (H ⧸ pCore 2 H) ed T
  have hAc : Nat.card A = 2 := by
    change Nat.card (omegaCenterIn (T : Subgroup (H ⧸ pCore 2 H))) = 2
    rw [hω]
    exact hTc
  have hYEeq : Y = E := by
    change ((omegaCenterIn (T : Subgroup (H ⧸ pCore 2 H))).comap q).map H.subtype = E
    rw [hω]
    change (((R : Subgroup H).map q).comap q).map H.subtype = E
    rw [comap_map_eq_self (show q.ker ≤ (R : Subgroup H) by
      rw [QuotientGroup.ker_mk']
      exact pCore_isPGroup.le_sylow_of_normal R),hR]
  obtain ⟨K,hK,hodd,hKcard,hKR,hKW⟩ :=
    reduced_linear_neighbor_torus h hab (hob a beta hab) hn hF e
  let : Finite K := Finite.of_injective (inclusion (hK.trans inf_le_left)) (inclusion_injective _)
  have hKn : K ≤ normalizer (Z Γ a : Set (Reduction.G₀ L S₀)) :=
    (hK.trans inf_le_right).trans (CommutingNontrivial.stabilizer_normalizes_Z Γ a)
  have hKH : K ≤ normalizer (H : Set (Reduction.G₀ L S₀)) :=
    (hK.trans inf_le_right).trans (sylowGenerated_normalized _)
  have hKE : K ≤ normalizer (E : Set (Reduction.G₀ L S₀)) := by
    apply le_trans (le_inf (hK.trans inf_le_right)
      ((hK.trans inf_le_left).trans (sylowGenerated_le _)))
    exact (stabilizer Γ a ⊓ stabilizer Γ beta).le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image _ (pCore 2 _))
  have hKY : K ≤ normalizer (Y : Set (Reduction.G₀ L S₀)) := hYEeq.symm ▸ hKE
  have hKQ : K ≤ normalizer (Q Γ a : Set (Reduction.G₀ L S₀)) :=
    (hK.trans inf_le_right).trans (CommutingNontrivial.stabilizer_normalizes_Q Γ a)
  have hQY : Q Γ a ≤ Y := by
    rw [hYEeq]
    exact Noncommuting.graph_Q_le_edgeCore ht hab
  have hN : ((Q Γ a).subgroupOf Y).Normal :=
    (normal_subgroupOf_iff_le_normalizer hQY).mpr
      (hYP.trans (CommutingNontrivial.stabilizer_normalizes_Q Γ a))
  have hsmall : ⁅Y,K⁆ ≤ Q Γ a := by
    apply small_quotient_commutator K Y (Q Γ a) hKY hKQ hN
    change ((Q Γ a).subgroupOf Y).index = 2
    change (Q Γ a).relIndex Y = 2
    exact hi.trans hAc
  have hKb : K = ⊥ := by
    apply bot_unique
    intro k hk
    apply mem_bot.mpr
    by_contra hk1
    let D := zpowers k
    have hDK : D ≤ K := zpowers_le.mpr hk
    let : Finite D := Finite.of_injective (inclusion hDK) (inclusion_injective _)
    let kβ : Hβ := ⟨k,(hK hk).1⟩
    have ho : Odd (orderOf kβ) := by
      have hh := hodd.of_dvd_nat (_root_.orderOf_dvd_natCard (⟨k,hk⟩ : K))
      simpa only [kβ,Subgroup.orderOf_mk] using hh
    have hfixed := reduced_natural_residual_neighbor_odd_fixed h hc hab hd hb hcomm
      (hob a beta hab) e hres kβ ho (fun he => hk1 (congrArg Subtype.val he))
    change Z Γ a ⊓ centralizer ({k} : Set (Reduction.G₀ L S₀)) = Z₀ at hfixed
    have hfix : Z Γ a ⊓ centralizer (D : Set (Reduction.G₀ L S₀)) = Z₀ := by
      apply le_antisymm
      · rw [←hfixed]
        exact inf_le_inf_left _ (centralizer_le (Set.singleton_subset_iff.mpr (mem_zpowers k)))
      · rw [←hfixed]
        rintro z ⟨hz,hzk⟩
        refine ⟨hz,?_⟩
        rintro _ ⟨m,rfl⟩
        exact (Commute.zpow_left (show Commute k z from
          (mem_centralizer_singleton_iff.mp hzk).symm) m).eq
    have hcop : Nat.Coprime (Nat.card D) (Nat.card (Z Γ a)) := by
      obtain ⟨m,hm⟩ := (IsElementaryAbelian.isPGroup 2 (Z Γ a)).exists_card_eq
      rw [hm]
      exact (hodd.of_dvd_nat (card_dvd_of_le hDK)).coprime_two_left.symm.pow_right m
    have hQcent : Q Γ a ≤ centralizer (Z Γ a : Set (Reduction.G₀ L S₀)) :=
      le_centralizer_iff.mp (CommutingNontrivial.Z_centralizes_Q Γ a (source_Z_Q_U ht a).1)
    change ⁅Z Γ a,Y⁆ ≤ Z₀ at hYZ
    change Z₀ ≤ centralizer (Y : Set (Reduction.G₀ L S₀)) at hZY
    have hzero := le_centralizer_of_coprime_fixed_layer (Z Γ a) D Y
      (hDK.trans hKn) (Group.isSolvable_of_comm fun x y => mul_comm x y) hcop
      (hYZ.trans (hfix.symm ▸ inf_le_right)) (hfix.symm ▸ hZY)
      ((commutator_mono le_rfl hDK).trans (hsmall.trans hQcent))
    exact hYnc (le_centralizer_iff.mp hzero)
  have hcK : Nat.card F - 1 = 1 := by
    rw [hKb,card_bot] at hKcard
    exact hKcard.symm
  have hFpos : 1 < Nat.card F := Finite.one_lt_card
  omega

/-- A natural beta residual section rules out the actual adjacent D₁₀ model. -/
theorem reduced_natural_residual_not_dihedral (h : HypothesisF11 L S₀)
    {a beta a' : Vertex (Reduction.reducedFamily L S₀)}
    (hc : IsCriticalPair (Reduction.reducedFamily L S₀) a a')
    (hab : (graph (Reduction.reducedFamily L S₀)).Adj a beta)
    (hd : (graph (Reduction.reducedFamily L S₀)).dist beta a' + 1 = b (Reduction.reducedFamily L S₀))
    (hb : 1 < b (Reduction.reducedFamily L S₀))
    (hcomm : ⁅Z (Reduction.reducedFamily L S₀) a, Z (Reduction.reducedFamily L S₀) a'⁆ = ⊥)
    (M : IsRankOneModel (graphLocalGroup (Reduction.reducedFamily L S₀) a ⧸
      pCore 2 (graphLocalGroup (Reduction.reducedFamily L S₀) a)))
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    {n : ℕ} (hn : 0 < n) (hF : Nat.card F = 2^n)
    (e : (graphLocalGroup (Reduction.reducedFamily L S₀) beta ⧸
      pCore 2 (graphLocalGroup (Reduction.reducedFamily L S₀) beta)) ≃* SL(2,F))
    (hres : NaturalResidualSection h beta e n)
    (ed : (graphLocalGroup (Reduction.reducedFamily L S₀) a ⧸
      pCore 2 (graphLocalGroup (Reduction.reducedFamily L S₀) a)) ≃* DihedralGroup 5) : False := by
  let hob := Reduction.reduced_graph_core_obstruction h
  have hFtwo := reduced_dihedral_natural_residual_field_two h hob hc hab hd hb hcomm M hn hF e hres ed
  let ht := Reduction.reduced_triple h
  let Γ := Reduction.reducedFamily L S₀
  let d := Reduction.reducedEarlierLocalTheorems h hob
  let H := graphLocalGroup Γ a
  let D := H ⧸ pCore 2 H
  let q := QuotientGroup.mk' (pCore 2 H)
  let : ∀ i, Finite (Γ i) := finite_endpoints ht
  let := Z_elementary Γ (fun v => (source_Z_Q_U ht v).1) a
  let : Finite H := Finite.of_injective (inclusion (sylowGenerated_le _)) (inclusion_injective _)
  let : Finite (Z Γ a) := Finite.of_injective (inclusion (Z_le_stabilizer Γ a)) (inclusion_injective _)
  let : Nontrivial (Z Γ a) := CommutingNontrivial.source_center_nontrivial ht a
  obtain ⟨R,hR,hYW,hYZ,hZY,hquadY,hindex⟩ :=
    reduced_natural_residual_omega_quadratic h hob hc hab hd hb hcomm M hn hF e hres
  let T : Sylow 2 D := R.mapSurjective (QuotientGroup.mk'_surjective _)
  let A := omegaCenterIn ((R : Subgroup H).map q)
  let Y := (A.comap q).map H.subtype
  let Z₀ := Z Γ a ⊓ (Subgroup.center (conjugateSpanBy (Q Γ a) (stabilizer Γ beta))).map
    (conjugateSpanBy (Q Γ a) (stabilizer Γ beta)).subtype
  change Z₀.relIndex (Z Γ a) = Nat.card F at hindex
  change Z₀ ≤ centralizer (Y : Set (Reduction.G₀ L S₀)) at hZY
  change ⁅⁅Z Γ a,Y⁆,Y⁆ = ⊥ at hquadY
  have hYH : Y ≤ H := map_subtype_le _
  have hYq : (Y.subgroupOf H).map q = A := by
    change ((A.comap q).map H.subtype |>.comap H.subtype).map q = A
    rw [comap_map_eq_self_of_injective H.subtype_injective,
      map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _)]
  obtain ⟨ρ,hact⟩ := CommutingNontrivial.source_exists_center_quotient_action ht d a (MulEquiv.refl D)
  change Representation (ZMod 2) D (Additive (Z Γ a)) at ρ
  change ∀ (l : H) (z : Additive (Z Γ a)),
    ((ρ (q l) z).toMul : Reduction.G₀ L S₀) =
      (l : Reduction.G₀ L S₀) * z.toMul * (l : Reduction.G₀ L S₀)⁻¹ at hact
  obtain ⟨T₀⟩ := Sylow.nonempty (p := 2) (G := stabilizer Γ a)
  have hgeom := Reduction.reduced_commuting_critical_geometry h hc hab hd hb hcomm
  have hz := intrinsic_local_center_eq_bot_of_neighbor_central ht
    (Reduction.reduced_borel_core_sylow h) (Reduction.reduced_vertex_sylow h) hab hgeom.2.2.1
  obtain ⟨S,hS,hgen,hres₀⟩ := CommutingNontrivial.source_center_module_prepared_of_center_eq_bot
    ht d a hz T₀ (MulEquiv.refl D) ρ hact
  have hgT : GeneratedByFixedSpace ρ (T : Subgroup D) := by
    obtain ⟨g,hg⟩ := MulAction.exists_smul_eq D S T
    rw [←hg]
    exact generatedByFixedSpace_of_equivariant_surjection ρ ρ
      (MulAut.conj g).toMonoidHom (ρ g)
      (fun v => ⟨ρ g⁻¹ v,ρ.self_inv_apply g v⟩)
      (by intro a v; simp only [MulEquiv.toMonoidHom_eq_coe,MonoidHom.coe_coe,
        MulAut.conj_apply,map_mul,Module.End.mul_apply,ρ.inv_self_apply]) S hgen
  have hZL : Z Γ a ≤ H := CommutingNontrivial.pGroup_le_localGroup Γ d a _
    (IsElementaryAbelian.isPGroup 2 _) (Z_le_stabilizer Γ a)
  have hnZ : H ≤ normalizer (Z Γ a : Set (Reduction.G₀ L S₀)) :=
    (sylowGenerated_le _).trans (CommutingNontrivial.stabilizer_normalizes_Z Γ a)
  have hq : IsQuadratic ρ A := by
    rw [←hYq]
    apply BinaryConjugationSection.isQuadratic_of_triple_commutator_le H (Z Γ a) ⊥ Y
      ρ q (CommutingNontrivial.centerSection H (Z Γ a) hZL hnZ q ρ hact)
    rw [commutator_comm Y (Z Γ a),commutator_comm]
    exact hquadY.le
  have hi := CommutingNontrivial.center_action_fixed_index H (Z Γ a) Y hZL hnZ hYH q ρ hact
  rw [hYq] at hi
  have hle : Nat.card (Additive (Z Γ a) ⧸ fixedSpace ρ A) ≤ Nat.card F := by
    rw [hi,←hindex]
    exact relIndex_le_of_le_left hZY (by rw [hindex]; exact Nat.card_pos.ne')
  have hE : (stabilizer Γ a ⊓ stabilizer Γ beta).pCoreIn 2 ≤ H := by
    rw [←hR]
    exact map_subtype_le _
  have hER : ((stabilizer Γ a ⊓ stabilizer Γ beta).pCoreIn 2).subgroupOf H =
      (R : Subgroup H) := by
    rw [←hR]
    exact comap_map_eq_self_of_injective H.subtype_injective _
  have hfaith := CommutingNontrivial.source_centerless_two_actor_faithful ht d a hz
    ((stabilizer Γ a ⊓ stabilizer Γ beta).pCoreIn 2) (isPGroup_pCoreIn 2 _) hE
    (MulEquiv.refl D) ρ hact
  change Function.Injective
    (ρ.comp ((((stabilizer Γ a ⊓ stabilizer Γ beta).pCoreIn 2).subgroupOf H).map q).subtype)
      at hfaith
  rw [hER] at hfaith
  change Function.Injective (ρ.comp (T : Subgroup D).subtype) at hfaith
  have hdis : Disjoint ρ.ker (T : Subgroup D) := by
    apply disjoint_iff_inf_le.mpr
    rintro t ⟨hk,ht⟩
    have he : (⟨t,ht⟩ : (T : Subgroup D)) = 1 := hfaith (by
      change ρ t = ρ 1
      rw [map_one]
      exact hk)
    exact mem_bot.mpr (congrArg Subtype.val he)
  obtain ⟨hTc,hω⟩ := dihedral_sylow_omega D ed T
  have hAc : Nat.card A = 2 := by
    change Nat.card (omegaCenterIn (T : Subgroup D)) = 2
    rw [hω]
    exact hTc
  exact Noncommuting.dihedral_fixed_generated_index_obstruction ed ρ T A
    (map_subtype_le _) (by rw [hAc]; decide) hgT hdis (hle.trans_eq (hFtwo.trans hAc.symm))

end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingTrivial
