module
public import Stellmacher.SectionTen.TenOneOmegaMiddleResidual
public import Stellmacher.SectionTen.TenOneLargeCentralizerCoreAction
public import Stellmacher.SectionNine.NineThreeOrbitEdgeCoreCentralizer
public import Stellmacher.SectionFiveToSeven.CentralizerLocalTransitivity
public import Theory.GroupAction.AffineFourFixedCentralizer
public import Theory.GroupAction.PrimeDegreeCoprimeIndex

/-!
# The fixed component in source (16) lies in the terminal center

In the actual no-transvection Section Ten context, retain the supplied fixed
component D inside the neighborhood omega center: the terminal residual
centralizes D, the terminal stabilizer normalizes D, its intersection with the
terminal module is the terminal center, and together with the common module
intersection it generates that omega center. The terminal residual two-core
commutator is assumed to lie in the terminal center line. Then D itself lies
in that line. All subgroups and the original ambient embedding are retained.

The middle residual acts on the omega center modulo exactly the middle
four-center. Choose a terminal-core element whose action on the four-center
is nontrivial; its fixed subgroup there is the terminal line. From a supposed
point of D outside that line, form its affine coset modulo the four-center.
The actual middle residual and terminal residual core preserve these four
points. The fixed-orbit theorem supplies a nonidentity point still in D whose
centralizer has index prime to three in that acting group. The coprime-index
transfer makes its centralizer transitive on the three middle neighbors.
The terminal residual already centralizes the point and is locally transitive.
Connectedness and the native faithful-action theorem (7.2) force the point
to be identity, a contradiction.

Source: Stellmacher (10.1), Journal of Algebra 190 (1997), printed p.64,
the last paragraph before (16). This proves the fixed-component step used for
the neighborhood omega-center equality. It does not use the incompatible
printed equality between the full W-centralizer and the module intersection.
-/

namespace Stellmacher.SectionTen
open Later SectionsFiveToSeven CosetGraphContext SevenSix SectionNine
open scoped IsMulCommutative
universe u
variable {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
  {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
  {embedding : G →* H} {T A B : Subgroup G}

omit [Finite G] in
private theorem normalizes_omega (Q : Subgroup G) :
    Subgroup.normalizer (Q : Set G) ≤ Subgroup.normalizer (omegaOneCenter Q : Set G) := by
  let K : Subgroup Q := (omega₁ (G := Subgroup.center Q) (p := 2)).map (Subgroup.center Q).subtype
  let _ : (omega₁ (G := Subgroup.center Q) (p := 2)).Characteristic := omega₁_characteristic (Subgroup.center Q)
  let _ : K.Characteristic := inferInstance
  exact BenderSuzuki.External.hkt_normalizer_le_normalizer_map_subtype_of_characteristic Q K

@[instance_reducible] private noncomputable def neighborAction (Γ : CosetGraphContext G T A B)
    (middle : Γ.Vertex) (K : Subgroup G) (hKP : K ≤ GAt Γ middle) :
    MulAction K {neighbor // Γ.adjacent middle neighbor} where
  smul actor neighbor := ⟨Γ.act (actor : G)⁻¹ neighbor,by
    have hadj := adjacent_act Γ (actor : G)⁻¹ neighbor.property
    rwa [(Set.ext_iff.mp (Γ.stabilizer_def middle) _).mp (hKP (K.inv_mem actor.property))] at hadj⟩
  one_smul neighbor := by
    apply Subtype.ext
    change Γ.act (1 : G)⁻¹ neighbor = neighbor
    simp only [inv_one,Γ.act_one]
  mul_smul first second neighbor := by
    apply Subtype.ext
    change Γ.act ((first:G)*(second:G))⁻¹ neighbor =
      Γ.act (first:G)⁻¹ (Γ.act (second:G)⁻¹ neighbor)
    rw [mul_inv_rev,Γ.act_mul]

public theorem ten_one_large_omega_fixed_subgroup_le_center
    (ctx : AmbientSectionTenContext H S0 S P1 P2 embedding T A B)
    (middle : ctx.Γ.Vertex)
    (hpath : IsCriticalPathOffset ctx.Γ ctx.criticalPath 2 middle)
    (hno : ∀ actor : G, actor ∈ VAt ctx.Γ ctx.criticalPath.firstStep →
      actor ∉ QAt ctx.Γ ctx.criticalPath.a' → ¬ QuotientCardEq
        (⁅VAt ctx.Γ ctx.criticalPath.a', Subgroup.zpowers actor⁆ ⊔
          ZAt ctx.Γ ctx.criticalPath.a') (ZAt ctx.Γ ctx.criticalPath.a') 2)
    (D : Subgroup G)
    (hDO : D ≤ omegaOneCenter (GeneratedNeighborhoodV ctx.Γ middle))
    (hDE : D ≤ Subgroup.centralizer (EAt ctx.Γ ctx.criticalPath.a' : Set G))
    (_hnormal : GAt ctx.Γ ctx.criticalPath.a' ≤ Subgroup.normalizer (D : Set G))
    (hDV : D ⊓ VAt ctx.Γ ctx.criticalPath.a' = ZAt ctx.Γ ctx.criticalPath.a')
    (_hsplit : omegaOneCenter (GeneratedNeighborhoodV ctx.Γ middle) =
      (VAt ctx.Γ ctx.criticalPath.firstStep ⊓ VAt ctx.Γ ctx.criticalPath.a') ⊔ D)
    (hOU : ⁅omegaOneCenter (GeneratedNeighborhoodV ctx.Γ middle),
      twoCoreIn (EAt ctx.Γ ctx.criticalPath.a')⁆ ≤ ZAt ctx.Γ ctx.criticalPath.a') :
    D ≤ ZAt ctx.Γ ctx.criticalPath.a' := by
  classical
  let P := GAt ctx.Γ middle
  let Q := QAt ctx.Γ middle
  let Pn := GAt ctx.Γ ctx.criticalPath.a'
  let E := EAt ctx.Γ middle
  let En := EAt ctx.Γ ctx.criticalPath.a'
  let V := VAt ctx.Γ ctx.criticalPath.a'
  let W := GeneratedNeighborhoodV ctx.Γ middle
  let O := omegaOneCenter W
  let Z := ZAt ctx.Γ middle
  let L := ZAt ctx.Γ ctx.criticalPath.a'
  let U := twoCoreIn En
  let K := E ⊔ U
  have hopen := sectionTenOpeningData ctx middle hpath
  obtain ⟨horbit,hfirst,hterminal,_⟩ := sectionTenOpeningGeometry ctx middle hpath
  have hshort : 1 < ctx.criticalPath.length := by rw [ctx.critical_length]; decide
  have hlong : 2 < ctx.criticalPath.length := by rw [ctx.critical_length]; decide
  obtain ⟨alignment,_,halign⟩ := lemma_seven_five_endpoint_alignment
    ctx.sectionSeven ctx.Γ ctx.criticalPath ctx.commutator_eq
  have hLPn : Pn ≤ Subgroup.centralizer (L : Set G) :=
    nine_next_center_centralizes_stabilizer ctx.toLocalContext.toSectionNineLocalContext
      ctx.criticalPath.a' ⟨alignment,halign⟩
  have hLcard : Nat.card L = 2 := (nine_next_center_commutator_and_kernel
    ctx.toAmbientSectionNineContext hshort ctx.criticalPath.a' ⟨alignment,halign⟩).1
  have hLZ : L ≤ Z := by
    change ZAt ctx.Γ ctx.criticalPath.a' ≤ ZAt ctx.Γ middle
    rw [hopen.center_direct_product.1]
    exact le_sup_right
  have hZV : Z ≤ V := nine_seven_neighbor_center_le_module ctx.Γ (ctx.Γ.adjacent_symm hterminal)
  have hZI : Z ≤ VAt ctx.Γ ctx.criticalPath.firstStep ⊓ V := le_inf
    (nine_seven_neighbor_center_le_module ctx.Γ (ctx.Γ.adjacent_symm hfirst)) hZV
  have hZO : Z ≤ O := hZI.trans
    (ten_one_large_centralizer_setup ctx middle hpath hno).2.2.2.2.2.2.1
  have hPO : P ≤ Subgroup.normalizer (O : Set G) :=
    (nine_seven_stabilizer_normalizes_neighborhood ctx.Γ middle).trans (normalizes_omega W)
  have hPZ : P ≤ Subgroup.normalizer (Z : Set G) := stabilizer_le_normalizer_z ctx.Γ middle
  have hOW : O ≤ W := (omegaOneCenter_le_centerAmbient W).trans (Subgroup.map_subtype_le _)
  have hWQ : W ≤ Q := nine_seven_neighborhood_le_own_core
    ctx.toLocalContext.toSectionNineLocalContext hlong middle
  have hQP : Q ≤ P := by
    change ctx.Γ.twoCoreAt middle ≤ P
    rw [ctx.Γ.twoCoreAt_def]
    exact twoCoreIn_le P
  have hOP : O ≤ P := hOW.trans (hWQ.trans hQP)
  have hEP : E ≤ P := by
    change ctx.Γ.twoResidualAt middle ≤ P
    rw [ctx.Γ.twoResidualAt_def]
    exact twoResidualIn_le P
  have hEnPn : En ≤ Pn := by
    change ctx.Γ.twoResidualAt ctx.criticalPath.a' ≤ Pn
    rw [ctx.Γ.twoResidualAt_def]
    exact twoResidualIn_le Pn
  have hUQn : U ≤ QAt ctx.Γ ctx.criticalPath.a' := by
    change twoCoreIn (ctx.Γ.twoResidualAt ctx.criticalPath.a') ≤ ctx.Γ.twoCoreAt ctx.criticalPath.a'
    rw [ctx.Γ.twoResidualAt_def,ctx.Γ.twoCoreAt_def,residual_core_eq_inter_core]
    exact inf_le_right
  have hUP : U ≤ P := hUQn.trans
    (((lemma_seven_three ctx.sectionSeven ctx.Γ).sylow_and_core _ _
      ((mem_neighborhood_iff_adjacent ctx.Γ).mpr (ctx.Γ.adjacent_symm hterminal)) default).2.2)
  have hUPn : U ≤ Pn := (twoCoreIn_le En).trans hEnPn
  have hUtwo : IsPGroup 2 U := (pCore_isPGroup (p := 2) (G := En)).map En.subtype
  have hUnot : ¬ U ≤ Q := nine_seven_residual_core_escapes_neighbor
    ctx.toLocalContext.toSectionNineLocalContext ctx.criticalPath.a' middle
      ⟨alignment,halign⟩ (ctx.Γ.adjacent_symm hterminal)
  have hUnotC : ¬ U ≤ Subgroup.centralizer (Z : Set G) := by
    intro hc
    exact hUnot (nine_three_orbit_pgroup_centralizer
      ctx.toLocalContext.toSectionNineLocalContext middle horbit U hUtwo hUP hc)
  obtain ⟨t,htU,htnot⟩ := SetLike.not_le_iff_exists.mp hUnotC
  let F := Z ⊓ Subgroup.centralizer ({t} : Set G)
  have hLF : L ≤ F := le_inf hLZ (by
    intro l hl
    exact Subgroup.mem_centralizer_singleton_iff.mpr
      (Subgroup.mem_centralizer_iff.mp (hLPn (hUPn htU)) l hl))
  have hFne : F ≠ Z := by
    intro heq
    apply htnot
    apply Subgroup.mem_centralizer_iff.mpr
    intro z hz
    exact Subgroup.mem_centralizer_singleton_iff.mp ((heq.symm ▸ hz).2)
  have hFlt : Nat.card F < 4 := by
    have hle := Subgroup.card_le_of_le (show F ≤ Z from inf_le_left)
    have hne : Nat.card F ≠ Nat.card Z := fun heq =>
      hFne (Subgroup.eq_of_le_of_card_ge inf_le_left heq.ge)
    exact (Nat.lt_of_le_of_ne hle hne).trans_eq hopen.center_card
  have hFcard : Nat.card F = 2 := by
    have hdiv : Nat.card F ∣ 4 := hopen.center_card ▸ Subgroup.card_dvd_of_le (show F ≤ Z from inf_le_left)
    have hlo : 2 ≤ Nat.card F := hLcard ▸ Subgroup.card_le_of_le hLF
    interval_cases hc : Nat.card F <;> norm_num at *
  have hFL : F = L := (Subgroup.eq_of_le_of_card_ge hLF (by rw [hFcard,hLcard])).symm
  have hKP : K ≤ P := sup_le hEP hUP
  have hOE : ⁅O,E⁆ = Z := ten_one_omega_middle_residual_commutator ctx middle hpath hOU
  have hOK : ⁅O,K⁆ ≤ Z := by
    have hh := SectionEight.eight_six_commutator_sSup_le ({E,U} : Set (Subgroup G)) O Z P hPZ
      (by intro R hR; rcases hR with rfl | hR; exact hEP
          have : R = U := Set.mem_singleton_iff.mp hR; subst R; exact hUP)
      (by intro R hR; rcases hR with rfl | hR
          · rw [Subgroup.commutator_comm]; exact hOE.le
          · have : R = U := Set.mem_singleton_iff.mp hR; subst R
            rw [Subgroup.commutator_comm]; exact hOU.trans hLZ)
    simpa only [sSup_pair,Subgroup.commutator_comm] using hh
  let _ : IsElementaryAbelian 2 O := omegaOneCenterAmbient_elementaryAbelian W
  have hLD : L ≤ D := hDV.symm.le.trans inf_le_left
  by_contra hnot
  obtain ⟨d,hd,hdnot⟩ := SetLike.not_le_iff_exists.mp hnot
  have hdZ : d ∉ Z := fun hz => hdnot (hDV.le ⟨hd,hZV hz⟩)
  have htd : t*d=d*t := Subgroup.mem_centralizer_iff.mp (hDE hd) t (twoCoreIn_le En htU)
  have hfixed : Z ⊓ Subgroup.centralizer ({t} : Set G) ≤ D := by
    change F ≤ D
    rw [hFL]
    exact hLD
  obtain ⟨y,hyD,hyne,hcop⟩ := Subgroup.exists_fixed_centralizer_three_coprime_index_on_four_coset
    K O Z D (hKP.trans hPO) (hKP.trans hPZ) hZO hopen.center_card hOK hDO
      (⟨t,Subgroup.mem_sup_right htU⟩ : K) d hd hdZ htd hfixed
  let C := Subgroup.centralizer ({y} : Set G)
  let J := C.subgroupOf K
  let Neighbors := {neighbor // ctx.Γ.adjacent middle neighbor}
  let _ : Finite ctx.Γ.Vertex := ctx.Γ.finiteVertex
  let _ : Finite Neighbors := inferInstance
  let _ := neighborAction ctx.Γ middle K hKP
  let _ : MulAction.IsPretransitive K Neighbors := by
    constructor
    intro left right
    obtain ⟨g,hg,hmove⟩ := nine_seven_residual_neighbor_transitive ctx.sectionSeven ctx.Γ
      middle left right left.property right.property
    refine ⟨⟨g⁻¹,K.inv_mem (Subgroup.mem_sup_left hg)⟩,?_⟩
    apply Subtype.ext
    change ctx.Γ.act (g⁻¹)⁻¹ left = right
    simpa only [inv_inv] using hmove
  have hdegree : Nat.card Neighbors = 3 :=
    (cubic_local_action_of_sl2Two_quotient ctx.Γ ctx.sectionSeven middle hopen.quotient_model).degree
  let _ : MulAction.IsPretransitive J Neighbors :=
    MulAction.isPretransitive_of_prime_card_of_coprime_index Nat.prime_three hdegree J hcop
  have hmid : IsActionTransitiveOn ctx.Γ (P ⊓ C) (neighborhood ctx.Γ middle) := by
    intro left right hleft hright
    let l : Neighbors := ⟨left,(mem_neighborhood_iff_adjacent ctx.Γ).mp hleft⟩
    let r : Neighbors := ⟨right,(mem_neighborhood_iff_adjacent ctx.Γ).mp hright⟩
    obtain ⟨g,hmove⟩ := MulAction.exists_smul_eq J l r
    refine ⟨⟨((g:K):G)⁻¹,⟨P.inv_mem (hKP (g:K).property),C.inv_mem g.property⟩⟩,?_⟩
    exact congrArg Subtype.val hmove
  have hend : IsActionTransitiveOn ctx.Γ (Pn ⊓ C) (neighborhood ctx.Γ ctx.criticalPath.a') := by
    intro left right hleft hright
    obtain ⟨g,hg,hmove⟩ := nine_seven_residual_neighbor_transitive ctx.sectionSeven ctx.Γ
      ctx.criticalPath.a' left right
        ((mem_neighborhood_iff_adjacent ctx.Γ).mp hleft)
        ((mem_neighborhood_iff_adjacent ctx.Γ).mp hright)
    refine ⟨⟨g,⟨hEnPn hg,?_⟩⟩,hmove⟩
    exact Subgroup.mem_centralizer_singleton_iff.mpr
      (Subgroup.mem_centralizer_iff.mp (hDE hyD) g hg)
  have hyP : y ∈ P := hOP (hDO hyD)
  have hVW : V ≤ W := le_sSup ⟨_,(mem_neighborhood_iff_adjacent ctx.Γ).mpr hterminal,rfl⟩
  have hOV : O ≤ Subgroup.centralizer (V : Set G) :=
    ((omegaOneCenter_le_centerAmbient W).trans (centerAmbient_le_centralizer W)).trans
      (Subgroup.centralizer_le hVW)
  have hyQn : y ∈ QAt ctx.Γ ctx.criticalPath.a' := hopen.endpoint_centralizer (hOV (hDO hyD))
  have hyPn : y ∈ Pn := by
    have hQnPn : QAt ctx.Γ ctx.criticalPath.a' ≤ Pn := by
      change ctx.Γ.twoCoreAt ctx.criticalPath.a' ≤ Pn
      rw [ctx.Γ.twoCoreAt_def]
      exact twoCoreIn_le Pn
    exact hQnPn hyQn
  exact hyne (element_eq_one_of_adjacent_centralizer_transitivity ctx.sectionSeven ctx.Γ
    middle ctx.criticalPath.a' hterminal y ⟨hyP,hyPn⟩ hmid hend)

end Stellmacher.SectionTen
