module
public import CFSG.Quasithin.ChapterC.Section01.NaturalSixControl.SymplecticSetup.BackwardEscape
public import Theory.GroupAction.SubgroupQuotientFullAction
public import Theory.GroupTheory.PResidual.NormalSubgroup

/-!
# The forward hyperplane kernel in the native symplectic source

For neighboring original vertices, the kernel centralizing the forward
moving layer's intersection with B is normalized by the entire starting
stabilizer. If that intersection has index at most two, self-duality of the
natural module makes its commutator a line, and the full point-core action
puts the line in the common edge seed.

A normal subgroup outside the two-core contains the component. Applied to
the action on a normal section, this gives B-placement whenever the opposite
critical layer acts trivially on that section. All conclusions use the
literal characteristic replacement and feed the source forward-index proof.

Source: Meierfrankenfeld--Stellmacher (1993), (5.9), printed pp.920--922.
These are its kernel and normal-section inputs; the strict forward index
and terminal critical-distance exclusion remain separate arguments.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped commutatorElement Pointwise

private theorem fixed_mod_central_normalizes_centralizer {G : Type*} [Group G]
    (A Q L : Subgroup G) (hLQ : L ≤ normalizer (Q : Set G))
    (hLA : ⁅L,A⁆ ≤ centralizer (Q : Set G)) :
    L ≤ normalizer ((Q ⊓ centralizer (A : Set G) : Subgroup G) : Set G) := by
  apply le_normalizer_iff.mpr
  intro l hl q hq
  refine ⟨(mem_normalizer_iff.mp (hLQ hl) q).mp hq.1,?_⟩
  intro a ha
  have hh := hLA (commutator_mem_commutator (L.inv_mem hl) ha)
  have h1 : Commute ⁅l⁻¹,a⁆ q := (hh q hq.1).symm
  have h2 : Commute a q := hq.2 a ha
  have hc : Commute (l⁻¹*a*l) q := by
    have he : ⁅l⁻¹,a⁆*a=l⁻¹*a*l := by simp [commutatorElement_def,mul_assoc]
    exact he ▸ h1.mul_left h2
  have hm := hc.map (MulAut.conj l).toMonoidHom
  change Commute (l*(l⁻¹*a*l)*l⁻¹) (l*q*l⁻¹) at hm
  have he : l*(l⁻¹*a*l)*l⁻¹=a := by group
  rw [he] at hm
  exact hm.eq

private theorem commutator_sup_fixed {G : Type*} [Group G]
    (U Z A : Subgroup G) (hZU : Z ≤ normalizer (U : Set G))
    (hZA : Z ≤ centralizer (A : Set G)) :
    ⁅U ⊔ Z,A⁆ = ⁅U,A⁆ := by
  apply le_antisymm
  · apply commutator_le.mpr
    intro x hx a ha
    have hprod : x ∈ (U : Set G) * (Z : Set G) :=
      (coe_mul_of_right_le_normalizer_left U Z hZU) ▸ hx
    obtain ⟨v,hv,z,hz,rfl⟩ := hprod
    have he : ⁅z,a⁆ = 1 := commutatorElement_eq_one_iff_mul_comm.mpr (hZA hz a ha).symm
    rw [commutatorElement_mul_left_eq_conj_mul,he,mul_one,mul_inv_cancel,one_mul]
    exact commutator_mem_commutator hv ha
  · exact commutator_mono le_sup_left le_rfl

open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
namespace CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup.Source
variable {M : Type*} [Group M] [Finite M] {L R W : Subgroup M} [L.Normal] [W.Normal]
  (s : Source L R W)

theorem moving_hyperplane_kernel_normalized (hb : 2 < s.geometry.b R) {a c t : Vertex R}
    (ha : color R a = false)
    (hat : Adjacent R a t) (hct : Adjacent R c t) :
    stabilizer R a ≤ normalizer ((Q R a ⊓ centralizer
      (U R c ⊓ B R a (s.geometry.Z_normal _) : Set (FreeAmalgam R)) :
        Subgroup (FreeAmalgam R)) : Set (FreeAmalgam R)) := by
  let K := U R c ⊓ B R a (s.geometry.Z_normal _)
  have hb' : 2 < criticalDistance R a (s.geometry.exists_critical a ha) := by
    rw [s.geometry.distance_constant a ha]
    exact hb
  have hVL := s.geometry.V_local a ha hb'
  have hLK : ⁅Ltilde R a,K⁆ ≤ centralizer (Q R a : Set (FreeAmalgam R)) := by
    apply le_trans _ (commutator_eq_bot_iff_le_centralizer.mp (Z_centralizes_Q R a ha))
    apply commutator_le.mpr
    intro l hl k hk
    exact ((mem_B_iff R a _ hVL k).mp hk.2).2 l hl
  have hLN := fixed_mod_central_normalizes_centralizer K (Q R a) (Ltilde R a)
    ((Ltilde_le_stabilizer a).trans (Q_normalized R a)) hLK
  have htG : Q R t ≤ stabilizer R a := fun _ hx => hx.2 _ (adjacent_symm R hat)
  have htC : Q R t ≤ stabilizer R c := fun _ hx => hx.2 _ (adjacent_symm R hct)
  have htK : Q R t ≤ normalizer (K : Set (FreeAmalgam R)) :=
    (le_inf (htC.trans (U_normalized c))
      (htG.trans (Escape.Propagation.Rigidity.B_normalized hb a ha))).trans
        inf_normalizer_le_normalizer_inf
  have htCK : Q R t ≤ normalizer (centralizer (K : Set (FreeAmalgam R)) : Set (FreeAmalgam R)) :=
    htK.trans (le_normalizer_of_normal_subgroupOf (Subgroup.centralizer_le_normalizer _))
  have htN := (le_inf (htG.trans (Q_normalized R a)) htCK).trans
    inf_normalizer_le_normalizer_inf
  rw [←s.residual_edge_generation ha hat]
  exact sup_le hLN htN


theorem moving_hyperplane_commutator_le_seed
    (h : NativeCentralLayer s) (u : Model.S)
    (hfull : R.map s.projection = Model.E.map (MulAut.conj u).toMonoidHom)
    {a c t : Vertex R} (ha : color R a = false) (hc : color R c = false)
    (hat : Adjacent R a t) (hct : Adjacent R c t)
    (hindex : (B R a (s.geometry.Z_normal _)).relIndex (U R c) ≤ 2) :
    let T₀ := Q R a ⊓ centralizer
      (U R c ⊓ B R a (s.geometry.Z_normal _) : Set (FreeAmalgam R))
    Nat.card (⁅U R c,T₀⁆ : Subgroup (FreeAmalgam R)) ≤ 2 ∧
      ⁅U R c,T₀⁆ ≤ Z R t := by
  let K := U R c ⊓ B R a (s.geometry.Z_normal _)
  let T₀ := Q R a ⊓ centralizer (K : Set (FreeAmalgam R))
  change Nat.card (⁅U R c,T₀⁆ : Subgroup (FreeAmalgam R)) ≤ 2 ∧ ⁅U R c,T₀⁆ ≤ Z R t
  have ht : color R t = true := by
    have hn := adjacent_color_ne R hat
    rw [ha] at hn
    cases ht : color R t <;> simp_all
  have hQaQt : Q R a ≤ Q R t := Q_le_adjacent_h R ht hat
  have hT : T₀ ≤ Q R t := inf_le_left.trans hQaQt
  have htGc : Q R t ≤ stabilizer R c := fun _ hx => hx.2 _ (adjacent_symm R hct)
  have hKfix : K ≤ centralizer (T₀ : Set (FreeAmalgam R)) :=
    le_centralizer_iff.mp inf_le_right
  let := finite_Z R c
  let : Finite (U R c) := Finite.of_injective
    (inclusion (DistanceEight.U_le_Z R c)) (inclusion_injective _)
  have hidx : (centralizer (T₀ : Set (FreeAmalgam R))).relIndex (U R c) ≤ 2 := by
    have hh := relIndex_le_of_le_left hKfix
      (index_ne_zero_of_finite (H := K.subgroupOf (U R c)))
    change (centralizer (T₀ : Set (FreeAmalgam R))).relIndex (U R c) ≤
      K.relIndex (U R c) at hh
    simpa only [K,inf_relIndex_left] using hh.trans (by simpa only [K,inf_relIndex_left] using hindex)
  have hcard : Nat.card (⁅U R c,T₀⁆ : Subgroup (FreeAmalgam R)) ≤ 2 := by
    rw [←s.moving_fixedIndex_eq_commutator_card h
      (s.projection_surjective_of_radical_image_le_conjugate u hfull.le) c hc T₀ (hT.trans htGc)]
    exact hidx
  have hseedQt : Z R t ≤ centralizer (Q R t : Set (FreeAmalgam R)) := by
    intro z hz
    rw [Z,if_neg (by simp [ht])] at hz
    exact (mem_omegaCenter_iff.mp hz).2.2
  have hseedGc : Z R t ≤ stabilizer R c :=
    (adjacent_Z_le R hc hct).trans (Z_le_stabilizer R c)
  have hZcomm : ⁅Z R c,T₀⁆ = ⁅U R c,T₀⁆ := by
    rw [s.Z_eq_moving_sup_edge_at h hc hct]
    exact commutator_sup_fixed _ _ _ (hseedGc.trans (U_normalized c))
      (hseedQt.trans (centralizer_le hT))
  have hfixed : ⁅U R c,T₀⁆ ≤ centralizer (Q R t : Set (FreeAmalgam R)) := by
    rw [←hZcomm]
    exact s.small_edge_commutator_le_centralizer u hfull hc hct T₀ hT (hZcomm ▸ hcard)
  have hZ : ⁅U R c,T₀⁆ ≤ Z R c := by
    rw [←hZcomm]
    exact le_normalizer_iff_commutator_le_left.mp ((hT.trans htGc).trans (Z_normalized R c))
  have hQc : Z R c ≤ Q R c := (s.geometry.omega_bound c hc (by
    rw [s.geometry.distance_constant c hc]
    exact s.criticalDistance_pos)).trans (omegaCenter_le _)
  have hQt : ⁅U R c,T₀⁆ ≤ Q R t := hZ.trans (hQc.trans (Q_le_adjacent_h R ht hct))
  refine ⟨hcard,?_⟩
  intro x hx
  rw [Z,if_neg (by simp [ht])]
  apply mem_omegaCenter_iff.mpr
  refine ⟨hQt hx,?_,hfixed hx⟩
  exact (mem_omegaCenter_iff.mp ((s.geometry.omega_bound c hc (by
    rw [s.geometry.distance_constant c hc]
    exact s.criticalDistance_pos)) (hZ hx))).2.1
end CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup.Source

namespace CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup.Source
variable {M : Type*} [Group M] [Finite M] {L R W : Subgroup M} [L.Normal] [W.Normal]
  (s : Source L R W)

omit [Finite M] in
theorem component_le_normal_of_not_le_core
    (hq : Function.Surjective s.projection) (N : Subgroup M) [N.Normal]
    (hne : ¬ N ≤ pCore 2 M) : L ≤ N := by
  let := Subgroup.Normal.map (inferInstance : N.Normal) s.projection hq
  have hn : N.map s.projection ≠ ⊥ := by
    intro he
    exact hne (s.projection_kernel ▸ (map_eq_bot_iff N).mp he)
  have hAlt : alternatingGroup (Fin 6) ≤ N.map s.projection :=
    Equiv.Perm.alternatingGroup_le_of_normal (by simp) ((nontrivial_iff_ne_bot _).mpr hn)
  have hLN : L ≤ N ⊔ R := by
    have he : (L.map s.projection).comap s.projection ≤
        (N.map s.projection).comap s.projection := comap_mono (s.component_image ▸ hAlt)
    rw [comap_map_eq,comap_map_eq,s.projection_kernel] at he
    exact le_sup_left.trans (he.trans (sup_le_sup_left s.core_le N))
  have hsup : N ⊔ R = ⊤ := by
    apply top_unique
    rw [←s.sup_eq_top]
    exact sup_le hLN le_sup_right
  rw [←s.residual]
  exact sInf_le ⟨inferInstance,isPGroup_quotient_of_sup_eq_top N R s.two_group hsup⟩

omit [Finite M] in
theorem component_commutator_le_of_normal_section
    (hq : Function.Surjective s.projection)
    (D Z A : Subgroup M) [D.Normal] [Z.Normal]
    (hcomm : ⁅D,A⁆ ≤ Z) (hne : ¬ A ≤ pCore 2 M) :
    ⁅D,L⁆ ≤ Z := by
  obtain ⟨f,hf⟩ := exists_quotient_conjugation_action (⊤ : Subgroup M) D Z
    le_normalizer_of_normal le_normalizer_of_normal inferInstance
  let g := f.comp (topEquiv : (⊤ : Subgroup M) ≃* M).symm.toMonoidHom
  have hAg : A ≤ g.ker := by
    intro a ha
    apply MulEquiv.ext
    intro v
    obtain ⟨x,rfl⟩ := QuotientGroup.mk'_surjective (Z.subgroupOf D) v
    change f ⟨a,mem_top _⟩ _ = _
    rw [hf]
    apply (QuotientGroup.eq_iff_div_mem).mpr
    change a*(x:M)*a⁻¹/(x:M) ∈ Z
    rw [div_eq_mul_inv,←commutatorElement_def]
    rw [commutator_comm] at hcomm
    exact hcomm (commutator_mem_commutator ha x.property)
  have hL : L ≤ g.ker := s.component_le_normal_of_not_le_core hq g.ker
    (fun hh => hne (hAg.trans hh))
  rw [commutator_comm]
  apply commutator_le.mpr
  intro l hl d hd
  have he : f ⟨l,mem_top _⟩ = 1 := hL hl
  have hh := hf ⟨l,mem_top _⟩ ⟨d,hd⟩
  rw [he] at hh
  have hm := QuotientGroup.eq_iff_div_mem.mp hh.symm
  change l*d*l⁻¹/d ∈ Z at hm
  simpa only [div_eq_mul_inv,commutatorElement_def] using hm


theorem normalized_radius_le_B_of_critical_commutator
    (u : Model.S)
    (hfull : R.map s.projection = Model.E.map (MulAut.conj u).toMonoidHom)
    (hb : 2 < s.geometry.b R) {e : Vertex R}
    (p : CriticalPath R s.geometry (alpha R) e)
    (D : Subgroup (FreeAmalgam R)) (hDV : D ≤ V R (alpha R))
    (hDN : stabilizer R (alpha R) ≤ normalizer (D : Set (FreeAmalgam R)))
    (hcomm : ⁅D,Z R e⁆ ≤ Z R (alpha R)) :
    D ≤ B R (alpha R) (s.geometry.Z_normal _) := by
  let D₀ := D.comap (embedM R)
  let Z₀ := (Z R (alpha R)).comap (embedM R)
  let A₀ := (Z R e).comap (embedM R)
  have hDG : D ≤ (embedM R).range :=
    (hDV.trans (s.geometry.V_local (alpha R) rfl hb)).trans_eq (stabilizer_m_base R)
  have hDm : D₀.map (embedM R) = D := map_comap_eq_self hDG
  have hZm : Z₀.map (embedM R) = Z R (alpha R) :=
    map_comap_eq_self ((Z_le_stabilizer R (alpha R)).trans_eq (stabilizer_m_base R))
  have hAm : A₀.map (embedM R) = Z R e := map_comap_eq_self
    ((critical_Z_le_stabilizer R s.geometry (alpha R) rfl
      s.criticalDistance_pos p.critical).trans_eq (stabilizer_m_base R))
  have hg (m : M) : embedM R m ∈ stabilizer R (alpha R) := by
    change embedM R m ∈ stabilizer R (mVertex R 1)
    rw [stabilizer_m_base]
    exact ⟨m,rfl⟩
  let : D₀.Normal := ⟨by
    intro d hd m
    change embedM R (m*d*m⁻¹) ∈ D
    rw [map_mul,map_mul,map_inv]
    exact (mem_normalizer_iff.mp (hDN (hg m)) (embedM R d)).mp hd⟩
  let : Z₀.Normal := ⟨by
    intro d hd m
    change embedM R (m*d*m⁻¹) ∈ Z R (alpha R)
    rw [map_mul,map_mul,map_inv]
    exact (mem_normalizer_iff.mp ((Z_normalized R _) (hg m)) (embedM R d)).mp hd⟩
  have hcomm₀ : ⁅D₀,A₀⁆ ≤ Z₀ := by
    apply (map_le_map_iff_of_injective (embedM_injective R)).mp
    rwa [map_commutator,hDm,hAm,hZm]
  have hne : ¬ A₀ ≤ pCore 2 M := by
    intro he
    have hh := map_mono (f := embedM R) he
    rw [hAm,←Q_alpha R s.two_group s.core_le] at hh
    exact (critical_reverse R s.geometry s.edgeCentralizerCondition
      (alpha R) rfl s.criticalDistance_pos e p.end_color p.critical).2 hh
  have hDL := s.component_commutator_le_of_normal_section
    (s.projection_surjective_of_radical_image_le_conjugate u hfull.le) D₀ Z₀ A₀ hcomm₀ hne
  have hm := map_mono (f := embedM R) hDL
  rw [map_commutator,hDm,hZm,show L.map (embedM R) = Ltilde R (alpha R) by
    rw [Ltilde_alpha,s.residual]] at hm
  intro d hd
  apply (mem_B_iff R (alpha R) _ (s.geometry.V_local (alpha R) rfl hb) d).mpr
  refine ⟨hDV hd,?_⟩
  intro l hl
  rw [commutator_comm] at hm
  exact hm (commutator_mem_commutator hl hd)
end CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup.Source

namespace CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup.SourceData
variable {K : Type*} [Group K] [Finite K]
  {L W : Subgroup K} [L.Normal] [W.Normal] {T : Sylow 2 K}
  (d : NaturalSixControl.SourceData L W T) (hm : IntrinsicMSPair d)
local notation "J" => (L ⊔ d.B : Subgroup K)
local notation "R" => d.B.subgroupOf J

/-- The literal original reduction supplies the complete forward-kernel inputs. -/
theorem reducedSource_block_or_forward_kernel
    (r : CharacteristicReduction (L.subgroupOf J) R)
    {a c t : Vertex r.radical} (ha : color r.radical a = false)
    (hc : color r.radical c = false) (hat : Adjacent r.radical a t)
    (hct : Adjacent r.radical c t)
    (hb : 2 < ((originalSource d hm).reduce r).geometry.b r.radical)
    (hindex : (B r.radical a (((originalSource d hm).reduce r).geometry.Z_normal _)).relIndex
      (U r.radical c) ≤ 2) :
    IsAlternatingBlock L 6 ∨
      (let T₀ := Q r.radical a ⊓ centralizer
         (U r.radical c ⊓ B r.radical a (((originalSource d hm).reduce r).geometry.Z_normal _) :
           Set (FreeAmalgam r.radical))
       stabilizer r.radical a ≤ normalizer (T₀ : Set (FreeAmalgam r.radical)) ∧
       Nat.card (⁅U r.radical c,T₀⁆ : Subgroup (FreeAmalgam r.radical)) ≤ 2 ∧
       ⁅U r.radical c,T₀⁆ ≤ Z r.radical t) := by
  rcases reducedSource_block_or_full_point_image d hm r with hblock | hfull
  · exact Or.inl hblock
  · right
    let s := (originalSource d hm).reduce r
    have h := reduced_nativeCentralLayer d hm r
    have hf : r.radical.map s.projection = Model.E.map (MulAut.conj d.relabeler.val⁻¹).toMonoidHom := by
      simpa only [Model.pointCore_eq_exceptional] using hfull
    exact ⟨s.moving_hyperplane_kernel_normalized hb ha hat hct,
      s.moving_hyperplane_commutator_le_seed h _ hf ha hc hat hct hindex⟩
end CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup.SourceData
