module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicFourShifts

/-!
# Selected critical lines at distance four in the original cubic graph

A selected backward critical commutator is central at its original midpoint.
The radius bound puts it in the midpoint central omega subgroup. The first
edge normalizes it because the point-core image is abelian; the opposite
seed centralizes it by critical distance. These two subgroups generate the
midpoint stabilizer. Its centralizer therefore has a normal symmetric image
containing an odd permutation, hence the whole symmetric group. The original
component's no-supplement theorem lifts this equality through the retained
order-three kernel. The argument never replaces that kernel by the two-core.

An order-four quadratic subgroup of a point core is the pointwise fixer,
inside that point core, of its moved natural space. Consequently a large
critical image cannot have its full moving commutator fixed by the entire
edge: that would put the order-eight point core inside an order-four group.
Applying this to the selected central commutator forces both backward
critical images and their commutator to have order two. The argument uses
the natural quotient of the whole moving cover and retains its possible
central attachment of order two.

The whole-core and literal C.1.32 consumers strengthen the existing
nonabelian generating configuration at the same original base vertex,
keeping its local conjugator and every overlap vertex. The plane and Sylow
images remain explicit alternatives. This proves the selected-commutator
step, not the final distance-four contradiction. The remaining distance-four
exclusion, other radical images, natural exhaustion and both intrinsic
block reconstructions still require their source proofs.

Source: Meierfrankenfeld--Stellmacher (1993), (3.3)(ii) and the selected
commutator argument of (5.12), printed pp.866--867,924--927;
Aschbacher--Smith C.1.31--32, printed pp.135--136. The proof adapts
Natural.Exhaustion.LargeDistance.SectionFive.SelectedFour to the actual
cubic projection, using its own graph, odd-kernel lifting and both covers.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender BinaryPermutation
open Theory.SpecificGroups.SymmetricSix
open Theory.SpecificGroups.SymmetricSix.BinaryFlags
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
open CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup
open scoped IsMulCommutative commutatorElement Pointwise
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicFull
universe u
variable {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
  (h : SmallMSPair KnownSimple.IsKnownSimple L R) (e : CentralMarking L)
  (hz : Nat.card (center (L ⧸ pCore 2 L)) = 3)
  (hk : layerKernel L R = extensionKernel h)
local notation "M" => (L ⊔ R : Subgroup G)
local notation "Rg" => edge L R
local notation "W" => (⁅centralOmega L R,L.subgroupOf (L ⊔ R)⁆ : Subgroup M)
local notation "π" => CubicAction.projection h e hz hk
local instance : IsElementaryAbelian 2 W := IsElementaryAbelian.of_le (commutator_le_left _ _)
private theorem edge_derived_le_core_of_abelian_image
    (hab : ⁅(Rg).map π,(Rg).map π⁆ = ⊥)
    {a t : Vertex Rg} (ha : color Rg a = false)
    (hat : Adjacent Rg a t) :
    ⁅Q Rg t,Q Rg t⁆ ≤ Q Rg a := by
  have hr : ⁅Rg,Rg⁆ ≤ pCore 2 M := by
    apply two_subgroup_le_core_of_le_extensionKernel h hz ⁅Rg,Rg⁆
      (h.relative_radical.isPGroup.to_le ((Subgroup.commutator_le_sup Rg Rg).trans (sup_idem Rg).le))
    rw [←CubicAction.projection_kernel h e hz hk,←Subgroup.map_eq_bot_iff,map_commutator]
    exact hab
  have hbase : ⁅Q Rg (beta Rg),Q Rg (beta Rg)⁆ ≤
      Q Rg (alpha Rg) := by
    rw [Q_beta,Q_alpha Rg (h.relative_radical.isPGroup)
      (h.relative_radical.twoCore_le),←map_commutator]
    exact map_mono hr
  obtain ⟨g,hg|hg⟩ := (adjacent_iff_exists_common Rg a t).mp hat
  · rcases hg with ⟨rfl,rfl⟩
    have hh := map_mono (f := (MulAut.conj g⁻¹).toMonoidHom) hbase
    rw [map_commutator,←Q_act,←Q_act] at hh
    simpa only [alpha,beta,act_mVertex,act_hVertex,one_mul] using hh
  · rw [hg.1] at ha
    cases ha

private theorem fixed_mod_central_normalizes_line {H : Type*} [Group H]
    (A Q D : Subgroup H) (hAQ : A ≤ normalizer (Q : Set H))
    (hDQ : D ≤ normalizer (Q : Set H))
    (hDA : ⁅D,A⁆ ≤ centralizer (Q : Set H)) :
    D ≤ normalizer ((⁅A,Q⁆ : Subgroup H) : Set H) := by
  apply le_normalizer_closure_iff.mpr
  rintro d hd _ ⟨a,ha,q,hq,rfl⟩
  have hq' : d*q*d⁻¹ ∈ Q := (mem_normalizer_iff.mp (hDQ hd) q).mp hq
  have hk : ⁅d,a⁆ ∈ centralizer (Q : Set H) := hDA (commutator_mem_commutator hd ha)
  have hcomm : ⁅a,d*q*d⁻¹⁆ ∈ Q :=
    le_normalizer_iff_commutator_le_right.mp hAQ (commutator_mem_commutator ha hq')
  have hzero : ⁅⁅d,a⁆,d*q*d⁻¹⁆ = 1 :=
    commutatorElement_eq_one_iff_mul_comm.mpr (hk _ hq').symm
  rw [conjugate_commutatorElement,show d*a*d⁻¹ = ⁅d,a⁆*a by
    simp [commutatorElement_def,mul_assoc],commutatorElement_mul_left_eq_conj_mul,
    hzero,mul_one,←hk _ hcomm,mul_inv_cancel_right]
  exact commutator_mem_commutator ha hq'


include h e hz hk in
theorem critical_commutator_normalized_first_of_abelian_image
    (hab : ⁅(Rg).map π,(Rg).map π⁆ = ⊥)
    {a endpoint : Vertex Rg} (p : CriticalPath Rg (sourceGeometry h) a endpoint) :
    Q Rg (p.walk.getVert 1) ≤ normalizer ((⁅Z Rg a,Z Rg endpoint⁆:Subgroup (FreeAmalgam Rg)):Set (FreeAmalgam Rg)) := by
  let D := ⁅Z Rg a,Z Rg endpoint⁆
  let t := p.walk.getVert 1
  have hpos : 0<p.walk.length := p.length_eq_b ▸ (sourceDistance_pos h)
  have hat : Adjacent Rg a t := by
    apply (cosetGraph_adj Rg _ _).mp
    simpa only [SimpleGraph.Walk.getVert_zero,Nat.zero_add] using
      p.walk.adj_getVert_succ (i:=0) hpos
  have ht : color Rg t=true := by
    have hn := adjacent_color_ne Rg hat
    rw [p.start_color] at hn
    cases hc : color Rg t <;> simp_all
  have hZe : Z Rg endpoint≤Q Rg t := by
    apply Z_le_Q_of_dist_lt Rg endpoint ((sourceGeometry h).exists_critical endpoint p.end_color)
    rw [SimpleGraph.dist_comm,p.dist_end,(sourceGeometry h).distance_constant endpoint p.end_color]
    change p.walk.length-1<(sourceGeometry h).b Rg
    rw [←p.length_eq_b]
    omega
  have hQtG : Q Rg t≤stabilizer Rg a := fun _ hx => hx.2 a (adjacent_symm Rg hat)
  have hQtZ := hQtG.trans (Z_normalized Rg a)
  have hder : ⁅Q Rg t,Z Rg endpoint⁆≤centralizer (Z Rg a:Set (FreeAmalgam Rg)) :=
    ((commutator_mono le_rfl hZe).trans (edge_derived_le_core_of_abelian_image h e hz hk hab p.start_color hat)).trans
      (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp
        (Z_centralizes_Q Rg a p.start_color)))
  exact (show Q Rg t≤normalizer (D:Set (FreeAmalgam Rg)) from by
    dsimp only [D]
    rw [commutator_comm (Z Rg a)]
    exact fixed_mod_central_normalizes_line (Z Rg endpoint) (Z Rg a) (Q Rg t)
      (hZe.trans hQtZ) hQtZ hder)

private theorem even_quadratic_conjugate_bound (A : Subgroup S) (g : S)
    (hcore : A≤pointCore.map (MulAut.conj g).toMonoidHom)
    (heven : A≤alternatingGroup (Fin 6)) (hq : QuadraticPointCore.Quadratic A) :
    Nat.card A≤2 := by
  let B:=A.map (MulAut.conj g⁻¹).toMonoidHom
  have hB : B≤pointCore := by
    rintro _ ⟨a,ha,rfl⟩
    obtain ⟨b,hb,he⟩ := hcore ha
    rw [←he]
    change g⁻¹*(g*b*g⁻¹)*g∈pointCore
    rw [show g⁻¹*(g*b*g⁻¹)*g=b by group]
    exact hb
  have hBe : B≤alternatingGroup (Fin 6) :=
    (map_mono heven).trans_eq (Subgroup.Normal.map_conj_eq _ g⁻¹)
  have hh:=QuadraticPointCore.even_quadratic_card_le_two B (le_inf hB hBe)
    (QuadraticPointCore.quadratic_conjugate A hq g⁻¹)
  rwa [card_map_of_injective (MulAut.conj g⁻¹).injective] at hh

private theorem normal_eq_top_of_odd_image
    (N : Subgroup M) [N.Normal] (hQ : pCore 2 M≤N)
    (hodd : ¬ N.map π≤alternatingGroup (Fin 6)) : N=⊤ := by
  have hne : ¬ N≤extensionKernel h := by
    intro hh
    apply hodd
    rw [show N.map π=⊥ from
      (map_eq_bot_iff N).mpr (hh.trans_eq (CubicAction.projection_kernel h e hz hk).symm)]
    exact bot_le
  have hnon : N.map π ≠ ⊥ := by
    intro he
    exact hne ((CubicAction.projection_kernel h e hz hk) ▸ (map_eq_bot_iff N).mp he)
  let : (N.map π).Normal := Subgroup.Normal.map inferInstance _ (CubicEven.projection_surjective h e hz hk)
  have hAlt : alternatingGroup (Fin 6) ≤ N.map π :=
    Equiv.Perm.alternatingGroup_le_of_normal (by simp) ((nontrivial_iff_ne_bot _).mpr hnon)
  obtain ⟨a,ha,hodd⟩ := SetLike.not_le_iff_exists.mp hodd
  have hsign : Equiv.Perm.sign a = -1 :=
    (Int.units_eq_one_or _).resolve_left (fun h => hodd (Equiv.Perm.mem_alternatingGroup.mpr h))
  have htop : N.map π=⊤ := by
    apply top_unique
    intro x _
    by_cases hx : x∈alternatingGroup (Fin 6)
    · exact hAlt hx
    · have hxsign : Equiv.Perm.sign x = -1 :=
        (Int.units_eq_one_or _).resolve_left (fun h => hx (Equiv.Perm.mem_alternatingGroup.mpr h))
      have hmem : x*a⁻¹∈alternatingGroup (Fin 6) := by
        rw [Equiv.Perm.mem_alternatingGroup,map_mul,map_inv,hxsign,hsign]
        decide
      have hh := (N.map π).mul_mem (hAlt hmem) ha
      simpa only [inv_mul_cancel_right] using hh
  have hNE : N ⊔ extensionKernel h = ⊤ := by
    have he := congrArg (Subgroup.comap π) htop
    rwa [comap_map_eq,CubicAction.projection_kernel h e hz hk,comap_top] at he
  have hEN : extensionKernel h ≤ N := by
    have he := extensionKernel_no_supplement h N (hNE ▸ le_top)
    rw [extensionKernel_twoCore h,sup_of_le_left hQ] at he
    exact he
  rwa [sup_of_le_left hEN] at hNE

private theorem normalized_subgroup_central_of_critical_odd
    (D A : Subgroup (FreeAmalgam Rg))
    (hD : D≤stabilizer Rg (alpha Rg))
    (hn : stabilizer Rg (alpha Rg)≤normalizer (D:Set (FreeAmalgam Rg)))
    (hQ : Q Rg (alpha Rg)≤centralizer (D:Set (FreeAmalgam Rg)))
    (hAC : A≤centralizer (D:Set (FreeAmalgam Rg)))
    (hodd : ¬ (A.comap (embedM Rg)).map π≤alternatingGroup (Fin 6)) :
    D≤centralizer (stabilizer Rg (alpha Rg):Set (FreeAmalgam Rg)) := by
  let D₀ := D.comap (embedM Rg)
  let N := centralizer (D₀:Set M)
  have hDm : D₀.map (embedM Rg)=D := map_comap_eq_self (hD.trans_eq (stabilizer_m_base Rg))
  have hg (m:M) : embedM Rg m∈stabilizer Rg (alpha Rg) := by
    change embedM Rg m∈stabilizer Rg (mVertex Rg 1)
    rw [stabilizer_m_base]
    exact ⟨m,rfl⟩
  let : D₀.Normal := ⟨by
    intro z hd m
    change embedM Rg (m*z*m⁻¹)∈D
    rw [map_mul,map_mul,map_inv]
    exact (mem_normalizer_iff.mp (hn (hg m)) _).mp hd⟩
  let : N.Normal := inferInstance
  have hQ0 : pCore 2 M≤N := by
    intro m hm z hd
    apply embedM_injective Rg
    simp only [map_mul]
    exact hQ (by rw [Q_alpha Rg (h.relative_radical.isPGroup) (h.relative_radical.twoCore_le)]; exact mem_map_of_mem _ hm) _ hd
  have hAN : A.comap (embedM Rg)≤N := by
    intro a ha z hd
    apply embedM_injective Rg
    simp only [map_mul]
    exact hAC ha _ hd
  have htop : N=⊤ := normal_eq_top_of_odd_image h e hz hk N hQ0
    (fun hh => hodd ((map_mono hAN).trans hh))
  rintro z hd g hg'
  obtain ⟨m,rfl⟩ := (show stabilizer Rg (alpha Rg)≤(embedM Rg).range from
    (stabilizer_m_base Rg).le) hg'
  obtain ⟨x,hx,rfl⟩ := hDm.symm ▸ hd
  have hc : m∈N := htop ▸ mem_top m
  simpa only [map_mul] using (congrArg (embedM Rg) (hc x hx)).symm


private theorem selected_graphImage_le_pointCore_of_le_edge (u : S)
    (hR : (Rg).map π ≤ pointCore.map (MulAut.conj u).toMonoidHom)
    (t : Vertex Rg) (hat : Adjacent Rg (alpha Rg) t)
    (A : Subgroup (FreeAmalgam Rg)) (hAt : A ≤ Q Rg t) :
    ∃ v : S, CubicAction.graphImage h e hz hk A ≤ pointCore.map (MulAut.conj v).toMonoidHom := by
  obtain ⟨g,hg|hg⟩ := edge_transitive Rg hat (base_adjacent Rg)
  · have hgM : g ∈ (embedM Rg).range := by
      change g ∈ Mbar Rg
      rw [← stabilizer_m_base Rg]
      exact hg.1
    obtain ⟨m,rfl⟩ := hgM
    have hQt : (Q Rg t).map
        (MulAut.conj ((embedM Rg m)⁻¹)).toMonoidHom =
          (Rg).map (embedM Rg) := by
      rw [← Q_act,hg.2]
      exact Q_beta Rg
    have hAm (x : M) (hx : x ∈ A.comap (embedM Rg)) :
        m⁻¹*x*m ∈ Rg := by
      have hh := ((map_mono hAt).trans_eq hQt) (mem_map_of_mem
        (MulAut.conj ((embedM Rg m)⁻¹)).toMonoidHom hx)
      obtain ⟨r,hr,he⟩ := hh
      have heq : r = m⁻¹*x*m := by
        apply embedM_injective Rg
        change embedM Rg r = (embedM Rg m)⁻¹ *
          embedM Rg x * ((embedM Rg m)⁻¹)⁻¹ at he
        simpa only [map_mul,map_inv,inv_inv] using he
      exact heq ▸ hr
    refine ⟨π m * u,?_⟩
    rintro _ ⟨x,hx,rfl⟩
    obtain ⟨r,hr,he⟩ := hR (mem_map_of_mem π (hAm x hx))
    refine ⟨r,hr,?_⟩
    change (π m*u)*r*(π m*u)⁻¹=π x
    have he' : u*r*u⁻¹ = (π m)⁻¹*π x*π m := by
      change u*r*u⁻¹ = π (m⁻¹*x*m) at he
      simpa only [map_mul,map_inv] using he
    calc
      (π m*u)*r*(π m*u)⁻¹ =
          π m*(u*r*u⁻¹)*(π m)⁻¹ := by group
      _ = π x := by rw [he']; group
  · have hh : color Rg (beta Rg) = false := by
      change color Rg (hVertex Rg 1) = false
      rw [← hg.1,action_preserves_color]
      rfl
    cases hh


include h in
private theorem selected_critical_seed_commutator_le {a c : Vertex Rg}
    (p : CriticalPath Rg (sourceGeometry h) a c) :
    ⁅Z Rg a,Z Rg c⁆ ≤ Z Rg a ⊓ Z Rg c := by
  have hac : Z Rg a ≤ stabilizer Rg c :=
    Z_le_stabilizer_of_dist_le a _ p.critical.1.le
  have hca : Z Rg c ≤ stabilizer Rg a :=
    critical_Z_le_stabilizer Rg (sourceGeometry h) a p.start_color
      (by rw [(sourceGeometry h).distance_constant a p.start_color]; exact sourceDistance_pos h)
      p.critical
  exact le_inf
    (le_normalizer_iff_commutator_le_left.mp (hca.trans (Z_normalized Rg a)))
    (le_normalizer_iff_commutator_le_right.mp (hac.trans (Z_normalized Rg c)))

private theorem seed_le_stabilizer_of_dist_le {a b : Vertex Rg}
    (ha : color Rg a = false)
    (hd : (cosetGraph Rg).dist a b ≤ sourceDistance h) :
    Z Rg a ≤ stabilizer Rg b := by
  apply Z_le_stabilizer_of_dist_le a ((sourceGeometry h).exists_critical a ha)
  rwa [(sourceGeometry h).distance_constant a ha]

private theorem graph_seed_quadratic (a : Vertex Rg) (ha : color Rg a = false)
    (hd : (cosetGraph Rg).dist a (alpha Rg) ≤ sourceDistance h) :
    QuadraticPointCore.Quadratic (CubicAction.graphImage h e hz hk (Z Rg a)) := by
  let A := (Z Rg a).comap (embedM Rg)
  have hm : A.map (embedM Rg) = Z Rg a :=
    map_comap_eq_self ((seed_le_stabilizer_of_dist_le (h := h) ha hd).trans_eq (stabilizer_m_base Rg))
  have hZa : Z Rg (alpha Rg) ≤ stabilizer Rg a :=
    seed_le_stabilizer_of_dist_le (h := h) rfl (by rwa [SimpleGraph.dist_comm])
  let := (sourceGeometry h).Z_elementary (sourceDistance_pos h) a ha
  have hcomm : ⁅U Rg (alpha Rg),Z Rg a⁆ ≤ Z Rg a :=
    le_normalizer_iff_commutator_le_right.mp ((show U Rg (alpha Rg) ≤ Z Rg (alpha Rg) from
      le_normalizer_iff_commutator_le_left.mp
        ((map_subtype_le _).trans (Z_normalized Rg (alpha Rg)))).trans
      (hZa.trans (Z_normalized Rg a)))
  apply image_quadratic_of_commutator h e hz hk A
  intro x hx y hy
  apply embedM_injective Rg
  simp only [map_mul]
  have hx' : embedM Rg x ∈ Z Rg a := by
    apply hcomm
    rw [←graph_U_map h e hz,←hm,←map_commutator]
    exact mem_map_of_mem _ hx
  exact (le_centralizer_iff_isMulCommutative.mpr inferInstance) hx' _ hy

include h e hz hk in
private theorem selected_graphImage_card {a' : Vertex Rg}
    (p : CriticalPath Rg (sourceGeometry h) (alpha Rg) a') :
    Nat.card (CubicAction.graphImage h e hz hk (Z Rg a')) =
      (Q Rg (alpha Rg)).relIndex (Z Rg a') := by
  let A := (Z Rg a').comap (embedM Rg)
  have hm : A.map (embedM Rg) = Z Rg a' := map_comap_eq_self
    ((critical_Z_le_stabilizer Rg (sourceGeometry h) (alpha Rg) rfl
      (sourceDistance_pos h) p.critical).trans_eq (stabilizer_m_base Rg))
  let := (sourceGeometry h).Z_elementary (sourceDistance_pos h) a' p.end_color
  change Nat.card (A.map π) = _
  rw [CubicAction.permutation_image_card_of_two h e hz hk A
    ((IsElementaryAbelian.isPGroup 2 (Z Rg a')).comap_of_injective _ (embedM_injective Rg)),
    Q_alpha Rg h.relative_radical.isPGroup h.relative_radical.twoCore_le,←hm,
    relIndex_map_map_of_injective _ _ (embedM_injective Rg)]

include h e hz hk in
/-- Every opposite critical image contains an odd permutation, for either
central cover. Point-core containment is sufficient. -/
theorem critical_opposite_image_not_le_alternating (u : S)
    (hR : (Rg).map π ≤ pointCore.map (MulAut.conj u).toMonoidHom)
    {a' : Vertex Rg}
    (p : CriticalPath Rg (sourceGeometry h) (alpha Rg) a') :
    ¬ CubicAction.graphImage h e hz hk (Z Rg a') ≤ alternatingGroup (Fin 6) := by
  intro heven
  by_cases hlarge : 4 ≤ (Q Rg a').relIndex (Z Rg (alpha Rg))
  · have hp := sourceDistance_pos h
    have hl : p.walk.length = sourceDistance h := p.length_eq_b
    have hat : Adjacent Rg (alpha Rg) (p.walk.getVert 1) := by
      have hh := (cosetGraph_adj Rg _ _).mp (p.walk.adj_getVert_succ (i := 0) (by omega))
      simpa only [SimpleGraph.Walk.getVert_zero] using hh
    have hAt : Z Rg a' ≤ Q Rg (p.walk.getVert 1) := by
      apply Z_le_Q_of_dist_lt Rg a' ((sourceGeometry h).exists_critical a' p.end_color)
      rw [(sourceGeometry h).distance_constant _ p.end_color,SimpleGraph.dist_comm,p.dist_end]
      change p.walk.length-1 < sourceDistance h
      omega
    obtain ⟨v,hv⟩ := selected_graphImage_le_pointCore_of_le_edge h e hz hk u hR _ hat _ hAt
    have hbound := even_quadratic_conjugate_bound _ v hv heven
      (graph_seed_quadratic h e hz hk a' p.end_color (by rw [SimpleGraph.dist_comm,←p.shortest]; exact p.length_eq_b.le))
    rw [selected_graphImage_card h e hz hk p] at hbound
    have hrev := reverse_critical_image_four_le h e hz hk hp p hlarge
    omega
  · obtain ⟨a,hs,ha⟩ := small_critical_image_eq_swap h e hz hk p (by omega)
    have ham : a ∈ CubicAction.graphImage h e hz hk (Z Rg a') := by
      change a ∈ ((Z Rg a').comap (embedM Rg)).map π
      rw [ha]
      exact mem_zpowers a
    have hh := Equiv.Perm.mem_alternatingGroup.mp (heven ham)
    rw [hs.sign_eq] at hh
    norm_num at hh

include h e hz hk in
/-- A selected critical commutator is fixed at the midpoint. The original
point-core containment, central cover and generating edge are retained. -/
theorem selected_critical_commutator_central
    (u : S)
    (hR : (Rg).map π ≤ pointCore.map (MulAut.conj u).toMonoidHom)
    {m c a' : Vertex Rg}
    (p : CriticalPath Rg (sourceGeometry h) m c)
    (q : CriticalPath Rg (sourceGeometry h) (alpha Rg) a')
    (hm : (cosetGraph Rg).dist m (alpha Rg) ≤ 2)
    (hcm : (cosetGraph Rg).dist c (alpha Rg) ≤ 2)
    (hce : (cosetGraph Rg).dist c a' < sourceDistance h)
    (hgen : Q Rg (p.walk.getVert 1) ⊔ Z Rg a' = stabilizer Rg (alpha Rg)) :
    ⁅Z Rg m,Z Rg c⁆ ≤
      centralizer (stabilizer Rg (alpha Rg) : Set (FreeAmalgam Rg)) := by
  let D := ⁅Z Rg m,Z Rg c⁆
  have hVm : Z Rg m ≤ V Rg (alpha Rg) :=
    le_iSup_of_le m (le_iSup_of_le hm le_rfl)
  have hVc : Z Rg c ≤ V Rg (alpha Rg) :=
    le_iSup_of_le c (le_iSup_of_le hcm le_rfl)
  have hDX : D ≤ X Rg (alpha Rg) :=
    (commutator_mono hVm hVc).trans ((radius_bounds_at h e hz hk (alpha Rg) rfl m c).2.1)
  have hDQ : D ≤ Q Rg (alpha Rg) := hDX.trans (omegaCenter_le _)
  have hQC : Q Rg (alpha Rg) ≤ centralizer (D : Set (FreeAmalgam Rg)) :=
    le_centralizer_iff.mp (hDX.trans (fun _ hx => (mem_omegaCenter_iff.mp hx).2.2))
  have hDc : D ≤ Z Rg c := (selected_critical_seed_commutator_le h p).trans inf_le_right
  have hC : Z Rg a' ≤ centralizer (D : Set (FreeAmalgam Rg)) := by
    apply le_centralizer_iff.mp
    apply (hDc.trans (Z_le_Q_of_dist_lt Rg c ((sourceGeometry h).exists_critical c p.end_color) ?_)).trans
      (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp
        (Z_centralizes_Q Rg a' q.end_color)))
    rwa [(sourceGeometry h).distance_constant c p.end_color]
  have hab : ⁅(Rg).map π,(Rg).map π⁆ = ⊥ := by
    let := pointCore_elementary
    let : IsElementaryAbelian 2 (pointCore.map (MulAut.conj u).toMonoidHom) := IsElementaryAbelian.map _
    let helem : IsElementaryAbelian 2 ((Rg).map π) :=
      IsElementaryAbelian.of_le (B := pointCore.map (MulAut.conj u).toMonoidHom) hR
    exact (commutator_eq_bot_iff_le_centralizer.mpr
      (le_centralizer_iff_isMulCommutative.mpr helem.toIsMulCommutative))
  have hN : stabilizer Rg (alpha Rg) ≤ normalizer (D : Set (FreeAmalgam Rg)) := by
    rw [←hgen]
    exact sup_le (critical_commutator_normalized_first_of_abelian_image h e hz hk hab p)
      (hC.trans (Subgroup.centralizer_le_normalizer _))
  exact normalized_subgroup_central_of_critical_odd h e hz hk D (Z Rg a')
    (hDQ.trans (fun _ hx => hx.1)) hN hQC hC
    (critical_opposite_image_not_le_alternating h e hz hk u hR q)


include h e hz hk in
private theorem full_point_large_actor_not_fixed (u : S)
    (hfull : (Rg).map π = pointCore.map (MulAut.conj u).toMonoidHom)
    (A : Subgroup M) (hA : A ≤ Rg) (hcard : 4 ≤ Nat.card (A.map π))
    (hfix : ⁅W,A⁆ ≤ centralizer (Rg : Set M)) : False := by
  have hAc := (map_mono hA).trans hfull.le
  have hquad := image_quadratic_of_commutator h e hz hk A
    (hfix.trans (centralizer_le hA))
  have horder : Nat.card (A.map π) = 4 :=
    Nat.le_antisymm (QuadraticPointCore.conjugate_core_bound _ u hAc hquad) hcard
  have hle : (Rg).map π ≤ A.map π := by
    rw [←QuadraticPointCore.conjugate_four_moved_fixer _ u hAc hquad horder]
    intro y hy
    exact ⟨hfull.le hy,(image_centralizes_moved h e hz hk A Rg hfix hy).2⟩
  have hi := Nat.card_le_card_of_injective (inclusion hle) (inclusion_injective hle)
  rw [horder,hfull,card_map_of_injective (MulAut.conj u).injective,pointCore_card] at hi
  omega

include h e hz hk in
private theorem full_point_large_edge_commutator_not_central_base (u : S)
    (hfull : (Rg).map π = pointCore.map (MulAut.conj u).toMonoidHom)
    (A : Subgroup (FreeAmalgam Rg)) (hA : A ≤ Q Rg (beta Rg))
    (hcard : 4 ≤ (Q Rg (alpha Rg)).relIndex A) :
    ¬ ⁅U Rg (alpha Rg),A⁆ ≤ centralizer (Q Rg (beta Rg) : Set (FreeAmalgam Rg)) := by
  intro hfix
  let A₀ := A.comap (embedM Rg)
  have hA₀ : A₀ ≤ Rg := by
    intro x hx
    obtain ⟨r,hr,he⟩ := (hA.trans_eq (Q_beta Rg)) hx
    exact (embedM_injective Rg he) ▸ hr
  have hmapA : A₀.map (embedM Rg) = A := map_comap_eq_self
    (hA.trans ((Q_beta Rg).trans_le (map_le_range _ _)))
  have hcard₀ : 4 ≤ Nat.card (A₀.map π) := by
    rw [CubicAction.permutation_image_card_of_two h e hz hk A₀
      (h.relative_radical.isPGroup.to_le hA₀)]
    rwa [Q_alpha Rg h.relative_radical.isPGroup h.relative_radical.twoCore_le,←hmapA,
      relIndex_map_map_of_injective _ _ (embedM_injective Rg)] at hcard
  apply full_point_large_actor_not_fixed h e hz hk u hfull A₀ hA₀ hcard₀
  intro x hx r hr
  apply embedM_injective Rg
  simp only [map_mul]
  apply hfix
  · have hh := mem_map_of_mem (embedM Rg) hx
    rwa [map_commutator,graph_U_map h e hz,hmapA] at hh
  · rw [Q_beta]
    exact mem_map_of_mem _ hr

include h e hz hk in
/-- A large actor in a point-core edge cannot have its full moving
commutator fixed by that edge. The calculation uses the natural quotient
of either entire moving cover, retaining the central attachment. -/
theorem full_point_large_edge_commutator_not_central (u : S)
    (hfull : (Rg).map π = pointCore.map (MulAut.conj u).toMonoidHom)
    {a t : Vertex Rg} (ha : color Rg a = false) (hat : Adjacent Rg a t)
    (A : Subgroup (FreeAmalgam Rg)) (hA : A ≤ Q Rg t)
    (hcard : 4 ≤ (Q Rg a).relIndex A) :
    ¬ ⁅U Rg a,A⁆ ≤ centralizer (Q Rg t : Set (FreeAmalgam Rg)) := by
  intro hfix
  obtain ⟨g,hg | hg⟩ := edge_transitive Rg hat (base_adjacent Rg)
  · let f := (MulAut.conj g⁻¹).toMonoidHom
    have hQ : (Q Rg a).map f = Q Rg (alpha Rg) := by rw [←Q_act,hg.1]; rfl
    have hQt : (Q Rg t).map f = Q Rg (beta Rg) := by rw [←Q_act,hg.2]; rfl
    have hU : (U Rg a).map f = U Rg (alpha Rg) := by rw [←U_act,hg.1]; rfl
    have hi : 4 ≤ (Q Rg (alpha Rg)).relIndex (A.map f) := by
      rw [←hQ,relIndex_map_map_of_injective _ _ (MulAut.conj g⁻¹).injective]
      exact hcard
    apply full_point_large_edge_commutator_not_central_base h e hz hk u hfull
      (A.map f) ((map_mono hA).trans_eq hQt) hi
    rw [←hU,←hQt,←map_commutator]
    exact (map_mono hfix).trans (map_centralizer_le_centralizer_image _ f)
  · have hn : color Rg (beta Rg) = false := by
      change color Rg (hVertex Rg 1) = false
      rw [←hg.1,action_preserves_color,ha]
    cases hn

include h e hz hk in
/-- An entire first edge fixing the critical commutator forces both
critical images to have order two, on the original cubic graph. -/
theorem critical_indices_two_of_first_edge_central (u : S)
    (hfull : (Rg).map π = pointCore.map (MulAut.conj u).toMonoidHom)
    {a a' : Vertex Rg} (p : CriticalPath Rg (sourceGeometry h) a a')
    (hcentral : ⁅Z Rg a,Z Rg a'⁆ ≤
      centralizer (Q Rg (p.walk.getVert 1) : Set (FreeAmalgam Rg))) :
    (Q Rg a').relIndex (Z Rg a) = 2 ∧
      (Q Rg a).relIndex (Z Rg a') = 2 := by
  apply small_critical_indices h e hz hk p
  by_contra! hlarge
  have hp := sourceDistance_pos h
  have hl : p.walk.length = sourceDistance h := p.length_eq_b
  have hat : Adjacent Rg a (p.walk.getVert 1) := by
    have hh := (cosetGraph_adj Rg _ _).mp (p.walk.adj_getVert_succ (i := 0) (by omega))
    simpa only [SimpleGraph.Walk.getVert_zero] using hh
  have hAt : Z Rg a' ≤ Q Rg (p.walk.getVert 1) := by
    apply Z_le_Q_of_dist_lt Rg a' ((sourceGeometry h).exists_critical a' p.end_color)
    rw [(sourceGeometry h).distance_constant _ p.end_color,SimpleGraph.dist_comm,p.dist_end]
    change p.walk.length-1 < sourceDistance h
    omega
  exact full_point_large_edge_commutator_not_central h e hz hk u hfull p.start_color
    hat (Z Rg a') hAt (reverse_critical_image_four_le h e hz hk hp p hlarge)
    ((commutator_mono (DistanceEight.U_le_Z Rg a) le_rfl).trans hcentral)

include h e hz hk in
/-- The same selected commutator has order two and both critical images
have order two, without a zero fixed-space assumption on the cover. -/
theorem selected_critical_indices_two
    (u : S)
    (hfull : (Rg).map π = pointCore.map (MulAut.conj u).toMonoidHom)
    {m c a' : Vertex Rg}
    (p : CriticalPath Rg (sourceGeometry h) m c)
    (q : CriticalPath Rg (sourceGeometry h) (alpha Rg) a')
    (hm : (cosetGraph Rg).dist m (alpha Rg) ≤ 2)
    (hcm : (cosetGraph Rg).dist c (alpha Rg) ≤ 2)
    (hce : (cosetGraph Rg).dist c a' < sourceDistance h)
    (hgen : Q Rg (p.walk.getVert 1) ⊔ Z Rg a' = stabilizer Rg (alpha Rg)) :
    (Q Rg c).relIndex (Z Rg m) = 2 ∧
      (Q Rg m).relIndex (Z Rg c) = 2 ∧
      Nat.card (⁅Z Rg m,Z Rg c⁆ : Subgroup (FreeAmalgam Rg)) = 2 := by
  have hcentral := selected_critical_commutator_central h e hz hk u hfull.le p q hm hcm hce hgen
  have hi := critical_indices_two_of_first_edge_central h e hz hk u hfull p
    (hcentral.trans (centralizer_le (show Q Rg (p.walk.getVert 1) ≤
      stabilizer Rg (alpha Rg) by rw [←hgen]; exact le_sup_left)))
  exact ⟨hi.1,hi.2,small_critical_commutator_card h e hz hk p (by omega)⟩

include h e hz hk in
/-- At distance four, the prescribed backward chain has small images.
The original generating edge and every path vertex remain literal. -/
theorem selected_backward_indices_two_of_distance_four
    (u : S)
    (hfull : (Rg).map π = pointCore.map (MulAut.conj u).toMonoidHom)
    (hb : sourceDistance h = 4) {a' c : Vertex Rg}
    (p : CriticalPath Rg (sourceGeometry h) (alpha Rg) a')
    (q : CriticalPath Rg (sourceGeometry h) c (p.walk.getVert (p.walk.length-2)))
    (hq2 : q.walk.getVert 2 = alpha Rg)
    (hgen : Q Rg (q.walk.getVert 1) ⊔ Z Rg a' = stabilizer Rg (alpha Rg)) :
    (Q Rg (p.walk.getVert (p.walk.length-2))).relIndex (Z Rg c) = 2 ∧
      (Q Rg c).relIndex (Z Rg (p.walk.getVert (p.walk.length-2))) = 2 ∧
      Nat.card (⁅Z Rg c,Z Rg (p.walk.getVert (p.walk.length-2))⁆ :
        Subgroup (FreeAmalgam Rg)) = 2 := by
  have hl : p.walk.length = 4 := p.length_eq_b.trans hb
  have hql : q.walk.length = 4 := q.length_eq_b.trans hb
  apply selected_critical_indices_two h e hz hk u hfull q p
  · simpa only [hq2] using (q.dist_start (i := 2) (by omega)).le
  · have hh := (p.dist_start (i := p.walk.length-2) (Nat.sub_le _ _)).le
    simpa only [SimpleGraph.dist_comm,hl,Nat.reduceSub] using hh
  · rw [p.dist_end,hl,hb]
    decide
  · exact hgen


include h e hz hk in
/-- The original point-core branch supplies a generating distance-four
configuration whose selected backward critical images and commutator have
order two. That commutator is central at the original midpoint. The local
conjugator, nonabelian selected span and complete overlap are retained. -/
theorem point_image_small_central_generating_configuration
    (u : S) (hR : (Rg).map π ≤ pointCore.map (MulAut.conj u).toMonoidHom) :
    sourceDistance h = 4 ∧
      ∃ a', ∃ p : CriticalPath Rg (sourceGeometry h) (alpha Rg) a',
        ⁅localZSpan Rg (p.walk.getVert 2) (alpha Rg),
          localZSpan Rg (p.walk.getVert 2) (alpha Rg)⁆ ≠ ⊥ ∧
        ∃ c t x, x ∈ stabilizer Rg (alpha Rg) ∧
          act Rg x (p.walk.getVert 2) = c ∧
          Adjacent Rg (alpha Rg) t ∧ Adjacent Rg c t ∧
          Q Rg t ⊔ Z Rg a' = stabilizer Rg (alpha Rg) ∧
          ∃ q : CriticalPath Rg (sourceGeometry h) c (p.walk.getVert (p.walk.length-2)),
            q.walk.getVert 1 = t ∧
            (∀ i ≤ p.walk.length-2, q.walk.getVert (i+2) = p.walk.getVert i) ∧
            (Q Rg (p.walk.getVert (p.walk.length-2))).relIndex (Z Rg c) = 2 ∧
            (Q Rg c).relIndex (Z Rg (p.walk.getVert (p.walk.length-2))) = 2 ∧
            Nat.card (⁅Z Rg c,Z Rg (p.walk.getVert (p.walk.length-2))⁆ :
              Subgroup (FreeAmalgam Rg)) = 2 ∧
            ⁅Z Rg c,Z Rg (p.walk.getVert (p.walk.length-2))⁆ ≤
              centralizer (stabilizer Rg (alpha Rg) : Set (FreeAmalgam Rg)) := by
  obtain ⟨hb,a',p,hnon,c,t,x,hx,hxc,hat,hct,hgen,q,hq1,hover⟩ :=
    point_image_nonabelian_generating_configuration h e hz hk u hR
  have hfull := full_point_image_of_contained h e hz hk u hR
  have hl : p.walk.length = 4 := p.length_eq_b.trans hb
  have hql : q.walk.length = 4 := q.length_eq_b.trans hb
  have hq2 : q.walk.getVert 2 = alpha Rg := by
    simpa only [Nat.zero_add,SimpleGraph.Walk.getVert_zero] using hover 0 (Nat.zero_le _)
  have hgen' : Q Rg (q.walk.getVert 1) ⊔ Z Rg a' = stabilizer Rg (alpha Rg) := by
    rwa [hq1]
  have hi := selected_backward_indices_two_of_distance_four h e hz hk u hfull hb p q hq2 hgen'
  have hcentral := selected_critical_commutator_central h e hz hk u hR q p
    (by simpa only [hq2] using (q.dist_start (i := 2) (by omega)).le)
    (by have hh := (p.dist_start (i := p.walk.length-2) (Nat.sub_le _ _)).le
        simpa only [SimpleGraph.dist_comm,hl,Nat.reduceSub] using hh)
    (by rw [p.dist_end,hl,hb]; decide) hgen'
  exact ⟨hb,a',p,hnon,c,t,x,hx,hxc,hat,hct,hgen,q,hq1,hover,hi.1,hi.2.1,hi.2.2,hcentral⟩

omit hk in
include h e hz in
/-- Whole-core application: the original point-core branch now supplies
the nonabelian selected span and a generating backward configuration with
small critical images and a central order-two commutator at distance four. Plane and Sylow radical images remain separate branches. -/
theorem coreExhaustion_or_cubic_small_central_generating_configuration :
    CoreExhaustion L R ∨ ∃ hk : layerKernel L R = extensionKernel h,
      Function.Surjective (CubicAction.projection h e hz hk) ∧
      2 < sourceDistance h ∧
      (∀ a : Vertex Rg, color Rg a = false →
        Nat.card (U Rg a) = 16 ∨ Nat.card (U Rg a) = 32) ∧
      ∃ u : S,
        ((Rg).map (CubicAction.projection h e hz hk) =
            pointCore.map (MulAut.conj u).toMonoidHom ∧
          sourceDistance h = 4 ∧
          ∃ a', ∃ p : CriticalPath Rg (sourceGeometry h) (alpha Rg) a',
            ⁅localZSpan Rg (p.walk.getVert 2) (alpha Rg),
              localZSpan Rg (p.walk.getVert 2) (alpha Rg)⁆ ≠ ⊥ ∧
            ∃ c t x, x ∈ stabilizer Rg (alpha Rg) ∧
              act Rg x (p.walk.getVert 2) = c ∧
              Adjacent Rg (alpha Rg) t ∧ Adjacent Rg c t ∧
              Q Rg t ⊔ Z Rg a' = stabilizer Rg (alpha Rg) ∧
              ∃ q : CriticalPath Rg (sourceGeometry h) c
                  (p.walk.getVert (p.walk.length-2)),
                q.walk.getVert 1 = t ∧
                (∀ i ≤ p.walk.length-2, q.walk.getVert (i+2) = p.walk.getVert i) ∧
                (Q Rg (p.walk.getVert (p.walk.length-2))).relIndex (Z Rg c) = 2 ∧
                (Q Rg c).relIndex (Z Rg (p.walk.getVert (p.walk.length-2))) = 2 ∧
                Nat.card (⁅Z Rg c,Z Rg (p.walk.getVert (p.walk.length-2))⁆ :
                  Subgroup (FreeAmalgam Rg)) = 2 ∧
                ⁅Z Rg c,Z Rg (p.walk.getVert (p.walk.length-2))⁆ ≤
                  centralizer (stabilizer Rg (alpha Rg) : Set (FreeAmalgam Rg))) ∨
        (Rg).map (CubicAction.projection h e hz hk) =
          D.map (MulAut.conj u).toMonoidHom ∨
        (Rg).map (CubicAction.projection h e hz hk) =
          borel.map (MulAut.conj u).toMonoidHom := by
  rcases coreExhaustion_or_cubic_radical_cases h e hz with
    hx | ⟨hk,hs,hb,hcovers,u,hpoint | hplane | hsylow⟩
  · exact Or.inl hx
  · refine Or.inr ⟨hk,hs,hb,hcovers,u,Or.inl ?_⟩
    exact ⟨hpoint.2,point_image_small_central_generating_configuration h e hz hk u hpoint.2.le⟩
  · exact Or.inr ⟨hk,hs,hb,hcovers,u,Or.inr (Or.inl hplane)⟩
  · exact Or.inr ⟨hk,hs,hb,hcovers,u,Or.inr (Or.inr hsylow)⟩

omit hk in
include h e hz in
/-- Literal C.1.32 consumer of the small central distance-four configuration,
retaining the original cubic projection and both full moving covers. -/
theorem rankTwo_or_cubic_small_central_generating_configuration :
    RankTwoAlternatives L R ∨ ∃ hk : layerKernel L R = extensionKernel h,
      Function.Surjective (CubicAction.projection h e hz hk) ∧
      2 < sourceDistance h ∧
      (∀ a : Vertex Rg, color Rg a = false →
        Nat.card (U Rg a) = 16 ∨ Nat.card (U Rg a) = 32) ∧
      ∃ u : S,
        ((Rg).map (CubicAction.projection h e hz hk) =
            pointCore.map (MulAut.conj u).toMonoidHom ∧
          sourceDistance h = 4 ∧
          ∃ a', ∃ p : CriticalPath Rg (sourceGeometry h) (alpha Rg) a',
            ⁅localZSpan Rg (p.walk.getVert 2) (alpha Rg),
              localZSpan Rg (p.walk.getVert 2) (alpha Rg)⁆ ≠ ⊥ ∧
            ∃ c t x, x ∈ stabilizer Rg (alpha Rg) ∧
              act Rg x (p.walk.getVert 2) = c ∧
              Adjacent Rg (alpha Rg) t ∧ Adjacent Rg c t ∧
              Q Rg t ⊔ Z Rg a' = stabilizer Rg (alpha Rg) ∧
              ∃ q : CriticalPath Rg (sourceGeometry h) c
                  (p.walk.getVert (p.walk.length-2)),
                q.walk.getVert 1 = t ∧
                (∀ i ≤ p.walk.length-2, q.walk.getVert (i+2) = p.walk.getVert i) ∧
                (Q Rg (p.walk.getVert (p.walk.length-2))).relIndex (Z Rg c) = 2 ∧
                (Q Rg c).relIndex (Z Rg (p.walk.getVert (p.walk.length-2))) = 2 ∧
                Nat.card (⁅Z Rg c,Z Rg (p.walk.getVert (p.walk.length-2))⁆ :
                  Subgroup (FreeAmalgam Rg)) = 2 ∧
                ⁅Z Rg c,Z Rg (p.walk.getVert (p.walk.length-2))⁆ ≤
                  centralizer (stabilizer Rg (alpha Rg) : Set (FreeAmalgam Rg))) ∨
        (Rg).map (CubicAction.projection h e hz hk) =
          D.map (MulAut.conj u).toMonoidHom ∨
        (Rg).map (CubicAction.projection h e hz hk) =
          borel.map (MulAut.conj u).toMonoidHom :=
  (coreExhaustion_or_cubic_small_central_generating_configuration h e hz).imp
    (rankTwo_of_exhaustion h e hz) id

end AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicFull
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
