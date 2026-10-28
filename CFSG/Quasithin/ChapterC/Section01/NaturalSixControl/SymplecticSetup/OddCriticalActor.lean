module
public import CFSG.Quasithin.ChapterC.Section01.NaturalSixControl.SymplecticSetup.CriticalGeneration
public import Theory.SpecificGroups.SymmetricSix.BinaryFlags.QuadraticPointCore.Conjugation
/-!
# Odd opposite images along native critical paths

Every opposite critical Z-image contains an odd permutation. If the forward
image has order below four, its existing fixed-space bound supplies a
transposition. Otherwise the reverse image has order at least four. The
critical commutator lies in the abelian opposite Z-layer, so this image acts
quadratically on the native natural module. Moving the first edge to the base
edge places the image in a conjugate point core. An even quadratic subgroup
there has order at most two, giving the contradiction.

Only containment of the radical image in a conjugate point core is needed.
The actual characteristic replacement supplies this containment directly.
No distance-four or radius central-quotient recognition premise is imposed.

This is the critical-actor consequence of MS93 (3.3), (5.2), and (5.5), used
in the native selected-chain argument for (5.12).
-/
public section
open Subgroup Theory.GroupTheory BinaryPermutation
open Theory.SpecificGroups.SymmetricSix.BinaryFlags
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
open scoped commutatorElement
namespace CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup

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

namespace Source
variable {M : Type*} [Group M] [Finite M] {L R W : Subgroup M} [L.Normal] [W.Normal]
  (s : Source L R W)

omit [Finite M] in
private theorem quadratic_image_of_centralizing_commutator (A : Subgroup M)
    (hc : ⁅W,A⁆≤centralizer (A:Set M)) :
    QuadraticPointCore.Quadratic (A.map s.projection) := by
  rintro _ ⟨a,ha,rfl⟩ _ ⟨b,hb,rfl⟩ v
  let w := s.coordinates.symm (Multiplicative.ofAdd v)
  let z : W := MulAut.conjNormal b w*w⁻¹
  have hzA : (z:M)∈⁅W,A⁆ := by
    rw [commutator_comm]
    exact commutator_mem_commutator hb w.property
  have hz : MulAut.conjNormal a z=z := by
    apply Subtype.ext
    change a*(z:M)*a⁻¹=(z:M)
    rw [hc hzA a ha,mul_inv_cancel_right]
  have hcz : (s.coordinates z).toAdd=Model.rho (s.projection b) v-v := by
    change (s.coordinates (MulAut.conjNormal b w*w⁻¹)).toAdd=_
    rw [map_mul,map_inv]
    simp only [toAdd_mul,toAdd_inv,s.action,w,MulEquiv.apply_symm_apply,sub_eq_add_neg]
    rfl
  have hact := s.action a z
  rw [hz,hcz] at hact
  exact hact.symm

/-- The opposite critical image always acts quadratically on the marked natural layer. -/
private theorem critical_opposite_image_quadratic (h : NativeCentralLayer s) {e : Vertex R}
    (p : CriticalPath R s.geometry (alpha R) e) :
    QuadraticPointCore.Quadratic (((Z R e).comap (embedM R)).map s.projection) := by
  let A := (Z R e).comap (embedM R)
  have hAe : A.map (embedM R)=Z R e := map_comap_eq_self
    ((critical_Z_le_stabilizer R s.geometry (alpha R) rfl s.criticalDistance_pos p.critical).trans_eq
      (stabilizer_m_base R))
  let := s.geometry.Z_elementary s.criticalDistance_pos e p.end_color
  have hcomm : ⁅U R (alpha R),Z R e⁆≤Z R e :=
    ((commutator_mono (DistanceEight.U_le_Z R _) le_rfl).trans
      (s.critical_Z_commutator_le_moving p)).trans
      (inf_le_right.trans (DistanceEight.U_le_Z R _))
  have hc : ⁅U R (alpha R),Z R e⁆≤centralizer (Z R e:Set (FreeAmalgam R)) :=
    hcomm.trans (le_centralizer_iff_isMulCommutative.mpr inferInstance)
  apply s.quadratic_image_of_centralizing_commutator A
  intro x hx a ha
  apply embedM_injective R
  simp only [map_mul]
  have hx' : embedM R x∈⁅U R (alpha R),Z R e⁆ := by
    rw [h.U_eq_module,←hAe,←map_commutator]
    exact mem_map_of_mem _ hx
  exact hc hx' _ ha

/-- The marked opposite critical image contains an odd permutation. -/
theorem critical_opposite_image_not_le_alternating (h : NativeCentralLayer s) (u : S)
    (hR : R.map s.projection≤pointCore.map (MulAut.conj u).toMonoidHom)
    {e : Vertex R} (p : CriticalPath R s.geometry (alpha R) e) :
    ¬ (((Z R e).comap (embedM R)).map s.projection≤alternatingGroup (Fin 6)) := by
  intro heven
  by_cases hlarge : 4≤(Q R e).relIndex (Z R (alpha R))
  · let A := (Z R e).comap (embedM R)
    have hAe : A.map (embedM R)=Z R e := map_comap_eq_self
      ((critical_Z_le_stabilizer R s.geometry (alpha R) rfl s.criticalDistance_pos p.critical).trans_eq
        (stabilizer_m_base R))
    have hr := s.reverse_critical_image_four_le h s.criticalDistance_pos p hlarge
    have hcard : 4≤Nat.card (A.map s.projection) := by
      rw [Q_alpha R s.two_group s.core_le,←hAe,
        relIndex_map_map_of_injective _ _ (embedM_injective R),←s.projection_kernel,relIndex_ker] at hr
      exact hr
    have hquad := s.critical_opposite_image_quadratic h p
    have hl := p.length_eq_b
    have hb : 0<s.geometry.b R := s.criticalDistance_pos
    have hat : Adjacent R (alpha R) (p.walk.getVert 1) := by
      have hh := (cosetGraph_adj R _ _).mp (p.walk.adj_getVert_succ (i:=0) (by omega))
      simpa only [SimpleGraph.Walk.getVert_zero] using hh
    have hAt : Z R e≤Q R (p.walk.getVert 1) := by
      apply Z_le_Q_of_dist_lt R e (s.geometry.exists_critical e p.end_color)
      rw [s.geometry.distance_constant _ p.end_color,SimpleGraph.dist_comm,p.dist_end (i:=1)]
      change p.walk.length-1<s.geometry.b R
      rw [hl]
      exact Nat.sub_lt hb (by decide)
    obtain ⟨g,hg|hg⟩ := edge_transitive R hat (base_adjacent R)
    · have hgM : g∈(embedM R).range := by
        change g∈Mbar R
        rw [←stabilizer_m_base R]
        exact hg.1
      obtain ⟨m,rfl⟩ := hgM
      have hQt : (Q R (p.walk.getVert 1)).map (MulAut.conj ((embedM R m)⁻¹)).toMonoidHom=
          R.map (embedM R) := by
        rw [←Q_act,hg.2]
        exact Q_beta R
      have hAm (x : M) (hx : x∈A) : m⁻¹*x*m∈R := by
        have hh := ((map_mono hAt).trans_eq hQt) (mem_map_of_mem
          (MulAut.conj ((embedM R m)⁻¹)).toMonoidHom hx)
        obtain ⟨r,hr,he⟩ := hh
        have heq : r=m⁻¹*x*m := by
          apply embedM_injective R
          change embedM R r=(embedM R m)⁻¹*embedM R x*((embedM R m)⁻¹)⁻¹ at he
          simpa only [map_mul,map_inv,inv_inv] using he
        exact heq ▸ hr
      have hplace : A.map s.projection≤pointCore.map
          (MulAut.conj (s.projection m*u)).toMonoidHom := by
        rintro _ ⟨x,hx,rfl⟩
        obtain ⟨r,hr,he⟩ := hR (mem_map_of_mem s.projection (hAm x hx))
        refine ⟨r,hr,?_⟩
        change (s.projection m*u)*r*(s.projection m*u)⁻¹=s.projection x
        have he' : u*r*u⁻¹=(s.projection m)⁻¹*s.projection x*s.projection m := by
          change u*r*u⁻¹=s.projection (m⁻¹*x*m) at he
          simpa only [map_mul,map_inv] using he
        calc
          (s.projection m*u)*r*(s.projection m*u)⁻¹=
              s.projection m*(u*r*u⁻¹)*(s.projection m)⁻¹ := by group
          _=s.projection x := by rw [he']; group
      have hbound := even_quadratic_conjugate_bound (A.map s.projection)
        (s.projection m*u) hplace heven hquad
      exact (by omega : ¬(4:Nat)≤2) (hcard.trans hbound)
    · have hh : color R (beta R)=false := by
        change color R (hVertex R 1)=false
        rw [←hg.1,action_preserves_color]
        rfl
      cases hh
  · obtain ⟨a,ha,hswap⟩ := s.exists_swap_reverse_critical_image_of_small p (by omega)
    have hh := heven ha
    change Equiv.Perm.sign a=1 at hh
    rw [hswap.sign_eq] at hh
    norm_num at hh
end Source
end CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup

namespace CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup.SourceData
variable {K : Type*} [Group K] [Finite K]
  {L W : Subgroup K} [L.Normal] [W.Normal] {T : Sylow 2 K}
  (d : NaturalSixControl.SourceData L W T)

/-- The actual characteristic replacement has an odd opposite critical image,
with its original path and quotient map. -/
theorem reducedSource_critical_opposite_image_not_le_alternating (hm : IntrinsicMSPair d)
    (r : CharacteristicReduction (L.subgroupOf (L⊔d.B)) (d.B.subgroupOf (L⊔d.B)))
    {e : Vertex r.radical}
    (p : CriticalPath r.radical ((originalSource d hm).reduce r).geometry (alpha r.radical) e) :
    ¬ (((Z r.radical e).comap (embedM r.radical)).map
      ((originalSource d hm).reduce r).projection≤alternatingGroup (Fin 6)) := by
  exact ((originalSource d hm).reduce r).critical_opposite_image_not_le_alternating
    (reduced_nativeCentralLayer d hm r) d.relabeler.val⁻¹
    (reducedSource_radical_image_le d hm r) p
end CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup.SourceData
