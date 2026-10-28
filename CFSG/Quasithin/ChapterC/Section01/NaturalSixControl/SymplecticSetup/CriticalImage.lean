module
public import CFSG.Quasithin.ChapterC.Section01.NaturalSixControl.SymplecticSetup.CriticalCommutator
public import CFSG.Quasithin.ChapterC.Section01.NaturalSixControl.SymplecticSetup.MovingLayer
public import Theory.GroupTheory.Commutator.CentralizingComplement
public import CFSG.Quasithin.ChapterC.Section01.NaturalSixControl.SymplecticSetup.PointImage
public import Theory.SpecificGroups.SymmetricSix.BinaryFlags.QuadraticPointCore.MovingFixer
/-!
# The critical radius commutator in the native point-core branch

The marked critical image has order at least four and acts quadratically on
its opposite natural layer. The finite point-core calculation identifies the
pointwise fixer of its moving image with the critical image itself. The radius
intersection centralizes that moving image, hence its image lies in the critical
image and its commutator on the opposite Z-layer lies in the starting Z-layer.

The final theorem uses the literal characteristic replacement and critical
path. Its only extra geometric inputs are b = 4 and the forward image bound;
no reverse-image bound, chosen actor or global X-layer splitting is assumed.

Source: Meierfrankenfeld--Stellmacher (1993), (3.3), printed pp.866--867,
and (5.2)(i), printed pp.913--914.
-/

@[expose] public section
open Subgroup BinaryPermutation
open scoped commutatorElement
open Theory.SpecificGroups.SymmetricSix.BinaryFlags
open Representation.BinaryOffender
namespace CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup.Source
variable {M : Type*} [Group M] [Finite M]
variable {L R W : Subgroup M} [L.Normal] [W.Normal] (s : Source L R W)
include s
omit [Finite M] [L.Normal] s in
private theorem commutator_mem_module (a : M) (w : W) : ⁅a,(w:M)⁆ ∈ W :=
  W.mul_mem ((inferInstance : W.Normal).conj_mem _ w.property a) (W.inv_mem w.property)

omit [Finite M] in
private theorem commutator_coordinates (a : M) (w : W) :
    (s.coordinates ⟨⁅a,(w : M)⁆,commutator_mem_module a w⟩).toAdd =
      naturalRepresentation (Fin 6) (s.projection a) (s.coordinates w).toAdd -
        (s.coordinates w).toAdd := by
  have he : (⟨⁅a,(w:M)⁆,commutator_mem_module a w⟩ : W) =
      MulAut.conjNormal a w * w⁻¹ := by
    apply Subtype.ext
    rfl
  rw [he,map_mul,map_inv]
  simp only [toAdd_mul,toAdd_inv,s.action,sub_eq_add_neg]

omit [Finite M] in
/-- The point-core fixer of the actual marked commutator image. -/
theorem moving_commutator_image_control (u : S)
    (hR : R.map s.projection ≤ pointCore.map (MulAut.conj u).toMonoidHom)
    (A Y : Subgroup M) (hA : A ≤ R) (hY : Y ≤ R)
    (hcard : 4 ≤ Nat.card (A.map s.projection))
    (hAA : ⁅W,A⁆ ≤ centralizer (A : Set M))
    (hAY : ⁅W,A⁆ ≤ centralizer (Y : Set M)) :
    Y.map s.projection ≤ A.map s.projection := by
  have hfix (B : Subgroup M) (hB : ⁅W,A⁆ ≤ centralizer (B : Set M)) :
      B.map s.projection ≤ subspaceKernel (naturalRepresentation (Fin 6))
        (subspaceCommutator (naturalRepresentation (Fin 6)) ⊤ (A.map s.projection)) ⊤ := by
    rintro _ ⟨b,hb,rfl⟩
    refine ⟨mem_top _,?_⟩
    have hk : subspaceCommutator (naturalRepresentation (Fin 6)) ⊤
        (A.map s.projection) ≤ LinearMap.ker (naturalRepresentation (Fin 6) (s.projection b)-LinearMap.id) := by
      apply Submodule.span_le.mpr
      rintro _ ⟨_,⟨a,ha,rfl⟩,v,_,rfl⟩
      let w := s.coordinates.symm (Multiplicative.ofAdd v)
      have hc : ⁅a,(w:M)⁆ ∈ ⁅W,A⁆ := by
        rw [commutator_comm]
        exact commutator_mem_commutator ha w.property
      let z : W := ⟨⁅a,(w:M)⁆,commutator_mem_module a w⟩
      have hz : MulAut.conjNormal b z = z := by
        apply Subtype.ext
        change b * ⁅a,(w:M)⁆ * b⁻¹ = ⁅a,(w:M)⁆
        rw [hB hc b hb,mul_inv_cancel_right]
      have hcz : (s.coordinates z).toAdd =
          naturalRepresentation (Fin 6) (s.projection a) v-v := by
        change (s.coordinates ⟨⁅a,(w:M)⁆,_⟩).toAdd = _
        rw [s.commutator_coordinates]
        simp only [w,MulEquiv.apply_symm_apply]
        rfl
      have hact := s.action b z
      rw [hz,hcz] at hact
      change naturalRepresentation (Fin 6) (s.projection b)
        (naturalRepresentation (Fin 6) (s.projection a) v-v) -
        (naturalRepresentation (Fin 6) (s.projection a) v-v)=0
      exact sub_eq_zero.mpr hact.symm
    intro v hv
    have hh := hk hv
    simpa only [LinearMap.mem_ker,LinearMap.sub_apply,LinearMap.id_apply,sub_eq_zero] using hh
  have hq : QuadraticPointCore.Quadratic (A.map s.projection) := by
    intro a ha b hb v
    exact (hfix A hAA ha).2 _
      (Submodule.subset_span ⟨b,hb,v,Submodule.mem_top,rfl⟩)
  have hAc := (map_mono hA).trans hR
  have hc : Nat.card (A.map s.projection) = 4 :=
    Nat.le_antisymm (QuadraticPointCore.conjugate_core_bound _ u hAc hq) hcard
  rw [←QuadraticPointCore.conjugate_four_moved_fixer _ u hAc hq hc]
  exact fun y hy => ⟨((map_mono hY).trans hR) hy,(hfix Y hAY hy).2⟩

open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph

/-- The finite point-core fixer calculation for actual embedded edge subgroups. -/
theorem edge_moving_image_control (u : S)
    (hR : R.map s.projection ≤ pointCore.map (MulAut.conj u).toMonoidHom)
    (A Y : Subgroup (FreeAmalgam R)) (hA : A ≤ Q R (beta R)) (hY : Y ≤ Q R (beta R))
    (hcard : 4 ≤ (Q R (alpha R)).relIndex A)
    (hAA : ⁅W.map (embedM R),A⁆ ≤ centralizer (A : Set (FreeAmalgam R)))
    (hAY : ⁅W.map (embedM R),A⁆ ≤ centralizer (Y : Set (FreeAmalgam R))) :
    Y ≤ Q R (alpha R) ⊔ A := by
  let A₀ := A.comap (embedM R)
  let Y₀ := Y.comap (embedM R)
  have hQ : Q R (beta R) = R.map (embedM R) := Q_beta R
  have hA₀ : A₀ ≤ R := by
    intro x hx
    obtain ⟨r,hr,he⟩ := (hA.trans_eq hQ) hx
    exact (embedM_injective R he) ▸ hr
  have hY₀ : Y₀ ≤ R := by
    intro x hx
    obtain ⟨r,hr,he⟩ := (hY.trans_eq hQ) hx
    exact (embedM_injective R he) ▸ hr
  have hmapA : A₀.map (embedM R) = A := by
    apply map_comap_eq_self
    exact hA.trans (hQ ▸ map_le_range (embedM R) R)
  have hmapY : Y₀.map (embedM R) = Y := by
    apply map_comap_eq_self
    exact hY.trans (hQ ▸ map_le_range (embedM R) R)
  have hcard₀ : 4 ≤ Nat.card (A₀.map s.projection) := by
    rw [Q_alpha R s.two_group s.core_le,←hmapA,
      relIndex_map_map_of_injective _ _ (embedM_injective R),←s.projection_kernel,
      relIndex_ker] at hcard
    exact hcard
  have hc (B : Subgroup M) (D : Subgroup (FreeAmalgam R))
      (hBD : B.map (embedM R) = D)
      (hC : ⁅W.map (embedM R),A⁆ ≤ centralizer (D : Set (FreeAmalgam R))) :
      ⁅W,A₀⁆ ≤ centralizer (B : Set M) := by
    intro x hx b hb
    apply embedM_injective R
    simp only [map_mul]
    have hx' : embedM R x ∈ ⁅W.map (embedM R),A⁆ := by
      rw [←hmapA,←map_commutator]
      exact mem_map_of_mem _ hx
    exact hC hx' _ (hBD ▸ mem_map_of_mem (embedM R) hb)
  have hm := s.moving_commutator_image_control u hR A₀ Y₀ hA₀ hY₀ hcard₀
    (hc A₀ A hmapA hAA) (hc Y₀ Y hmapY hAY)
  have hle : Y₀ ≤ pCore 2 M ⊔ A₀ := by
    have hc := comap_mono (f := s.projection) hm
    rw [comap_map_eq,comap_map_eq,s.projection_kernel] at hc
    exact (show Y₀ ≤ Y₀ ⊔ pCore 2 M from le_sup_left).trans
      (hc.trans (sup_comm _ _).le)
  rw [←hmapY,Q_alpha R s.two_group s.core_le,←hmapA,←Subgroup.map_sup]
  exact map_mono hle

/-- An edge actor centralizing the critical moving image has no larger
commutator on the actual Z-layer than the marked critical subgroup. -/
theorem edge_commutator_control (u : S)
    (hR : R.map s.projection ≤ pointCore.map (MulAut.conj u).toMonoidHom)
    (A Y : Subgroup (FreeAmalgam R)) (hA : A ≤ Q R (beta R)) (hY : Y ≤ Q R (beta R))
    (hcard : 4 ≤ (Q R (alpha R)).relIndex A)
    (hAA : ⁅W.map (embedM R),A⁆ ≤ centralizer (A : Set (FreeAmalgam R)))
    (hAY : ⁅W.map (embedM R),A⁆ ≤ centralizer (Y : Set (FreeAmalgam R))) :
    ⁅Z R (alpha R),Y⁆ ≤ ⁅Z R (alpha R),A⁆ := by
  have hn : A ≤ normalizer (Z R (alpha R) : Set (FreeAmalgam R)) :=
    (hA.trans (fun _ hx => hx.2 _ (adjacent_symm R (base_adjacent R)))).trans
      (Z_normalized R (alpha R))
  have hc : Q R (alpha R) ≤ centralizer (Z R (alpha R) : Set (FreeAmalgam R)) :=
    le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp
      (Z_centralizes_Q R (alpha R) rfl))
  rw [commutator_eq_of_centralizing_sup rfl hc hn]
  exact commutator_mono le_rfl (s.edge_moving_image_control u hR A Y hA hY hcard hAA hAY)

/-- The same finite calculation at any actual edge of the source graph. -/
theorem edge_commutator_control_at (h : NativeCentralLayer s) (u : S)
    (hR : R.map s.projection ≤ pointCore.map (MulAut.conj u).toMonoidHom)
    (c t : Vertex R) (hc : color R c = false) (hct : Adjacent R c t)
    (A Y : Subgroup (FreeAmalgam R)) (hA : A ≤ Q R t) (hY : Y ≤ Q R t)
    (hcard : 4 ≤ (Q R c).relIndex A)
    (hAA : ⁅U R c,A⁆ ≤ centralizer (A : Set (FreeAmalgam R)))
    (hAY : ⁅U R c,A⁆ ≤ centralizer (Y : Set (FreeAmalgam R))) :
    ⁅Z R c,Y⁆ ≤ ⁅Z R c,A⁆ := by
  obtain ⟨g,hg | hg⟩ := edge_transitive R hct (base_adjacent R)
  · let e := (MulAut.conj g⁻¹).toMonoidHom
    have hQ : (Q R c).map e = Q R (alpha R) := by rw [←Q_act,hg.1]; rfl
    have hQt : (Q R t).map e = Q R (beta R) := by rw [←Q_act,hg.2]; rfl
    have hU : (U R c).map e = W.map (embedM R) := by
      rw [←U_act,hg.1]
      exact h.U_eq_module
    have hZ : (Z R c).map e = Z R (alpha R) := by rw [←Z_act,hg.1]; rfl
    have hC (B : Subgroup (FreeAmalgam R))
        (hB : ⁅U R c,A⁆ ≤ centralizer (B : Set (FreeAmalgam R))) :
        ⁅W.map (embedM R),A.map e⁆ ≤ centralizer (B.map e : Set (FreeAmalgam R)) := by
      rw [←hU,←map_commutator]
      exact (map_mono hB).trans (map_centralizer_le_centralizer_image _ e)
    have hi : 4 ≤ (Q R (alpha R)).relIndex (A.map e) := by
      rw [←hQ,relIndex_map_map_of_injective _ _ (MulAut.conj g⁻¹).injective]
      exact hcard
    have hh := s.edge_commutator_control u hR (A.map e) (Y.map e)
      ((map_mono hA).trans_eq hQt) ((map_mono hY).trans_eq hQt) hi
      (hC A hAA) (hC Y hAY)
    rw [←hZ,←map_commutator,←map_commutator] at hh
    exact (map_le_map_iff_of_injective (MulAut.conj g⁻¹).injective).mp hh
  · have hn : color R (beta R) = false := by
      change color R (hVertex R 1) = false
      rw [←hg.1,action_preserves_color,hc]
    cases hn

open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
/-- In the native point-core branch, the whole opposite Z-layer satisfies
the commutator bound used in MS93 (5.2)(i). -/
theorem critical_radius_commutator_le_Z (h : NativeCentralLayer s) (u : S)
    (hR : R.map s.projection ≤ pointCore.map (MulAut.conj u).toMonoidHom)
    (hb : s.geometry.b R = 4) {a a' : Vertex R}
    (p : CriticalPath R s.geometry a a')
    (hcard : 4 ≤ (Q R a').relIndex (Z R a)) :
    ⁅V R a ⊓ Q R (p.walk.getVert (p.walk.length-2)),Z R a'⁆ ≤ Z R a := by
  have hl : p.walk.length = 4 := p.length_eq_b.trans hb
  let t := p.walk.getVert 3
  have ht : color R t = true := by
    have hh := p.vertex_color (i:=3) (by omega)
    have hn : ¬ color R t = false := by
      intro hh'
      have he := hh.mp hh'
      norm_num at he
    cases he : color R t <;> simp_all
  have hct : Adjacent R a' t := by
    have hh := p.walk.adj_getVert_succ (i:=3) (by omega)
    have hend : p.walk.getVert 4 = a' := by rw [←hl,p.walk.getVert_length]
    rw [hend] at hh
    exact adjacent_symm R ((cosetGraph_adj R _ _).mp hh)
  have het : Adjacent R (p.walk.getVert (p.walk.length-2)) t := by
    rw [hl]
    exact (cosetGraph_adj R _ _).mp (p.walk.adj_getVert_succ (i:=2) (by omega))
  have hAt : Z R a ≤ Q R t := by
    apply Z_le_Q_of_dist_lt R a (s.geometry.exists_critical a p.start_color)
    have hd : (cosetGraph R).dist a t = 3 := p.dist_start (by omega)
    have hk : criticalDistance R a (s.geometry.exists_critical a p.start_color) = 4 :=
      (s.geometry.distance_constant a p.start_color).trans hb
    rw [hd,hk]
    decide
  have hYt : V R a ⊓ Q R (p.walk.getVert (p.walk.length-2)) ≤ Q R t :=
    inf_le_right.trans (Q_le_adjacent_h R ht het)
  have hcomm : ⁅U R a',Z R a⁆ ≤ ⁅Z R a,Z R a'⁆ := by
    rw [commutator_comm]
    exact commutator_mono le_rfl (DistanceEight.U_le_Z R a')
  have hRZa : ⁅Z R a,Z R a'⁆ ≤ Z R a :=
    ((s.critical_Z_commutator_le_moving p).trans inf_le_left).trans (DistanceEight.U_le_Z R a)
  let := s.geometry.Z_elementary (by omega : 0 < s.geometry.b R) a p.start_color
  have hAA : ⁅U R a',Z R a⁆ ≤ centralizer (Z R a : Set (FreeAmalgam R)) :=
    (hcomm.trans hRZa).trans (le_centralizer_iff_isMulCommutative.mpr inferInstance)
  have hAY : ⁅U R a',Z R a⁆ ≤ centralizer
      (V R a ⊓ Q R (p.walk.getVert (p.walk.length-2)) : Set (FreeAmalgam R)) :=
    hcomm.trans (le_centralizer_iff.mp (s.critical_radius_intersection_centralizes (by omega) p))
  have hh := s.edge_commutator_control_at h u hR a' t p.end_color hct
    (Z R a) _ hAt hYt hcard hAA hAY
  rw [commutator_comm (Z R a') (Z R a)] at hh
  rw [commutator_comm]
  exact hh.trans hRZa
end CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup.Source

namespace CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup.SourceData
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
variable {K : Type*} [Group K] [Finite K]
    {L W : Subgroup K} [L.Normal] [W.Normal] {T : Sylow 2 K}
    (d : CFSG.Quasithin.ChapterC.NaturalSixControl.SourceData L W T)
/-- The original characteristic replacement supplies the marked natural layer
and point-core placement in the source-(5.2)(i) commutator bound. -/
theorem reducedSource_critical_radius_commutator_le_Z (h : IntrinsicMSPair d)
    (c : CharacteristicReduction (L.subgroupOf (L ⊔ d.B))
      (d.B.subgroupOf (L ⊔ d.B)))
    (hb : ((originalSource d h).reduce c).geometry.b c.radical = 4)
    {a a' : Vertex c.radical}
    (p : CriticalPath c.radical ((originalSource d h).reduce c).geometry a a')
    (hcard : 4 ≤ (Q c.radical a').relIndex (Z c.radical a)) :
    ⁅V c.radical a ⊓ Q c.radical (p.walk.getVert (p.walk.length-2)),Z c.radical a'⁆ ≤
      Z c.radical a := by
  apply Source.critical_radius_commutator_le_Z ((originalSource d h).reduce c)
    (reduced_nativeCentralLayer d h c) d.relabeler.val⁻¹ _ hb p hcard
  exact reducedSource_radical_image_le d h c
end CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup.SourceData
