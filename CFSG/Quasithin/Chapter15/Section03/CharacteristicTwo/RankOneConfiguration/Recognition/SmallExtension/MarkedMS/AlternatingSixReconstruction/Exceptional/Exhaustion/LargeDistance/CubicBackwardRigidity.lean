module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicBackwardFixedCore

/-!
# Backward displacement rigidity with the cubic kernel retained

The natural pairing controls an actor whose whole-cover displacement lies in
that of a fixed hyperplane. Its image lies in the original transposition group;
its full preimage is E joined to the original actor, retaining E/Q of order
three. Oriented edge coordinates transport this bound to the full reverse
critical kernel. The extra edge seed centralizes the edge core, so the full
and moving fixed seeds have the same displacement.

Consequently, an endpoint actor bounded by the reverse kernel's predecessor
commutator fixes that entire kernel. Residual transport preserves the small
kernel commutator. If it is nonzero, it therefore cannot become the entire
endpoint displacement. CubicResidualShift applies this to the actual source
walk and the whole-core and C.1.32 consumers.

Source: Meierfrankenfeld--Stellmacher (1993), (3.3)(ii), pp.866--867, and
(5.8), p.920. Adapts Natural.Exhaustion.LargeDistance.SectionFive.BackwardRigidity
with the cubic action kernel retained. Predecessor-slice placement, the
remaining edge choices and final reconstruction remain with
qt-e-ms-small-a6-reconstruction.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender BinaryPermutation
open scoped IsMulCommutative commutatorElement Pointwise
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicFull
open Theory.SpecificGroups.SymmetricSix.BinaryFlags
open CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup
universe u
private theorem small_actor_le_of_moved_le
    (A D : Subgroup (Equiv.Perm (Fin 6))) (hA : A ≠ ⊥)
    (hsmall : fixedCodim (naturalRepresentation (Fin 6)) A ≤ 1)
    (hmoved : subspaceCommutator (naturalRepresentation (Fin 6)) ⊤ D ≤
      subspaceCommutator (naturalRepresentation (Fin 6)) ⊤ A) : D ≤ A := by
  open NaturalPairing in
  have hfixed : fixedSpace (naturalRepresentation (Fin 6)) A ≤
      fixedSpace (naturalRepresentation (Fin 6)) D := by
    rw [moved_eq_fixed_orthogonal,moved_eq_fixed_orthogonal] at hmoved
    have hh := form.orthogonal_le hmoved
    simpa only [LinearMap.BilinForm.orthogonal_orthogonal form_nondegenerate form_alt.isRefl] using hh
  have hsup : fixedSpace (naturalRepresentation (Fin 6)) (A ⊔ D) =
      fixedSpace (naturalRepresentation (Fin 6)) A := by
    have hh : fixedSpace (naturalRepresentation (Fin 6)) (A ⊔ D) =
        fixedSpace (naturalRepresentation (Fin 6)) A ⊓ fixedSpace (naturalRepresentation (Fin 6)) D :=
      (naturalRepresentation (Fin 6)).invariants_comp_sup A D
    rw [hh,inf_eq_left.mpr hfixed]
  have hsupsmall : fixedCodim (naturalRepresentation (Fin 6)) (A ⊔ D) ≤ 1 := by
    change Module.finrank (ZMod 2) ((natural (Fin 6)) ⧸
      fixedSpace (naturalRepresentation (Fin 6)) (A ⊔ D)) ≤ 1
    rw [hsup]
    exact hsmall
  have hsupne : A ⊔ D ≠ ⊥ := fun he => hA (le_bot_iff.mp (he ▸ le_sup_left))
  obtain ⟨t,_,ht,he⟩ := PointCoreTranspositionFixed.small_image_eq_zpowers
    (A ⊔ D) hsupne hsupsmall
  have hc : Nat.card (A ⊔ D : Subgroup (Equiv.Perm (Fin 6))) = 2 := by
    rw [he,Nat.card_zpowers,ht.orderOf]
  have hAc := (one_lt_card_iff_ne_bot A).mpr hA
  have heq : A = A ⊔ D := eq_of_le_of_card_ge le_sup_left (by omega)
  exact heq ▸ le_sup_right

variable {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
  (h : SmallMSPair KnownSimple.IsKnownSimple L R) (e : CentralMarking L)
  (hz : Nat.card (center (L ⧸ pCore 2 L)) = 3)
  (hk : layerKernel L R = extensionKernel h)
local notation "M" => (L ⊔ R : Subgroup G)
local notation "W" => (⁅centralOmega L R,L.subgroupOf (L ⊔ R)⁆ : Subgroup M)
local notation "π" => CubicAction.projection h e hz hk
local notation "Rg" => edge L R
local instance : IsElementaryAbelian 2 W := IsElementaryAbelian.of_le (commutator_le_left _ _)
private abbrev coverAction : Representation (ZMod 2) (Equiv.Perm (Fin 6)) (Additive W) := by
  let := h.relative_normal
  exact NormalElementaryQuotient.representation W π
    (CubicEven.projection_surjective h e hz hk) (CubicAction.moved_projection_kernel h e hz hk)
private def coverMap : Additive W →ₗ[ZMod 2] natural (Fin 6) :=
  Classical.choose (CubicAction.moved_natural_projection h e hz hk)
private theorem coverMap_surjective : Function.Surjective (coverMap h e hz hk) :=
  (Classical.choose_spec (CubicAction.moved_natural_projection h e hz hk)).1
private theorem coverMap_equivariant (g : Equiv.Perm (Fin 6)) (v : Additive W) :
    coverMap h e hz hk (coverAction h e hz hk g v) =
      naturalRepresentation (Fin 6) g (coverMap h e hz hk v) := by
  let := h.relative_normal
  obtain ⟨a,rfl⟩ := CubicEven.projection_surjective h e hz hk g
  have he : coverAction h e hz hk (π a) v = Additive.ofMul (MulAut.conjNormal a v.toMul) := by
    apply Additive.toMul.injective
    apply Subtype.ext
    exact NormalElementaryQuotient.representation_apply W π
      (CubicEven.projection_surjective h e hz hk) (CubicAction.moved_projection_kernel h e hz hk) a v
  rw [he]
  exact (Classical.choose_spec (CubicAction.moved_natural_projection h e hz hk)).2.2 a v


omit hk in
include h e hz in
private theorem vertex_seed_eq_moving_sup_edge {c b : Vertex Rg}
    (hc : color Rg c = false) (hcb : Adjacent Rg c b) :
    Z Rg c = U Rg c ⊔ Z Rg b := by
  obtain ⟨g,hg | hg⟩ := (adjacent_iff_exists_common Rg c b).mp hcb
  · rcases hg with ⟨rfl,rfl⟩
    have hb := CubicAction.graph_Z_eq_moved_sup_edge h e hz (base_adjacent Rg)
    rw [graph_U_map h e hz] at hb
    have he := congrArg (fun A : Subgroup (FreeAmalgam Rg) =>
      A.map (MulAut.conj g⁻¹).toMonoidHom) hb
    rw [Subgroup.map_sup,←Z_act,←U_act,←Z_act] at he
    simpa [alpha,beta] using he
  · rw [hg.1] at hc
    cases hc

include h e hz hk in
/-- The fixed hyperplane's displacement bounds the whole actor image.
Its preimage retains the original cubic kernel E, for either full cover. -/
theorem cover_actor_le_of_fixed_displacement (u : Equiv.Perm (Fin 6))
    (hR : (Rg).map π ≤ pointCore.map (MulAut.conj u).toMonoidHom)
    (A D : Subgroup M) (hA : A ≤ Rg)
    (hne : ¬ A ≤ pCore 2 M)
    (hindex : (centralizer (A : Set M)).relIndex (W) ≤ 2)
    (hcomm : ⁅W,D⁆ ≤
      ⁅W ⊓ centralizer (A : Set M),Rg⁆) :
    D ≤ extensionKernel h ⊔ A := by
  let := h.relative_normal
  let U := W
  let f := coverMap h e hz hk
  let Dnat := subspaceCommutator (naturalRepresentation (Fin 6)) ⊤ (A.map π)
  let T := (Dnat.comap f).toAddSubgroup.toSubgroup'.map U.subtype
  have hnA : A.map π ≠ ⊥ := by
    intro he
    apply hne
    exact two_subgroup_le_core_of_le_extensionKernel h hz A
      (h.relative_radical.isPGroup.to_le hA)
      ((CubicAction.projection_kernel h e hz hk) ▸ (map_eq_bot_iff A).mp he)
  have hsmall : fixedCodim (coverAction h e hz hk) (A.map π) ≤ 1 := by
    rw [NormalElementaryQuotient.centralizer_index_eq_fixedCodim
      (W) π (CubicEven.projection_surjective h e hz hk)
      (CubicAction.moved_projection_kernel h e hz hk)] at hindex
    exact (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp hindex
  have hnat : fixedCodim (naturalRepresentation (Fin 6)) (A.map π) ≤ 1 :=
    (fixedCodim_le_of_equivariant_surjection (coverAction h e hz hk) (naturalRepresentation (Fin 6))
      f (coverMap_surjective h e hz hk)
      (coverMap_equivariant h e hz hk) (A.map π)).trans hsmall
  have hdisp := PointCoreTranspositionFixed.small_image_fixed_displacement_le u
    (A.map π) ((map_mono hA).trans hR) hnA hnat
  have hT : ⁅U ⊓ centralizer (A : Set M),Rg⁆ ≤ T := by
    apply commutator_le.mpr
    intro v hv r hr
    have hcu : ⁅v,r⁆ ∈ U := (commutator_le_left U Rg)
      (commutator_mem_commutator hv.1 hr)
    refine ⟨⟨⁅v,r⁆,hcu⟩,?_,rfl⟩
    change f (Additive.ofMul (⟨⁅v,r⁆,hcu⟩ : U)) ∈ Dnat
    rw [NormalElementaryQuotient.vector_commutator U π (CubicEven.projection_surjective h e hz hk)
      (CubicAction.moved_projection_kernel h e hz hk) ⟨v,hv.1⟩ r,map_sub]
    change f (Additive.ofMul ⟨v,hv.1⟩) -
      f (coverAction h e hz hk (π r) (Additive.ofMul ⟨v,hv.1⟩)) ∈ Dnat
    rw [show f (coverAction h e hz hk (π r) (Additive.ofMul ⟨v,hv.1⟩)) =
      naturalRepresentation (Fin 6) (π r) (f (Additive.ofMul ⟨v,hv.1⟩)) from
        coverMap_equivariant h e hz hk _ _]
    apply Dnat.neg_mem_iff.mp
    rw [neg_sub]
    apply hdisp
    apply Submodule.subset_span
    refine ⟨π r,hR (mem_map_of_mem _ hr),f (Additive.ofMul ⟨v,hv.1⟩),?_,rfl⟩
    have hfixed := (NormalElementaryQuotient.mem_fixedSpace_image U π (CubicEven.projection_surjective h e hz hk)
      (CubicAction.moved_projection_kernel h e hz hk) A
      (Additive.ofMul ⟨v,hv.1⟩)).mpr hv.2
    intro a
    change naturalRepresentation (Fin 6) a (f (Additive.ofMul ⟨v,hv.1⟩)) =
      f (Additive.ofMul ⟨v,hv.1⟩)
    exact (coverMap_equivariant h e hz hk a _).symm.trans (congrArg f (hfixed a))
  have hspace : subspaceCommutator (coverAction h e hz hk) ⊤ (D.map π) ≤ Dnat.comap f := by
    have hh : NormalElementaryQuotient.commutatorSpace U D =
        subspaceCommutator (coverAction h e hz hk) ⊤ (D.map π) :=
      NormalElementaryQuotient.commutatorSpace_eq U π (CubicEven.projection_surjective h e hz hk)
        (CubicAction.moved_projection_kernel h e hz hk) D
    rw [←hh]
    intro v hv
    change (v.toMul : M) ∈ ⁅U,D⁆ at hv
    obtain ⟨w,hw,he⟩ := hT (hcomm hv)
    have he' : w = v.toMul := Subtype.ext he
    change Additive.ofMul w ∈ Dnat.comap f at hw
    simpa only [he',ofMul_toMul] using hw
  have hm : subspaceCommutator (naturalRepresentation (Fin 6)) ⊤ (D.map π) =
      (subspaceCommutator (coverAction h e hz hk) ⊤ (D.map π)).map f := by
    have hh := subspaceCommutator_map_embedding (naturalRepresentation (Fin 6))
      (coverAction h e hz hk) (MonoidHom.id _) f
      (fun g v => (coverMap_equivariant h e hz hk g v).symm) (D.map π) ⊤
    have hf : f.range = ⊤ := LinearMap.range_eq_top.mpr
      (coverMap_surjective h e hz hk)
    simpa only [Submodule.map_top,hf,map_id] using hh
  have him : D.map π ≤ A.map π :=
    small_actor_le_of_moved_le _ _ hnA hnat (hm ▸ Submodule.map_le_iff_le_comap.mpr hspace)
  have hle := (le_comap_map π D).trans (comap_mono him)
  rw [Subgroup.comap_map_eq,(CubicAction.projection_kernel h e hz hk)] at hle
  exact hle.trans_eq (sup_comm _ _)

include h e hz in
private theorem full_fixed_seed_edge_commutator
    {c t : Vertex Rg} (hcol : color Rg c = false)
    (hct : Adjacent Rg c t)
    (A : Subgroup (FreeAmalgam Rg)) (hA : A ≤ Q Rg t)
    (D : Subgroup (FreeAmalgam Rg)) (hD : D ≤ Q Rg t) :
    ⁅Z Rg c ⊓ centralizer (A : Set (FreeAmalgam Rg)),D⁆ =
      ⁅U Rg c ⊓ centralizer (A : Set (FreeAmalgam Rg)),D⁆ := by
  let F := U Rg c ⊓ centralizer (A : Set (FreeAmalgam Rg))
  have ht : color Rg t = true := by
    have hh := adjacent_color_ne Rg hct
    rw [hcol] at hh
    cases he : color Rg t <;> simp_all
  have hseed : Z Rg t ≤ centralizer (Q Rg t : Set (FreeAmalgam Rg)) := by
    intro x hx
    rw [Z,if_neg (by simp [ht])] at hx
    exact (mem_omegaCenter_iff.mp hx).2.2
  have hseedA := hseed.trans (centralizer_le hA)
  have hseedN : Z Rg t ≤ normalizer (U Rg c : Set (FreeAmalgam Rg)) :=
    ((adjacent_Z_le Rg hcol hct).trans (Z_le_stabilizer Rg c)).trans (U_normalized c)
  have heq : Z Rg c ⊓ centralizer (A : Set (FreeAmalgam Rg)) = F ⊔ Z Rg t := by
    rw [vertex_seed_eq_moving_sup_edge h e hz hcol hct,
      sup_comm (U Rg c),inf_centralizer_sup_of_centralizing _ _ _ hseedN hseedA]
    exact sup_comm _ _
  rw [heq]
  apply le_antisymm _ (commutator_mono le_sup_left le_rfl)
  apply commutator_le.mpr
  intro x hx r hr
  have hn : Z Rg t ≤ normalizer (F : Set (FreeAmalgam Rg)) :=
    (le_inf hseedN (hseedA.trans (centralizer (A : Set (FreeAmalgam Rg))).le_normalizer)).trans
      inf_normalizer_le_normalizer_inf
  have hp : x ∈ (F : Set (FreeAmalgam Rg)) * (Z Rg t : Set (FreeAmalgam Rg)) := by
    rw [←coe_mul_of_right_le_normalizer_left F (Z Rg t) hn]
    exact hx
  obtain ⟨w,hw,z,hz,rfl⟩ := hp
  have hzero : ⁅z,r⁆ = 1 := commutatorElement_eq_one_iff_mul_comm.mpr (hseed hz r (hD hr)).symm
  rw [commutatorElement_mul_left_eq_conj_mul,hzero,mul_one,mul_inv_cancel,one_mul]
  exact commutator_mem_commutator hw hr

include h e hz hk in
/-- The bound on the literal oriented edge retains the whole initial
centralizer, including its odd quotient over the two-core. -/
theorem edge_actor_le_of_fixed_displacement
    (u : Equiv.Perm (Fin 6))
    (hR : (Rg).map π ≤ pointCore.map (MulAut.conj u).toMonoidHom)
    {c t : Vertex Rg} (hcol : color Rg c = false)
    (hct : Adjacent Rg c t)
    (A D : Subgroup (FreeAmalgam Rg)) (hA : A ≤ Q Rg t)
    (hD : D ≤ stabilizer Rg c) (hne : ¬ A ≤ Q Rg c)
    (hindex : (centralizer (A : Set (FreeAmalgam Rg))).relIndex (U Rg c) ≤ 2)
    (hcomm : ⁅U Rg c,D⁆ ≤
      ⁅Z Rg c ⊓ centralizer (A : Set (FreeAmalgam Rg)),Q Rg t⁆) :
    D ≤ (stabilizer Rg c ⊓ centralizer (X Rg c : Set (FreeAmalgam Rg))) ⊔ A := by
  have hcoords : ∃ i : M →* FreeAmalgam Rg, Function.Injective i ∧
      i.range = stabilizer Rg c ∧
      (Rg).map i = Q Rg t ∧ (pCore 2 M).map i = Q Rg c ∧
      (W).map i = U Rg c ∧
      (extensionKernel h).map i = stabilizer Rg c ⊓ centralizer (X Rg c : Set (FreeAmalgam Rg)) := by
    obtain ⟨g,hg|hg⟩ := (adjacent_iff_exists_common Rg c t).mp hct
    · rcases hg with ⟨rfl,rfl⟩
      let i := (MulAut.conj g⁻¹).toMonoidHom.comp (embedM Rg)
      refine ⟨i,(MulAut.conj g⁻¹).injective.comp (embedM_injective Rg),?_,?_,?_,?_,?_⟩
      · change ((MulAut.conj g⁻¹).toMonoidHom.comp (embedM Rg)).range = _
        have he : (embedM Rg).range = stabilizer Rg (alpha Rg) :=
          (stabilizer_m_base Rg).symm
        rw [MonoidHom.range_comp,he,←stabilizer_act]
        simp only [alpha,act_mVertex,one_mul]
      · have he := Q_act Rg g (beta Rg)
        rw [Q_beta] at he
        simpa only [beta,act_hVertex,one_mul,map_map] using he.symm
      · have he := Q_act Rg g (alpha Rg)
        rw [Q_alpha Rg (h.relative_radical.isPGroup) (h.relative_radical.twoCore_le)] at he
        simpa only [alpha,act_mVertex,one_mul,map_map] using he.symm
      · have he := U_act Rg g (alpha Rg)
        rw [←graph_U_map h e hz] at he
        simpa only [alpha,act_mVertex,one_mul,map_map] using he.symm
      · have hi : Function.Injective i := (MulAut.conj g⁻¹).injective.comp (embedM_injective Rg)
        have hr : i.range = stabilizer Rg (mVertex Rg g) := by
          rw [MonoidHom.range_comp]
          change (Mbar Rg).map _ = _
          rw [←stabilizer_m_base Rg]
          simpa only [alpha,act_mVertex,one_mul] using (stabilizer_act Rg g (alpha Rg)).symm
        have hX : (centralOmega L R).map i = X Rg (mVertex Rg g) := by
          rw [←map_map,←graph_X h]
          simpa only [alpha,act_mVertex,one_mul] using (X_act Rg g (alpha Rg)).symm
        rw [←hk,←hX,←hr]
        apply le_antisymm
        · exact le_inf (map_le_range _ _) (map_centralizer_le_centralizer_image _ _)
        · rintro x ⟨⟨y,rfl⟩,hx⟩
          refine ⟨y,?_,rfl⟩
          intro z hz
          exact hi (by simpa only [map_mul] using hx _ (mem_map_of_mem i hz))
    · rw [hg.1] at hcol
      cases hcol
  obtain ⟨i,hi,hir,hiR,hiQ,hiU,hiE⟩ := hcoords
  have hmA : (A.comap i).map i = A := map_comap_eq_self
    (hA.trans (hiR ▸ map_le_range i _))
  have hmD : (D.comap i).map i = D := map_comap_eq_self (hD.trans_eq hir.symm)
  have hAr : A.comap i ≤ Rg := by
    apply (map_le_map_iff_of_injective hi).mp
    rwa [hmA,hiR]
  have hAn : ¬ A.comap i ≤ pCore 2 M := by
    intro hh
    apply hne
    have hm := map_mono (f := i) hh
    rwa [hmA,hiQ] at hm
  have hidx : (centralizer (A.comap i : Set M)).relIndex (W) ≤ 2 := by
    rw [←hiU,←hmA,←inf_relIndex_right,inf_comm,
      map_inf_centralizer_of_injective i hi,relIndex_map_map_of_injective _ _ hi,
      inf_relIndex_left] at hindex
    exact hindex
  have hcomm' : ⁅W,D.comap i⁆ ≤
      ⁅W ⊓ centralizer (A.comap i : Set M),Rg⁆ := by
    apply (map_le_map_iff_of_injective hi).mp
    rw [map_commutator (W),hiU,hmD,map_commutator,←map_inf_centralizer_of_injective i hi,
      hiU,hiR,hmA]
    rw [full_fixed_seed_edge_commutator h e hz hcol hct A hA (Q Rg t) le_rfl] at hcomm
    exact hcomm
  have hm := map_mono (f := i)
    (cover_actor_le_of_fixed_displacement h e hz hk u hR (A.comap i) (D.comap i) hAr hAn hidx hcomm')
  rwa [Subgroup.map_sup,hiE,hmA,hmD] at hm

include h e hz hk in
/-- A displacement controlled by the full reverse kernel's predecessor
commutator forces pointwise fixation of that full kernel. -/
theorem critical_kernel_displacement_actor
    (hb : 2 < sourceDistance h)
    (u : Equiv.Perm (Fin 6))
    (hR : (Rg).map π ≤ pointCore.map (MulAut.conj u).toMonoidHom)
    {a a' : Vertex Rg}
    (p : CriticalPath Rg (sourceGeometry h) a a')
    (hsmall : (Q Rg a').relIndex (Z Rg a) < 4)
    (D : Subgroup (FreeAmalgam Rg)) (hD : D ≤ stabilizer Rg a')
    (hcomm : ⁅U Rg a',D⁆ ≤
      ⁅Z Rg a' ⊓ Q Rg a,Q Rg (p.walk.getVert (p.walk.length-2))⁆) :
    D ≤ (stabilizer Rg a' ⊓ centralizer (X Rg a' : Set (FreeAmalgam Rg))) ⊔ Z Rg a ∧
      D ≤ centralizer (Z Rg a' ⊓ Q Rg a : Set (FreeAmalgam Rg)) := by
  have hl : 2 < p.walk.length := p.length_eq_b ▸ hb
  let t := p.walk.getVert (p.walk.length-1)
  have hat : Adjacent Rg a' t := by
    have hh := p.walk.adj_getVert_succ (i := p.walk.length-1) (by omega)
    rw [show p.walk.length-1+1=p.walk.length by omega,p.walk.getVert_length] at hh
    exact adjacent_symm Rg ((cosetGraph_adj Rg _ _).mp hh)
  have ht : color Rg t = true := by
    have hh := adjacent_color_ne Rg hat
    rw [p.end_color] at hh
    cases he : color Rg t <;> simp_all
  have hpred : Q Rg (p.walk.getVert (p.walk.length-2)) ≤ Q Rg t := by
    apply Q_le_adjacent_h Rg ht
    have hh := p.walk.adj_getVert_succ (i := p.walk.length-2) (by omega)
    rw [show p.walk.length-2+1=p.walk.length-1 by omega] at hh
    exact (cosetGraph_adj Rg _ _).mp hh
  have hZt : Z Rg a ≤ Q Rg t := by
    apply Z_le_Q_of_dist_lt Rg _ ((sourceGeometry h).exists_critical _ p.start_color)
    rw [(sourceGeometry h).distance_constant _ p.start_color,p.dist_start (Nat.sub_le _ _)]
    have he : p.walk.length = sourceDistance h := p.length_eq_b
    change p.walk.length-1 < sourceDistance h
    omega
  have hfixed : Z Rg a' ⊓ Q Rg a =
      Z Rg a' ⊓ centralizer (Z Rg a : Set (FreeAmalgam Rg)) := by
    let q := CriticalPath.ofPair (geometry := sourceGeometry h) p.end_color
      (critical_reverse Rg (sourceGeometry h) (sourceEdgeCentralizer h e)
        a p.start_color (by
          rw [(sourceGeometry h).distance_constant a p.start_color]
          exact sourceDistance_pos h) a' p.end_color p.critical)
    exact (critical_seed_centralizer_intersection h e q).symm
  let := finite_Z Rg a'
  let : Finite (U Rg a') := Finite.of_injective
    (inclusion (DistanceEight.U_le_Z Rg a')) (inclusion_injective _)
  have hindex : (centralizer (Z Rg a : Set (FreeAmalgam Rg))).relIndex
      (U Rg a') ≤ 2 := by
    have hQC : Q Rg a ≤ centralizer (Z Rg a : Set (FreeAmalgam Rg)) :=
      le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp
        (Z_centralizes_Q Rg a p.start_color))
    exact ((relIndex_le_of_le_left hQC index_ne_zero_of_finite).trans
      (relIndex_le_of_le_right (DistanceEight.U_le_Z Rg a') index_ne_zero_of_finite)).trans_eq
        (small_critical_indices h e hz hk p hsmall).2
  have hupper := hcomm.trans (commutator_mono le_rfl hpred)
  rw [hfixed] at hupper
  have hle := edge_actor_le_of_fixed_displacement h e hz hk u hR p.end_color hat
    (Z Rg a) D hZt hD p.critical.2 hindex hupper
  refine ⟨hle,hle.trans (sup_le ?_ ?_)⟩
  · exact inf_le_right.trans (centralizer_le (inf_le_left.trans
      ((sourceGeometry h).omega_bound a' p.end_color (by
        rw [(sourceGeometry h).distance_constant a' p.end_color]
        exact sourceDistance_pos h))))
  · exact (commutator_eq_bot_iff_le_centralizer.mp
      (Z_centralizes_Q Rg a p.start_color)).trans (centralizer_le inf_le_right)


include h e hz hk in
/-- A nonzero backward-kernel commutator cannot equal the entire endpoint
displacement after the same residual transporter. Slice placement is explicit. -/
theorem critical_kernel_residual_displacement_ne
    (hb : 2 < sourceDistance h)
    (u : Equiv.Perm (Fin 6))
    (hR : (Rg).map π ≤ pointCore.map (MulAut.conj u).toMonoidHom)
    {a a' : Vertex Rg}
    (p : CriticalPath Rg (sourceGeometry h) a a')
    (hsmall : (Q Rg a').relIndex (Z Rg a) < 4)
    (hslice : Z Rg a' ⊓ Q Rg a ≤
      B Rg (p.walk.getVert (p.walk.length-2)) ((sourceGeometry h).Z_normal _))
    (D : Subgroup (FreeAmalgam Rg))
    (hD : D ≤ Q Rg (p.walk.getVert (p.walk.length-2)))
    (hne : ⁅Z Rg a' ⊓ Q Rg a,D⁆ ≠ ⊥)
    (k : FreeAmalgam Rg)
    (hkm : k ∈ Ltilde Rg (p.walk.getVert (p.walk.length-2))) :
    ⁅U Rg a',D.map (MulAut.conj k).toMonoidHom⁆ ≠
      ⁅Z Rg a' ⊓ Q Rg a,D⁆ := by
  intro he
  have hcol : color Rg (p.walk.getVert (p.walk.length-2)) = false := by
    apply (p.vertex_color (Nat.sub_le _ _)).mpr
    have heven := sourceDistance_even h
    rw [Nat.even_iff] at heven ⊢
    have hh : p.walk.length = sourceDistance h := p.length_eq_b
    omega
  have hcard := small_critical_kernel_predecessor_card h e hz hk hb u hR p hsmall
  have htransport := small_slice_commutator_residual_transport (h := h)
    hb hcol _ hslice hcard D hD k hkm
  have hDk : D.map (MulAut.conj k).toMonoidHom ≤ stabilizer Rg a' := by
    have hkQ : (Q Rg (p.walk.getVert (p.walk.length-2))).map
        (MulAut.conj k).toMonoidHom = Q Rg (p.walk.getVert (p.walk.length-2)) :=
      mem_normalizer_iff_map_conj_eq.mp ((Q_normalized Rg _)
        (Ltilde_le_stabilizer _ hkm))
    apply ((map_mono hD).trans_eq hkQ).trans
    have hl : 2 < p.walk.length := p.length_eq_b ▸ hb
    let t := p.walk.getVert (p.walk.length-1)
    have hat : Adjacent Rg a' t := by
      have hh := p.walk.adj_getVert_succ (i := p.walk.length-1) (by omega)
      rw [show p.walk.length-1+1=p.walk.length by omega,p.walk.getVert_length] at hh
      exact adjacent_symm Rg ((cosetGraph_adj Rg _ _).mp hh)
    have ht : color Rg t = true := by
      have hh := adjacent_color_ne Rg hat
      rw [p.end_color] at hh
      cases he : color Rg t <;> simp_all
    apply (Q_le_adjacent_h Rg ht ?_).trans
      (show Q Rg t ≤ stabilizer Rg a' from
        fun _ hx => hx.2 _ (adjacent_symm Rg hat))
    have hh := p.walk.adj_getVert_succ (i := p.walk.length-2) (by omega)
    rw [show p.walk.length-2+1=p.walk.length-1 by omega] at hh
    exact (cosetGraph_adj Rg _ _).mp hh
  have hactor := (critical_kernel_displacement_actor h e hz hk hb u hR p hsmall
    (D.map (MulAut.conj k).toMonoidHom) hDk
    (he.le.trans (commutator_mono le_rfl hD))).2
  apply hne
  rw [←htransport,commutator_comm]
  exact commutator_eq_bot_iff_le_centralizer.mpr hactor


end AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicFull
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
