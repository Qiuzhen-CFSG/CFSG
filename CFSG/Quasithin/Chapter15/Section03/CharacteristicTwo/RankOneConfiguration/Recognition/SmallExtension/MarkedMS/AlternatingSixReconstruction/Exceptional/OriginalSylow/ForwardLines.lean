module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.OriginalSylow.Paths
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicLargeClosure
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicForwardClosure
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.FullSeed
import all Theory.SpecificGroups.SymmetricSix.BinaryFlags.PointOrbits

/-!
# Whole-seed forward lines for the original Borel graph

A small forward Baumann slice supplies a small critical pair by reversing
an actual compatible prefix. This gives displacement coordinates on the
whole seed, with both possible moving covers retained. A conjugate point
core contained in the Borel fixes the edge seed; its noncentral vectors
therefore have the duad orbit. Their centralizers and any escaping actor
admit a simultaneous generation and movement conjugator.

The source normal-closure argument consequently makes the forward kernel
line central at the starting vertex for either critical image size.

Source: Meierfrankenfeld--Stellmacher (1993), (5.9), pp.920--921.
The coordinate and normal-closure arguments extend CubicLargeClosure's
point-core calculation to containment. The original graph and cubic
kernel are unchanged. Strict slices and the terminal exclusions remain open.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender BinaryPermutation
open Theory.SpecificGroups.SymmetricSix
open Theory.SpecificGroups.SymmetricSix.BinaryFlags
open Theory.SpecificGroups.SymmetricSix.BinaryFlags.PointOrbits
open scoped IsMulCommutative commutatorElement Pointwise
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Exceptional.OriginalSylow
open Exhaustion Exhaustion.LargeDistance Exhaustion.LargeDistance.CubicFull
open Natural.Exhaustion.LargeDistance.SectionFive.SeedCoordinates
universe u
variable {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
  (h : SmallMSPair KnownSimple.IsKnownSimple L R) (e : CentralMarking L)
  (hz : Nat.card (center (L ⧸ pCore 2 L)) = 3)
  (hk : layerKernel L R = extensionKernel h)
local notation "M" => (L ⊔ R : Subgroup G)
local notation "π" => CubicAction.projection h e hz hk
local notation "Rg" => edge L R

include h e hz hk in
private theorem contained_point_seed_orbit
    {b : Vertex Rg} (q : CriticalPath Rg (sourceGeometry h) (alpha Rg) b)
    (hsmall : (Q Rg b).relIndex (Z Rg (alpha Rg)) < 4)
    (u : S6) (hfull : pointCore.map (MulAut.conj u).toMonoidHom ≤ (Rg).map π)
    (v : radiusSeed L R) (hv : (v : M) ∉ center M)
    (hvR : (v : M) ∈ centralizer (Rg : Set M)) :
    letI := seed_elementary (h := h)
    ∃ f : Duad → Additive (radiusSeed L R), Function.Injective f ∧
      (∀ g d, seedAction h e hz hk g (f d) = f (g • d)) ∧
      ∃ d, f d = Additive.ofMul v := by
  let := seed_elementary (h := h)
  let ρ := seedAction h e hz hk
  obtain ⟨j,hj,hcoords⟩ := full_seed_displacement_coordinates h e hz hk q hsmall
  obtain ⟨w,hw⟩ := hcoords (Additive.ofMul v)
  have hfix (g : S6) (hg : g ∈ pointCore.map (MulAut.conj u).toMonoidHom) :
      ρ g (Additive.ofMul v) = Additive.ofMul v := by
    obtain ⟨r,hr,rfl⟩ := hfull hg
    apply Additive.toMul.injective
    apply Subtype.ext
    rw [seedAction_conjugate]
    change r*(v:M)*r⁻¹=(v:M)
    rw [hvR r hr,mul_inv_cancel_right]
  have hvfix : ¬ ∀ g, ρ g (Additive.ofMul v)=Additive.ofMul v := by
    intro hh
    apply hv
    apply mem_center_iff.mpr
    intro m
    have he := congrArg (fun y : Additive (radiusSeed L R) => (y.toMul : M)) (hh (π m))
    rw [seedAction_conjugate] at he
    exact mul_inv_eq_iff_eq_mul.mp he
  exact coordinates_point_orbit ρ j hj (Additive.ofMul v) w hw u hfix hvfix

include h e hz hk in
/-- A full seed vector fixed by the original radical has a generating conjugate
for every actor escaping the entire cubic kernel. -/
private theorem contained_point_seed_generator
    {b : Vertex Rg} (q : CriticalPath Rg (sourceGeometry h) (alpha Rg) b)
    (hsmall : (Q Rg b).relIndex (Z Rg (alpha Rg)) < 4)
    (u : S6) (hfull : pointCore.map (MulAut.conj u).toMonoidHom ≤ (Rg).map π)
    (v : radiusSeed L R)
    (hv : (v : M) ∉ center M)
    (hvR : (v : M) ∈ centralizer (Rg : Set M))
    (A : Subgroup M) (hA : ¬ A ≤ extensionKernel h) :
    ∃ g ∈ L.subgroupOf (L ⊔ R),
      centralizer ({g * (v : M) * g⁻¹} : Set M) ⊔ A = ⊤ ∧
      g * (v : M) * g⁻¹ ∉ centralizer (A : Set M) := by
  let := seed_elementary (h := h)
  obtain ⟨f,hf,heq,j,hj⟩ := contained_point_seed_orbit h e hz hk q hsmall u hfull v hv hvR
  obtain ⟨a,ha,han⟩ := SetLike.not_le_iff_exists.mp hA
  have hat : π a ≠ 1 := by
    intro he
    apply han
    rw [←(CubicAction.projection_kernel h e hz hk)]
    exact he
  have hm : ∃ k : Duad, π a • k ≠ k := by
    by_contra! hh
    apply hat
    exact eq_of_smul_eq_smul (α := Duad) (fun k => (hh k).trans (one_smul _ _).symm)
  obtain ⟨k,hkMove⟩ := hm
  obtain ⟨t,ht⟩ := MulAction.exists_smul_eq (alternatingGroup (Fin 6)) j k
  have htL : t.val ∈ (L.subgroupOf (L ⊔ R)).map π := by
    rw [CubicAction.component_image h e hz hk]
    exact t.property
  obtain ⟨g,hg,hgt⟩ := htL
  let w : Additive (radiusSeed L R) := seedAction h e hz hk (π g) (Additive.ofMul v)
  have hw : w = f k := by
    dsimp only [w]
    rw [←hj,hgt,heq]
    exact congrArg f ht
  have hwval : (w.toMul : M) = g * (v : M) * g⁻¹ :=
    seedAction_conjugate h e hz hk g (Additive.ofMul v)
  have hC : centralizer ({g * (v : M) * g⁻¹} : Set M) =
      (MulAction.stabilizer S6 k).comap π := by
    ext m
    rw [mem_centralizer_singleton_iff]
    change _ ↔ π m • k = k
    have hh := seedAction_conjugate h e hz hk m w
    rw [hw,heq] at hh
    constructor
    · intro hm
      apply hf
      apply Additive.toMul.injective
      apply Subtype.ext
      rw [←hwval] at hm
      rw [←hw] at hh ⊢
      exact hh.trans (by rw [hm,mul_inv_cancel_right])
    · intro hm
      rw [hm] at hh
      rw [←hw,hwval] at hh
      exact mul_inv_eq_iff_eq_mul.mp hh.symm
  have hmax : IsCoatom (centralizer ({g * (v : M) * g⁻¹} : Set M)) := by
    rw [hC]
    exact isCoatom_comap_of_surjective (CubicEven.projection_surjective h e hz hk)
      (MulAction.IsPreprimitive.isCoatom_stabilizer_of_isPreprimitive S6 k)
  have haC : a ∉ centralizer ({g * (v : M) * g⁻¹} : Set M) := by
    rw [hC]
    exact hkMove
  refine ⟨g,hg,?_,?_⟩
  · apply hmax.2
    apply lt_of_le_of_ne le_sup_left
    intro he
    exact haC (he.symm ▸ (show a ∈ centralizer ({g * (v : M) * g⁻¹} : Set M) ⊔ A from mem_sup_right ha))
  · intro hc
    apply haC
    rw [mem_centralizer_singleton_iff]
    exact hc a ha

include h e hz hk in
/-- A noncentral line in the incident edge seed has a simultaneous generating
centralizer and movement choice for every escaping two-actor. -/
theorem contained_point_seed_line_generator
    {b : Vertex Rg} (q : CriticalPath Rg (sourceGeometry h) (alpha Rg) b)
    (hsmall : (Q Rg b).relIndex (Z Rg (alpha Rg)) < 4)
    (u : S6) (hfull : pointCore.map (MulAut.conj u).toMonoidHom ≤ (Rg).map π)
    {a : Vertex Rg} (ha : color Rg a = false) {t : Vertex Rg} (hat : Adjacent Rg a t)
    (A₁ : Subgroup (FreeAmalgam Rg))
    (hAG : A₁ ≤ stabilizer Rg a) (htwo : IsPGroup 2 A₁)
    (hescape : ¬ A₁ ≤ Q Rg a)
    (H : Subgroup (FreeAmalgam Rg)) (hHt : H ≤ Z Rg t)
    (hcard : Nat.card H = 2)
    (hcentral : ¬ H ≤ centralizer (stabilizer Rg a : Set (FreeAmalgam Rg))) :
    ∃ g ∈ Ltilde Rg a,
      (stabilizer Rg a ⊓ centralizer
        (H.map (MulAut.conj g).toMonoidHom : Set (FreeAmalgam Rg))) ⊔
          A₁ = stabilizer Rg a ∧
      ¬ H.map (MulAut.conj g).toMonoidHom ≤ centralizer
        (A₁ : Set (FreeAmalgam Rg)) := by
  classical
  obtain ⟨z,hzn,hunique⟩ := (Nat.card_eq_two_iff' (1 : H)).mp hcard
  have hznot : (z : FreeAmalgam Rg) ∉ centralizer
      (stabilizer Rg a : Set (FreeAmalgam Rg)) := by
    intro hz
    apply hcentral
    intro x hx
    by_cases hx1 : x = 1
    · exact hx1 ▸ one_mem _
    · have he : (⟨x,hx⟩ : H) = z := hunique _ (fun he => hx1 (congrArg Subtype.val he))
      have hxz : x = (z : FreeAmalgam Rg) := congrArg Subtype.val he
      rw [hxz]
      exact hz
  have hcoords : ∃ i : M →* FreeAmalgam Rg, Function.Injective i ∧
      i.range = stabilizer Rg a ∧ (pCore 2 M).map i = Q Rg a ∧
      (radiusSeed L R).map i = Z Rg a ∧ (Rg).map i = Q Rg t := by
    have hbase : (radiusSeed L R).map (embedM Rg) = Z Rg (alpha Rg) :=
      map_comap_eq_self ((Z_le_stabilizer Rg _).trans_eq (stabilizer_m_base Rg))
    obtain ⟨g,hg|hg⟩ := (adjacent_iff_exists_common Rg a t).mp hat
    · rcases hg with ⟨rfl,rfl⟩
      let i := (MulAut.conj g⁻¹).toMonoidHom.comp (embedM Rg)
      refine ⟨i,(MulAut.conj g⁻¹).injective.comp (embedM_injective Rg),?_,?_,?_,?_⟩
      · rw [MonoidHom.range_comp]
        change (Mbar Rg).map (MulAut.conj g⁻¹).toMonoidHom = _
        rw [←stabilizer_m_base]
        simpa only [alpha,act_mVertex,one_mul] using (stabilizer_act Rg g (alpha Rg)).symm
      · have he := Q_act Rg g (alpha Rg)
        rw [Q_alpha Rg h.relative_radical.isPGroup h.relative_radical.twoCore_le] at he
        simpa only [alpha,act_mVertex,one_mul,map_map] using he.symm
      · have he := Z_act Rg g (alpha Rg)
        rw [←hbase] at he
        simpa only [alpha,act_mVertex,one_mul,map_map] using he.symm
      · have he := Q_act Rg g (beta Rg)
        rw [Q_beta] at he
        simpa only [beta,act_hVertex,one_mul,map_map] using he.symm
    · rw [hg.1] at ha
      cases ha
  obtain ⟨i,hi,hir,hiQ,hiZ,hiR⟩ := hcoords
  obtain ⟨v,hv,hvz⟩ := (show (z : FreeAmalgam Rg) ∈ (radiusSeed L R).map i from
    hiZ.symm ▸ (hHt.trans (adjacent_Z_le Rg ha hat)) z.property)
  have hvnot : v ∉ center M := by
    intro hv
    apply hznot
    intro m hm
    obtain ⟨m,rfl⟩ := hir.symm ▸ hm
    rw [←hvz,←map_mul,←map_mul]
    exact congrArg i (mem_center_iff.mp hv m)
  have hA : A₁ ≤ i.range := hAG.trans_eq hir.symm
  let A := A₁.comap i
  have hmA : A.map i = A₁ := map_comap_eq_self hA
  have hnA : ¬ A ≤ extensionKernel h := by
    intro he
    have ht : IsPGroup 2 A := htwo.comap_of_injective i hi
    have hh := map_mono (f := i)
      (two_subgroup_le_core_of_le_extensionKernel h hz A ht he)
    rw [hmA,hiQ] at hh
    exact hescape hh
  have hvR : v ∈ centralizer (Rg : Set M) := by
    intro r hr
    apply hi
    simp only [map_mul]
    rw [hvz]
    have ht : color Rg t = true := by
      have hh := adjacent_color_ne Rg hat
      rw [ha] at hh
      cases he : color Rg t <;> simp_all
    have hz' := hHt z.property
    rw [Z,if_neg (by simp [ht])] at hz'
    exact (mem_omegaCenter_iff.mp hz').2.2 (i r) (hiR ▸ mem_map_of_mem i hr)
  obtain ⟨g,hg,hgen,hmove⟩ :=
    contained_point_seed_generator h e hz hk q hsmall u hfull ⟨v,hv⟩ hvnot hvR A hnA
  let j : M →* stabilizer Rg a :=
    i.codRestrict _ (fun x => hir ▸ (show i x ∈ i.range from ⟨x,rfl⟩))
  have hgL : i g ∈ Ltilde Rg a := by
    have hg' : g ∈ pResidual 2 M := (h.relative_residual).symm ▸ hg
    exact mem_map_of_mem (stabilizer Rg a).subtype
      ((map_pResidual_le 2 j) (mem_map_of_mem j hg'))
  let C := centralizer ({g * v * g⁻¹} : Set M)
  let HC := H.map (MulAut.conj (i g)).toMonoidHom
  have hC : C.map i ≤ stabilizer Rg a ⊓
      centralizer (HC : Set (FreeAmalgam Rg)) := by
    rintro _ ⟨x,hx,rfl⟩
    refine ⟨hir ▸ (show i x ∈ i.range from ⟨x,rfl⟩),?_⟩
    rintro y ⟨w,hw,rfl⟩
    by_cases hw1 : w = 1
    · simp only [hw1,map_one,one_mul,mul_one]
    · have he : (⟨w,hw⟩ : H) = z := hunique _ (fun he => hw1 (congrArg Subtype.val he))
      have hwz : w = (z : FreeAmalgam Rg) := congrArg Subtype.val he
      rw [hwz,←hvz]
      change (i g * i v * (i g)⁻¹) * i x = i x * (i g * i v * (i g)⁻¹)
      simpa only [map_mul,map_inv] using congrArg i
        (mem_centralizer_singleton_iff.mp hx).symm
  refine ⟨i g,hgL,?_,?_⟩
  · apply le_antisymm (sup_le inf_le_left (hA.trans_eq hir))
    have hm := congrArg (Subgroup.map i) hgen
    rw [Subgroup.map_sup,hmA,←MonoidHom.range_eq_map,hir] at hm
    calc
      stabilizer Rg a = C.map i ⊔ A₁ := hm.symm
      _ ≤ _ := sup_le_sup_right hC _
  · intro hfix
    apply hmove
    intro x hx
    have hzH : i (g * v * g⁻¹) ∈ HC := by
      have hh := mem_map_of_mem (MulAut.conj (i g)).toMonoidHom z.property
      change (i g * (z : FreeAmalgam Rg) * (i g)⁻¹) ∈ HC at hh
      simpa only [←hvz,map_mul,map_inv] using hh
    apply hi
    simpa only [map_mul] using hfix hzH (i x) hx


include h e hz hk in
/-- A small forward slice gives a small critical pair, even if its original
critical pair has large image. Reverse the extended prefix and use the
strict reciprocal bound, then transport that actual pair to the base. -/
theorem borel_small_slice_critical_witness
    (hb : 2 < sourceDistance h) (u : Equiv.Perm (Fin 6))
    (hfull : (Rg).map (CubicAction.projection h e hz hk) =
      Theory.SpecificGroups.SymmetricSix.borel.map (MulAut.conj u).toMonoidHom)
    {a a' : Vertex Rg} (p : CriticalPath Rg (sourceGeometry h) a a')
    (hslice : (B Rg a ((sourceGeometry h).Z_normal _)).relIndex
      (U Rg (p.walk.getVert 2)) ≤ 2) :
    ∃ b, ∃ _q : CriticalPath Rg (sourceGeometry h) (alpha Rg) b,
      (Q Rg b).relIndex (Z Rg (alpha Rg)) = 2 := by
  obtain ⟨d,r,hr1,hr2⟩ := (borel_critical_paths h e hz hk u hfull p).2.2.1
  have hsmall : (Q Rg d).relIndex (Z Rg (p.walk.getVert 2)) < 4 := by
    by_contra! hlarge
    have hi := (large_critical_slices_gt_two h e hz hk hb r hlarge).2
    rw [hr2] at hi
    omega
  obtain ⟨g,hg⟩ := exists_mVertex_of_color Rg r.start_color
  have hbase : act Rg g⁻¹ (p.walk.getVert 2) = alpha Rg := by
    rw [hg,act_mVertex,mul_inv_cancel]
    rfl
  have hex : Nonempty (CriticalPath Rg (sourceGeometry h)
      (act Rg g⁻¹ (p.walk.getVert 2)) (act Rg g⁻¹ d)) := ⟨r.act g⁻¹⟩
  rw [hbase] at hex
  obtain ⟨q⟩ := hex
  have hsmall₀ : (Q Rg (act Rg g⁻¹ d)).relIndex (Z Rg (alpha Rg)) < 4 := by
    rw [←hbase,Q_act,Z_act,relIndex_map_map_of_injective _ _ (MulAut.conj g⁻¹⁻¹).injective]
    exact hsmall
  exact ⟨act Rg g⁻¹ d,q,(small_critical_indices h e hz hk q hsmall₀).1⟩

include h e hz hk in
private theorem borel_contains_point_core (u : S6)
    (hR : (Rg).map π = Theory.SpecificGroups.SymmetricSix.borel.map
      (MulAut.conj u).toMonoidHom) :
    ∃ v : S6, pointCore.map (MulAut.conj v).toMonoidHom ≤ (Rg).map π := by
  have hp : pointCore ≤ Theory.SpecificGroups.SymmetricSix.borel.map
      (MulAut.conj flagRelabel).toMonoidHom := by
    rw [Theory.SpecificGroups.SymmetricSix.borel,
      map_inf _ _ _ (MulAut.conj flagRelabel).injective,
      flagRelabel_duad]
    change pointCore ≤ H1 ⊓ H2.map (MulAut.conj flagRelabel).toMonoidHom
    rw [flagRelabel_syntheme]
    exact pointCore_le_flag
  refine ⟨u * flagRelabel⁻¹, ?_⟩
  rw [hR]
  rintro _ ⟨v,hv,rfl⟩
  obtain ⟨w,hw,he⟩ := hp hv
  refine ⟨w,hw,?_⟩
  rw [←he]
  change u*w*u⁻¹ = (u*flagRelabel⁻¹)*(flagRelabel*w*flagRelabel⁻¹)*(u*flagRelabel⁻¹)⁻¹
  group

include h e hz hk in
/-- Every small forward-slice line is central at its starting vertex in the
original Borel branch, including large critical images. -/
theorem borel_forward_line_central
    (hb : 2 < sourceDistance h) {a' : Vertex Rg}
    (p : CriticalPath Rg (sourceGeometry h) (alpha Rg) a')
    (u : S6) (hfull : (Rg).map π = Theory.SpecificGroups.SymmetricSix.borel.map (MulAut.conj u).toMonoidHom)
    (hslice : (B Rg (alpha Rg) ((sourceGeometry h).Z_normal _)).relIndex
      (U Rg (p.walk.getVert 2)) ≤ 2) :
    ⁅U Rg (p.walk.getVert 2),Q Rg (alpha Rg) ⊓ centralizer
      (U Rg (p.walk.getVert 2) ⊓ B Rg (alpha Rg)
        ((sourceGeometry h).Z_normal _) : Set (FreeAmalgam Rg))⁆ ≤
      centralizer (stabilizer Rg (alpha Rg) : Set (FreeAmalgam Rg)) := by
  by_cases hsmall : (Q Rg a').relIndex (Z Rg (alpha Rg)) < 4
  · exact small_forward_line_central h e hz hk hb p hsmall hslice
  have hlarge : 4 ≤ (Q Rg a').relIndex (Z Rg (alpha Rg)) := by omega
  obtain ⟨b,q,hq⟩ := borel_small_slice_critical_witness h e hz hk hb u hfull p hslice
  obtain ⟨A₁,hA₁U,hA₁n,hcontrol⟩ := large_critical_restricted_actor h e hz hk p hlarge
  have hA₁Z := hA₁U.trans (DistanceEight.U_le_Z Rg a')
  have hA₁G := hA₁Z.trans (critical_Z_le_stabilizer Rg (sourceGeometry h) (alpha Rg) rfl
    (sourceDistance_pos h) p.critical)
  let := (sourceGeometry h).Z_elementary (sourceDistance_pos h) a' p.end_color
  have hA₁two : IsPGroup 2 A₁ := (IsElementaryAbelian.isPGroup 2 (Z Rg a')).to_le hA₁Z
  let c := p.walk.getVert 2
  let t := p.walk.getVert 1
  let T := Q Rg (alpha Rg) ⊓ centralizer
    (U Rg c ⊓ B Rg (alpha Rg)
      ((sourceGeometry h).Z_normal _) : Set (FreeAmalgam Rg))
  let H := ⁅U Rg c,T⁆
  change H ≤ centralizer (stabilizer Rg (alpha Rg) : Set (FreeAmalgam Rg))
  by_contra hnon
  have hne : H ≠ ⊥ := by intro he; exact hnon (he ▸ bot_le)
  have hl : 2 < p.walk.length := p.length_eq_b ▸ hb
  have hat : Adjacent Rg (alpha Rg) t := by
    apply (cosetGraph_adj Rg _ _).mp
    simpa only [SimpleGraph.Walk.getVert_zero] using p.walk.adj_getVert_succ (i := 0) (by omega)
  have hct : Adjacent Rg c t := adjacent_symm Rg
    ((cosetGraph_adj Rg _ _).mp (p.walk.adj_getVert_succ (i := 1) (by omega)))
  have hline := selected_forward_kernel_line h e hz hk hb p hslice
  have hHZ : H ≤ Z Rg (alpha Rg) :=
    hline.2.trans (adjacent_Z_le Rg rfl hat)
  let := finite_Z Rg (alpha Rg)
  let : Finite H := Finite.of_injective (inclusion hHZ) (inclusion_injective _)
  have hcard : Nat.card H = 2 := by
    have hp := (one_lt_card_iff_ne_bot H).mpr hne
    have hh : Nat.card H ≤ 2 := hline.1
    omega
  have hUB : ¬ U Rg c ≤ B Rg (alpha Rg) ((sourceGeometry h).Z_normal _) := by
    intro hh
    apply hne
    apply commutator_eq_bot_iff_le_centralizer.mpr
    apply le_centralizer_iff.mp
    intro x hx y hy
    exact hx.2 y ⟨hy,hh hy⟩
  have hUV : U Rg c ≤ V Rg (alpha Rg) :=
    (DistanceEight.U_le_Z Rg c).trans
      (le_iSup_of_le c (le_iSup_of_le (by rw [SimpleGraph.dist_comm,p.dist_start (by omega)]) le_rfl))
  have hTN : stabilizer Rg (alpha Rg) ≤ normalizer (T : Set (FreeAmalgam Rg)) :=
    selected_forward_kernel_normalized (h := h) hb rfl hat hct
  obtain ⟨v,hv⟩ := borel_contains_point_core h e hz hk u hfull
  obtain ⟨g,hg,hgen,hmove⟩ := contained_point_seed_line_generator h e hz hk q (by omega)
    v hv rfl hat A₁ hA₁G hA₁two hA₁n H hline.2 hcard hnon
  have hgG := Ltilde_le_stabilizer (alpha Rg) hg
  let f := (MulAut.conj g).toMonoidHom
  let A := (U Rg c).map f
  let J := H.map f
  have hVm : (V Rg (alpha Rg)).map f = V Rg (alpha Rg) :=
    mem_normalizer_iff_map_conj_eq.mp (DistanceEight.V_normalized Rg _ hgG)
  have hBm : (B Rg (alpha Rg) ((sourceGeometry h).Z_normal _)).map f =
      B Rg (alpha Rg) ((sourceGeometry h).Z_normal _) :=
    mem_normalizer_iff_map_conj_eq.mp (Escape.Propagation.Rigidity.B_normalized hb _ rfl hgG)
  have hTm : T.map f = T := mem_normalizer_iff_map_conj_eq.mp (hTN hgG)
  have hZm : (Z Rg (alpha Rg)).map f = Z Rg (alpha Rg) :=
    mem_normalizer_iff_map_conj_eq.mp (Z_normalized Rg _ hgG)
  have hAV : A ≤ V Rg (alpha Rg) := hVm ▸ map_mono hUV
  have hAB : ¬ A ≤ B Rg (alpha Rg) ((sourceGeometry h).Z_normal _) := by
    intro hh
    apply hUB
    apply (map_le_map_iff_of_injective (f := f) (MulAut.conj g).injective).mp
    rwa [hBm]
  have hJZ : J ≤ Z Rg (alpha Rg) := hZm ▸ map_mono hHZ
  have hJcard : Nat.card J ≤ 2 := by
    rw [show Nat.card J = Nat.card H from card_map_of_injective (MulAut.conj g).injective,hcard]
  have hcomm : ⁅A,T⁆ ≤ J := by
    change ⁅(U Rg c).map f,T⁆ ≤ H.map f
    rw [show H = ⁅U Rg c,T⁆ from rfl,map_commutator,hTm]
  exact controlled_line_false_of_actor h e hz hb p A₁ hA₁G hA₁two hA₁n hcontrol A T J
    hAV hAB inf_le_left hTN hJZ hJcard
    (fun hh => hmove (hh.trans (centralizer_le hA₁Z))) hgen hcomm
    (selected_forward_kernel_contains_inner_layers (h := h) hb p)


end AlternatingSixReconstruction.Exceptional.OriginalSylow
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
