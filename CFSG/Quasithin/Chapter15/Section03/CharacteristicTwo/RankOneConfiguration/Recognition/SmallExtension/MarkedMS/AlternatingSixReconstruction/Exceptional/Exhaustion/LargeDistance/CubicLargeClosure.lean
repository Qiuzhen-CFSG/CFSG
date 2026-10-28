module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicLargeSlices
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicSliceShift
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicForwardClosure
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.FullSeed
import all Theory.SpecificGroups.SymmetricSix.BinaryFlags.PointOrbits

/-!
# Full-seed orbits and large-image forward lines

A vector in the entire cubic seed fixed by the point core has even
six-letter displacement coordinates. Two point-core involutions suffice:
each has a fixed letter, so a constant displacement must vanish, and
their fixed-vector equations pair all six coordinates. A noncentral such
vector therefore has a duad orbit, including its central attachment.
Its centralizer admits one component conjugate generating the local group
with any actor escaping the full cubic kernel; that actor moves the same
conjugate.

The literal incident-edge embeddings apply this calculation to the whole
forward commutator line. For a large critical image the controlled
restricted actor now replaces the transposition used in the small-image
proof. The line is central at the starting vertex. Normal generation
identifies the full selected span's kernel commutator with this line,
and the same residual conjugator gives a central line at the shifted
center for both critical image sizes. Above distance four the entire shifted
span fixes both inner layers and lies in the old endpoint two-core, with
the full old endpoint seed in the shifted center two-core.
Whole-core and literal C.1.32
applications use these statements on the original cubic graph.

The internal imports reuse only the six-coordinate definitions and normal
closure helpers in the existing proof split. No natural replacement graph
or action is identified with the exceptional graph. Both moving covers
and the odd covering kernel are retained.

The full point-core equality remains a hypothesis. Large-image shifted
orbit exclusion, radical-image identification, exact-four, R4/R6 and the
terminal exclusions, independent natural exhaustion, and both full
reconstruction outcomes remain required.

Source: Meierfrankenfeld--Stellmacher (1993), (3.3)(ii), pp.866--867,
and the forward-line centrality and shifted construction of (5.9),
pp.920--921.
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
namespace AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicFull
open Natural.Exhaustion.LargeDistance.SectionFive.SeedCoordinates
section Coordinates
variable {Y : Type*} [AddCommGroup Y] [Module (ZMod 2) Y]
  (ρ : Representation (ZMod 2) S6 Y)
  (j : (coreRepresentation (Fin 6)).IntertwiningMap ρ)
  (hj : ∀ i k : Fin 6, i ≠ k → j (pairVector i k) ≠ 0)

include hj in
private theorem coordinate_kernel_constant (v : core (Fin 6)) (hv : j v = 0) :
    ∀ i k, v.val i = v.val k := by
  intro i k
  by_contra hn
  have hik : i ≠ k := fun he => hn (he ▸ rfl)
  have he : j (displacement (Equiv.swap i k) v.val) = 0 := by
    change j (coreRepresentation (Fin 6) (Equiv.swap i k) v - v) = 0
    rw [map_sub, j.isIntertwining, hv, map_zero, sub_self]
  rw [displacement_swap, map_smul] at he
  have hbit : v.val i + v.val k = 1 :=
    (by decide : ∀ a b : ZMod 2, a ≠ b → a+b=1) _ _ hn
  rw [hbit,one_smul] at he
  exact hj i k hik he

include hj in
private theorem fixed_coordinates_of_fixed_letter
    (z : Y) (w : Full (Fin 6))
    (hw : ∀ g, ρ g z-z = j (displacement g w))
    (g : S6) (hg : ρ g z = z) (a : Fin 6) (ha : g a = a) :
    representation (Fin 6) g w = w := by
  have hz : j (displacement g w) = 0 := by rw [←hw, hg, sub_self]
  have hc := coordinate_kernel_constant ρ j hj _ hz
  have ha' : g.symm a = a := by
    apply g.injective
    rw [Equiv.apply_symm_apply,ha]
  have hzero : (displacement g w).val a = 0 := by
    change w (g.symm a)-w a=0
    rw [ha',sub_self]
  funext k
  exact sub_eq_zero.mp ((hc k a).trans hzero)

include hj in
private theorem point_fixed_coordinates_even
    (z : Y) (w : Full (Fin 6))
    (hw : ∀ g, ρ g z-z = j (displacement g w))
    (hfix : ∀ g ∈ pointCore, ρ g z = z) : w ∈ core (Fin 6) := by
  have hgen1 : swap01 * swap23 ∈ pointCore := by
    rw [pointCore_eq_closure]
    exact subset_closure (by simp)
  have hgen2 : swap45 ∈ pointCore := by
    rw [pointCore_eq_closure]
    exact subset_closure (by simp)
  have h1 := fixed_coordinates_of_fixed_letter ρ j hj z w hw
    (swap01 * swap23) (hfix _ hgen1) 4 (by decide)
  have h2 := fixed_coordinates_of_fixed_letter ρ j hj z w hw
    swap45 (hfix _ hgen2) 0 (by decide)
  have h01 := congrFun h1 0
  have h23 := congrFun h1 2
  have h45 := congrFun h2 4
  change w 1 = w 0 at h01
  change w 3 = w 2 at h23
  change w 5 = w 4 at h45
  change (∑ i, w i) = 0
  rw [Fin.sum_univ_six,h01,h23,h45]
  calc
    _ = (w 0+w 0)+(w 2+w 2)+(w 4+w 4) := by abel
    _ = 0 := by simp only [CharTwo.add_self_eq_zero]

private theorem coordinates_transport
    (z : Y) (w : Full (Fin 6))
    (hw : ∀ g, ρ g z-z = j (displacement g w)) (u : S6) :
    ∀ g, ρ g (ρ u z)-ρ u z =
      j (displacement g (representation (Fin 6) u w)) := by
  intro g
  have h1 := hw (g*u)
  have h2 := hw u
  rw [map_mul,Module.End.mul_apply] at h1
  have he : displacement (g*u) w-displacement u w =
      displacement g (representation (Fin 6) u w) := by
    apply Subtype.ext
    change (representation (Fin 6) (g*u) w-w) -
      (representation (Fin 6) u w-w) = _
    rw [map_mul,Module.End.mul_apply]
    change (representation (Fin 6) g (representation (Fin 6) u w)-w) -
      (representation (Fin 6) u w-w) =
      representation (Fin 6) g (representation (Fin 6) u w)-representation (Fin 6) u w
    abel
  calc
    _ = (ρ g (ρ u z)-z)-(ρ u z-z) := by abel
    _ = j (displacement (g*u) w)-j (displacement u w) := by rw [h1,h2]
    _ = _ := by rw [←map_sub,he]

include hj in
private theorem conjugate_point_fixed_coordinates_even
    (z : Y) (w : Full (Fin 6))
    (hw : ∀ g, ρ g z-z = j (displacement g w)) (u : S6)
    (hfix : ∀ g ∈ pointCore.map (MulAut.conj u).toMonoidHom, ρ g z = z) :
    w ∈ core (Fin 6) := by
  have hf (g : S6) (hg : g ∈ pointCore) : ρ g (ρ u⁻¹ z) = ρ u⁻¹ z := by
    have he := congrArg (ρ u⁻¹) (hfix _ (mem_map_of_mem (MulAut.conj u).toMonoidHom hg))
    change ρ u⁻¹ (ρ (u*g*u⁻¹) z) = ρ u⁻¹ z at he
    simpa only [←Module.End.mul_apply,←map_mul,inv_mul_cancel_left,mul_assoc] using he
  have hw' := point_fixed_coordinates_even ρ j hj (ρ u⁻¹ z)
    (representation (Fin 6) u⁻¹ w) (coordinates_transport ρ j z w hw u⁻¹) hf
  change augmentation (Fin 6) (representation (Fin 6) u⁻¹ w) = 0 at hw'
  rwa [augmentation_permute] at hw'

include hj in
private theorem coordinate_duads_injective :
    Function.Injective (fun d => j (coverDuad d)) := by
  intro d k he
  change j (coverDuad d) = j (coverDuad k) at he
  have hz : j (coverDuad d-coverDuad k) = 0 := by rw [map_sub,he,sub_self]
  have hc := coordinate_kernel_constant ρ j hj _ hz
  apply naturalDuad_injective
  apply Subtype.ext
  apply (Submodule.Quotient.eq _).mpr
  apply (mem_constants_iff _).mpr
  exact ⟨(coverDuad d-coverDuad k).val 0,fun i => hc i 0⟩

include hj in
private theorem coordinates_point_orbit
    (z : Y) (w : Full (Fin 6))
    (hw : ∀ g, ρ g z-z = j (displacement g w)) (u : S6)
    (hfix : ∀ g ∈ pointCore.map (MulAut.conj u).toMonoidHom, ρ g z = z)
    (hz : ¬ ∀ g, ρ g z = z) :
    ∃ f : Duad → Y, Function.Injective f ∧
      (∀ g d, ρ g (f d) = f (g • d)) ∧ ∃ d, f d = z := by
  let v : core (Fin 6) := ⟨w,conjugate_point_fixed_coordinates_even ρ j hj z w hw u hfix⟩
  let c := z-j v
  have hc (g : S6) : ρ g c = c := by
    have he := hw g
    change ρ g z-z = j (coreRepresentation (Fin 6) g v-v) at he
    rw [map_sub,j.isIntertwining] at he
    dsimp only [c]
    rw [map_sub]
    exact sub_eq_sub_iff_sub_eq_sub.mp he
  have hsum : c+j v = z := sub_add_cancel _ _
  have hfamily (d : Y) (hd : ∀ g, ρ g d = d) :
      Function.Injective (fun k => d+j (coverDuad k)) ∧
        (∀ g k, ρ g (d+j (coverDuad k)) = d+j (coverDuad (g • k))) := by
    refine ⟨fun k l hh => coordinate_duads_injective ρ j hj (add_left_cancel hh),?_⟩
    intro g k
    rw [map_add,hd,←j.isIntertwining,coverDuad_map]
  rcases cover_cases v with hv | hv | ⟨d,hv | hv⟩
  · exfalso
    apply hz
    intro g
    rw [hv,map_zero,add_zero] at hsum
    rw [←hsum]
    exact hc g
  · exfalso
    apply hz
    intro g
    rw [←hsum,map_add,hc,←j.isIntertwining,hv,coverOne_map]
  · refine ⟨fun k => c+j (coverDuad k),(hfamily c hc).1,(hfamily c hc).2,d,?_⟩
    rwa [hv] at hsum
  · let c' := c+j coverOne
    have hc' (g : S6) : ρ g c' = c' := by
      dsimp only [c']
      rw [map_add,hc,←j.isIntertwining,coverOne_map]
    refine ⟨fun k => c'+j (coverDuad k),(hfamily c' hc').1,(hfamily c' hc').2,d,?_⟩
    rw [hv,map_add,←add_assoc] at hsum
    exact hsum

end Coordinates

universe u
variable {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
  (h : SmallMSPair KnownSimple.IsKnownSimple L R) (e : CentralMarking L)
  (hz : Nat.card (center (L ⧸ pCore 2 L)) = 3)
  (hk : layerKernel L R = extensionKernel h)
local notation "M" => (L ⊔ R : Subgroup G)
local notation "π" => CubicAction.projection h e hz hk
local notation "Rg" => edge L R

include h e hz hk in
private theorem fixed_seed_point_orbit
    {b : Vertex Rg} (q : CriticalPath Rg (sourceGeometry h) (alpha Rg) b)
    (hsmall : (Q Rg b).relIndex (Z Rg (alpha Rg)) < 4)
    (u : S6) (hfull : (Rg).map π = pointCore.map (MulAut.conj u).toMonoidHom)
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
    rw [←hfull] at hg
    obtain ⟨r,hr,rfl⟩ := hg
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
theorem fixed_seed_conjugate_generator
    {b : Vertex Rg} (q : CriticalPath Rg (sourceGeometry h) (alpha Rg) b)
    (hsmall : (Q Rg b).relIndex (Z Rg (alpha Rg)) < 4)
    (u : S6) (hfull : (Rg).map π = pointCore.map (MulAut.conj u).toMonoidHom)
    (v : radiusSeed L R)
    (hv : (v : M) ∉ center M)
    (hvR : (v : M) ∈ centralizer (Rg : Set M))
    (A : Subgroup M) (hA : ¬ A ≤ extensionKernel h) :
    ∃ g ∈ L.subgroupOf (L ⊔ R),
      centralizer ({g * (v : M) * g⁻¹} : Set M) ⊔ A = ⊤ ∧
      g * (v : M) * g⁻¹ ∉ centralizer (A : Set M) := by
  let := seed_elementary (h := h)
  obtain ⟨f,hf,heq,j,hj⟩ := fixed_seed_point_orbit h e hz hk q hsmall u hfull v hv hvR
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
theorem fixed_seed_line_generator_of_actor
    {b : Vertex Rg} (q : CriticalPath Rg (sourceGeometry h) (alpha Rg) b)
    (hsmall : (Q Rg b).relIndex (Z Rg (alpha Rg)) < 4)
    (u : S6) (hfull : (Rg).map π = pointCore.map (MulAut.conj u).toMonoidHom)
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
    fixed_seed_conjugate_generator h e hz hk q hsmall u hfull ⟨v,hv⟩ hvnot hvR A hnA
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



include h e hz in
private theorem controlled_line_false_of_actor
    (hb : 2 < sourceDistance h) {a' : Vertex Rg}
    (p : CriticalPath Rg (sourceGeometry h) (alpha Rg) a')
    (A₁ : Subgroup (FreeAmalgam Rg))
    (hA₁G : A₁ ≤ stabilizer Rg (alpha Rg)) (hA₁two : IsPGroup 2 A₁)
    (hA₁n : ¬ A₁ ≤ Q Rg (alpha Rg))
    (hcontrol : ∀ Y : Subgroup (FreeAmalgam Rg), Y ≤ Q Rg (alpha Rg) →
      Y ≤ stabilizer Rg a' → ⁅Y,A₁⁆ ≤ Z Rg (alpha Rg))
    (A T₀ H₁ : Subgroup (FreeAmalgam Rg))
    (hAV : A ≤ V Rg (alpha Rg)) (hAB : ¬ A ≤ B Rg (alpha Rg) ((sourceGeometry h).Z_normal _))
    (hTQ : T₀ ≤ Q Rg (alpha Rg))
    (hTN : stabilizer Rg (alpha Rg) ≤ normalizer (T₀ : Set (FreeAmalgam Rg)))
    (hHZ : H₁ ≤ Z Rg (alpha Rg)) (hcard : Nat.card H₁ ≤ 2)
    (hHe : ¬ H₁ ≤ centralizer (Z Rg a' : Set (FreeAmalgam Rg)))
    (hgen : (stabilizer Rg (alpha Rg) ⊓ centralizer (H₁ : Set (FreeAmalgam Rg))) ⊔
      A₁ = stabilizer Rg (alpha Rg))
    (hcomm : ⁅A,T₀⁆ ≤ H₁)
    (hinner : Z Rg (p.walk.getVert (p.walk.length-2)) ⊔ (Z Rg a' ⊓ Q Rg (alpha Rg)) ≤ T₀) :
    False := by
  have hb2 : 2 < sourceDistance h := by omega
  let P := stabilizer Rg (alpha Rg) ⊓ centralizer (H₁ : Set (FreeAmalgam Rg))
  have hVQ := (sourceGeometry h).V_le_Q hb2 (alpha Rg) rfl
  have hVG := (sourceGeometry h).V_local (alpha Rg) rfl hb2
  have hZQ : Z Rg (alpha Rg) ≤ centralizer (Q Rg (alpha Rg) : Set (FreeAmalgam Rg)) :=
    commutator_eq_bot_iff_le_centralizer.mp (Z_centralizes_Q Rg (alpha Rg) rfl)
  have hQH : Q Rg (alpha Rg) ≤ centralizer (H₁ : Set (FreeAmalgam Rg)) :=
    (le_centralizer_iff.mp hZQ).trans (centralizer_le hHZ)
  have hZaV : Z Rg (alpha Rg) ≤ V Rg (alpha Rg) := by
    exact le_iSup_of_le (alpha Rg) (le_iSup_of_le (by simp :
      (cosetGraph Rg).dist (alpha Rg) (alpha Rg) ≤ 2) le_rfl)
  have hAZ : ⁅Z Rg (alpha Rg) ⊔ A,T₀⁆ ≤ H₁ := by
    rw [commutator_sup_centralized_left (Z Rg (alpha Rg)) A T₀
      ((hAV.trans hVG).trans (Z_normalized Rg (alpha Rg)))
      (hZQ.trans (centralizer_le hTQ)) ((hAV.trans hVG).trans hTN)]
    exact hcomm
  have hAP : Z Rg (alpha Rg) ⊔ A ≤ P :=
    le_inf ((sup_le hZaV hAV).trans hVG)
      ((sup_le hZaV hAV).trans (hVQ.trans hQH))
  have hTP : T₀ ≤ P := le_inf (hTQ.trans (fun _ hx => hx.1)) (hTQ.trans hQH)
  have hHP : H₁ ≤ P := le_inf (hHZ.trans (Z_le_stabilizer Rg (alpha Rg)))
    (hHZ.trans (hZaV.trans (hVQ.trans hQH)))
  obtain ⟨Y,hAY,hYV,hPY,hYT⟩ := exists_normal_span_with_commutator
    P (Z Rg (alpha Rg) ⊔ A) T₀ H₁ (V Rg (alpha Rg)) hAP (sup_le hZaV hAV) hTP hHP
    (inf_le_left.trans hTN) (inf_le_right.trans (centralizer_le_normalizer H₁))
    (inf_le_left.trans (DistanceEight.V_normalized Rg (alpha Rg))) hAZ
  have hc : color Rg (p.walk.getVert (p.walk.length-2)) = false := by
    apply (p.vertex_color (Nat.sub_le _ _)).mpr
    have he := (sourceGeometry h).even (alpha Rg) rfl
    change Even (sourceDistance h) at he
    rw [Nat.even_iff] at he ⊢
    have hl : p.walk.length = sourceDistance h := p.length_eq_b
    omega
  have hQeC : Q Rg a' ≤ centralizer (Z Rg a' : Set (FreeAmalgam Rg)) :=
    le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp
      (Z_centralizes_Q Rg a' p.end_color))
  have hpreQe : Z Rg (p.walk.getVert (p.walk.length-2)) ≤ Q Rg a' := by
    apply Z_le_Q_of_dist_lt Rg _ ((sourceGeometry h).exists_critical _ hc)
    rw [(sourceGeometry h).distance_constant _ hc,p.dist_end]
    have hl : p.walk.length = sourceDistance h := p.length_eq_b
    change p.walk.length-(p.walk.length-2) < sourceDistance h
    omega
  have hkill (D : Subgroup (FreeAmalgam Rg)) (hDH : D ≤ H₁)
      (hDe : D ≤ centralizer (Z Rg a' : Set (FreeAmalgam Rg))) : D = ⊥ := by
    by_contra hn
    let := finite_Z Rg (alpha Rg)
    let : Finite H₁ := Finite.of_injective (inclusion hHZ) (inclusion_injective _)
    let : Finite D := Finite.of_injective (inclusion hDH) (inclusion_injective _)
    have hpos := (one_lt_card_iff_ne_bot D).mpr hn
    have he : D = H₁ := eq_of_le_of_card_ge hDH (by omega)
    exact hHe (he ▸ hDe)
  have hYpre : ⁅Y,Z Rg (p.walk.getVert (p.walk.length-2))⁆ = ⊥ := by
    apply hkill _ ((commutator_mono le_rfl (le_sup_left.trans hinner)).trans hYT)
    exact (le_normalizer_iff_commutator_le_right.mp
      ((hYV.trans (radius_le_predecessor_stabilizer (h := h) hb p)).trans
        (Z_normalized Rg _))).trans (hpreQe.trans hQeC)
  have hYpreC := commutator_eq_bot_iff_le_centralizer.mp hYpre
  have hYpreQ : Y ≤ Q Rg (p.walk.getVert (p.walk.length-2)) := by
    apply two_subgroup_seed_centralizer_le_core h e hz hc Y
      ((Q_isPGroup Rg h.relative_radical.isPGroup h.relative_radical.twoCore_le
        (alpha Rg) rfl).to_le (hYV.trans hVQ))
    exact le_inf (hYV.trans (radius_le_predecessor_stabilizer (h := h) hb p)) hYpreC
  have hYeG : Y ≤ stabilizer Rg a' := by
    have hl : 2 < p.walk.length := p.length_eq_b ▸ hb
    let t := p.walk.getVert (p.walk.length-1)
    have hat : Adjacent Rg a' t := by
      have hh := p.walk.adj_getVert_succ (i := p.walk.length-1) (by omega)
      rw [show p.walk.length-1+1 = p.walk.length by omega,p.walk.getVert_length] at hh
      exact adjacent_symm Rg ((cosetGraph_adj Rg _ _).mp hh)
    have hct : Adjacent Rg (p.walk.getVert (p.walk.length-2)) t := by
      have hh := p.walk.adj_getVert_succ (i := p.walk.length-2) (by omega)
      rw [show p.walk.length-2+1 = p.walk.length-1 by omega] at hh
      exact (cosetGraph_adj Rg _ _).mp hh
    have ht : color Rg t = true := by
      have hh := adjacent_color_ne Rg hat
      rw [p.end_color] at hh
      cases he : color Rg t <;> simp_all
    exact (hYpreQ.trans (Q_le_adjacent_h Rg ht hct)).trans
      (fun _ hx => hx.2 _ (adjacent_symm Rg hat))
  have hYe : ⁅Y,A₁⁆ ≤ Z Rg (alpha Rg) :=
    hcontrol Y (hYV.trans hVQ) hYeG
  have hZeY : A₁ ≤ normalizer (Y : Set (FreeAmalgam Rg)) :=
    le_normalizer_iff_commutator_le_left.mpr (hYe.trans (le_sup_left.trans hAY))
  have hGY : stabilizer Rg (alpha Rg) ≤ normalizer (Y : Set (FreeAmalgam Rg)) := by
    rw [←hgen]
    exact sup_le hPY hZeY
  exact hAB (le_sup_right.trans (hAY.trans
    (normalized_radius_le_slice_of_controlled_actor h e hz hb2 rfl Y A₁
      hYV hGY hA₁G hA₁two hA₁n hYe)))


include h e hz hk in
/-- Every small forward-slice line is central at its starting vertex in the
full point-core branch, including large critical images. -/
theorem full_point_forward_line_central
    (hb : 2 < sourceDistance h) {a' : Vertex Rg}
    (p : CriticalPath Rg (sourceGeometry h) (alpha Rg) a')
    (u : S6) (hfull : (Rg).map π = pointCore.map (MulAut.conj u).toMonoidHom)
    (hslice : (B Rg (alpha Rg) ((sourceGeometry h).Z_normal _)).relIndex
      (U Rg (p.walk.getVert 2)) ≤ 2) :
    ⁅U Rg (p.walk.getVert 2),Q Rg (alpha Rg) ⊓ centralizer
      (U Rg (p.walk.getVert 2) ⊓ B Rg (alpha Rg)
        ((sourceGeometry h).Z_normal _) : Set (FreeAmalgam Rg))⁆ ≤
      centralizer (stabilizer Rg (alpha Rg) : Set (FreeAmalgam Rg)) := by
  by_cases hsmall : (Q Rg a').relIndex (Z Rg (alpha Rg)) < 4
  · exact small_forward_line_central h e hz hk hb p hsmall hslice
  have hlarge : 4 ≤ (Q Rg a').relIndex (Z Rg (alpha Rg)) := by omega
  obtain ⟨b,q,hq⟩ := full_point_small_slice_critical_witness h e hz hk hb u hfull p hslice
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
  obtain ⟨g,hg,hgen,hmove⟩ := fixed_seed_line_generator_of_actor h e hz hk q (by omega)
    u hfull rfl hat A₁ hA₁G hA₁two hA₁n H hline.2 hcard hnon
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


include h e hz hk in
/-- Normal generation identifies the entire selected span commutator with
the forward line for both critical image sizes. -/
theorem full_point_selected_span_forward_commutator
    (hb : 2 < sourceDistance h) {a' : Vertex Rg}
    (p : CriticalPath Rg (sourceGeometry h) (alpha Rg) a')
    (u : S6) (hfull : (Rg).map π = pointCore.map (MulAut.conj u).toMonoidHom)
    (hslice : (B Rg (alpha Rg) ((sourceGeometry h).Z_normal _)).relIndex
      (U Rg (p.walk.getVert 2)) ≤ 2) :
    let P := localZSpan Rg (p.walk.getVert 2) (alpha Rg)
    let T := Q Rg (alpha Rg) ⊓ centralizer
      (U Rg (p.walk.getVert 2) ⊓ B Rg (alpha Rg)
        ((sourceGeometry h).Z_normal _) : Set (FreeAmalgam Rg))
    let H := ⁅U Rg (p.walk.getVert 2),Q Rg (alpha Rg) ⊓ centralizer
      (U Rg (p.walk.getVert 2) ⊓ B Rg (alpha Rg)
        ((sourceGeometry h).Z_normal _) : Set (FreeAmalgam Rg))⁆
    ⁅P,T⁆ = H ∧ ⁅P,P⁆ ≤ H ∧
      H ≤ centralizer (stabilizer Rg (alpha Rg) : Set (FreeAmalgam Rg)) := by
  let c := p.walk.getVert 2
  let t := p.walk.getVert 1
  let T := Q Rg (alpha Rg) ⊓ centralizer
    (U Rg c ⊓ B Rg (alpha Rg)
      ((sourceGeometry h).Z_normal _) : Set (FreeAmalgam Rg))
  let H := ⁅U Rg c,T⁆
  let P := localZSpan Rg c (alpha Rg)
  have hfixed : H ≤ centralizer (stabilizer Rg (alpha Rg) : Set (FreeAmalgam Rg)) :=
    full_point_forward_line_central h e hz hk hb p u hfull hslice
  have hHN : stabilizer Rg (alpha Rg) ≤ normalizer (H : Set (FreeAmalgam Rg)) :=
    (le_centralizer_iff.mp hfixed).trans (Subgroup.centralizer_le_normalizer _)
  have hl : 2 < p.walk.length := p.length_eq_b ▸ hb
  have hcol : color Rg c = false := (p.vertex_color (by omega)).mpr (by decide)
  have hat : Adjacent Rg (alpha Rg) t := by
    apply (cosetGraph_adj Rg _ _).mp
    simpa only [SimpleGraph.Walk.getVert_zero] using p.walk.adj_getVert_succ (i := 0) (by omega)
  have hct : Adjacent Rg c t := adjacent_symm Rg
    ((cosetGraph_adj Rg _ _).mp (p.walk.adj_getVert_succ (i := 1) (by omega)))
  have ht : color Rg t = true := by
    have hh := adjacent_color_ne Rg hat
    change false ≠ color Rg t at hh
    cases he : color Rg t <;> simp_all
  have hTQt : T ≤ Q Rg t := inf_le_left.trans (Q_le_adjacent_h Rg ht hat)
  have hseed : Z Rg t ≤ centralizer (T : Set (FreeAmalgam Rg)) := by
    intro z hz x hx
    rw [Z,if_neg (by simp [ht])] at hz
    exact (mem_omegaCenter_iff.mp hz).2.2 x (hTQt hx)
  have hTN : stabilizer Rg (alpha Rg) ≤ normalizer (T : Set (FreeAmalgam Rg)) :=
    selected_forward_kernel_normalized (h := h) hb rfl hat hct
  have hZcG : Z Rg c ≤ stabilizer Rg (alpha Rg) :=
    ((Z_le_localZSpan Rg c (alpha Rg)).trans (localZSpan_le_V Rg (by
      rw [SimpleGraph.dist_comm,p.dist_start (by omega)]))).trans
      ((sourceGeometry h).V_local _ rfl hb)
  have hZc : ⁅Z Rg c,T⁆ ≤ H := by
    rw [vertex_seed_eq_moving_sup_edge h e hz hcol hct]
    apply commutator_sup_le_of_relative_normal (stabilizer Rg (alpha Rg))
      _ _ T _ hHN ((DistanceEight.U_le_Z Rg c).trans hZcG)
      ((adjacent_Z_le Rg rfl hat).trans (Z_le_stabilizer Rg _)) le_rfl
    exact (commutator_eq_bot_iff_le_centralizer.mpr hseed).le.trans bot_le
  have hPT : ⁅P,T⁆ ≤ H := by
    dsimp only [P]
    rw [localZSpan_eq_conjugates]
    apply commutator_iSup_le_of_relative_normal (stabilizer Rg (alpha Rg)) T _ _ hHN
    · intro g
      have hgmap : (stabilizer Rg (alpha Rg)).map
          (MulAut.conj (g : FreeAmalgam Rg)⁻¹).toMonoidHom = stabilizer Rg (alpha Rg) :=
        mem_normalizer_iff_map_conj_eq.mp ((stabilizer Rg (alpha Rg)).le_normalizer
          ((stabilizer Rg (alpha Rg)).inv_mem g.property))
      exact (map_mono hZcG).trans_eq hgmap
    · intro g
      have hm := map_mono (f := (MulAut.conj (g : FreeAmalgam Rg)⁻¹).toMonoidHom) hZc
      have hTm : T.map (MulAut.conj (g : FreeAmalgam Rg)⁻¹).toMonoidHom = T :=
        mem_normalizer_iff_map_conj_eq.mp (hTN ((stabilizer Rg (alpha Rg)).inv_mem g.property))
      have hHm : H.map (MulAut.conj (g : FreeAmalgam Rg)⁻¹).toMonoidHom = H :=
        mem_normalizer_iff_map_conj_eq.mp (hHN ((stabilizer Rg (alpha Rg)).inv_mem g.property))
      rwa [map_commutator,hTm,hHm] at hm
  have hPP : ⁅P,P⁆ ≤ H :=
    (commutator_mono le_rfl (selected_span_le_forward_kernel (h := h) hb p)).trans hPT
  exact ⟨le_antisymm hPT (commutator_mono
    ((DistanceEight.U_le_Z Rg c).trans (Z_le_localZSpan Rg _ _)) le_rfl),hPP,hfixed⟩



namespace SmallSliceShift
variable {h} {a' : Vertex (edge L R)}
  {p : CriticalPath (edge L R) (sourceGeometry h) (alpha (edge L R)) a'}
  (s : SmallSliceShift h p)

include e hz hk in
/-- The full point-core argument transports the span commutator without
a small-critical-image assumption. -/
theorem full_point_span_commutator
    (hb : 2 < sourceDistance h) (u : S6)
    (hfull : (Rg).map π = pointCore.map (MulAut.conj u).toMonoidHom)
    (hslice : (B Rg (alpha Rg) ((sourceGeometry h).Z_normal _)).relIndex
      (U Rg (p.walk.getVert 2)) ≤ 2) : ⁅s.span,s.kernel⁆ = s.line := by
  have hh := congrArg (Subgroup.map (MulAut.conj s.conjugator).toMonoidHom)
    (full_point_selected_span_forward_commutator h e hz hk hb p u hfull hslice).1
  rw [map_commutator,←s.span_map] at hh
  exact hh

include e hz hk in
/-- The shifted line has order two and is central at its own center
for both critical image sizes. -/
theorem full_point_line_facts
    (hb : 2 < sourceDistance h) (u : S6)
    (hfull : (Rg).map π = pointCore.map (MulAut.conj u).toMonoidHom)
    (hslice : (B Rg (alpha Rg) ((sourceGeometry h).Z_normal _)).relIndex
      (U Rg (p.walk.getVert 2)) ≤ 2) :
    Nat.card s.line = 2 ∧
      s.line ≤ centralizer (stabilizer Rg s.centerVertex : Set (FreeAmalgam Rg)) := by
  have hel := full_point_critical_forward_eligible h e hz hk hb u hfull p
  have hh := forward_slice_noncentral_line h e hz hk hb p hslice hel
  refine ⟨(card_map_of_injective (MulAut.conj s.conjugator).injective).trans hh.1,?_⟩
  have hm := map_mono (f := (MulAut.conj s.conjugator).toMonoidHom)
    (full_point_forward_line_central h e hz hk hb p u hfull hslice)
  rw [Theory.GroupTheory.map_centralizer_equiv,
    show (MulAut.conj s.conjugator : FreeAmalgam Rg → FreeAmalgam Rg) =
      (MulAut.conj s.conjugator).toMonoidHom from rfl,←Subgroup.coe_map] at hm
  have he := stabilizer_act Rg s.conjugator⁻¹ (alpha Rg)
  rw [inv_inv] at he
  rwa [←he] at hm

include e hz hk in
/-- The shifted span fixes the predecessor seed and full reverse kernel,
with its predecessor-core placement retained. -/
theorem full_point_inner_control (hb : 4 < sourceDistance h)
    (u : S6) (hfull : (Rg).map π = pointCore.map (MulAut.conj u).toMonoidHom)
    (hslice : (B Rg (alpha Rg) ((sourceGeometry h).Z_normal _)).relIndex
      (U Rg (p.walk.getVert 2)) ≤ 2)
:
    s.span ≤ Q Rg (p.walk.getVert (p.walk.length-2)) ∧
      s.span ≤ stabilizer Rg a' ∧
      ⁅s.span,Z Rg (p.walk.getVert (p.walk.length-2)) ⊔ (Z Rg a' ⊓ Q Rg s.centerVertex)⁆ = ⊥ := by
  have hcard := (s.full_point_line_facts e hz hk (by omega) u hfull hslice).1
  have hcomm := s.full_point_span_commutator e hz hk (by omega) u hfull hslice
  have hinner := s.inner_le_kernel hb
  have hkill (D : Subgroup (FreeAmalgam Rg)) (hD : D ≤ s.line)
      (hDZ : D ≤ centralizer (Z Rg s.endpoint : Set (FreeAmalgam Rg))) : D = ⊥ := by
    by_contra hn
    have hfinite : Finite s.line := Nat.finite_of_card_ne_zero (by omega)
    let := hfinite
    let : Finite D := Finite.of_injective (inclusion hD) (inclusion_injective _)
    have hp := (one_lt_card_iff_ne_bot D).mpr hn
    have he : D = s.line := eq_of_le_of_card_ge hD (by omega)
    apply s.moves
    change s.line ≤ _
    rwa [he] at hDZ
  have hpre : ⁅s.span,Z Rg (p.walk.getVert (p.walk.length-2))⁆ = ⊥ := by
    apply hkill _ ((commutator_mono le_rfl (le_sup_left.trans hinner)).trans_eq hcomm)
    exact (le_normalizer_iff_commutator_le_right.mp
      ((s.span_le_predecessor_stabilizer hb).trans (Z_normalized Rg _))).trans
        (le_sup_left.trans (s.inner_seed_centralizes_endpoint hb))
  have hpreQ : s.span ≤ Q Rg (p.walk.getVert (p.walk.length-2)) := by
    apply two_subgroup_seed_centralizer_le_core h e hz (predecessor_color (h := h) (p := p)) s.span
      ((Q_isPGroup Rg h.relative_radical.isPGroup h.relative_radical.twoCore_le
        s.centerVertex s.center_color).to_le (s.span_le_core (by omega)))
    exact le_inf (s.span_le_predecessor_stabilizer hb) (commutator_eq_bot_iff_le_centralizer.mp hpre)
  have hGe : s.span ≤ stabilizer Rg a' := by
    have hl : 4 < p.walk.length := p.length_eq_b ▸ hb
    let t := p.walk.getVert (p.walk.length-1)
    have hta : Adjacent Rg a' t := by
      have hh := p.walk.adj_getVert_succ (i := p.walk.length-1) (by omega)
      rw [show p.walk.length-1+1=p.walk.length by omega,p.walk.getVert_length] at hh
      exact adjacent_symm Rg ((cosetGraph_adj Rg _ _).mp hh)
    have hpt : Adjacent Rg (p.walk.getVert (p.walk.length-2)) t := by
      have hh := p.walk.adj_getVert_succ (i := p.walk.length-2) (by omega)
      rw [show p.walk.length-2+1=p.walk.length-1 by omega] at hh
      exact (cosetGraph_adj Rg _ _).mp hh
    have ht : color Rg t = true := by
      have hh := adjacent_color_ne Rg hta
      rw [p.end_color] at hh
      cases he : color Rg t <;> simp_all
    exact (hpreQ.trans (Q_le_adjacent_h Rg ht hpt)).trans
      (fun _ hx => hx.2 _ (adjacent_symm Rg hta))
  have hK : ⁅s.span,Z Rg a' ⊓ Q Rg s.centerVertex⁆ = ⊥ := by
    apply hkill _ ((commutator_mono le_rfl (le_sup_right.trans hinner)).trans_eq hcomm)
    exact ((commutator_mono le_rfl inf_le_left).trans
      (le_normalizer_iff_commutator_le_right.mp (hGe.trans (Z_normalized Rg a')))).trans
        (le_sup_right.trans (s.inner_seed_centralizes_endpoint hb))
  refine ⟨hpreQ,hGe,commutator_eq_bot_iff_le_centralizer.mpr ?_⟩
  apply le_centralizer_iff.mpr
  exact sup_le (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hpre))
    (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hK))

include e hz hk in
/-- The shifted center is either critical with the old endpoint, or the
entire shifted span lies in that endpoint's two-core. -/
theorem full_point_old_endpoint_alternative (hb : 4 < sourceDistance h)
    (u : S6) (hfull : (Rg).map π = pointCore.map (MulAut.conj u).toMonoidHom)
    (hslice : (B Rg (alpha Rg) ((sourceGeometry h).Z_normal _)).relIndex
      (U Rg (p.walk.getVert 2)) ≤ 2)
:
    CriticalPair Rg s.centerVertex a' ((sourceGeometry h).exists_critical _ s.center_color) ∨
      (Z Rg a' ≤ Q Rg s.centerVertex ∧ s.span ≤ Q Rg a') := by
  have hi := s.full_point_inner_control e hz hk hb u hfull hslice
  by_cases he : Z Rg a' ≤ Q Rg s.centerVertex
  · refine Or.inr ⟨he,?_⟩
    apply two_subgroup_seed_centralizer_le_core h e hz p.end_color s.span
      ((Q_isPGroup Rg h.relative_radical.isPGroup h.relative_radical.twoCore_le
        s.centerVertex s.center_color).to_le (s.span_le_core (by omega)))
    refine le_inf hi.2.1 ?_
    apply commutator_eq_bot_iff_le_centralizer.mp
    apply le_bot_iff.mp
    apply (commutator_mono le_rfl (show Z Rg a' ≤
      Z Rg (p.walk.getVert (p.walk.length-2)) ⊔ (Z Rg a' ⊓ Q Rg s.centerVertex) from
        (le_inf le_rfl he).trans le_sup_right)).trans_eq hi.2.2
  · have hd : (cosetGraph Rg).dist a' s.centerVertex ≤ sourceDistance h := by
      have hh := (cosetGraph_connected Rg).dist_triangle (u := s.centerVertex)
        (v := p.walk.getVert 2) (w := a')
      rw [s.center_distance (by omega),p.dist_end] at hh
      rw [SimpleGraph.dist_comm]
      have hl : p.walk.length = sourceDistance h := p.length_eq_b
      omega
    have hlo := criticalDistance_le Rg a' ((sourceGeometry h).exists_critical _ p.end_color) he
    have hc : CriticalPair Rg a' s.centerVertex ((sourceGeometry h).exists_critical _ p.end_color) := by
      refine ⟨?_,he⟩
      rw [(sourceGeometry h).distance_constant _ p.end_color] at hlo ⊢
      exact le_antisymm hd hlo
    exact Or.inl (critical_reverse Rg (sourceGeometry h) (sourceEdgeCentralizer h e)
      a' p.end_color (by
        rw [(sourceGeometry h).distance_constant _ p.end_color]
        exact sourceDistance_pos h) s.centerVertex s.center_color hc)
include e hz hk in
theorem full_point_not_critical_old_endpoint (hb : 4 < sourceDistance h)
    (u : S6) (hfull : (Rg).map π = pointCore.map (MulAut.conj u).toMonoidHom)
    (hslice : (B Rg (alpha Rg) ((sourceGeometry h).Z_normal _)).relIndex
      (U Rg (p.walk.getVert 2)) ≤ 2)
    (heligible : ¬ U Rg (p.walk.getVert 2) ≤ B Rg (alpha Rg) ((sourceGeometry h).Z_normal _)) :
    ¬ CriticalPair Rg s.centerVertex a' ((sourceGeometry h).exists_critical _ s.center_color) := by
  intro hc
  let q : CriticalPath Rg (sourceGeometry h) s.centerVertex a' :=
    CriticalPath.ofPair s.center_color hc
  have hi := s.full_point_inner_control e hz hk hb u hfull hslice
  have hDV : s.span ≤ V Rg s.centerVertex := by
    apply localZSpan_le_V
    rw [SimpleGraph.dist_comm]
    change (cosetGraph Rg).dist (act Rg s.conjugator⁻¹ (alpha Rg)) (p.walk.getVert 2) ≤ 2
    rw [←s.fixes_second,dist_act]
    rw [p.dist_start (by have hl : p.walk.length = sourceDistance h := p.length_eq_b; omega)]
  have hfix : s.span ≤ centralizer (Z Rg a' ⊓ Q Rg s.centerVertex : Set (FreeAmalgam Rg)) := by
    intro x hx z hz
    have hz' : z ∈ (Z Rg (p.walk.getVert (p.walk.length-2)) ⊔
        (Z Rg a' ⊓ Q Rg s.centerVertex) : Subgroup (FreeAmalgam Rg)) :=
      Subgroup.mem_sup_right hz
    exact (commutator_eq_bot_iff_le_centralizer.mp hi.2.2) hx z hz'
  exact s.span_not_le_slice (by omega) heligible
    (critical_kernel_normal_radius_le_slice h e hz hk (by omega) q s.span hDV
      (localZSpan_normalized Rg _ _) hi.2.1 hfix)

include e hz hk in
/-- The entire shifted span lies in the old endpoint's two-core, with the
full old endpoint seed in the shifted center's two-core. This discharges
the critical-pair alternative in the saved (5.9) shift. -/
theorem full_point_old_endpoint_core (hb : 4 < sourceDistance h)
    (u : S6) (hfull : (Rg).map π = pointCore.map (MulAut.conj u).toMonoidHom)
    (hslice : (B Rg (alpha Rg) ((sourceGeometry h).Z_normal _)).relIndex
      (U Rg (p.walk.getVert 2)) ≤ 2)
    (heligible : ¬ U Rg (p.walk.getVert 2) ≤ B Rg (alpha Rg) ((sourceGeometry h).Z_normal _)) :
    Z Rg a' ≤ Q Rg s.centerVertex ∧ s.span ≤ Q Rg a' :=
  (s.full_point_old_endpoint_alternative e hz hk hb u hfull hslice).resolve_left
    (s.full_point_not_critical_old_endpoint e hz hk hb u hfull hslice heligible)

end SmallSliceShift

include h e hz hk in
/-- The literal shifted configuration has a central line at its shifted
center and the full span commutator equals that line, for either critical
image size. Both moving covers and the original cubic kernel are retained. -/
theorem full_point_small_slice_shift_control
    (hb : 2 < sourceDistance h) (u : S6)
    (hfull : (Rg).map π = pointCore.map (MulAut.conj u).toMonoidHom)
    {a' : Vertex Rg} (p : CriticalPath Rg (sourceGeometry h) (alpha Rg) a')
    (hslice : (B Rg (alpha Rg) ((sourceGeometry h).Z_normal _)).relIndex
      (U Rg (p.walk.getVert 2)) ≤ 2) :
    ∃ s : SmallSliceShift h p, ⁅s.span,s.kernel⁆ = s.line ∧
      Nat.card s.line = 2 ∧
      s.line ≤ centralizer (stabilizer Rg s.centerVertex : Set (FreeAmalgam Rg)) ∧
      (¬ s.span ≤ B Rg s.centerVertex ((sourceGeometry h).Z_normal _)) ∧
      (4 < sourceDistance h → Z Rg a' ≤ Q Rg s.centerVertex ∧ s.span ≤ Q Rg a') := by
  have hel := full_point_critical_forward_eligible h e hz hk hb u hfull p
  have hex : Nonempty (SmallSliceShift h p) := by
    by_cases hs : (Q Rg a').relIndex (Z Rg (alpha Rg)) < 4
    · exact exists_small_slice_shift h e hz hk hb u hfull p hs hslice hel
    · obtain ⟨s,_,_⟩ := large_image_small_slice_shift h e hz hk hb p (by omega) hslice hel
      exact ⟨s⟩
  obtain ⟨s⟩ := hex
  have hspan := full_point_selected_span_forward_commutator h e hz hk hb p u hfull hslice
  have hline := forward_slice_noncentral_line h e hz hk hb p hslice hel
  refine ⟨s,?_,?_,?_,s.span_not_le_slice hb hel,
    fun hb4 => s.full_point_old_endpoint_core e hz hk hb4 u hfull hslice hel⟩
  · have hh := congrArg (Subgroup.map (MulAut.conj s.conjugator).toMonoidHom) hspan.1
    rw [map_commutator,←s.span_map] at hh
    exact hh
  · exact (card_map_of_injective (MulAut.conj s.conjugator).injective).trans hline.1
  · have hm := map_mono (f := (MulAut.conj s.conjugator).toMonoidHom) hspan.2.2
    rw [Theory.GroupTheory.map_centralizer_equiv,
      show (MulAut.conj s.conjugator : FreeAmalgam Rg → FreeAmalgam Rg) =
        (MulAut.conj s.conjugator).toMonoidHom from rfl,←Subgroup.coe_map] at hm
    have he := stabilizer_act Rg s.conjugator⁻¹ (alpha Rg)
    rw [inv_inv] at he
    rwa [←he] at hm

omit hk in
include h e hz in
/-- Whole-core consumer of the full-seed orbit and forward-line argument.
The large-image branch now has the same central shifted-line control.
Point-core equality and the remaining terminal exclusions stay explicit. -/
theorem coreExhaustion_or_cubic_full_point_central_shifts :
    CoreExhaustion L R ∨ ∃ hk : layerKernel L R = extensionKernel h,
      Function.Surjective (CubicAction.projection h e hz hk) ∧
      2 < sourceDistance h ∧
      (∀ a : Vertex Rg, color Rg a = false → Nat.card (U Rg a) = 16 ∨ Nat.card (U Rg a) = 32) ∧
      ∀ u : S6,
        (Rg).map (CubicAction.projection h e hz hk) = pointCore.map (MulAut.conj u).toMonoidHom →
        ∀ (a' : Vertex Rg) (p : CriticalPath Rg (sourceGeometry h) (alpha Rg) a'),
          (B Rg (alpha Rg) ((sourceGeometry h).Z_normal _)).relIndex
            (U Rg (p.walk.getVert 2)) ≤ 2 →
          ∃ s : SmallSliceShift h p, ⁅s.span,s.kernel⁆ = s.line ∧
            Nat.card s.line = 2 ∧
            s.line ≤ centralizer (stabilizer Rg s.centerVertex : Set (FreeAmalgam Rg)) ∧
            (¬ s.span ≤ B Rg s.centerVertex ((sourceGeometry h).Z_normal _)) ∧
      (4 < sourceDistance h → Z Rg a' ≤ Q Rg s.centerVertex ∧ s.span ≤ Q Rg a') := by
  rcases CubicEven.coreExhaustion_or_cubic_fullSymmetric h e hz with hx | ⟨hk,hs,hb⟩
  · exact Or.inl hx
  · exact Or.inr ⟨hk,hs,hb,graph_U_card h e hz hk,
      fun u hu _ p hp => full_point_small_slice_shift_control h e hz hk hb u hu p hp⟩

omit hk in
include h e hz in
/-- Literal C.1.32 application of central shifted-line control for every
small forward slice in the full point-core branch. -/
theorem rankTwo_or_cubic_full_point_central_shifts :
    RankTwoAlternatives L R ∨ ∃ hk : layerKernel L R = extensionKernel h,
      Function.Surjective (CubicAction.projection h e hz hk) ∧
      2 < sourceDistance h ∧
      (∀ a : Vertex Rg, color Rg a = false → Nat.card (U Rg a) = 16 ∨ Nat.card (U Rg a) = 32) ∧
      ∀ u : S6,
        (Rg).map (CubicAction.projection h e hz hk) = pointCore.map (MulAut.conj u).toMonoidHom →
        ∀ (a' : Vertex Rg) (p : CriticalPath Rg (sourceGeometry h) (alpha Rg) a'),
          (B Rg (alpha Rg) ((sourceGeometry h).Z_normal _)).relIndex
            (U Rg (p.walk.getVert 2)) ≤ 2 →
          ∃ s : SmallSliceShift h p, ⁅s.span,s.kernel⁆ = s.line ∧
            Nat.card s.line = 2 ∧
            s.line ≤ centralizer (stabilizer Rg s.centerVertex : Set (FreeAmalgam Rg)) ∧
            (¬ s.span ≤ B Rg s.centerVertex ((sourceGeometry h).Z_normal _)) ∧
      (4 < sourceDistance h → Z Rg a' ≤ Q Rg s.centerVertex ∧ s.span ≤ Q Rg a') :=
  (coreExhaustion_or_cubic_full_point_central_shifts h e hz).imp
    (rankTwo_of_exhaustion h e hz) id

end AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicFull
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
