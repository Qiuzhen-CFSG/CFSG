module
public import Theory.SpecificGroups.SymmetricSix.BinaryFlags.StrictCubeInvariant
import all Theory.SpecificGroups.SymmetricSix.BinaryFlags.StrictCubeInvariant
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.Terminal.SixteenReverseStrict
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.Terminal.SixteenSmallSelection
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.Terminal.SixteenEqualSecondBackward
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.Terminal.SourceKernelFailure
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.Terminal.SixteenCompatibleBackward
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.SixteenUnequal

/-!
# Derived-mover fixation on the full unequal-sixteen seed

The unequal opposite mover maps onto the full Sylow sixteen. Its derived
image contains the double transposition (01)(23), whose fixed space on both
six-letter covers is exactly the fixed space of the three-transposition cube.
Central generation restores every full central attachment of the seed.

Source: MS93 (5.5)(b,c), (5.12)(1), printed pp.915,924--925.
-/

public noncomputable section
open Representation Representation.BinaryOffender BinaryPermutation
open Theory.SpecificGroups.SymmetricSix.BinaryFlags
open CFSG.Quasithin.ChapterB.Offenders CFSG.Quasithin.ChapterB.Offenders.Six
open scoped commutatorElement
open Subgroup Theory.GroupTheory
open scoped commutatorElement Pointwise IsMulCommutative
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.Terminal.SixteenClosure
universe u
variable {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
  {h : SmallMSPair KnownSimple.IsKnownSimple L R} {e : CentralMarking L}
  {hz : center (L ⧸ pCore 2 L) = ⊥} {hn : InitialNatural h e hz}
  {d : Replacement L R}
local notation "edgeMover" => fun a t : Vertex d.radical =>
  SmallMover.join (U d.radical a) (Q d.radical a) (Q d.radical t) 4

private theorem core_certificate : ∀ x : Fin 6 → ZMod 2,
    (∑ i, x i) = 0 → representation (Fin 6) (swap01 * swap23) x = x →
      x 0 = x 1 ∧ x 2 = x 3 ∧ x 4 = x 5 := by
  decide +kernel

/-- In both six-letter covers, the derived involution of the Sylow sixteen
has exactly the cube fixed space. This assertion is only the finite module
calculation; it does not supply an actual local actor from graph hypotheses. -/
private theorem core_fixed_derived_le_cube (x : core (Fin 6))
    (hx : coreRepresentation (Fin 6) (swap01 * swap23) x = x) :
    x ∈ fixedSpace (coreRepresentation (Fin 6)) Theory.SpecificGroups.SymmetricSix.BinaryFlags.D := by
  apply StrictCubeInvariant.paired_fixed
  exact core_certificate x.val ((mem_core (Fin 6) x.val).mp x.property)
    (congrArg Subtype.val hx)

private theorem natural_certificate : ∀ x : Fin 6 → ZMod 2,
    (∑ i, x i) = 0 →
    (∃ c : ZMod 2, ∀ i, x ((swap01 * swap23).symm i) - x i = c) →
      x 0 = x 1 ∧ x 2 = x 3 ∧ x 4 = x 5 := by
  decide +kernel

private theorem natural_fixed_derived_le_cube (x : natural (Fin 6))
    (hx : naturalRepresentation (Fin 6) (swap01 * swap23) x = x) :
    x ∈ fixedSpace (naturalRepresentation (Fin 6)) Theory.SpecificGroups.SymmetricSix.BinaryFlags.D := by
  obtain ⟨y,rfl⟩ := coreToNatural_surjective x
  have hh := congrArg Subtype.val hx
  have he : deletedRepresentation (Fin 6) (swap01 * swap23)
      ((constants (Fin 6)).mkQ y.val) = (constants (Fin 6)).mkQ y.val := hh
  have hp := natural_certificate y.val ((mem_core (Fin 6) y.val).mp y.property)
    ((deleted_fixed_iff _ _).mp he)
  intro g
  exact (coreToNatural_equivariant g.val y).symm.trans
    (congrArg (coreToNatural (Fin 6)) (StrictCubeInvariant.paired_fixed y hp g))

private theorem derived_actor_mem : swap01 * swap23 ∈ ⁅sylowCarrier,sylowCarrier⁆ := by
  have he : ⁅sylowWords 1,sylowWords 8⁆ = swap01 * swap23 := by decide +kernel
  rw [←he]
  exact commutator_mem_commutator ((mem_sylowCarrier_iff _).mpr ⟨1,rfl⟩)
    ((mem_sylowCarrier_iff _).mpr ⟨8,rfl⟩)

private theorem fixed_imp_conjugate {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    (ρ : Representation (ZMod 2) (Equiv.Perm (Fin 6)) V)
    (A C : Subgroup (Equiv.Perm (Fin 6)))
    (hfix : fixedSpace ρ A ≤ fixedSpace ρ C) (u : Equiv.Perm (Fin 6)) :
    fixedSpace ρ (A.map (MulAut.conj u).toMonoidHom) ≤
      fixedSpace ρ (C.map (MulAut.conj u).toMonoidHom) := by
  intro x hx
  have hleft (v : V) : ρ u⁻¹ (ρ u v) = v := by
    rw [←Module.End.mul_apply,←map_mul,inv_mul_cancel,map_one,Module.End.one_apply]
  have hright (v : V) : ρ u (ρ u⁻¹ v) = v := by
    rw [←Module.End.mul_apply,←map_mul,mul_inv_cancel,map_one,Module.End.one_apply]
  have hx0 : ρ u⁻¹ x ∈ fixedSpace ρ A := by
    intro a
    change ρ a.val (ρ u⁻¹ x) = ρ u⁻¹ x
    have hh := congrArg (ρ u⁻¹)
      (hx ⟨(MulAut.conj u) a.val,mem_map_of_mem _ a.property⟩)
    change ρ u⁻¹ (ρ (u*a.val*u⁻¹) x) = ρ u⁻¹ x at hh
    simpa only [map_mul,Module.End.mul_apply,hleft] using hh
  rintro ⟨g,hg⟩
  obtain ⟨a,ha,rfl⟩ := hg
  have hh := congrArg (ρ u) (hfix hx0 ⟨a,ha⟩)
  change ρ u (ρ a (ρ u⁻¹ x)) = ρ u (ρ u⁻¹ x) at hh
  change ρ (u*a*u⁻¹) x = x
  simpa only [map_mul,Module.End.mul_apply,hright] using hh

private theorem model_fixer_transfer {M N : Type*}
    [AddCommGroup M] [Module (ZMod 2) M]
    [AddCommGroup N] [Module (ZMod 2) N]
    (σ : Representation (ZMod 2) (Equiv.Perm (Fin 6)) M)
    (τ : Representation (ZMod 2) (Equiv.Perm (Fin 6)) N)
    (E : M ≃ₗ[ZMod 2] N) (hE : ∀ g v, E (σ g v) = τ g (E v))
    (A C : Subgroup (Equiv.Perm (Fin 6)))
    (hf : fixedSpace τ A ≤ fixedSpace τ C) :
    fixedSpace σ A ≤ fixedSpace σ C := by
  intro v hv
  have he : E v ∈ fixedSpace τ A := by
    intro a
    exact (hE a.val v).symm.trans (congrArg E (hv a))
  intro c
  apply E.injective
  exact (hE c.val v).trans (hf he c)

private theorem cover_derived_fixer (s : FullSymmetricAction h e hz hn d)
    (u : Equiv.Perm (Fin 6)) (J E : Subgroup d.overgroup)
    (hJ : J.map s.projection = (D 6).map (MulAut.conj u).toMonoidHom)
    (hE : E.map s.projection = sylowCarrier.map (MulAut.conj u).toMonoidHom) :
    replacementMoved d ⊓ centralizer ((⁅E,E⁆ : Subgroup d.overgroup) : Set d.overgroup) ≤
      centralizer (J : Set d.overgroup) := by
  let := replacementMoved_normal h d
  let σ := coverAction s
  have hker := s.projection_kernel.trans (moved_centralizer s).symm
  have hf : fixedSpace σ ((⁅E,E⁆ : Subgroup d.overgroup).map s.projection) ≤
      fixedSpace σ (J.map s.projection) := by
    rw [map_commutator,hE,hJ,←map_commutator,←SixteenSmall.cube_eq]
    rcases cover_model s with ⟨F,hF⟩ | ⟨F,hF⟩
    · apply model_fixer_transfer σ (naturalRepresentation (Fin 6)) F hF
      apply fixed_imp_conjugate
      intro x hx
      exact natural_fixed_derived_le_cube x (hx ⟨_,derived_actor_mem⟩)
    · apply model_fixer_transfer σ (coreRepresentation (Fin 6)) F hF
      apply fixed_imp_conjugate
      intro x hx
      exact core_fixed_derived_le_cube x (hx ⟨_,derived_actor_mem⟩)
  intro x hx
  let v : Additive (replacementMoved d) := Additive.ofMul ⟨x,hx.1⟩
  have hv := (NormalElementaryQuotient.mem_fixedSpace_image (replacementMoved d)
    s.projection s.surjective hker ⁅E,E⁆ v).mpr hx.2
  exact (NormalElementaryQuotient.mem_fixedSpace_image (replacementMoved d)
    s.projection s.surjective hker J v).mp (hf hv)

private theorem supplement_of_index_two {F : Type*} [Group F]
    (E A T : Subgroup F) (hET : E ≤ T) (hAT : A ≤ T)
    (hi : E.relIndex T = 2) (hne : ¬ A ≤ E) : E ⊔ A = T := by
  have hST : E ⊔ A ≤ T := sup_le hET hAT
  have hm := relIndex_mul_relIndex E (E ⊔ A) T le_sup_left hST
  rw [hi] at hm
  have hd : E.relIndex (E ⊔ A) ∣ 2 := ⟨(E ⊔ A).relIndex T,by omega⟩
  rcases Nat.prime_two.eq_one_or_self_of_dvd _ hd with he | he
  · exact (hne (le_sup_right.trans (relIndex_eq_one.mp he))).elim
  · rw [he] at hm
    have hone : (E ⊔ A).relIndex T = 1 := by omega
    exact le_antisymm hST (relIndex_eq_one.mp hone)

include e hz hn in
/-- On unequal neighboring movers, fixing the opposite mover's derived
subgroup fixes the original cube on the entire seed, including its central
attachment. No residual-membership claim about that derived subgroup is used. -/
theorem unequal_derived_fixer_knownSimple
    (hcard : Nat.card (d.radical.map (SourceReduction.projection h e hz hn d)) = 16)
    (hb : 2 < replacementDistance h d)
    {a c t : Vertex d.radical} (ha : color d.radical a = false)
    (hat : Adjacent d.radical a t) (hct : Adjacent d.radical c t)
    (hne : edgeMover c t ≠ edgeMover a t)
    (hgen : X d.radical a = U d.radical a ⊔
      (X d.radical a ⊓ centralizer (stabilizer d.radical a : Set (FreeAmalgam d.radical)))) :
    Z d.radical a ⊓ centralizer
      ((⁅edgeMover c t,edgeMover c t⁆ : Subgroup (FreeAmalgam d.radical)) : Set _) ≤
      centralizer (edgeMover a t : Set (FreeAmalgam d.radical)) := by
  let s := fullSymmetricAction_knownSimple h e hz hn d hb
  have hcent := DistanceTwo.centralLayer_knownSimple G L R h e hz hn d
  have ht : color d.radical t = true := by
    have hh := adjacent_color_ne d.radical hat
    rw [ha] at hh
    cases hh' : color d.radical t <;> simp_all
  have hc : color d.radical c = false := by
    have hh := adjacent_color_ne d.radical hct
    rw [ht] at hh
    cases hh' : color d.radical c <;> simp_all
  have hcoords : ∃ i : d.overgroup →* FreeAmalgam d.radical, Function.Injective i ∧
      i.range = stabilizer d.radical a ∧ d.radical.map i = Q d.radical t ∧
      (pCore 2 d.overgroup).map i = Q d.radical a ∧
      (replacementMoved d).map i = U d.radical a := by
    obtain ⟨g,hg|hg⟩ := (adjacent_iff_exists_common d.radical a t).mp hat
    · rcases hg with ⟨hga,hgt⟩
      rw [hga,hgt]
      let i := (MulAut.conj g⁻¹).toMonoidHom.comp (embedM d.radical)
      refine ⟨i,(MulAut.conj g⁻¹).injective.comp (embedM_injective d.radical),?_,?_,?_,?_⟩
      · rw [MonoidHom.range_comp]
        have he : (embedM d.radical).range = stabilizer d.radical (alpha d.radical) :=
          (stabilizer_m_base d.radical).symm
        rw [he]
        simpa only [alpha,act_mVertex,one_mul] using (stabilizer_act d.radical g (alpha d.radical)).symm
      · have he := Q_act d.radical g (beta d.radical)
        rw [Q_beta] at he
        simpa only [beta,act_hVertex,one_mul,map_map] using he.symm
      · have he := Q_act d.radical g (alpha d.radical)
        rw [Q_alpha d.radical (replacement_radical_isPGroup h d) (replacement_core_le_radical h d)] at he
        simpa only [alpha,act_mVertex,one_mul,map_map] using he.symm
      · have he := U_act d.radical g (alpha d.radical)
        rw [hcent.U_eq_moved] at he
        simpa only [alpha,act_mVertex,one_mul,map_map] using he.symm
    · rw [hg.1] at ha
      cases ha
  obtain ⟨i,hinj,hir,hiR,hiQ,hiU⟩ := hcoords
  let J₀ := SmallMover.join (replacementMoved d) (pCore 2 d.overgroup) d.radical 4
  let J := edgeMover a t
  let E := edgeMover c t
  let E₀ := E.comap i
  let Z₀ := (Z d.radical a).comap i
  have hJmap : J₀.map i = J := by
    rw [SmallMover.join_map i hinj,hiU,hiQ,hiR]
  have hET : E ≤ Q d.radical t := SmallMover.join_le _ _ _ _
  have hEr : E ≤ i.range := hET.trans
    (hir ▸ (show Q d.radical t ≤ stabilizer d.radical a from
      fun _ hx => hx.2 a (adjacent_symm d.radical hat)))
  have hEmap : E₀.map i = E := map_comap_eq_self hEr
  have hnot : ¬ Q d.radical a ≤ E := fun hcore =>
    SixteenUnequal.sixteen_unequal_containing_core_not_centrally_generated_knownSimple
      (e := e) (hz := hz) (hn := hn) hb hcard ha hat hct hne hcore hgen
  obtain ⟨_,_,_,hEi,_,_⟩ := SixteenUnequal.sixteen_edge_small_mover_knownSimple
    (e := e) (hz := hz) (hn := hn) hb hcard hc hct
  have hsup : E ⊔ Q d.radical a = Q d.radical t :=
    supplement_of_index_two E _ _ hET (Q_le_adjacent_h d.radical ht hat) hEi hnot
  have hsup₀ : E₀ ⊔ pCore 2 d.overgroup = d.radical := by
    apply map_injective hinj
    rw [Subgroup.map_sup,hEmap,hiQ,hiR]
    exact hsup
  obtain ⟨u,hN,_,hj,himage,_⟩ := Nonelementary.normalizer_small_movers_knownSimple
    (e := e) (hz := hz) (hn := hn) (SixteenUnequal.sixteen_nonelementary hcard) hb
  have hnormal := SylowLarge.sixteen_radical_normalizer_knownSimple
    (e := e) (hz := hz) (hn := hn) hb hcard
  have hJimage : J₀.map s.projection = (D 6).map (MulAut.conj u).toMonoidHom := by
    rw [hnormal] at hj himage
    rw [show J₀ = _ from hj]
    exact himage
  have hRimage : d.radical.map s.projection = sylowCarrier.map (MulAut.conj u).toMonoidHom := by
    rwa [hnormal] at hN
  have hEimage : E₀.map s.projection = sylowCarrier.map (MulAut.conj u).toMonoidHom := by
    rw [←hRimage,←hsup₀,Subgroup.map_sup,←s.projection_kernel,Subgroup.map_ker_self,sup_bot_eq]
  have hlocal := cover_derived_fixer s u J₀ E₀ hJimage hEimage
  have hZrange : Z d.radical a ≤ i.range := (Z_le_stabilizer d.radical a).trans_eq hir.symm
  have hZmap : Z₀.map i = Z d.radical a := map_comap_eq_self hZrange
  have hXZ := SylowPairedFixer.central_generation_eq_seed (h := h) ha hat hgen
  have hUZ : replacementMoved d ≤ Z₀ := by
    intro x hx
    exact DistanceEight.U_le_Z d.radical a (hiU ▸ mem_map_of_mem i hx)
  have hZsup : Z₀ ≤ replacementMoved d ⊔ center d.overgroup := by
    apply (map_le_map_iff_of_injective hinj).mp
    rw [Subgroup.map_sup,hiU,hZmap,←hXZ,hgen]
    refine sup_le le_sup_left (le_trans ?_ le_sup_right)
    intro x hx
    obtain ⟨y,hy⟩ := hZrange (hXZ ▸ hx.1)
    refine ⟨y,?_,hy⟩
    apply mem_center_iff.mpr
    intro r
    apply hinj
    simpa only [map_mul,hy] using (hx.2 (i r) (hir ▸ ⟨r,rfl⟩))
  intro x hx j hj
  obtain ⟨y,hy⟩ := hZrange hx.1
  have hyZ : y ∈ Z₀ := by change i y ∈ Z d.radical a; rw [hy]; exact hx.1
  have hyfix : y ∈ centralizer ((⁅E₀,E₀⁆ : Subgroup d.overgroup) : Set d.overgroup) := by
    intro k hk
    apply hinj
    have hk' : i k ∈ (⁅E,E⁆ : Subgroup (FreeAmalgam d.radical)) := by
      rw [←hEmap,←map_commutator]
      exact mem_map_of_mem i hk
    simpa only [map_mul,hy] using hx.2 (i k) hk'
  obtain ⟨w,hw,v,hv,rfl⟩ := mem_sup_of_normal_right.mp (hZsup hyZ)
  have hvfix : v ∈ centralizer ((⁅E₀,E₀⁆ : Subgroup d.overgroup) : Set d.overgroup) :=
    fun k _ => mem_center_iff.mp hv k
  have hwfix : w ∈ centralizer ((⁅E₀,E₀⁆ : Subgroup d.overgroup) : Set d.overgroup) := by
    have hh := (centralizer ((⁅E₀,E₀⁆ : Subgroup d.overgroup) : Set d.overgroup)).mul_mem hyfix
      ((centralizer ((⁅E₀,E₀⁆ : Subgroup d.overgroup) : Set d.overgroup)).inv_mem hvfix)
    simpa only [mul_inv_cancel_right] using hh
  have hyJ : w*v ∈ centralizer (J₀ : Set d.overgroup) :=
    (centralizer (J₀ : Set d.overgroup)).mul_mem (hlocal ⟨hw,hwfix⟩)
      (fun k _ => mem_center_iff.mp hv k)
  change j ∈ J at hj
  rw [←hJmap] at hj
  obtain ⟨k,hk,rfl⟩ := hj
  simpa only [map_mul,hy] using congrArg i (hyJ k hk)

end AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.Terminal.SixteenClosure
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
