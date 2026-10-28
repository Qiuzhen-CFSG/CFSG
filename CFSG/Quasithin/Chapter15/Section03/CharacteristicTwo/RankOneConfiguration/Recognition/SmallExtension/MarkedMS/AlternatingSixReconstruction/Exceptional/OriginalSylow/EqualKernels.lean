module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.OriginalSylow.UncontrolledKernels
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.OriginalSylow.SmallSlices
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.OriginalSylow.DistinctShifts
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicOmegaGeneration

import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.OriginalSylow.EndSlices
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.OriginalSylow.UncontrolledKernels
/-!
# Combined reverse-kernel lines for equal Borel movers

A quadratic actor on a critical transposition's fixed hyperplane has
involutory permutation image: its square fixes that hyperplane, hence is
in the transposition group, and parity excludes a nontrivial square.
The Borel cover calculation then bounds the combined displacement by two.

Apply this to two neighboring seeds against the same full reverse kernel.
When both displacements are nonzero, the two actual movers centralize the
common line. The zero case is excluded at a strict slice using the paired
endpoint generation: the other kernel's fixed seed span becomes normal,
so the original critical-radius theorem puts it in the Baumann slice.

EqualShifts retains the same transporter and uses these results to exclude
both trapped candidates. Both full covers, of orders sixteen and thirty-two,
and the original cubic projection kernel E are retained throughout.

Source: Meierfrankenfeld--Stellmacher (1993), (3.3) and (5.7), printed
pp.866--867,919; Aschbacher--Smith C.1.31--32, pp.135--136.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender BinaryPermutation
open scoped IsMulCommutative commutatorElement Pointwise
open Theory.SpecificGroups.SymmetricSix Theory.SpecificGroups.SymmetricSix.BinaryFlags CoreCrossing
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Exceptional.OriginalSylow
open Exhaustion Exhaustion.LargeDistance Exhaustion.LargeDistance.CubicFull
local notation "borel" => Theory.SpecificGroups.SymmetricSix.borel

private theorem square_eq_one_of_swap_power (τ g : S) (hτ : τ.IsSwap)
    (h : g^2 ∈ zpowers τ) : g^2=1 := by
  rw [mem_zpowers_iff_mem_range_orderOf,hτ.orderOf] at h
  obtain ⟨n,hn,he⟩ := Finset.mem_image.mp h
  have hnlt := Finset.mem_range.mp hn
  interval_cases n
  · simpa only [pow_zero] using he.symm
  · rw [pow_one] at he
    have hs := congrArg Equiv.Perm.sign he
    have hg : Equiv.Perm.sign g ^ 2 = 1 := Int.units_sq _
    rw [hτ.sign_eq,map_pow,hg] at hs
    exact (by decide : (-1 : ℤˣ) ≠ 1) hs |>.elim

private theorem canonical_cover_fixer
    {Y : Type*} [AddCommGroup Y] [Module (ZMod 2) Y]
    (σ : Representation (ZMod 2) S Y)
    (hm : SixCover.IsNaturalOrCore σ (MonoidHom.id S))
    (g : S)
    (hfix : ∀ v ∈ fixedSpace σ (zpowers swap45), σ g v = v) :
    g ∈ zpowers swap45 := by
  rcases hm with ⟨E,hE⟩ | ⟨E,hE⟩
  · apply (constant_displacement_iff g).mp
    intro v hv
    have hvfix := swap45_fixes_hyperplane v hv
    have hqfix : naturalRepresentation (Fin 6) swap45 (coreToNatural (Fin 6) v) =
        coreToNatural (Fin 6) v := by
      rw [←coreToNatural_equivariant,hvfix]
    have hvE : E.symm (coreToNatural (Fin 6) v) ∈ fixedSpace σ (zpowers swap45) := by
      rw [mem_fixedSpace_zpowers_iff]
      apply E.injective
      rw [hE,LinearEquiv.apply_symm_apply,MonoidHom.id_apply,hqfix]
    have hh := congrArg E (hfix _ hvE)
    rw [hE,MonoidHom.id_apply,LinearEquiv.apply_symm_apply] at hh
    have hz : coreToNatural (Fin 6) (coreRepresentation (Fin 6) g v-v) = 0 := by
      rw [map_sub,coreToNatural_equivariant,hh,sub_self]
    have hz' : ((coreRepresentation (Fin 6) g v-v : C) : Fin 6 → ZMod 2) ∈ constants (Fin 6) := by
      exact (Submodule.Quotient.mk_eq_zero _).mp (congrArg Subtype.val hz)
    obtain ⟨c,hc⟩ := Submodule.mem_span_singleton.mp hz'
    exact Submodule.mem_span_singleton.mpr ⟨c,Subtype.ext hc⟩
  · apply (fixes_orbitSpan_iff g).mp
    rw [orbitSpan_eq_hyperplane]
    intro v hv
    have hvE : E.symm v ∈ fixedSpace σ (zpowers swap45) := by
      rw [mem_fixedSpace_zpowers_iff]
      apply E.injective
      rw [hE,MonoidHom.id_apply,LinearEquiv.apply_symm_apply,
        swap45_fixes_hyperplane v hv]
    have hh := congrArg E (hfix _ hvE)
    simpa only [hE,MonoidHom.id_apply,LinearEquiv.apply_symm_apply] using hh

private theorem cover_fixer
    {Y : Type*} [AddCommGroup Y] [Module (ZMod 2) Y]
    (σ : Representation (ZMod 2) S Y)
    (hm : SixCover.IsNaturalOrCore σ (MonoidHom.id S))
    (t g : S) (hs : t.IsSwap)
    (hfix : ∀ v ∈ fixedSpace σ (zpowers t), σ g v = v) :
    g ∈ zpowers t := by
  obtain ⟨a,b,hab,rfl⟩ := hs
  obtain ⟨u,hu⟩ := isConj_iff.mp (Equiv.Perm.isConj_swap (by decide : (4:Fin 6) ≠ 5) hab)
  change u*swap45*u⁻¹ = Equiv.swap a b at hu
  have hh : u⁻¹*g*u ∈ zpowers swap45 := by
    apply canonical_cover_fixer σ hm
    intro v hv
    have huf : σ u v ∈ fixedSpace σ (zpowers (Equiv.swap a b)) := by
      rw [mem_fixedSpace_zpowers_iff]
      rw [←hu,map_mul,map_mul,Module.End.mul_apply,Module.End.mul_apply,
        σ.inv_self_apply,(mem_fixedSpace_zpowers_iff _ _ _).mp hv]
    have hf := hfix _ huf
    simp only [map_mul,Module.End.mul_apply,hf,σ.inv_self_apply]
  have hm := mem_map_of_mem (MulAut.conj u).toMonoidHom hh
  rw [MonoidHom.map_zpowers] at hm
  change u*(u⁻¹*g*u)*u⁻¹ ∈ zpowers (u*swap45*u⁻¹) at hm
  simpa only [hu,mul_assoc,
    mul_inv_cancel_left,mul_inv_cancel,mul_one] using hm

private theorem quadratic_cover_elementary
    {Y : Type*} [AddCommGroup Y] [Module (ZMod 2) Y]
    (σ : Representation (ZMod 2) S Y)
    (hm : SixCover.IsNaturalOrCore σ (MonoidHom.id S))
    (t : S) (hs : t.IsSwap) (P : Subgroup S)
    (hquad : subspaceCommutator σ
      (subspaceCommutator σ (fixedSpace σ (zpowers t)) P) P = ⊥) :
    (∀ g ∈ P, g^2=1) ∧ (∀ g ∈ P, ∀ k ∈ P, Commute g k) := by
  have hsquare (g : S) (hg : g ∈ P) : g^2=1 := by
    apply square_eq_one_of_swap_power t g hs
    apply cover_fixer σ hm t (g^2) hs
    intro v hv
    have hw : σ g v-v ∈ subspaceCommutator σ (fixedSpace σ (zpowers t)) P :=
      Submodule.subset_span ⟨g,hg,v,hv,rfl⟩
    have hh := ((subspaceCommutator_eq_bot_iff _ _ _).mp hquad) hw ⟨g,hg⟩
    change σ g (σ g v-v)=σ g v-v at hh
    simp only [sub_eq_add_neg,ZModModule.neg_eq_self,map_add] at hh
    have hh' : σ g (σ g v) + σ g v = v + σ g v := hh.trans (add_comm _ _)
    simpa only [pow_two,map_mul,Module.End.mul_apply] using add_right_cancel hh'
  refine ⟨hsquare,?_⟩
  intro g hg k hk
  have hgg := hsquare g hg
  have hkk := hsquare k hk
  have hprod := hsquare (g*k) (P.mul_mem hg hk)
  change g*k=k*g
  calc
    g*k = (g*k)⁻¹ := (inv_eq_of_mul_eq_one_right (by simpa only [pow_two] using hprod)).symm
    _ = k⁻¹*g⁻¹ := mul_inv_rev _ _
    _ = k*g := by
      rw [inv_eq_of_mul_eq_one_right (by simpa only [pow_two] using hkk),
        inv_eq_of_mul_eq_one_right (by simpa only [pow_two] using hgg)]

universe u
variable {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
  (h : SmallMSPair KnownSimple.IsKnownSimple L R) (e : CentralMarking L)
  (hz : Nat.card (center (L ⧸ pCore 2 L)) = 3)
  (hk : layerKernel L R = extensionKernel h)
local notation "M" => (L ⊔ R : Subgroup G)
local notation "Rg" => edge L R
local notation "W₀" => (⁅centralOmega L R,L.subgroupOf M⁆ : Subgroup M)
local notation "π" => CubicAction.projection h e hz hk
local instance : IsElementaryAbelian 2 W₀ := IsElementaryAbelian.of_le (commutator_le_left _ _)
open Representation.NormalElementaryQuotient

include h e hz hk in
/-- A trapped quadratic combined actor moves at most a line of the full
reverse seed kernel when its endpoint displacement escapes the starting seed. -/
theorem borel_quadratic_reverse_kernel_card
    (u : S) (hR : (Rg).map π = borel.map (MulAut.conj u).toMonoidHom)
    {a z : Vertex Rg} (p : CriticalPath Rg (sourceGeometry h) a z)
    (hp : (Q Rg z).relIndex (Z Rg a) < 4)
    (T : Subgroup (FreeAmalgam Rg))
    (hT : T ≤ Q Rg (p.walk.getVert (p.walk.length-2)))
    (hTa : T ≤ Q Rg a)
    (hKT : ⁅Z Rg z ⊓ Q Rg a,T⁆ ≤ Z Rg a)
    (hescape : ¬ ⁅T,Z Rg z⁆ ≤ Z Rg a) :
    Nat.card (⁅Z Rg z ⊓ Q Rg a,T⁆ : Subgroup (FreeAmalgam Rg)) ≤ 2 := by
  have hb := distance_gt_two h e hz hk
  have hfixed : ⁅U Rg z ⊓ centralizer (Z Rg a : Set (FreeAmalgam Rg)),T⁆ =
      ⁅Z Rg z ⊓ Q Rg a,T⁆ := by
    rw [←critical_moving_kernel_eq_fixed h e p]
    exact ((critical_kernel_predecessor_moving h e hz hb p).2.2 _ hT).symm
  have hcontrol : ¬ ⁅U Rg z,T⁆ ≤
      ⁅U Rg z ⊓ centralizer (Z Rg a : Set (FreeAmalgam Rg)),T⁆ ⊔ ⁅U Rg z,Z Rg a⁆ := by
    intro hh
    apply hescape
    rw [commutator_comm,critical_predecessor_seed_movement h e hz hb p _ hT]
    rw [hfixed] at hh
    exact hh.trans (sup_le hKT (by
      rw [commutator_comm]
      exact (commutator_mono le_rfl (DistanceEight.U_le_Z Rg z)).trans
        (critical_seed_commutator_le h p)))
  let := h.relative_normal
  obtain ⟨i,hi,hir,hiR,hiQ,hiU,hA,hP,hJ,hAr,hPr,hJr,hApi,hPpi,hJpi,hFi,hfix⟩ :=
    borel_predecessor_cover_chart h e hz hk u hR p T hT 1 (one_mem _)
  obtain ⟨⟨τ,hτ,hτswap,hτeq⟩,hcrit⟩ :=
    plane_small_critical_chart_actor h e hz hk p hp i hi hiQ hiU hA hAr
  let A := (Z Rg a).comap i
  let P := T.comap i
  let F := W₀ ⊓ centralizer (A : Set M)
  let σ : Representation (ZMod 2) S (Additive W₀) :=
    NormalElementaryQuotient.representation W₀ π (CubicEven.projection_surjective h e hz hk)
      (CubicAction.moved_projection_kernel h e hz hk)
  have hF : F.map i = U Rg z ⊓ centralizer (Z Rg a : Set (FreeAmalgam Rg)) := by
    rw [←map_inf_centralizer_of_injective i hi,hiU,hA]
  have hQ : ⁅⁅F,P⁆,P⁆ = ⊥ := by
    apply (map_injective (f := i) hi)
    rw [map_commutator,map_commutator,hF,hP,hfixed,Subgroup.map_bot]
    exact le_bot_iff.mp ((commutator_mono hKT le_rfl).trans_eq
      (le_bot_iff.mp ((commutator_mono le_rfl hTa).trans_eq
        (Z_centralizes_Q Rg a p.start_color))))
  have hFs : subgroupSpace W₀ F = fixedSpace σ (zpowers τ) := by
    rw [←hτeq]
    ext v
    change ((v.toMul : M) ∈ W₀ ∧ (v.toMul : M) ∈ centralizer (A : Set M)) ↔ _
    rw [NormalElementaryQuotient.mem_fixedSpace_image W₀ π
      (CubicEven.projection_surjective h e hz hk) (CubicAction.moved_projection_kernel h e hz hk)]
    exact and_iff_right v.toMul.property
  have hq : subspaceCommutator σ
      (subspaceCommutator σ (fixedSpace σ (zpowers τ)) (P.map π)) (P.map π) = ⊥ := by
    rw [←hFs,←subgroupSpace_commutator W₀ π (CubicEven.projection_surjective h e hz hk)
      (CubicAction.moved_projection_kernel h e hz hk) F P inf_le_left,
      ←subgroupSpace_commutator W₀ π (CubicEven.projection_surjective h e hz hk)
      (CubicAction.moved_projection_kernel h e hz hk) ⁅F,P⁆ P
        ((commutator_mono inf_le_left le_rfl).trans (commutator_le_left _ _)),hQ]
    ext v
    change (v.toMul : M) = 1 ↔ v = 0
    exact ⟨fun hv => Additive.toMul.injective (Subtype.ext hv),fun hv => hv ▸ rfl⟩
  obtain ⟨h2,hab⟩ := quadratic_cover_elementary σ (moved_subgroup_cover_model h e hz hk) τ hτswap (P.map π) hq
  have hcomm : ∀ g ∈ P.map π, Commute τ g := by
    obtain ⟨j,hj,hje⟩ := hτ
    rintro _ ⟨g,hg,rfl⟩
    rw [←hje]
    change _ * _ = _ * _
    rw [←map_mul,←map_mul]
    congr 1
    apply hi
    simp only [map_mul]
    exact (commutator_eq_bot_iff_le_centralizer.mp (Z_centralizes_Q Rg a p.start_color)
      hj (i g) (hTa hg)).symm
  have hbound := borel_cover_uncontrolled_fixed_card h e hz hk u τ (hApi hτ)
    hτswap A P hτeq hPpi h2 hab hcomm (by
      intro hh
      apply hcontrol
      have hm := map_mono (f := i) hh
      rwa [Subgroup.map_sup,map_commutator W₀ P i,hiU,hP,
        map_commutator _ P i,hF,hP,map_commutator W₀ A i,hiU,hA] at hm)
  rw [←card_map_of_injective hi,map_commutator,hF,hP,hfixed] at hbound
  exact hbound

include h e hz hk in
/-- The combined actor bounds the two displacements against one and the same
reverse kernel. If both are nonzero, the actual two movers centralize their
common line. The zero case is kept explicit. -/
theorem borel_equal_paired_kernel_line
    (u : S) (hR : (Rg).map π = borel.map (MulAut.conj u).toMonoidHom)
    {a z c d t v : Vertex Rg}
    (p : CriticalPath Rg (sourceGeometry h) a z)
    (hp : (Q Rg z).relIndex (Z Rg a) < 4)
    (hat : Adjacent Rg a t) (hct : Adjacent Rg c t)
    (hav : Adjacent Rg a v) (hdv : Adjacent Rg d v)
    (heq : edgeOffenderJoin a t = edgeOffenderJoin c t)
    (heq' : edgeOffenderJoin a v = edgeOffenderJoin d v)
    (hgen : edgeOffenderJoin a t ⊔ edgeOffenderJoin a v = stabilizer Rg a)
    (hbad : Z Rg c ≤ Q Rg (p.walk.getVert (p.walk.length-2)))
    (hbad' : Z Rg d ≤ Q Rg (p.walk.getVert (p.walk.length-2)))
    (hescape : ¬ ⁅Z Rg c,Z Rg z⁆ ≤ Z Rg a) :
    let A := Z Rg z ⊓ Q Rg a
    let H := ⁅A,Z Rg c ⊔ Z Rg d⁆
    Nat.card H = 2 ∧ ⁅A,Z Rg c⁆ = H ∧
      (⁅A,Z Rg d⁆ = ⊥ ∨
        (⁅A,Z Rg d⁆ = H ∧ H ≤ centralizer (stabilizer Rg a : Set (FreeAmalgam Rg)))) := by
  have hb := distance_gt_two h e hz hk
  have hc : color Rg c = false := by
    have h1 := adjacent_color_ne Rg hat
    have h2 := adjacent_color_ne Rg hct
    rw [p.start_color] at h1
    cases hh : color Rg c <;> cases hh' : color Rg t <;> simp_all
  have hd : color Rg d = false := by
    have h1 := adjacent_color_ne Rg hav
    have h2 := adjacent_color_ne Rg hdv
    rw [p.start_color] at h1
    cases hh : color Rg d <;> cases hh' : color Rg v <;> simp_all
  have hC := borel_equal_thompson_core_commutator h e hz hk u hR p hp hc hat hct heq
  have hD := borel_equal_thompson_core_commutator h e hz hk u hR p hp hd hav hdv heq'
  let A := Z Rg z ⊓ Q Rg a
  let T := Z Rg c ⊔ Z Rg d
  let H := ⁅A,T⁆
  have hCQ : Z Rg c ≤ Q Rg a :=
    ((Z_le_localZSpan Rg _ _).trans (localZSpan_le_V Rg
      (CFSG.Quasithin.ChapterC.Sp4Four.DistanceReduction.neighbor_distance_le_two hat hct))).trans
        ((sourceGeometry h).V_le_Q hb a p.start_color)
  have hDQ : Z Rg d ≤ Q Rg a :=
    ((Z_le_localZSpan Rg _ _).trans (localZSpan_le_V Rg
      (CFSG.Quasithin.ChapterC.Sp4Four.DistanceReduction.neighbor_distance_le_two hav hdv))).trans
        ((sourceGeometry h).V_le_Q hb a p.start_color)
  have hAC : ⁅A,Z Rg c⁆ ≤ ⁅Z Rg c,Q Rg a⁆ := by
    rw [commutator_comm]
    exact commutator_mono le_rfl inf_le_right
  have hAD : ⁅A,Z Rg d⁆ ≤ ⁅Z Rg d,Q Rg a⁆ := by
    rw [commutator_comm]
    exact commutator_mono le_rfl inf_le_right
  have hHZ : H ≤ Z Rg a := by
    dsimp only [H,T]
    rw [commutator_comm]
    apply commutator_sup_le_of_relative_normal (stabilizer Rg a) _ _ _ _
      (Z_normalized Rg a) (hCQ.trans (fun _ hx => hx.1))
      (hDQ.trans (fun _ hx => hx.1))
    · rw [commutator_comm]; exact hAC.trans (hC.1.trans inf_le_left)
    · rw [commutator_comm]; exact hAD.trans (hD.1.trans inf_le_left)
  have hcard : Nat.card H ≤ 2 := borel_quadratic_reverse_kernel_card h e hz hk u hR p hp T
    (sup_le hbad hbad') (sup_le hCQ hDQ) hHZ (by
      intro hh
      exact hescape ((commutator_mono le_sup_left le_rfl).trans hh))
  have hne : ⁅A,Z Rg c⁆ ≠ ⊥ := by
    intro he
    apply hescape
    apply small_critical_predecessor_commutator h e hz hk hb p hp (Z Rg c) hbad
    exact commutator_eq_bot_iff_le_centralizer.mp ((commutator_comm _ _).trans he)
  let := finite_Z Rg a
  let : Finite H := Finite.of_injective (inclusion hHZ) (inclusion_injective _)
  have hCH : ⁅A,Z Rg c⁆ ≤ H := commutator_mono le_rfl le_sup_left
  have hDH : ⁅A,Z Rg d⁆ ≤ H := commutator_mono le_rfl le_sup_right
  let : Finite (⁅A,Z Rg c⁆ : Subgroup (FreeAmalgam Rg)) :=
    Finite.of_injective (inclusion hCH) (inclusion_injective _)
  have hpos := (one_lt_card_iff_ne_bot ⁅A,Z Rg c⁆).mpr hne
  have hle := card_le_of_le hCH
  have hHcard : Nat.card H = 2 := by omega
  have hCH_eq : ⁅A,Z Rg c⁆ = H := eq_of_le_of_card_ge hCH (by omega)
  refine ⟨hHcard,hCH_eq,?_⟩
  by_cases hd0 : ⁅A,Z Rg d⁆ = ⊥
  · exact Or.inl hd0
  right
  let : Finite (⁅A,Z Rg d⁆ : Subgroup (FreeAmalgam Rg)) :=
    Finite.of_injective (inclusion hDH) (inclusion_injective _)
  have hdpos := (one_lt_card_iff_ne_bot ⁅A,Z Rg d⁆).mpr hd0
  have hDH_eq : ⁅A,Z Rg d⁆ = H := eq_of_le_of_card_ge hDH (by omega)
  refine ⟨hDH_eq,?_⟩
  change H ≤ centralizer (stabilizer Rg a : Set (FreeAmalgam Rg))
  apply le_centralizer_iff.mp
  rw [←hgen]
  apply sup_le
  · apply le_centralizer_iff.mp
    rw [←hCH_eq]
    exact hAC.trans (commutator_eq_bot_iff_le_centralizer.mp hC.2)
  · apply le_centralizer_iff.mp
    rw [←hDH_eq]
    exact hAD.trans (commutator_eq_bot_iff_le_centralizer.mp hD.2)
include h e hz hk in
/-- At a strict slice, the second reverse-kernel commutator cannot vanish
when the first endpoint is uncontrolled. Both actual endpoints and the
selector's generation identity are retained. -/
theorem borel_equal_strict_other_kernel_ne_bot
    (u : S) (hR : (Rg).map π = borel.map (MulAut.conj u).toMonoidHom)
    {z z' c t : Vertex Rg}
    (p : CriticalPath Rg (sourceGeometry h) (alpha Rg) z)
    (q : CriticalPath Rg (sourceGeometry h) (alpha Rg) z')
    (hp : (Q Rg z).relIndex (Z Rg (alpha Rg)) < 4)
    (hq : (Q Rg z').relIndex (Z Rg (alpha Rg)) < 4)
    (hat : Adjacent Rg (alpha Rg) t) (hct : Adjacent Rg c t)
    (heq : edgeOffenderJoin (alpha Rg) t = edgeOffenderJoin c t)
    (hgen : (edgeOffenderJoin (alpha Rg) t ⊔ Z Rg z) ⊔ Z Rg z' = stabilizer Rg (alpha Rg))
    (hbad : Z Rg c ≤ Q Rg (p.walk.getVert (p.walk.length-2)))
    (hbad' : Z Rg c ≤ Q Rg (q.walk.getVert (q.walk.length-2)))
    (hstrict : 2 < (B Rg (alpha Rg) ((sourceGeometry h).Z_normal _)).relIndex (U Rg c))
    (hescape : ¬ ⁅Z Rg c,Z Rg z⁆ ≤ Z Rg (alpha Rg)) :
    ⁅Z Rg z' ⊓ Q Rg (alpha Rg),Z Rg c⁆ ≠ ⊥ := by
  intro hz0
  have hb := distance_gt_two h e hz hk
  have ht : color Rg t = true := by
    have hh := adjacent_color_ne Rg hat
    change false ≠ color Rg t at hh
    cases he : color Rg t <;> simp_all
  have hc : color Rg c = false := by
    have hh := adjacent_color_ne Rg hct
    rw [ht] at hh
    cases he : color Rg c <;> simp_all
  let A := Z Rg z ⊓ Q Rg (alpha Rg)
  let D := Z Rg c ⊓ centralizer (A : Set (FreeAmalgam Rg))
  let J := edgeOffenderJoin c t
  let Y := D ⊔ Z Rg (alpha Rg)
  have hcore := borel_equal_thompson_core_commutator h e hz hk u hR p hp hc hat hct heq
  have hHZ : ⁅A,Z Rg c⁆ ≤ Z Rg (alpha Rg) := by
    rw [commutator_comm]
    exact (commutator_mono le_rfl inf_le_right).trans (hcore.1.trans inf_le_left)
  have hunc : ¬ ⁅Z Rg c,Z Rg z⁆ ≤ Z Rg (alpha Rg) ⊔ ⁅A,Z Rg c⁆ := by
    rw [sup_of_le_left hHZ]
    exact hescape
  obtain ⟨hcard,hAJ,_⟩ := borel_uncontrolled_reverse_kernel_mover h e hz hk u hR
    p hp hat hct hbad hunc
  have hJT : J ≤ Q Rg t :=
    (remaining_edge_thompson h e hz hk u (Or.inr hR) hc hct).2.2.1
  have hAG : A ≤ stabilizer Rg c :=
    (hAJ.trans hJT).trans (fun _ hx => hx.2 _ (adjacent_symm Rg hct))
  have hHc : ⁅A,Z Rg c⁆ ≤ Z Rg c :=
    le_normalizer_iff_commutator_le_right.mp (hAG.trans (Z_normalized Rg c))
  let := finite_Z Rg c
  let : Finite (⁅A,Z Rg c⁆ : Subgroup (FreeAmalgam Rg)) :=
    Finite.of_injective (inclusion hHc) (inclusion_injective _)
  have hsmall : Nat.card (⁅U Rg c,A⁆ : Subgroup (FreeAmalgam Rg)) ≤ 2 := by
    have hle : ⁅U Rg c,A⁆ ≤ ⁅A,Z Rg c⁆ := by
      rw [commutator_comm A]
      exact commutator_mono (DistanceEight.U_le_Z Rg c) le_rfl
    exact (card_le_of_le hle).trans hcard
  have hindex := moving_small_commutator_fixed_index h e hz hk hc A hAG hsmall
  have hDindex : D.relIndex (U Rg c) ≤ 2 := by
    have he : D ⊓ U Rg c = U Rg c ⊓ centralizer (A : Set (FreeAmalgam Rg)) := by
      dsimp only [D]
      rw [inf_right_comm,inf_of_le_right (DistanceEight.U_le_Z Rg c)]
    rw [←inf_relIndex_right D (U Rg c),he,inf_relIndex_left]
    exact hindex
  have hquad : ⁅⁅Z Rg c,J⁆,J⁆ = ⊥ :=
    remaining_edge_full_seed_quadratic h e hz hk u (Or.inr hR) hc hct
  have hab : ⁅J,J⁆ ≤ centralizer (Z Rg c : Set (FreeAmalgam Rg)) := by
    apply commutator_eq_bot_iff_le_centralizer.mp
    apply commutator_commutator_eq_bot_of_rotate
    · simpa only [commutator_comm J (Z Rg c)] using hquad
    · exact hquad
  have hJD : J ≤ normalizer (D : Set (FreeAmalgam Rg)) :=
    abelian_action_preserves_fixed J (Z Rg c) A
      ((hJT.trans (fun _ hx => hx.2 _ (adjacent_symm Rg hct))).trans (Z_normalized Rg c))
      hAJ hab
  have hJZ : J ≤ normalizer (Z Rg (alpha Rg) : Set (FreeAmalgam Rg)) :=
    (hJT.trans (fun _ hx => hx.2 _ (adjacent_symm Rg hat))).trans (Z_normalized Rg _)
  have hZcV : Z Rg c ≤ V Rg (alpha Rg) :=
    (Z_le_localZSpan Rg _ _).trans (localZSpan_le_V Rg
      (CFSG.Quasithin.ChapterC.Sp4Four.DistanceReduction.neighbor_distance_le_two hat hct))
  have hDcomm : ⁅D,Z Rg z⁆ ≤ Z Rg (alpha Rg) :=
    small_critical_predecessor_commutator h e hz hk hb p hp D
      (inf_le_left.trans hbad) inf_le_right
  have hDcomm' : ⁅D,Z Rg z'⁆ ≤ Z Rg (alpha Rg) := by
    apply (commutator_mono inf_le_left le_rfl).trans
    apply small_critical_predecessor_commutator h e hz hk hb q hq (Z Rg c) hbad'
    exact commutator_eq_bot_iff_le_centralizer.mp ((commutator_comm _ _).trans hz0)
  have hmove {w : Vertex Rg}
      (r : CriticalPath Rg (sourceGeometry h) (alpha Rg) w)
      (hm : ⁅D,Z Rg w⁆ ≤ Z Rg (alpha Rg)) :
      ⁅Y,Z Rg w⁆ ≤ Z Rg (alpha Rg) := by
    apply commutator_sup_le_of_relative_normal (stabilizer Rg (alpha Rg))
      D (Z Rg (alpha Rg)) (Z Rg w) (Z Rg (alpha Rg)) (Z_normalized Rg _)
      ((inf_le_left.trans hZcV).trans ((sourceGeometry h).V_local _ rfl hb))
      (Z_le_stabilizer Rg _) hm
    exact le_normalizer_iff_commutator_le_left.mp
      ((critical_Z_le_stabilizer Rg (sourceGeometry h) (alpha Rg) rfl
        (sourceDistance_pos h) r.critical).trans (Z_normalized Rg _))
  have hpY := hmove p hDcomm
  have hYN : stabilizer Rg (alpha Rg) ≤ normalizer (Y : Set (FreeAmalgam Rg)) := by
    rw [←hgen,heq]
    exact sup_le (sup_le
      ((le_inf hJD hJZ).trans (normalizer_inf_normalizer_le_normalizer_sup _ _))
      (le_normalizer_iff_commutator_le_left.mpr (hpY.trans le_sup_right)))
      (le_normalizer_iff_commutator_le_left.mpr ((hmove q hDcomm').trans le_sup_right))
  have hDB : D ≤ B Rg (alpha Rg) ((sourceGeometry h).Z_normal _) :=
    le_sup_left.trans (normalized_radius_le_slice_of_critical_commutator h e hz hb p Y
      (sup_le (inf_le_left.trans hZcV) (Z_le_VBall Rg _ 2)) hYN hpY)
  let : Finite (U Rg c) := Finite.of_injective (inclusion (DistanceEight.U_le_Z Rg c))
    (inclusion_injective _)
  have hbound := (relIndex_le_of_le_left hDB (index_ne_zero_of_finite :
    D.relIndex (U Rg c) ≠ 0)).trans hDindex
  omega

end AlternatingSixReconstruction.Exceptional.OriginalSylow
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
